import Untyped.Subst
import Untyped.Term

instance inst_Lazy {T : Type} [Repr T] : Repr (Unit -> T) where
  reprPrec := λ _ => λ _ => .text "lazy"

inductive Value : Type where
| var : Nat -> List (Unit -> Value) -> Value
| lam : Value -> (Term × List (Unit -> Value)) -> Value
deriving Repr

instance inst_evalInhabited : Inhabited (List Term -> Term -> Value) where
  default := λ _ => λ _ => Value.var 0 []

-- partial def eval : List Value -> Term -> Value
-- | Γ, .var x => eval Γ (List.getD Γ x (.var x))
-- | Γ, .app f a =>
--   match eval Γ f with
--   | .var x Γ => .var x (a::Γ)
--   | .lam _ (t, Γ) => eval (a::Γ) t
-- | Γ, .lam A t => .lam (eval Γ A) (.mk t Γ)

def eval : Nat -> List (Unit -> Value) -> Term -> Value
| 0, _, _ => .var 0 []
| _ + 1, Γ, .var x => List.getD Γ x (λ _ => .var x []) ()
| g + 1, Γ, .app f a =>
  let a' := λ _ => eval (g + 1) Γ a
  match eval (g + 1) Γ f with
  | .var x Γ => .var x (a'::Γ)
  | .lam _ (t, Γ) => eval g (a'::Γ) t
| g + 1, Γ, .lam A t => .lam (eval (g + 1) Γ A) (t, Γ)

#eval eval 0 [] (.lam (.var 0) (.var 0))

inductive Eval : Nat -> List (Unit -> Value) -> Term -> Value -> Prop
| var :
  (h : x < Γ.length) ->
  Eval g Γ (.var x) (List.get Γ (Fin.mk x h) ())
| app_var :
  Eval g Γ a (a' ()) ->
  Eval g Γ f (.var x Γ) ->
  Eval g Γ (.app f a) (.var x (a'::Γ))
| app_lam :
  Eval (g + 1) Γ a (a' ()) ->
  Eval (g + 1) Γ f (.lam _ (t, Γ)) ->
  Eval g (a'::Γ) t t' ->
  Eval (g + 1) Γ (.app f a) t'
| lam :
  Eval g Γ A A' ->
  Eval g Γ (.lam A t) (.lam A' (t, Γ))

def vconv : Nat -> Nat -> Value -> Value -> Bool
| _, _, .var x [], .var y [] => x == y
| g, ℓ, .var x (.cons h1 t1), .var y (.cons h2 t2) =>
  vconv g ℓ (.var x t1) (.var y t2)
  && vconv g ℓ (h1 ()) (h2 ())
| g + 1, ℓ, .lam A1 (t1, Γ1), .lam A2 (t2, Γ2) =>
  let t1' := eval (g + 1) ((λ _ => .var ℓ [])::Γ1) t1
  let t2' := eval (g + 1) ((λ _ => .var ℓ [])::Γ2) t2
  vconv (g + 1) ℓ A1 A2
  && vconv g (ℓ + 1) t1' t2'
| _, _, _, _ => false

inductive VConv : Nat -> Nat -> Value -> Value -> Prop where
| var_empty : VConv g ℓ (.var x []) (.var x [])
| var_cons :
  VConv g ℓ (h1 ()) (h2 ()) ->
  VConv g ℓ (.var x t1) (.var y t2) ->
  VConv g ℓ (.var x (h1 :: t1)) (.var y (h2 :: t2))
| lam :
  Eval (g + 1) ((λ _ => .var ℓ [])::Γ1) t1 t1' ->
  Eval (g + 1) ((λ _ => .var ℓ [])::Γ2) t2 t2' ->
  VConv (g + 1) ℓ A1 A2 ->
  VConv g (ℓ + 1) t1' t2' ->
  VConv (g + 1) ℓ (.lam A1 (t1, Γ1)) (.lam A2 (t2, Γ2))

def conv : Nat -> Term -> Term -> Bool
| g, t1, t2 =>
  let t1' := eval g [] t1
  let t2' := eval g [] t2
  vconv g 0 t1' t2'

inductive Conv : Nat -> Term -> Term -> Prop where
| conv :
  Eval g Γ a a' ->
  Eval g Γ b b' ->
  VConv g 0 a' b' ->
  Conv g a b

-- def build_spine : Term -> List Term -> Term
-- | t, [] => t
-- | t, .cons hd tl => build_spine (.app t hd) tl

-- def quote : Nat -> Value -> Term
-- | g, .var x Γ => sorry
-- | g, .lam A (t, Γ) =>
--   let A' := quote g A
--   let t' := quote g (eval g ((λ _ => .var 0 []) :: Γ) t)
--   .lam A' t'
