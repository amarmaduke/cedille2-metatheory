
import Common

namespace Cedille

  inductive Projection where
  | first
  | second

  instance : OfNat Projection 1 where
    ofNat := Projection.first

  instance : OfNat Projection 2 where
    ofNat := Projection.second

  inductive Mode where
  | free
  | erased
  | type

  notation "m0" => Mode.erased
  notation "mt" => Mode.type
  notation "mf" => Mode.free

  inductive Binder where
  | lam (m : Mode)
  | pi (m : Mode)
  | inter

  inductive Constructor where
  | app (m : Mode)
  | pair
  | proj (i : Projection)
  | eq
  | refl
  | subst
  | promote
  | delta
  | phi

  inductive Constant where
  | typeU : Constant
  | kindU : Constant

  notation:300 "Term" => @Syntax Binder Constructor Constant

  def const (k : Constant) : Term := Syntax.const k
  def typeu : Term := Syntax.const Constant.typeU
  def kindu : Term := Syntax.const Constant.kindU
  def free (x : Name) : Term := Syntax.free x
  def bound (i : Nat) : Term := Syntax.bound i
  def lam (m : Mode) (t1 : Term) (t2 : Term) : Term
    := Syntax.bind (Binder.lam m) t1 t2
  def pi (m : Mode) (t1 : Term) (t2 : Term) : Term
    := Syntax.bind (Binder.pi m) t1 t2
  def inter (t1 : Term) (t2 : Term) : Term := Syntax.bind Binder.inter t1 t2
  def app (m : Mode) (t1 t2 : Term) : Term
    := Syntax.ctor (Constructor.app m) t1 t2 kindu
  def pair (t1 t2 t3 : Term) : Term := Syntax.ctor Constructor.pair t1 t2 t3
  def proj (n : Projection) (t : Term) : Term := Syntax.ctor (Constructor.proj n) t kindu kindu
  def eq (t1 t2 t3 : Term) : Term := Syntax.ctor Constructor.eq t1 t2 t3
  def refl (t : Term) : Term := Syntax.ctor Constructor.refl t kindu kindu
  def subst (t1 t2 : Term) : Term := Syntax.ctor Constructor.subst t1 t2 kindu
  def promote (t : Term) : Term := Syntax.ctor Constructor.promote t kindu kindu
  def delta (t : Term) : Term := Syntax.ctor Constructor.delta t kindu kindu
  def phi (t1 t2 : Term) : Term := Syntax.ctor Constructor.phi t1 t2 kindu

  def fv (t : Term) := Syntax.fv t
  def lc (i : Nat) (t : Term) := Syntax.lc i t
  def size (t : Term) := Syntax.size t
  def shift (t : Term) (a c : Nat) := Syntax.shift t a c

  notation:400 a:400 " @ω " b:401 => app mf a b
  notation:400 a:400 " @0 " b:401 => app m0 a b
  notation:400 a:400 " @τ " b:401 => app mt a b

  -- notation:200 "[" i:200 " := " x:200 "]" t:200 => @Syntax.opn Binder Constructor Constant i x t
  -- notation:200 "[" i:200 " =: " x:200 "]" t:200 => @Syntax.cls Binder Constructor Constant i x t
  -- notation:200 "{" i:200 " |-> " x:200 "}" t:200 => @Syntax.opn Binder Constructor Constant i (free x) t
  -- notation:200 "{" i:200 " <-| " x:200 "}" t:200 => @Syntax.cls Binder Constructor Constant (bound i) x t

  syntax "ᴎ" ident "," term : term
  macro_rules | `(ᴎ $id , $F) => `(∃ (S : FvSet!), ($id : Name) -> $id ∉ S -> $F)

  def idt : Term := pi m0 typeu (pi mf (bound 0) (bound 1))

  def cbool : Term := pi m0 typeu (pi mf (bound 0) (pi mf (bound 1) (bound 2)))
  def ctt : Term := lam m0 typeu (lam mf (bound 0) (lam mf (bound 1) (bound 1)))
  def cff : Term := lam m0 typeu (lam mf (bound 0) (lam mf (bound 1) (bound 0)))

  def erase (t : Term) : Term :=
    match t with
    | Syntax.free x => free x
    | Syntax.bound i => bound i
    | Syntax.const c => const c
    | Syntax.bind (Binder.lam m) t1 t2 =>
      match m with
      | m0 => erase t2
      | mt => lam mt (erase t1) (erase t2)
      | mf => lam mf kindu (erase t2)
    | Syntax.bind (Binder.pi m) t1 t2 => pi m (erase t1) (erase t2)
    | Syntax.bind Binder.inter t1 t2 => inter (erase t1) (erase t2)
    | Syntax.ctor (Constructor.app m) t1 t2 _ =>
      match m with
      | m0 => erase t1
      | m => app m (erase t1) (erase t2)
    | Syntax.ctor Constructor.pair t1 _t2 _ => erase t1
    | Syntax.ctor (Constructor.proj _) t _ _ => erase t
    | Syntax.ctor Constructor.eq t1 t2 t3 => eq (erase t1) (erase t2) (erase t3)
    | Syntax.ctor Constructor.refl _t _ _ => lam mf kindu (bound 0)
    | Syntax.ctor Constructor.subst t1 _ _ => erase t1
    | Syntax.ctor Constructor.promote t _ _ => erase t
    | Syntax.ctor Constructor.delta t _ _ => erase t
    | Syntax.ctor Constructor.phi t1 _t2 _t3 => erase t1

  inductive Red : Term -> Term -> Sort _ where
  | beta {m t1 t2 t3} : Red (app m (lam m t1 t2) t3) ([0 := t3]t2)
  | fst : Red (proj 1 (pair t1 t2 t3)) t1
  | snd : Red (proj 2 (pair t1 t2 t3)) t2
  | subst : Red (subst (refl t1) t2) (lam mf (t2 @τ t1) (bound 0))
  | promote : Red (promote (refl (proj i t))) (refl t)
  | bind1 : Red t1 t1' -> Red (Syntax.bind k t1 t2) (Syntax.bind k t1' t2)
  | bind2 : Red t2 t2' -> Red (Syntax.bind k t1 t2) (Syntax.bind k t1 t2')
  | ctor1 : Red t1 t1' -> Red (Syntax.ctor k t1 t2 t3) (Syntax.ctor k t1' t2 t3)
  | ctor2 : Red t2 t2' -> Red (Syntax.ctor k t1 t2 t3) (Syntax.ctor k t1 t2' t3)
  | ctor3 : Red t3 t3' -> Red (Syntax.ctor k t1 t2 t3) (Syntax.ctor k t1 t2 t3')

  notation:150 t1:150 " -β> " t2:150 => Red t1 t2

  inductive RedStar : Term -> Term -> Prop where
  | refl : RedStar t t
  | step : t1 -β> t2 -> RedStar t2 t3 -> RedStar t1 t3

  notation:150 t1:150 " -β>* " t2:150 => RedStar t1 t2
  notation:150 t1:150 " -β>+ " t2:150 => ∃ k : Term, t1 -β> k ∧ k -β>* t2

  inductive BetaConv : Term -> Term -> Prop where
  | conv : t1 -β>* t -> t2 -β>* t -> BetaConv t1 t2

  notation:150 t1:150 " =β= " t2:150 => BetaConv t1 t2

  inductive Conv : Term -> Term -> Prop where
  | conv :
    t1 -β>* t1' ->
    t2 -β>* t2' ->
    (erase t1') =β= (erase t2') ->
    Conv t1 t2

  notation:150 t1:150 " === " t2:150 => Conv t1 t2

  inductive PseObj : Term -> Prop
  | ax : PseObj (const K)
  | var : PseObj (free x)
  | bind :
    k ≠ (Binder.lam m0) ->
    PseObj A ->
    ∀ S: FvSet!, (∀ x ∉ S, PseObj ({0 |-> x}B)) ->
    PseObj (Syntax.bind k A B)
  | lam :
    PseObj A ->
    ∀ S: FvSet!, (∀ x ∉ S, PseObj ({0 |-> x}t)) ->
    ∀ S: FvSet!, (∀ x ∉ S, x ∉ (fv ∘ erase) ({0 |-> x}t)) ->
    PseObj (lam m0 A t)
  | pair : PseObj t -> PseObj s -> PseObj T ->
    erase t =β= erase s ->
    PseObj (pair t s T)
  | ctor :
    k ≠ Constructor.pair ->
    PseObj t1 ->
    PseObj t2 ->
    PseObj t3 ->
    PseObj (Syntax.ctor k t1 t2 t3)

  namespace Mode
    def pi_domain (m : Mode) (K : Constant) : Term :=
      match m with
      | mf => typeu
      | mt => const K
      | m0 => const K

    def pi_codomain (m : Mode) : Term :=
      match m with
      | mf => typeu
      | mt => kindu
      | m0 => typeu
  end Mode

  mutual

  inductive Infer : Map! Term -> Term -> Term -> Prop
  -- Basic
  | ax :
    Wf Γ ->
    Infer Γ typeu kindu
  | var :
    Wf Γ ->
    (x, A) ∈ Γ ->
    Infer Γ (free x) A
  -- Functions
  | pi :
    ConInfer Γ A (Mode.pi_domain m K) ->
    ∀ S: FvSet!, (∀ x ∉ S, ConInfer (Γ ++ [x:A]) ({0 |-> x}B) (Mode.pi_codomain m)) ->
    Infer Γ (pi m A B) (Mode.pi_codomain m)
  | lam :
    ConInfer Γ A (Mode.pi_domain m K) ->
    ∀ S: FvSet!, (∀ x ∉ S, Infer (Γ ++ [x:A]) ({0 |-> x}t) ({0 |-> x}B)) ->
    ∀ S: FvSet!, (∀ x ∉ S, ConInfer (Γ ++ [x:A]) ({0 |-> x}B) (Mode.pi_codomain m)) ->
    ∀ S: FvSet!, (m = m0 -> ∀ x ∉ S, x ∉ (fv ∘ erase) ({0 |-> x}t)) ->
    Infer Γ (lam m A t) (pi m A B)
  | app :
    ConInfer Γ f (pi m A B) ->
    Check Γ a A ->
    Infer Γ (app m f a) ([0 := a]B)
  -- Intersections
  | inter :
    ConInfer Γ A typeu ->
    ∀ S: FvSet!, (∀ x ∉ S, ConInfer (Γ ++ [x:A]) ({0 |-> x}B) typeu) ->
    Infer Γ (inter A B) typeu
  | pair :
    ConInfer Γ T (pi mt A B) ->
    ConInfer Γ A typeu ->
    ∀ S: FvSet!, (∀ x ∉ S, ConInfer (Γ ++ [x:A]) ({0 |-> x}B) typeu) ->
    Check Γ t A ->
    ∀ S:FvSet!, (∀ x ∉ S, Check Γ s ([0 := t]B)) ->
    t === s ->
    Infer Γ (pair t s T) (inter A B)
  | fst :
    ConInfer Γ t (inter A B) ->
    Infer Γ (proj 1 t) A
  | snd :
    ConInfer Γ t (inter A B) ->
    Infer Γ (proj 2 t) ([0 := proj 1 t]B)
  -- Equality
  | eq :
    ConInfer Γ A typeu ->
    Check Γ a A ->
    Check Γ b A ->
    Infer Γ (eq A a b) typeu
  | refl :
    Infer Γ t A ->
    ConInfer Γ A typeu ->
    Infer Γ (refl t) (eq A t t)
  | subst :
    ConInfer Γ e (eq A a b) ->
    Check Γ P (pi mt A typeu) ->
    Infer Γ (subst e P) (pi mf (P @τ a) (P @τ b))
  | promote :
    ConInfer Γ e (eq T (proj i a) (proj j b)) ->
    ConInfer Γ a (inter A B) ->
    Check Γ b (inter A B) ->
    Infer Γ (promote e) (eq (inter A B) a b)
  | phi :
    ConInfer Γ f (pi mf A (inter A' B)) ->
    A === A' ->
    Check Γ e (pi mf A (eq A a (proj 1 (f @ω a)))) ->
    fv (erase e) = [] ->
    Infer Γ (phi f e) (pi mf A (inter A' B))
  | delta :
    Check Γ e (eq cbool ctt cff) ->
    Infer Γ (delta e) (pi m0 typeu (bound 0))

  inductive ConInfer : (Map! Term) -> Term -> Term -> Prop where
  | infer :
    Infer Γ t A ->
    A -β>* B ->
    ConInfer Γ t B

  inductive Check : (Map! Term) -> Term -> Term -> Prop where
  | check :
    Infer Γ t A ->
    ConInfer Γ B (const K) ->
    A === B ->
    Check Γ t B

  inductive Wf : (Map! Term) -> Prop where
  | nil : Wf List.nil
  | append : x ∉ (Map.fv Γ) -> Wf Γ -> ConInfer Γ A (const K) -> Wf (Γ ++ [x : A])

  end

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Infer Γ t A
  notation:170 Γ:170 " ⊢ " t:170 " >: " A:170 => ConInfer Γ t A
  notation:170 Γ:170 " ⊢ " t:170 " =: " A:170 => Check Γ t A
  notation:170 "⊢ " Γ:170 => Wf Γ

  -- namespace Infer
  --   def simple_rec (P : ∀ n, Map! (Term) -> Term -> Term -> Prop) := @Infer.rec
  --     (λ n Γ t a _ => @P n Γ t a)
  --     (λ n Γ t a _ => @P n Γ t a)
  --     (λ n Γ t a _ => @P n Γ t a)
  --     (λ _ _ => True)
  -- end Infer

end Cedille
