
import Common
import CC.Model
import Realizer

namespace CC.Model

  variable [M : CCModel]

  structure Interp (X : Type u) where
    i : VarMap X -> X
    tm : VarMap Realizer.Term -> Realizer.Term

  def vnil := VarMap.nil M.props

  abbrev Term := Option (Interp M.X)

  def dummy_term : Realizer.Term := .var 0

  def tm (j : VarMap Realizer.Term) : Term -> Realizer.Term
  | .some f => Interp.tm f j
  | .none => dummy_term

  def dummy_interp : M.X := M.props

  def interp (j : VarMap M.X) : Term -> M.X
  | .some f => Interp.i f j
  | .none => dummy_interp

  def const (x : M.X) (t : Realizer.Term) : Term :=
    .some { i := λ _ => x, tm := λ _ => t}

  def kind : Term := .none

  def prop : Term := const M.props Realizer.Term.K

  def ref (n : Nat) : Term :=
    .some { i := λ f => f n, tm := λ f => f n }

  def app (u v : Term) : Term :=
    .some {
      i := λ f => M.app (interp f u) (interp f v),
      tm := λ f => Realizer.Term.app (tm f u) (tm f v)
    }

  def cabs t m := Realizer.Term.K `@ (`λ m) `@ t

  def abs (A t : Term) : Term :=
    .some {
      i := λ f => M.lam (interp f A) (λ x => interp (VarMap.cons x f) t)
      tm := λ f => cabs (tm f A) (tm (Realizer.vlift f) t)
    }

  def cprod a b := Realizer.Term.K `@ a `@ (`λ b)

  def prod (A B : Term) : Term :=
    .some {
      i := λ f => M.prod (interp f A) (λ x => interp (VarMap.cons x f) B)
      tm := λ f => cprod (tm f A) (tm (Realizer.vlift f) B)
    }

  def lift_rec (n m : Nat) (t : Term) : Term := .some {
    i := λ f => interp (VarMap.lams m (VarMap.shift n) f) t
    tm := λ f => tm (VarMap.lams m (VarMap.shift n) f) t
  }

  def lift n := lift_rec n 0

  def subst_rec (arg : Term) (m : Nat) (t : Term) : Term := .some {
    i := λ f => interp (VarMap.lams m (VarMap.cons (interp (VarMap.shift m f) arg)) f) t
    tm := λ f => tm (VarMap.lams m (VarMap.cons (tm (VarMap.shift m f) arg)) f) t
  }

  def subst arg := subst_rec arg 0

  def red m n := ∀ j, Plus Realizer.Red (tm j m) (tm j n)

  theorem red_app1 : red f f' -> red (app f a) (app f' a) := by sorry

  theorem red_app2 : red a a' -> red (app f a) (app f a') := by sorry

  theorem red_abs1 : red A A' -> red (abs A t) (abs A' t) := by sorry

  theorem red_abs2 : red t t' -> red (abs A t) (abs A t') := by sorry

  theorem red_prod1 : red A A' -> red (prod A B) (prod A' B) := by sorry

  theorem red_prod2 : red B B' -> red (prod A B) (prod A B') := by sorry

  theorem red_beta : red (app (abs A b) t) (subst b t) := by sorry

  def conv m n := ∀ j, Conv Realizer.Red (tm j m) (tm j n)

  theorem red_conv : red t s -> conv t s := by sorry

  theorem conv_beta : conv t t' -> conv b b' -> conv (app (abs A b) t) (subst t' b') := by sorry

  theorem simul m :
    SN Realizer.Red m ->
    ∀ j m', m = tm j m' ->
    SN Realizer.Red (tm j m')
  := by sorry

  def prod_list (e : List Term) (U : Term) :=
    match e with
    | .nil => U
    | .cons T f => prod T (prod_list f U)

  def cst_fun (i : VarMap M.X) (e : List Term) (x : M.X) : M.X :=
    match e with
    | .nil => x
    | .cons T f => M.lam (interp i T) (λ y => cst_fun (VarMap.cons y i) f x)

  theorem witness_prod :
    (∀ i, M.inX x (interp i U)) ->
    M.inX (cst_fun i e x) (interp i (prod_list e U))
  := by sorry

  def kind_ok T := ∃ e, ∃ U, T = prod_list e U ∧ (∃ x, ∀ i, M.inX x (interp i U))

  theorem prop_kind_ok : kind_ok prop := by sorry

  theorem prod_kind_ok : kind_ok U -> kind_ok (prod T U) := by sorry

  theorem kind_ok_witness : kind_ok T -> ∃ x, M.inX x (interp i T) := by sorry


end CC.Model
