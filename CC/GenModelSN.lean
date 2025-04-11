
import Common
import Realizer
import CC.Model
import CC.MakeObject

namespace CC.Model

  class SNAddon [M : CCModel] where
    real : M.X -> Realizer.Sat.SatSet
    real_sort : real M.props = Realizer.Sat.SNSat
    real_prod A B := real (M.prod A B) =
      (Realizer.Sat.prod_sat (real A) (Realizer.Sat.inter_sat
        (PSigma (λ x => M.inX x A)) (λ p => real (B p.1))))
    daimon : M.X
    daimon_false : M.inX daimon (M.prod M.props (λ p => p))

  variable [M : CCModel] [snM : SNAddon]

  def in_int (i : VarMap M.X) (j : VarMap Realizer.Term) (t T : Term) :=
    t ≠ kind ∧
    match T with
    | .none => kind_ok t ∧ SN Realizer.Red (tm j t)
    | _ => M.inX (interp i t) (interp i T) ∧ Realizer.Sat.mem (tm j t) (snM.real (interp i T))

  abbrev Env := List Term

  def val_ok (e : Env) (i : VarMap M.X) (j : VarMap Realizer.Term) :=
    ∀ n T, e[n]? = .some T -> in_int i j (ref n) (lift (n + 1) T)

  def wf (e : Env) := ∃ i, ∃ j, val_ok e i j

  def typed (e : Env) (t A : Term) :=
    ∀ i j, val_ok e i j -> in_int i j t A

  def eq_typed (e : Env) (t t' : Term) :=
    ∀ i j, val_ok e i j -> interp i t = interp i t'

  theorem model_strong_normalization e t A :
    wf e -> typed e t A -> SN red_term t
  := by sorry

  def kinded e T := typed e T kind ∨ typed e T prop

  theorem kinded_not_kind : wf e -> kinded e T -> t ≠ kind := by sorry

  theorem kinded_kind_ok : kinded e T -> val_ok e i j -> ∃ x, M.inX x (interp i T) := by sorry

  theorem wf_nil : wf [] := by sorry

  theorem wf_cons : wf e -> kinded e T -> wf (.cons T e) := by sorry

  theorem refl : eq_typed e t t := by sorry

  theorem sym : eq_typed e t t' -> eq_typed e t' t := by sorry

  theorem trans : eq_typed e a b -> eq_typed e b c -> eq_typed e a c := by sorry

  theorem eq_typed_app :
    eq_typed e f f' ->
    eq_typed e a a' ->
    eq_typed e (app f a) (app f' a')
  := by sorry

  theorem eq_typed_abs :
    eq_typed e A A' ->
    eq_typed (A :: e) t t' ->
    T ≠ kind ->
    eq_typed e (abs A t) (abs A' t)
  := by sorry

  theorem eq_typed_prod :
    eq_typed e A A' ->
    eq_typed (A :: e) B B' ->
    T ≠ kind ->
    eq_typed e (prod A B) (prod A' B')
  := by sorry

  theorem eq_typed_beta :
    eq_typed (T :: e) b b' ->
    eq_typed e t t' ->
    typed e t T ->
    T ≠ kind ->
    eq_typed e (app (abs T b) t) (subst t' b')
  := by sorry

  theorem typed_props : typed e prop kind := by sorry

  theorem typed_var :
    e[n]? = .some A ->
    typed e (ref n) (lift (n + 1) T)
  := by sorry

  theorem typed_app :
    typed e v V ->
    typed e u (prod V Ur) ->
    V ≠ kind ->
    Ur ≠ kind ->
    typed e (app u v) (subst v Ur)
  := by sorry

  theorem typed_abs :
    kinded e T ->
    typed (T :: e) t U ->
    U ≠ kind ->
    typed e (abs T t) (prod T U)
  := by sorry

  theorem typed_beta :
    kinded e T ->
    typed (t :: e) t U ->
    typed e N T ->
    T ≠ kind ->
    U ≠ kind ->
    typed e (app (abs T t) N) (subst N U)
  := by sorry

  theorem typed_prod :
    s2 = kind ∨ s2 = prop ->
    kinded e T ->
    typed (T :: e) U s2 ->
    typed e (prod T U) s2
  := by sorry

  theorem typed_conv :
    typed e t T ->
    eq_typed e T T' ->
    T ≠ kind ->
    T' ≠ kind ->
    typed e t T'
  := by sorry

end CC.Model
