import Common
import Erased.Term

namespace Erased.Term
  def var_occurs : Term -> Nat -> Bool
  | var _ x, c => x == c
  | const _, _ => false
  | appt f a, c => var_occurs f c || var_occurs a c
  | app f a, c => var_occurs f c || var_occurs a c
  | lamt A t, c => var_occurs A c || var_occurs t (c + 1)
  | lam t, c => var_occurs t (c + 1)
  | all _ A B, c => var_occurs A c || var_occurs B (c + 1)
  | inter_ty A B, c => var_occurs A c || var_occurs B (c + 1)
  | eq a b, c => var_occurs a c || var_occurs b c

  def vars : Term -> Nat -> List Nat
  | var _ x, c => if c ≤ x then [x - c] else []
  | const _, _ => []
  | appt f a, c => vars f c ++ vars a c
  | app f a, c => vars f c ++ vars a c
  | lamt A t, c => vars A c ++ vars t (c + 1)
  | lam t, c => vars t (c + 1)
  | all _ A B, c => vars A c ++ vars B (c + 1)
  | inter_ty A B, c => vars A c ++ vars B (c + 1)
  | eq a b, c => vars a c ++ vars b c

  #eval var_occurs (lam (lam (var .type 3))) 1
end Erased.Term

namespace Erased
  theorem vars_no_zero_lemma σ τ :
    Term.var_occurs t v = false ->
    (∀ n, n ≠ v -> σ n = τ n) ->
    [σ]t = [τ]t
  := by sorry

  theorem vars_no_zero {t : Term} : t.var_occurs 0 = false -> ∀ v1 v2 σ, [v1 :: σ]t = [v2 :: σ]t := by
  intro h v1 v2 σ
  apply vars_no_zero_lemma; apply h
  intro n h2
  cases n <;> simp at *

end Erased
