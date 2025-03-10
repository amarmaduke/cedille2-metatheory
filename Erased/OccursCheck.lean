import Common
import Erased.Term

namespace Erased.Term
  @[simp]
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
end Erased.Term

namespace Erased
  theorem subst_hole_lift {σ τ : Subst Term} :
    (∀ n, n ≠ v -> σ n = τ n) -> (∀ n, n ≠ v + 1 -> ^σ n = ^τ n)
  := by
  intro h1 n h2
  cases n <;> simp at *
  case _ n =>
    unfold Subst.compose; simp
    rw [h1 n h2]

  theorem vars_no_zero_lemma1 σ τ :
    Term.var_occurs t v = false ->
    (∀ n, n ≠ v -> σ n = τ n) ->
    [σ]t = [τ]t
  := by
  intro h1 h2
  induction t generalizing v σ τ <;> simp at h1
  case _ K x => simp; rw [h2 x h1]
  case _ => simp
  case _ ih1 ih2 => simp at *; rw [ih1 _ _ h1.1 h2, ih2 _ _ h1.2 h2]; simp
  case _ ih1 ih2 => simp at *; rw [ih1 _ _ h1.1 h2, ih2 _ _ h1.2 h2]; simp
  case _ ih1 ih2 =>
    replace ih2 := @ih2 (v + 1) (^σ) (^τ) h1.2 (subst_hole_lift h2)
    simp at *; rw [ih1 _ _ h1.1 h2, ih2]; simp
  case _ ih =>
    replace ih := @ih (v + 1) (^σ) (^τ) h1 (subst_hole_lift h2)
    simp at *; rw [ih]
  case _ ih1 ih2 =>
    replace ih2 := @ih2 (v + 1) (^σ) (^τ) h1.2 (subst_hole_lift h2)
    simp at *; rw [ih1 _ _ h1.1 h2, ih2]; simp
  case _ ih1 ih2 =>
    replace ih2 := @ih2 (v + 1) (^σ) (^τ) h1.2 (subst_hole_lift h2)
    simp at *; rw [ih1 _ _ h1.1 h2, ih2]; simp
  case _ ih1 ih2 => simp at *; rw [ih1 _ _ h1.1 h2, ih2 _ _ h1.2 h2]; simp

  theorem subst_re_exists_lift {σ : Subst Term} :
    (∃ k, σ v = .re k) -> (∃ k, ^σ (v + 1) = .re k)
  := by
  intro h; cases h; case _ k h =>
    simp; unfold Subst.compose; simp
    apply Exists.intro (k + 1); rw [h]

  theorem subst_neq_lift {σ τ : Subst Term} :
    (σ n ≠ τ n) ->
    (∃ k, σ n = .re k) ->
    (^σ (n + 1) ≠ ^τ (n + 1))
  := by
  intro h1 h2 h3; simp at *
  unfold Subst.compose at h3; simp at h3
  apply h1; split at h3
  case _ t1 e1 =>
    split at h3
    case _ t2 e2 =>
      cases h2; case _ k h2 =>
        rw [h2] at e1; injection e1
    case _ y2 e2 => simp at *
  case _ y1 e1 =>
    split at h3
    case _ t2 e2 => simp at *
    case _ y2 e2 =>
      injection h3 with e
      injection e with e; subst e
      rw [e1, e2]

  theorem vars_no_zero_lemma2 σ τ :
    [σ]t = [τ]t ->
    (∃ k, σ v = .re k) ->
    (∃ k, τ v = .re k) ->
    σ v ≠ τ v ->
    Term.var_occurs t v = false
  := by
  intro h1 h2 h3 h4
  induction t generalizing v σ τ <;> simp at h1
  case _ K x =>
    simp; intro h; subst h
    cases h2; case _ k1 h2 =>
    cases h3; case _ k2 h3 =>
      rw [h2, h3] at h1; simp at h1
      subst h1; rw [<-h3] at h2
      apply h4 h2
  case _ => simp
  case _ ih1 ih2 =>
    simp; rw [ih1 _ _ h1.1 h2 h3 h4]
    rw [ih2 _ _ h1.2 h2 h3 h4]; simp
  case _ ih1 ih2 =>
    simp; rw [ih1 _ _ h1.1 h2 h3 h4]
    rw [ih2 _ _ h1.2 h2 h3 h4]; simp
  case _ t ih1 ih2 =>
    have lem1 : [^σ]t = [^τ]t := by simp; apply h1.2
    have lem2 := subst_re_exists_lift h2
    have lem3 := subst_re_exists_lift h3
    have lem4 := subst_neq_lift h4 h2
    replace ih2 := @ih2 (v + 1) (^σ) (^τ) lem1 lem2 lem3 lem4
    simp; rw [ih1 _ _ h1.1 h2 h3 h4]
    rw [ih2]; simp
  case _ t ih =>
    have lem1 : [^σ]t = [^τ]t := by simp; apply h1
    have lem2 := subst_re_exists_lift h2
    have lem3 := subst_re_exists_lift h3
    have lem4 := subst_neq_lift h4 h2
    replace ih := @ih (v + 1) (^σ) (^τ) lem1 lem2 lem3 lem4
    simp; rw [ih]
  case _ t ih1 ih2 =>
    have lem1 : [^σ]t = [^τ]t := by simp; apply h1.2
    have lem2 := subst_re_exists_lift h2
    have lem3 := subst_re_exists_lift h3
    have lem4 := subst_neq_lift h4 h2
    replace ih2 := @ih2 (v + 1) (^σ) (^τ) lem1 lem2 lem3 lem4
    simp; rw [ih1 _ _ h1.1 h2 h3 h4]
    rw [ih2]; simp
  case _ t ih1 ih2 =>
    have lem1 : [^σ]t = [^τ]t := by simp; apply h1.2
    have lem2 := subst_re_exists_lift h2
    have lem3 := subst_re_exists_lift h3
    have lem4 := subst_neq_lift h4 h2
    replace ih2 := @ih2 (v + 1) (^σ) (^τ) lem1 lem2 lem3 lem4
    simp; rw [ih1 _ _ h1.1 h2 h3 h4]
    rw [ih2]; simp
  case _ ih1 ih2 =>
    simp; rw [ih1 _ _ h1.1 h2 h3 h4]
    rw [ih2 _ _ h1.2 h2 h3 h4]; simp

  theorem vars_no_zero {t : Term} :
    t.var_occurs 0 = false <-> ∀ v1 v2 σ, [v1 :: σ]t = [v2 :: σ]t
  := by
  apply Iff.intro
  case _ =>
    intro h v1 v2 σ
    apply vars_no_zero_lemma1; apply h
    intro n h2
    cases n <;> simp at *
  case _ =>
    intro h
    apply @vars_no_zero_lemma2 _ 0 (.re 0 :: I) (.re 1 :: I)
    all_goals simp
    rw [h (.re 0) (.re 1) I]
end Erased
