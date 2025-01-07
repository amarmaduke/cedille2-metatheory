import Common.Term
import Common.Term.Substitution
import Common.Reduction.Definition

namespace Red

  theorem refl : t -β>* t := by apply RedStar.refl

  theorem trans_flip : x -β>* y -> y -β> z -> x -β>* z := by
  intro h1 h2
  induction h1
  case _ => apply RedStar.step h2 refl
  case _ h3 _h4 ih =>  apply RedStar.step h3 (ih h2)

  theorem trans : x -β>* y -> y -β>* z -> x -β>* z := by
  intro h1 h2
  induction h2
  case _ => simp [*]
  case _ h2 _h3 ih =>  apply ih (trans_flip h1 h2)

  theorem subst1_same σ : t -β> s -> [σ]t -β> [σ]s := by sorry
  -- intro h
  -- induction h generalizing σ
  -- all_goals try (case _ ih => simp; constructor; apply ih)
  -- case beta m A b t =>
  --   have h := @Red.beta m ([σ]A) ([^σ]b) ([σ]t)
  --   simp at *; exact h
  -- case proj1 B t s =>
  --   have h := @Red.proj1 ([σ]B) ([σ]t) ([σ]s)
  --   simp at *; exact h
  -- case proj2 B t s =>
  --   have h := @Red.proj2 ([σ]B) ([σ]t) ([σ]s)
  --   simp at *; exact h
  -- case substelim B t =>
  --   have h := @Red.substelim ([σ]B) ([σ]t)
  --   simp at *; exact h
  -- -- case conv_lam m A1 B A2 t n =>
  -- --   have h := @Red.conv_lam m ([σ]A1) ([^σ]B) ([σ]A2) ([^σ]t) n
  -- --   simp at *; exact h
  -- -- case conv_pair T t s n =>
  -- --   have h := @Red.conv_pair ([σ]T) ([σ]t) ([σ]s) n
  -- --   simp at *; exact h
  -- -- case conv_refl A t n =>
  -- --   have h := @Red.conv_refl ([σ]A) ([σ]t) n
  -- --   simp at *; exact h
  -- case conv_all K m A B n =>
  --   have h := @Red.conv_all K m ([σ]A) ([^σ]B) n
  --   simp at *; exact h
  -- case conv_prod A B n =>
  --   have h := @Red.conv_prod ([σ]A) ([^σ]B) n
  --   simp at *; exact h
  -- case conv_eq A a b n =>
  --   have h := @Red.conv_eq ([σ]A) ([σ]a) ([σ]b) n
  --   simp at *; exact h
  -- repeat sorry

  theorem subst_same σ : t -β>* s -> [σ]t -β>* [σ]s := by
  intro h
  induction h
  case _ => apply refl
  case _ h1 _h2 ih => apply RedStar.step (subst1_same σ h1) ih

  theorem subst_lift_rename σ τ :
    (∀ n k, σ n = .rename k -> τ n = .rename k) ->
    ∀ n k, ^σ n = .rename k -> ^τ n = .rename k
  := by
  intro h1 n k h2
  cases n <;> simp at *
  case _ => exact h2
  case _ n =>
    unfold Term.Subst.compose at *; simp at *
    generalize ydef : σ n = y at *
    cases y <;> simp at *
    case _ i => rw [h1 n i ydef]; simp [*]

  -- theorem subst_lift_replace σ τ :
  --   (∀ n t, σ n = .replace t -> ∃ t', τ n = .replace t' ∧ t =β> t') ->
  --   ∀ n t, ^σ n = .replace t -> ∃ t', ^τ n = .replace t' ∧ t =β> t'
  -- := by
  -- sorry

  -- theorem subst1 σ τ :
  --   (∀ n k, σ n = .rename k -> τ n = .rename k) ->
  --   (∀ n t, σ n = .replace t -> ∃ t', τ n = .replace t' ∧ t -β> t') ->
  --   t -β> s -> [σ]t -β> [τ]s
  -- := by
  -- intro h1 h2 j
  -- induction j
  -- case beta => sorry
  -- case proj1 => sorry
  -- case proj2 => sorry
  -- case substelim => sorry
  -- case lam_congr1 ih =>
  --   simp; apply Red.lam_congr1

  theorem congr3_1 t2 t3 (f : Term -> Term -> Term -> Term) :
    (∀ {t1 t2 t3 t1'}, t1 -β> t1' -> f t1 t2 t3 -β> f t1' t2 t3) ->
    t1 -β>* t1' ->
    f t1 t2 t3 -β>* f t1' t2 t3
  := by
  intro fh h2
  induction h2
  case _ => apply refl
  case _ h3 _h4 ih =>
    have h5 := @fh _ t2 t3 _ h3
    apply trans (RedStar.step h5 refl) ih

  theorem congr3_2 t1 t3 (f : Term -> Term -> Term -> Term) :
    (∀ {t1 t2 t3 t2'}, t2 -β> t2' -> f t1 t2 t3 -β> f t1 t2' t3) ->
    t2 -β>* t2' ->
    f t1 t2 t3 -β>* f t1 t2' t3
  := by
  intro fh h2
  induction h2
  case _ => apply refl
  case _ h3 _h4 ih =>
    have h5 := @fh t1 _ t3 _ h3
    apply trans (RedStar.step h5 refl) ih

  theorem congr3_3 t1 t2 (f : Term -> Term -> Term -> Term) :
    (∀ {t1 t2 t3 t3'}, t3 -β> t3' -> f t1 t2 t3 -β> f t1 t2 t3') ->
    t3 -β>* t3' ->
    f t1 t2 t3 -β>* f t1 t2 t3'
  := by
  intro fh h2
  induction h2
  case _ => apply refl
  case _ h3 _h4 ih =>
    have h5 := @fh t1 t2 _ _ h3
    apply trans (RedStar.step h5 refl) ih

  theorem congr3 (f : Term -> Term -> Term -> Term) :
    (∀ {t1 t2 t3 t1'}, t1 -β> t1' -> f t1 t2 t3 -β> f t1' t2 t3) ->
    (∀ {t1 t2 t3 t2'}, t2 -β> t2' -> f t1 t2 t3 -β> f t1 t2' t3) ->
    (∀ {t1 t2 t3 t3'}, t3 -β> t3' -> f t1 t2 t3 -β> f t1 t2 t3') ->
    t1 -β>* t1' -> t2 -β>* t2' -> t3 -β>* t3' ->
    f t1 t2 t3 -β>* f t1' t2' t3'
  := by
  intro f1 f2 f3 h1 h2 h3
  have r1 := congr3_1 t2 t3 f f1 h1
  have r2 := congr3_2 t1' t3 f f2 h2
  have r3 := congr3_3 t1' t2' f f3 h3
  apply trans r1; apply trans r2; apply trans r3; apply refl

  theorem congr2_1 t2 (f : Term -> Term -> Term) :
    (∀ {t1 t2 t1'}, t1 -β> t1' -> f t1 t2 -β> f t1' t2) ->
    t1 -β>* t1' ->
    f t1 t2 -β>* f t1' t2
  := by
  intro fh h
  apply congr3_1 t2 .none (λ t1 t2 _t3 => f t1 t2)
  intro t1 t2 _t3 t1' h; apply fh h
  exact h

  theorem congr2_2 t1 (f : Term -> Term -> Term) :
    (∀ {t1 t2 t2'}, t2 -β> t2' -> f t1 t2 -β> f t1 t2') ->
    t2 -β>* t2' ->
    f t1 t2 -β>* f t1 t2'
  := by
  intro fh h
  apply congr3_2 t1 .none (λ t1 t2 _t3 => f t1 t2)
  intro t1 t2 _t3 t1' h; apply fh h
  exact h

  theorem congr2 (f : Term -> Term -> Term) :
    (∀ {t1 t2 t1'}, t1 -β> t1' -> f t1 t2 -β> f t1' t2) ->
    (∀ {t1 t2 t2'}, t2 -β> t2' -> f t1 t2 -β> f t1 t2') ->
    t1 -β>* t1' -> t2 -β>* t2' ->
    f t1 t2 -β>* f t1' t2'
  := by
  intro f1 f2 h1 h2
  have r1 := congr2_1 t2 f f1 h1
  have r2 := congr2_2 t1' f f2 h2
  apply trans r1; apply trans r2; apply refl

  theorem congr1 (f : Term -> Term) :
    (∀ {t1 t1'}, t1 -β> t1' -> f t1 -β> f t1') ->
    t1 -β>* t1' ->
    f t1 -β>* f t1'
  := by
  intro fh h
  apply congr2_1 .none (λ t1 _t2 => f t1)
  intro t1 _t2 t1' h; apply fh h
  exact h

  theorem lam_congr : .lam m A t -β>* w -> ∃ A', ∃ t', w = .lam m A' t' ∧ A -β>* A' ∧ t -β>* t' := by
  intro h
  generalize udef : Term.lam m A t = u at *
  induction h generalizing m A t
  case _ =>
    subst udef; exists A; exists t
    apply And.intro; rfl
    apply And.intro; apply refl; apply refl
  case _ r1 r2 ih =>
    subst udef; cases r1
    case _ A' r =>
      replace ih := @ih m A' t rfl
      cases ih
      case _ q1 ih =>
      cases ih
      case _ q2 ih =>
        rw [ih.1]; exists q1; exists q2
        apply And.intro; rfl
        apply And.intro; apply RedStar.step r ih.2.1
        apply ih.2.2
    case _ t' r =>
      replace ih := @ih m A t' rfl
      cases ih
      case _ q1 ih =>
      cases ih
      case _ q2 ih =>
        rw [ih.1]; exists q1; exists q2
        apply And.intro; rfl
        apply And.intro; apply ih.2.1
        apply RedStar.step r ih.2.2

  theorem all_congr : .all m A B -β>* w -> ∃ A', ∃ B', w = .all m A' B' ∧ A -β>* A' ∧ B -β>* B' := by
  intro h
  generalize udef : Term.all m A B = u at *
  induction h generalizing m A B
  case _ =>
    subst udef; exists A; exists B
    apply And.intro; rfl
    apply And.intro; apply refl; apply refl
  case _ r1 r2 ih =>
    subst udef; cases r1
    case _ A' r =>
      replace ih := @ih m A' B rfl
      cases ih
      case _ q1 ih =>
      cases ih
      case _ q2 ih =>
        rw [ih.1]; exists q1; exists q2
        apply And.intro; rfl
        apply And.intro; apply RedStar.step r ih.2.1
        apply ih.2.2
    case _ t' r =>
      replace ih := @ih m A t' rfl
      cases ih
      case _ q1 ih =>
      cases ih
      case _ q2 ih =>
        rw [ih.1]; exists q1; exists q2
        apply And.intro; rfl
        apply And.intro; apply ih.2.1
        apply RedStar.step r ih.2.2

end Red

namespace RedConv

  theorem refl : A =β= A := by
  induction A
  all_goals (
    unfold RedConv; apply Exists.intro
    apply And.intro; apply RedStar.refl; apply RedStar.refl
  )

  theorem sym : A =β= B -> B =β= A := by
  intro h
  cases h
  case _ C ih => exists C; simp [*]



  theorem subst σ : A =β= B -> [σ]A =β= [σ]B := by
  intro h
  cases h
  case _ C h =>
    have h1 := Red.subst_same σ h.1
    have h2 := Red.subst_same σ h.2
    exists [σ]C

  theorem type_not_conv_to_kind : ¬ (★ =β= □) := by
  intro h
  cases h
  case _ w h =>
  cases h.1
  case _ =>
    cases h.2
    case _ r _ => cases r
  case _ r _ => cases r

  theorem lam_congr : .lam m1 A1 B1 =β= .lam m2 A2 B2 -> m1 = m2 ∧ A1 =β= A2 ∧ B1 =β= B2 := by
  intro h
  cases h
  case _ w h =>
    have h1 := Red.lam_congr h.1
    cases h1
    case _ A h1 =>
    cases h1
    case _ B h1 =>
    cases h1
    case _ e h1 =>
      subst e
      have h2 := Red.lam_congr h.2
      cases h2
      case _ A h2 =>
      cases h2
      case _ B h2 =>
      cases h2
      case _ e h2 =>
        injection e with e1 e2 e3; subst e1; subst e2; subst e3
        apply And.intro; rfl
        apply And.intro; exists A; apply And.intro; apply h1.1; apply h2.1
        exists B; apply And.intro; apply h1.2; apply h2.2

  theorem all_congr : .all m1 A1 B1 =β= .all m2 A2 B2 -> m1 = m2 ∧ A1 =β= A2 ∧ B1 =β= B2 := by
  intro h
  cases h
  case _ w h =>
    have h1 := Red.all_congr h.1
    cases h1
    case _ A h1 =>
    cases h1
    case _ B h1 =>
    cases h1
    case _ e h1 =>
      subst e
      have h2 := Red.all_congr h.2
      cases h2
      case _ A h2 =>
      cases h2
      case _ B h2 =>
      cases h2
      case _ e h2 =>
        injection e with e1 e2 e3; subst e1; subst e2; subst e3
        apply And.intro; rfl
        apply And.intro; exists A; apply And.intro; apply h1.1; apply h2.1
        exists B; apply And.intro; apply h1.2; apply h2.2

end RedConv
