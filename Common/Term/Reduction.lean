import Common.Term
import Common.Term.Substitution

namespace Term

  inductive Red : Term -> Term -> Prop where
  | beta : Red (.app m (.lam m A b) t) (b β[t])
  | proj1 : Red (.fst (.pair B t s)) t
  | proj2 : Red (.snd (.pair B t s)) s
  | substelim : Red (.subst B (.refl t)) (.lam mf (.app mt B t) (.bound .type 0))
  | lam_congr1 : Red A A' -> Red (.lam m A t) (.lam m A' t)
  | lam_congr2 : Red t t' -> Red (.lam m A t) (.lam m A t')
  | app_congr1 : Red f f' -> Red (.app m f t) (.app m f' t)
  | app_congr2 : Red t t' -> Red (.app m f t) (.app m f t')
  | all_congr1 : Red A A' -> Red (.all m A B) (.all m A' B)
  | all_congr2 : Red B B' -> Red (.all m A B) (.all m A B')
  | pair_congr1 : Red B B' -> Red (.pair B t s) (.pair B' t s)
  | pair_congr2 : Red t t' -> Red (.pair B t s) (.pair B t' s)
  | pair_congr3 : Red s s' -> Red (.pair B t s) (.pair B t s')
  | fst_congr : Red t t' -> Red (.fst t) (.fst t')
  | snd_congr : Red t t' -> Red (.snd t) (.snd t')
  | prod_congr1 : Red A A' -> Red (.prod A B) (.prod A' B)
  | prod_congr2 : Red B B' -> Red (.prod A B) (.prod A B')
  | refl_congr : Red t t' -> Red (.refl t) (.refl t')
  | subst_congr1 : Red B B' -> Red (.subst B e) (.subst B' e)
  | subst_congr2 : Red e e' -> Red (.subst B e) (.subst B e')
  | phi_congr1 : Red a a' -> Red (.phi a b e) (.phi a' b e)
  | phi_congr2 : Red b b' -> Red (.phi a b e) (.phi a b' e)
  | phi_congr3 : Red e e' -> Red (.phi a b e) (.phi a b e')
  | eq_congr1 : Red A A' -> Red (.eq A a b) (.eq A' a b)
  | eq_congr2 : Red a a' -> Red (.eq A a b) (.eq A a' b)
  | eq_congr3 : Red b b' -> Red (.eq A a b) (.eq A a b')
  | conv_congr1 : Red A A' -> Red (.conv A t c) (.conv A' t c)
  | conv_congr2 : Red t t' -> Red (.conv A t c) (.conv A t' c)

  inductive RedStar : Term -> Term -> Prop where
  | refl : RedStar t t
  | step : Red x y -> RedStar y z -> RedStar x z

  abbrev RedConv (A : Term) (B : Term) : Prop := ∃ C, RedStar A C ∧ RedStar B C

  inductive ParRed : Term -> Term -> Prop where
  | bound : ParRed (.bound K n) (.bound K n)
  | none : ParRed .none .none
  | const : ParRed (.const K) (.const K)
  | beta : ParRed A A' -> ParRed b b' -> ParRed t t' -> ParRed (.app m (.lam m A b) t) (b' β[t'])
  | proj1 : ParRed B B' -> ParRed t t' -> ParRed s s' -> ParRed (.fst (.pair B t s)) t'
  | proj2 : ParRed B B' -> ParRed t t' -> ParRed s s' -> ParRed (.snd (.pair B t s)) s'
  | substelim : ParRed B B' -> ParRed t t' -> ParRed (.subst B (.refl t)) (.lam mf (.app mt B' t') (.bound .type 0))
  | lam_congr : ParRed A A' -> ParRed t t' -> ParRed (.lam m A t) (.lam m A' t')
  | app_congr : ParRed f f' -> ParRed a a' -> ParRed (.app m f a) (.app m f' a')
  | all_congr : ParRed A A' -> ParRed B B' -> ParRed (.all m A B) (.all m A' B')
  | pair_congr : ParRed B B' -> ParRed t t' -> ParRed s s' -> ParRed (.pair B t s) (.pair B' t' s')
  | fst_congr : ParRed t t' -> ParRed (.fst t) (.fst t')
  | snd_congr : ParRed t t' -> ParRed (.snd t) (.snd t')
  | prod_congr : ParRed A A' -> ParRed B B' -> ParRed (.prod A B) (.prod A' B')
  | refl_congr : ParRed t t' -> ParRed (.refl t) (.refl t')
  | subst_congr : ParRed B B' -> ParRed e e' -> ParRed (.subst B e) (.subst B' e')
  | phi_congr : ParRed a a' -> ParRed b b' -> ParRed e e' -> ParRed (.phi a b e) (.phi a' b' e')
  | eq_congr : ParRed A A' -> ParRed a a' -> ParRed b b' -> ParRed (.eq A a b) (.eq A' a' b')
  | conv_congr : ParRed A A' -> ParRed t t' -> ParRed (.conv A t c) (.conv A' t' c)

  @[simp]
  def pcompl : Term -> Term
  | .app mf (.lam mf _ b) t
  | .app m0 (.lam m0 _ b) t
  | .app mt (.lam mt _ b) t => (pcompl b) β[pcompl t]
  | .fst (.pair _ t _) => pcompl t
  | .snd (.pair _ _ s) => pcompl s
  | .subst B (.refl t) => .lam mf (.app mt (pcompl B) (pcompl t)) (.bound .type 0)
  | .lam m A t => .lam m (pcompl A) (pcompl t)
  | .app m f a => .app m (pcompl f) (pcompl a)
  | .all m A B => .all m (pcompl A) (pcompl B)
  | .pair B t s => .pair (pcompl B) (pcompl t) (pcompl s)
  | .fst t => .fst (pcompl t)
  | .snd t => .snd (pcompl t)
  | .prod A B => .prod (pcompl A) (pcompl B)
  | .refl t => .refl (pcompl t)
  | .subst B e => .subst (pcompl B) (pcompl e)
  | .phi a b e => .phi (pcompl a) (pcompl b) (pcompl e)
  | .eq A a b => .eq (pcompl A) (pcompl a) (pcompl b)
  | .conv A t c => .conv (pcompl A) (pcompl t) c
  | .bound K n => .bound K n
  | .const K => .const K
  | .none => .none

  inductive ParRedStar : Term -> Term -> Prop where
  | refl : ParRedStar t t
  | step : ParRed x y -> ParRedStar y z -> ParRedStar x z

  abbrev ParRedConv (A : Term) (B : Term) : Prop := ∃ C, ParRedStar A C ∧ ParRedStar B C

end Term

infix:40 " -β> " => Term.Red
infix:39 " -β>* " => Term.RedStar
infix:38 " =β= " => Term.RedConv
infix:40 " =β> " => Term.ParRed
infix:39 " =β>* " => Term.ParRedStar
infix:38 " ≡β≡ " => Term.ParRedConv

namespace Term

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

  theorem subst1_same σ : t -β> s -> [σ]t -β> [σ]s := by
  intro h
  induction h generalizing σ
  all_goals try (case _ ih => simp; constructor; apply ih)
  case beta m A b t =>
    have h := @Red.beta m ([σ]A) ([^σ]b) ([σ]t)
    simp at *; exact h
  case proj1 B t s =>
    have h := @Red.proj1 ([σ]B) ([σ]t) ([σ]s)
    simp at *; exact h
  case proj2 B t s =>
    have h := @Red.proj2 ([σ]B) ([σ]t) ([σ]s)
    simp at *; exact h
  case substelim B t =>
    have h := @Red.substelim ([σ]B) ([σ]t)
    simp at *; exact h

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
    unfold Subst.compose at *; simp at *
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

end Red

namespace ParRed

  @[simp]
  theorem refl1 t : t =β> t := by
  induction t; all_goals constructor <;> simp [*]

  theorem refl t : t =β>* t := by constructor

  theorem trans_flip : x =β>* y -> y =β> z -> x =β>* z := by
  intro h1 h2
  induction h1
  case _ => apply ParRedStar.step h2; apply refl
  case _ h3 _h4 ih =>  apply ParRedStar.step h3 (ih h2)

  theorem trans : x =β>* y -> y =β>* z -> x =β>* z := by
  intro h1 h2
  induction h2; simp [*]
  case _ r1 _r2 ih =>
    apply ih; apply trans_flip h1 r1

  theorem from_red : s -β> t -> s =β> t := by
  intro h
  induction h
  all_goals (try constructor <;> simp [*])
  case beta => constructor; repeat apply refl1
  case proj1 => constructor; repeat apply refl1
  case proj2 => constructor; repeat apply refl1

  theorem from_redstar : s -β>* t -> s =β>* t := by
  intro h
  induction h
  case _ => constructor
  case _ h1 _h2 ih => constructor; apply (from_red h1); apply ih

  theorem to_red : s =β> t -> s -β>* t := by
  intro h
  induction h
  case bound => apply Term.Red.refl
  case none => apply Term.Red.refl
  case const => apply Term.Red.refl
  case beta A _A' b b' t t' m _ _ _ _ih1 ih2 ih3 =>
    have r1 := Red.congr2 (λ b t => .app m (.lam m A b) t)
      (by {
        intro t1 t2 t1' h; simp
        apply Red.app_congr1; apply Red.lam_congr2; apply h
      })
      (by {
        intro t1 t2 t2' h; simp
        apply Red.app_congr2; apply h
      })
      ih2 ih3
    simp at r1
    apply Red.trans_flip; apply r1; constructor
  case proj1 B _B' t t' s _s' _ _ _ _ih1 ih2 _ih3 =>
    have r1 := Red.congr1 (λ t => .fst (.pair B t s))
      (by {
        intro t t' h; simp
        apply Red.fst_congr; apply Red.pair_congr2; apply h
      })
      ih2
    simp at r1
    apply Red.trans_flip; apply r1; constructor
  case proj2 B _B' t _t' s s' _ _ _ _ih1 _ih2 ih3 =>
    have r1 := Red.congr1 (λ s => .snd (.pair B t s))
      (by {
        intro t t' h; simp
        apply Red.snd_congr; apply Red.pair_congr3; apply h
      })
      ih3
    simp at r1
    apply Red.trans_flip; apply r1; constructor
  case substelim B B' t t' _ _ ih1 ih2 =>
    have r1 := Red.congr2 (λ B t => .subst B (.refl t))
      (by {
        intro t1 t2 t1' h; simp
        apply Red.subst_congr1; apply h
      })
      (by {
        intro t1 t2 t2' h; simp
        apply Red.subst_congr2; apply Red.refl_congr; apply h
      })
      ih1 ih2
    simp at r1
    apply Red.trans_flip; apply r1; constructor
  case lam_congr ih1 ih2 => apply Red.congr2 (.lam _) .lam_congr1 .lam_congr2 ih1 ih2
  case app_congr ih1 ih2 => apply Red.congr2 (.app _) .app_congr1 .app_congr2 ih1 ih2
  case all_congr ih1 ih2 => apply Red.congr2 (.all _) .all_congr1 .all_congr2 ih1 ih2
  case pair_congr ih1 ih2 ih3 => apply Red.congr3 .pair .pair_congr1 .pair_congr2 .pair_congr3 ih1 ih2 ih3
  case fst_congr ih => apply Red.congr1 .fst .fst_congr ih
  case snd_congr ih => apply Red.congr1 .snd .snd_congr ih
  case prod_congr ih1 ih2 => apply Red.congr2 .prod .prod_congr1 .prod_congr2 ih1 ih2
  case refl_congr ih => apply Red.congr1 .refl .refl_congr ih
  case subst_congr ih1 ih2 => apply Red.congr2 .subst .subst_congr1 .subst_congr2 ih1 ih2
  case phi_congr ih1 ih2 ih3 => apply Red.congr3 .phi .phi_congr1 .phi_congr2 .phi_congr3 ih1 ih2 ih3
  case eq_congr ih1 ih2 ih3 => apply Red.congr3 .eq .eq_congr1 .eq_congr2 .eq_congr3 ih1 ih2 ih3
  case conv_congr ih1 ih2 => apply Red.congr2 (λ t1 t2 => .conv t1 t2 _) .conv_congr1 .conv_congr2 ih1 ih2

  theorem to_redstar : s =β>* t -> s -β>* t := by
  intro h
  induction h
  case _ => apply Red.refl
  case _ h _ ih => apply Red.trans (to_red h) ih

  theorem subst_same σ : s =β> t -> [σ]s =β> [σ]t := by
  intro h
  induction h generalizing σ
  case bound _ n => simp
  case none => simp
  case const => simp
  case beta A A' b b' t t' m _ _ _ ih1 ih2 ih3 =>
    have h3 := @ParRed.beta ([σ]A) ([σ]A') ([^σ]b) ([^σ]b') ([σ]t) ([σ]t') m
    simp at *; apply h3
    apply ih1 σ
    replace ih2 := ih2 (^σ)
    simp at ih2; apply ih2
    apply ih3 σ
  case proj1 B B' t t' s s' _ _ _ ih1 ih2 ih3 =>
    have h3 := @ParRed.proj1 ([σ]B) ([σ]B') ([σ]t) ([σ]t') ([σ]s) ([σ]s')
    simp at *; apply h3
    apply ih1 σ; apply ih2 σ; apply ih3 σ
  case proj2 B B' t t' s s' _ _ _ ih1 ih2 ih3 =>
    have h3 := @ParRed.proj2 ([σ]B) ([σ]B') ([σ]t) ([σ]t') ([σ]s) ([σ]s')
    simp at *; apply h3
    apply ih1 σ; apply ih2 σ; apply ih3 σ
  case substelim B B' t t' _ _ ih1 ih2 =>
    have h3 := @ParRed.substelim ([σ]B) ([σ]B') ([σ]t) ([σ]t')
    simp at *; apply h3
    apply ih1 σ; apply ih2 σ
  case lam_congr ih1 ih2 =>
    simp; constructor; apply ih1 σ
    replace ih2 := ih2 (^σ)
    simp at ih2; exact ih2
  case all_congr ih1 ih2 =>
    simp; constructor; apply ih1 σ
    replace ih2 := ih2 (^σ)
    simp at ih2; exact ih2
  case prod_congr ih1 ih2 =>
    simp; constructor; apply ih1 σ
    replace ih2 := ih2 (^σ)
    simp at ih2; exact ih2
  all_goals try (
    case _ ih1 => simp at *; constructor; apply ih1 σ
  )
  all_goals try (
    case _ ih1 ih2 => simp at *; constructor; apply ih1 σ; apply ih2 σ
  )
  all_goals try (
    case _ ih1 ih2 ih3 => simp at *; constructor; apply ih1 σ; apply ih2 σ; apply ih3 σ
  )

  theorem subst_lift_replace σ τ :
    (∀ n t, σ n = .replace t -> ∃ t', τ n = .replace t' ∧ t =β> t') ->
    ∀ n t, ^σ n = .replace t -> ∃ t', ^τ n = .replace t' ∧ t =β> t'
  := by
  intro h1 n t h2
  cases n <;> simp at *
  case _ n =>
    unfold Subst.compose at *; simp at *
    generalize ydef : σ n = y at *
    cases y <;> simp at *
    case _ q =>
      replace h1 := h1 n q ydef
      cases h1
      case _ w h1 =>
        rw [h1.1]; simp
        subst h2; apply subst_same; apply h1.2

  theorem subst (σ τ : Subst Term) :
    (∀ n t, σ n = .replace t -> ∃ t', τ n = .replace t' ∧ t =β> t') ->
    (∀ n k, σ n = .rename k -> τ n = .rename k) ->
    s =β> t -> [σ]s =β> [τ]t
  := by
  intro h1 h2 r
  induction r generalizing σ τ
  case bound _ n =>
    simp; generalize ydef : σ n = y at *
    cases y <;> simp
    case _ i => rw [h2 n i]; simp; rw [ydef]
    case _ t =>
      replace h1 := h1 n t ydef
      cases h1
      case _ t' h1 =>
        rw [h1.1]; simp; apply h1.2
  case none => simp
  case const => simp
  case beta A A' b b' t t' m _ _ _ ih1 ih2 ih3 =>
    have h3 := @ParRed.beta ([σ]A) ([τ]A') ([^σ]b) ([^τ]b') ([σ]t) ([τ]t') m
    simp at *; apply h3
    apply ih1 _ _ h1 h2
    replace ih2 := ih2 (^σ) (^τ) (subst_lift_replace _ _ h1) (Red.subst_lift_rename _ _ h2)
    simp at ih2; apply ih2
    apply ih3 _ _ h1 h2
  case proj1 B B' t t' s s' _ _ _ ih1 ih2 ih3 =>
    have h3 := @ParRed.proj1 ([σ]B) ([τ]B') ([σ]t) ([τ]t') ([σ]s) ([τ]s')
    simp at *; apply h3
    apply ih1 _ _ h1 h2; apply ih2 _ _ h1 h2; apply ih3 _ _ h1 h2
  case proj2 B B' t t' s s' _ _ _ ih1 ih2 ih3 =>
    have h3 := @ParRed.proj2 ([σ]B) ([τ]B') ([σ]t) ([τ]t') ([σ]s) ([τ]s')
    simp at *; apply h3
    apply ih1 _ _ h1 h2; apply ih2 _ _ h1 h2; apply ih3 _ _ h1 h2
  case substelim B B' t t' _ _ ih1 ih2 =>
    have h3 := @ParRed.substelim ([σ]B) ([τ]B') ([σ]t) ([τ]t')
    simp at *; apply h3
    apply ih1 _ _ h1 h2; apply ih2 _ _ h1 h2
  case lam_congr ih1 ih2 =>
    simp; constructor; apply ih1 _ _ h1 h2
    replace ih2 := ih2 (^σ) (^τ) (subst_lift_replace _ _ h1) (Red.subst_lift_rename _ _ h2)
    simp at ih2; exact ih2
  case all_congr ih1 ih2 =>
    simp; constructor; apply ih1 _ _ h1 h2
    replace ih2 := ih2 (^σ) (^τ) (subst_lift_replace _ _ h1) (Red.subst_lift_rename _ _ h2)
    simp at ih2; exact ih2
  case prod_congr ih1 ih2 =>
    simp; constructor; apply ih1 _ _ h1 h2
    replace ih2 := ih2 (^σ) (^τ) (subst_lift_replace _ _ h1) (Red.subst_lift_rename _ _ h2)
    simp at ih2; exact ih2
  all_goals try (
    case _ ih1 =>
    simp; constructor; apply ih1 _ _ h1 h2
  )
  all_goals try (
    case _ ih1 ih2 =>
    simp; constructor; apply ih1 _ _ h1 h2; apply ih2 _ _ h1 h2
  )
  all_goals try (
    case _ ih1 ih2 ih3 =>
    simp; constructor; apply ih1 _ _ h1 h2; apply ih2 _ _ h1 h2; apply ih3 _ _ h1 h2
  )

  theorem subst_beta : b =β> b' -> t =β> t' -> b β[t] =β> b' β[t'] := by
  intro h1 h2
  apply subst <;> simp [*]
  case _ =>
    intro n x h
    cases n <;> simp at *
    case _ => subst h; apply h2
  case _ =>
    intro n x h
    cases n <;> simp at *
    case _ => exact h

  theorem complete : s =β> t -> t =β> pcompl s := by
  intro h
  induction h
  case beta m _ _ _ _ _ _ =>
    cases m <;> simp
    all_goals (
      apply subst
      case _ =>
        intro n t h; simp at *
        cases n <;> simp at *
        subst h; simp [*]
      case _ =>
        intro n k h; simp at *
        cases n <;> simp at * <;> simp [*]
      case _ => simp [*]
    )
  case proj1 => simp [*]
  case proj2 => simp [*]
  case substelim =>
    simp; constructor; constructor;
    all_goals simp [*]
  case app_congr f f' a a' m h1 _h2 ih1 ih2 =>
    cases m
    case _ =>
      cases f
      all_goals (try constructor; apply ih1; apply ih2)
      case _ m' _ _ =>
      cases m' <;> simp at*
      case _ =>
        cases f' <;> cases h1
        case _ r1 r2 =>
          cases ih1
          case _ h1 h2 =>
            apply ParRed.beta; apply h1; apply h2; apply ih2
      case _ => apply ParRed.app_congr <;> simp [*]
      case _ => apply ParRed.app_congr <;> simp [*]
    case _ =>
      cases f
      all_goals (try constructor; apply ih1; apply ih2)
      case _ m' _ _ =>
      cases m' <;> simp at *
      case _ => apply ParRed.app_congr <;> simp [*]
      case _ =>
        cases f' <;> cases h1
        case _ r1 r2 =>
          cases ih1
          case _ h1 h2 =>
            apply ParRed.beta; apply h1; apply h2; apply ih2
      case _ => apply ParRed.app_congr <;> simp [*]
    case _ =>
      cases f
      all_goals (try constructor; apply ih1; apply ih2)
      case _ m' _ _ =>
      cases m' <;> simp at *
      case _ => apply ParRed.app_congr <;> simp [*]
      case _ => apply ParRed.app_congr <;> simp [*]
      case _ =>
        cases f' <;> cases h1
        case _ r1 r2 =>
          cases ih1
          case _ h1 h2 =>
            apply ParRed.beta; apply h1; apply h2; apply ih2
  case fst_congr t t' h ih =>
    cases t <;> simp at *
    all_goals (try constructor; apply ih)
    case pair B t s =>
      cases t' <;> try cases h
      case _ h1 h2 h3 =>
        cases ih
        case _ r1 r2 r3 =>
          apply ParRed.proj1
          apply r1; apply r2; apply r3
  case snd_congr t t' h ih =>
    cases t <;> simp at *
    all_goals (try constructor; apply ih)
    case pair B t s =>
      cases t' <;> try cases h
      case _ h1 h2 h3 =>
        cases ih
        case _ r1 r2 r3 =>
          apply ParRed.proj2
          apply r1; apply r2; apply r3
  case subst_congr B B' e e' _h1 h2 ih1 ih2 =>
    cases e <;> simp at *
    all_goals (try constructor; apply ih1; apply ih2)
    case _ e =>
      cases e' <;> try cases h2
      case _ h =>
        cases ih2
        case _ r =>
          apply ParRed.substelim; apply ih1; apply r
  all_goals (try simp; constructor <;> simp [*])
  all_goals (try simp)

  theorem strip : s =β> t1 -> s =β>* t2 -> ∃ t, t1 =β>* t ∧ t2 =β> t := by
  intro h1 h2
  induction h2 generalizing t1
  case _ t' => exists t1; apply And.intro; apply refl; apply h1
  case _ x y z r1 _r2 ih =>
    have r3 := complete r1
    replace ih := ih r3
    cases ih
    case _ w ih =>
      replace _r3 := ParRedStar.step r3 ih.1
      replace h1 := complete h1
      replace r3 := ParRedStar.step h1 ih.1
      exists w; apply And.intro; apply r3; apply ih.2

  theorem confluence : s =β>* t1 -> s =β>* t2 -> t1 ≡β≡ t2 := by
  intro h1 h2
  induction h1 generalizing t2
  case _ z =>
    exists t2; apply And.intro
    apply h2; apply refl
  case _ s y t1 r1 _r2 ih =>
    have h3 := strip r1 h2
    cases h3
    case _ w h3 =>
      replace ih := ih h3.1
      cases ih
      case _ q ih =>
        exists q; apply And.intro
        apply ih.1; apply ParRedStar.step
        apply h3.2; apply ih.2

end ParRed

namespace ParRedConv

  theorem refl : A ≡β≡ A := by
  induction A
  all_goals (
    apply Exists.intro; apply And.intro
    apply ParRedStar.refl; apply ParRedStar.refl
  )

  theorem sym : A ≡β≡ B -> B ≡β≡ A := by
  intro h
  cases h
  case _ C ih => exists C; simp [*]

  theorem trans : A ≡β≡ B -> B ≡β≡ C -> A ≡β≡ C := by
  intro h1 h2
  cases h1
  case _ C1 ih1 =>
    cases h2
    case _ C2 ih2 =>
      have conf := ParRed.confluence ih1.2 ih2.1
      cases conf
      case _ Z ih =>
        exists Z; apply And.intro
        apply ParRed.trans ih1.1 ih.1
        apply ParRed.trans ih2.2 ih.2

end ParRedConv

namespace Red

  theorem confluence : s -β>* t1 -> s -β>* t2 -> t1 =β= t2 := by
  intro h1 h2
  replace h1 := ParRed.from_redstar h1
  replace h2 := ParRed.from_redstar h2
  have conf := ParRed.confluence h1 h2
  cases conf
  case _ t conf =>
    exists t; apply And.intro
    apply ParRed.to_redstar conf.1
    apply ParRed.to_redstar conf.2

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

  theorem trans : A =β= B -> B =β= C -> A =β= C := by
  intro h1 h2
  unfold RedConv at *
  cases h1
  case _ C1 ih1 =>
    cases h2
    case _ C2 ih2 =>
      have conf := Red.confluence ih1.2 ih2.1
      cases conf
      case _ Z ih =>
        exists Z; apply And.intro
        apply Red.trans ih1.1 ih.1
        apply Red.trans ih2.2 ih.2

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

end RedConv

end Term
