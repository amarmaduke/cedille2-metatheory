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

end Term

infix:40 " -β> " => Term.Red
infix:39 " -β>* " => Term.RedStar
infix:40 " =β> " => Term.ParRed
infix:39 " =β>* " => Term.ParRedStar

namespace Term.Red

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

  theorem subst1 σ : t -β> s -> [σ]t -β> [σ]s := by
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

  theorem subst σ : t -β>* s -> [σ]t -β>* [σ]s := by
  intro h
  induction h
  case _ => apply refl
  case _ h1 _h2 ih => apply RedStar.step (subst1 σ h1) ih

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

namespace Term.Red

namespace Term.ParRed

  @[simp]
  theorem refl1 t : t =β> t := by
  induction t; all_goals constructor <;> simp [*]

  theorem refl t : t =β>* t := by constructor

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
    have r1 := congr2 (λ b t => .app m (.lam m A b) t)
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
    apply trans_flip; apply r1; constructor
  case proj1 B _B' t t' s _s' _ _ _ _ih1 ih2 _ih3 =>
    have r1 := congr1 (λ t => .fst (.pair B t s))
      (by {
        intro t t' h; simp
        apply Red.fst_congr; apply Red.pair_congr2; apply h
      })
      ih2
    simp at r1
    apply trans_flip; apply r1; constructor
  case proj2 B _B' t _t' s s' _ _ _ _ih1 _ih2 ih3 =>
    have r1 := congr1 (λ s => .snd (.pair B t s))
      (by {
        intro t t' h; simp
        apply Red.snd_congr; apply Red.pair_congr3; apply h
      })
      ih3
    simp at r1
    apply trans_flip; apply r1; constructor
  case substelim B B' t t' _ _ ih1 ih2 =>
    have r1 := congr2 (λ B t => .subst B (.refl t))
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
    apply trans_flip; apply r1; constructor
  case lam_congr ih1 ih2 => apply congr2 (.lam _) .lam_congr1 .lam_congr2 ih1 ih2
  case app_congr ih1 ih2 => apply congr2 (.app _) .app_congr1 .app_congr2 ih1 ih2
  case all_congr ih1 ih2 => apply congr2 (.all _) .all_congr1 .all_congr2 ih1 ih2
  case pair_congr ih1 ih2 ih3 => apply congr3 .pair .pair_congr1 .pair_congr2 .pair_congr3 ih1 ih2 ih3
  case fst_congr ih => apply congr1 .fst .fst_congr ih
  case snd_congr ih => apply congr1 .snd .snd_congr ih
  case prod_congr ih1 ih2 => apply congr2 .prod .prod_congr1 .prod_congr2 ih1 ih2
  case refl_congr ih => apply congr1 .refl .refl_congr ih
  case subst_congr ih1 ih2 => apply congr2 .subst .subst_congr1 .subst_congr2 ih1 ih2
  case phi_congr ih1 ih2 ih3 => apply congr3 .phi .phi_congr1 .phi_congr2 .phi_congr3 ih1 ih2 ih3
  case eq_congr ih1 ih2 ih3 => apply congr3 .eq .eq_congr1 .eq_congr2 .eq_congr3 ih1 ih2 ih3
  case conv_congr ih1 ih2 => apply congr2 (λ t1 t2 => .conv t1 t2 _) .conv_congr1 .conv_congr2 ih1 ih2

  theorem to_redstar : s =β>* t -> s -β>* t := by
  intro h
  induction h
  case _ => apply Red.refl
  case _ h _ ih => apply Red.trans (to_red h) ih

  theorem subst (σ τ : Subst Term) :
    (∀ n t t', σ n = .replace t -> τ n = .replace t' -> t =β> t') ->
    (∀ n k, σ n = .rename k -> τ n = .rename k) ->
    s =β> t -> [σ]s =β> [τ]t
  := by
  intro h1 h2 r
  sorry

  theorem complete : s =β> t -> t =β> pcompl s := by
  intro h
  induction h
  case beta m _ _ _ _ _ _ =>
    cases m <;> simp
    all_goals (
      apply subst
      case _ =>
        intro n t t' h1 h2; simp at *
        cases n <;> simp at *
        subst h1; subst h2; simp [*]
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

end Term.ParRed
