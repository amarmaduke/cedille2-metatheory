import Common
import Realizer.Term

namespace Realizer
  inductive Red : Term -> Term -> Prop where
  | beta : Red ((`λ b) `@ t) (b β[t])
  | app_congr1 : Red f f' -> Red (f `@ a) (f' `@ a)
  | app_congr2 : Red a a' -> Red (f `@ a) (f `@ a')
  | lam_congr : Red t t' -> Red (`λ t) (`λ t')

  inductive ParRed : Term -> Term -> Prop where
  | beta : ParRed b b' -> ParRed t t' -> ParRed ((`λ b) `@ t) (b' β[t'])
  | app : ParRed f f' -> ParRed a a' -> ParRed (f `@ a) (f' `@ a')
  | lam : ParRed t t' -> ParRed (`λ t) (`λ t')
  | var : ParRed (.var x) (.var x)

  infix:40 " -β> " => Red
  infix:40 " =β> " => ParRed
  notation:39 x:39 " -β>* " y:39 => Star Red x y
  notation:39 x:39 " =β>* " y:39 => Star ParRed x y
  notation:38 x:38 " =β= " y:38 => Conv Red x y

  namespace ParRed
    @[simp]
    def compl : Term -> Term
    | `λt `@  a => (compl t) β[compl a]
    | f `@ a => (compl f) `@ (compl a)
    | `λt => `λ(compl t)
    | .var x => .var x

    theorem refl : t =β> t := by
    induction t <;> constructor <;> simp [*]

    theorem subst_same σ : s =β> t -> [σ]s =β> [σ]t := by
    intro h; induction h generalizing σ <;> simp
    case _ b b' t t' _ _ ih1 ih2 =>
      have lem : (`λ([^σ]b) `@ ([σ]t)) =β> ([^σ]b') β[[σ]t'] := by
        apply ParRed.beta (ih1 ^σ) (ih2 _)
      simp at lem; apply lem
    any_goals try (
      case _ ih1 ih2 =>
        constructor; apply ih1; apply ih2
    )
    case _ ih => constructor; apply ih
    all_goals apply refl

    theorem subst (σ τ : Subst Term) :
      (∀ n t, σ n = .su t -> ∃ t', τ n = .su t' ∧ t =β> t') ->
      (∀ n k, σ n = .re k -> τ n = .re k) ->
      s =β> t -> [σ]s =β> [τ]t
    := by
    intro h1 h2 r
    induction r generalizing σ τ <;> simp
    case _ b b' t t' _ _ ih1 ih2 =>
      have lem : (`λ([^σ]b) `@ ([σ]t)) =β> ([^τ]b') β[[τ]t'] := by
        apply ParRed.beta
        replace ih1 := ih1 (^σ) (^τ) (Subst.lift_replace subst_same h1) (Subst.lift_rename h2)
        apply ih1; apply ih2 _ _ h1 h2
      simp at lem; apply lem
    all_goals try (
      case _ ih1 ih2 =>
        constructor; apply ih1 _ _ h1 h2; apply ih2 _ _ h1 h2
    )
    case _ _ ih =>
      constructor
      replace ih := ih (^σ) (^τ) (Subst.lift_replace subst_same h1) (Subst.lift_rename h2)
      simp at ih; apply ih
    all_goals try (
      case _ _ ih1 ih2 =>
        constructor; apply ih1 _ _ h1 h2
        replace ih2 := ih2 (^σ) (^τ) (Subst.lift_replace subst_same h1) (Subst.lift_rename h2)
        simp at ih2; apply ih2
    )
    case _ x =>
      generalize udef : σ x = u
      cases u <;> simp at *
      case _ y => rw [h2 x y udef]; simp; constructor
      case _ t =>
        cases (h1 x t udef); case _ v lem =>
          rw [lem.1]; simp; apply lem.2

    theorem red_beta : b =β> b' -> t =β> t' -> b β[t] =β> b' β[t'] := by
    intro r1 r2; apply subst
    case _ =>
      intro n s h; cases n <;> simp at *
      case _ => subst h; apply r2
    case _ =>
      intro n k h; cases n <;> simp at *; simp [*]
    case _ => apply r1

    theorem triangle : t =β> s -> s =β> compl t := by
    intro h; induction h <;> simp at * <;> try (constructor <;> simp [*])
    case _ b b' t t' r1 r2 ih1 ih2 => apply red_beta ih1 ih2
    case _ f f' a a' r2 _ ih1 ih2 =>
      cases f <;> simp at * <;> try (constructor <;> simp [*])
      case _ t =>
        cases f'; all_goals (try cases r2)
        case _ b =>
          cases ih1; case _ ih1 =>
            apply ParRed.beta ih1 ih2

    instance instReductionTriangle_ParRed : ReductionTriangle Term ParRed where
      compl := compl
      triangle := triangle
  end ParRed

  namespace Red
    theorem to_parred : x -β> y -> x =β> y := by
    intro h; induction h
    all_goals (try case _ ih => constructor; apply ih; apply ParRed.refl)
    all_goals (try case _ ih => constructor; apply ParRed.refl; apply ih)
    case _ => constructor; apply ParRed.refl; apply ParRed.refl
    case _ ih => constructor; apply ih

    theorem to_parred_star : x -β>* y -> x =β>* y := by
    intro r; induction r
    case _ => apply Star.refl
    case _ r1 r2 ih =>
      apply Star.step ih
      apply to_parred r2

    theorem from_parred : x =β> y -> x -β>* y := by
    intro r; induction r
    case _ ih1 ih2 =>
      apply Star.step
      apply Star.congr2 (λ t1 t2 => `λ t1 `@ t2) (λ r => Red.app_congr1 (Red.lam_congr r)) .app_congr2 ih1 ih2
      apply Red.beta
    case _ ih1 ih2 =>
      apply Star.congr2 (λ t1 t2 => t1 `@ t2) .app_congr1 .app_congr2 ih1 ih2
    case _ ih =>
      apply Star.congr1 (λ t => `λ t) .lam_congr ih
    case _ => apply Star.refl

    theorem from_parred_star : x =β>* y -> x -β>* y := by
    intro r; induction r
    case _ => apply Star.refl
    case _ r1 r2 ih =>
      apply Star.trans ih
      apply from_parred r2

    theorem confluence : t -β>* u -> t -β>* v -> u =β= v := by
    intro r1 r2
    replace r1 := to_parred_star r1
    replace r2 := to_parred_star r2
    have lem := Star.confluence r1 r2
    cases lem; case _ w r =>
      replace r1 := from_parred_star r.1
      replace r2 := from_parred_star r.2
      exists w

    theorem subst_same σ : x -β> y -> [σ]x -β> [σ]y := by
    intro r; induction r generalizing σ
    case _ b t =>
      simp; have lem : ((`λ [^σ]b) `@ [σ]t) -β> ([^σ]b) β[[σ]t] := @Red.beta ([^σ]b) ([σ]t)
      simp at lem; apply lem
    case _ ih => simp; apply Red.app_congr1 (ih σ)
    case _ ih => simp; apply Red.app_congr2 (ih σ)
    case _ r ih =>
      simp; replace ih := ih ^σ; simp at ih
      apply Red.lam_congr ih

    theorem subst σ τ :
      (∀ n t, σ n = .su t -> ∃ t', τ n = .su t' ∧ t -β>* t') ->
      (∀ n k, σ n = .re k -> τ n = .re k) ->
      t -β> s ->
      ([σ]t) -β>* ([τ]s)
    := by
    intro h1 h2 r; induction r generalizing σ τ <;> simp
    case _ b x =>
      have lem : ((`λ [^σ]b) `@ [σ]x) -β> ([^τ]b) β[[τ]x] := by

        sorry
      simp at lem; apply Star.stepr lem Star.refl
    case _ => sorry
    case _ => sorry
    case _ => sorry


  end Red

  instance instReductionRespectsSubstitution_Red : ReductionRespectsSubstitution Term Red where
    subst := Red.subst_same

  theorem normal_no_redex : t.normal -> ∀ t', ¬ t -β> t' := by
  intro h t' r
  induction h generalizing t'
  case _ => cases r
  case _ h1 h2 h3 ih1 ih2 =>
    cases r
    case _ => unfold Term.neutral at h1; simp at h1
    case _ r => apply ih1 _ r
    case _ r => apply ih2 _ r
  case _ h ih =>
    cases r
    case _ r => apply ih _ r

  theorem redex_decide t : t.normal ∨ (∃ t', t -β> t') := by
  induction t
  case var => apply Or.inl; constructor
  case app f a ih1 ih2 =>
    cases ih1
    case inl ih1 =>
      cases ih2
      case inl ih2 =>
        generalize zdef : f.neutral = z
        cases z
        case false =>
          unfold Term.neutral at zdef
          cases f <;> simp at zdef
          case lam b =>
            apply Or.inr; apply Exists.intro (b β[a])
            apply Red.beta
        case true =>
          apply Or.inl; constructor
          apply zdef; apply ih1; apply ih2
      case inr ih2 =>
        cases ih2; case intro a' r =>
          apply Or.inr; apply Exists.intro (f `@ a')
          apply Red.app_congr2 r
    case inr ih1 =>
      cases ih1; case intro f' r =>
        apply Or.inr; apply Exists.intro (f' `@ a)
        apply Red.app_congr1 r
  case lam t ih =>
    cases ih
    case inl ih =>
      apply Or.inl; constructor
      apply ih
    case inr ih =>
      cases ih; case intro t' r =>
      apply Or.inr; apply Exists.intro (`λ t')
      apply Red.lam_congr r

end Realizer
