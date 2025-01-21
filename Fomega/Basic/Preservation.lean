import Common
import Fomega.Proof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Classification

namespace Fomega.Proof

  @[simp]
  abbrev LamDestructLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, T) => ∀ A b B, t = `λ b -> T =β= Π[A] B ->
    ∃ C, ((∃ K, A =β= C ∧ Γ ⊢ C : .const K)
    ∧ (∃ K D, B =β= D ∧ (C::Γ) ⊢ D : .const K ∧ (C::Γ) ⊢ b : D))
  | .wf => λ () => True

  theorem lam_destruct_lemma : Judgment v Γ ix -> LamDestructLemmaType Γ v ix := by
  intro j; induction j <;> simp at *
  case lam A' K1 K2 B' t j1 j2 j3 _ _ _ =>
    intro A b B h1 h2; subst h1
    have lem := Red.Conv.all_congr h2; exists A'
    apply And.intro; apply And.intro; apply Red.Conv.sym lem.1
    exists (dom K1 K2); exists K2; exists B'; apply And.intro
    apply Red.Conv.sym lem.2; apply And.intro; apply j2; apply j3
  case conv A' B' _ _ _ cv ih1 _ih2 =>
    intro A b B h1 h2; subst h1
    have lem := Red.Conv.trans cv h2
    apply ih1 A b B rfl lem

  @[simp]
  abbrev PairDestructLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, T) => ∀ c d A B, t = .pair c d -> T =β= .times A B ->
    (∃ C, A =β= C ∧ Γ ⊢ c : C ∧ Γ ⊢ C : ★)
    ∧ (∃ D, B =β= D ∧ Γ ⊢ d : D ∧ Γ ⊢ D : ★)
  | .wf => λ () => True

  theorem pair_destruct_lemma : Judgment v Γ ix -> PairDestructLemmaType Γ v ix := by
  intro j; induction j <;> simp at *
  case pair Γ a A b B j1 j2 j3 j4 _ _ _ _ =>
    intro c d A' B' h1 h2 h3; subst h1; subst h2
    have lem := Red.Conv.times_congr h3
    apply And.intro; exists A; apply And.intro; apply Red.Conv.sym lem.1
    apply And.intro; apply j1; apply j3
    exists B; apply And.intro; apply Red.Conv.sym lem.2
    apply And.intro; apply j2; apply j4
  case conv A' B' _ _ _ cv ih1 _ih2 =>
    intro c d A B h1 h2; subst h1
    have lem := Red.Conv.trans cv h2
    apply ih1 c d A B rfl lem

  inductive CtxRed : Ctx Term -> Ctx Term -> Prop where
  | nil : CtxRed [] []
  | head : A -β> A' -> CtxRed Γ Γ' -> CtxRed (A::Γ) (A'::Γ')
  | tail : CtxRed Γ Γ' -> CtxRed (A::Γ) (A::Γ')

  namespace CtxRed
    theorem refl : CtxRed Γ Γ := by
    induction Γ
    case _ => constructor
    case _ hd tl ih => apply tail; apply ih

    theorem nth x : CtxRed Γ Γ' -> Γ d@ x = Γ' d@ x ∨ Γ d@ x -β> Γ' d@ x := by
    intro j; induction j generalizing x; simp
    case _ A A' Γ Γ' r1 _r2 ih =>
      cases x <;> simp
      case _ => apply Or.inr; apply Red.red1_subst_same; apply r1
      case _ x =>
        cases (ih x)
        case _ ih => rw [ih]; apply Or.inl rfl
        case _ ih => apply Or.inr; apply Red.red1_subst_same; apply ih
    case _ Γ Γ' A _ ih =>
      cases x <;> simp
      case _ x =>
        cases (ih x)
        case _ h => apply Or.inl; rw [h]
        case _ h => apply Or.inr; apply Red.red1_subst_same; apply h
  end CtxRed

  @[simp]
  abbrev Preservation1Type (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, A) => ∀ {t' Γ'}, t = t' ∨ t -β> t' -> CtxRed Γ Γ' -> Γ' ⊢ t' : A
  | .wf => λ () => ∀ {Γ'}, CtxRed Γ Γ' -> ⊢ Γ' ∧ (∀ x, ∃ K, Γ' ⊢ Γ d@ x : .const K)

  theorem preservation1 : Judgment v Γ ix -> Preservation1Type Γ v ix := by
  intro j; induction j <;> simp at *
  case nil =>
    intro Γ' r
    cases r; apply And.intro
    constructor; exists .kind
    unfold default; unfold instInhabited_Term; simp
    constructor; constructor
  case cons Γ A K j1 j2 ih1 ih2 =>
    intro Γ' r
    cases r
    case _ r1 r2 =>
      apply And.intro
      case _ => constructor; apply (ih1 r2).1; apply ih2 (Or.inr r1) r2
      case _ =>
        intro x; cases x <;> simp at *
        case _ =>
          have lem := ih2 (Or.inl rfl) r2
          have lem2 := ih2 (Or.inr r1) r2
          replace lem := weaken lem2 lem; simp at lem
          exists K
        case _ x =>
          have lem := (ih1 r2).2 x
          cases lem; case _ K lem =>
            have lem2 := ih2 (Or.inr r1) r2
            replace lem := weaken lem2 lem; simp at lem
            exists K
    case _ Γ' r =>
      apply And.intro
      case _ => constructor; apply (ih1 r).1; apply ih2 (Or.inl rfl) r
      case _ =>
        intro x; cases x <;> simp at *
        case _ =>
          have lem := ih2 (Or.inl rfl) r
          replace lem := weaken lem lem; simp at *
          exists K
        case _ x =>
          have lem := (ih1 r).2 x
          cases lem; case _ K lem =>
            have lem2 := ih2 (Or.inl rfl) r
            replace lem := weaken lem2 lem; simp at lem
            exists K
  case ax Γ j ih =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 => rw [<-r1]; constructor; apply (ih r2).1
    case _ r1 => cases r1
  case var Γ T x j1 j2 ih =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 =>
      rw [<-r1]; have lem := CtxRed.nth x r2
      cases lem
      case _ r => constructor; apply (ih r2).1; rw [j2, r]
      case _ r =>
        have lem := (ih r2).2 x
        cases lem; case _ K lem =>
          apply @Judgment.conv _ _ (Γ' d@ x) _ K
          constructor; apply (ih r2).1; rfl
          rw [j2]; apply lem; rw [j2]
          exists Γ' d@ x; apply And.intro
          apply Star.refl; apply Star.step Star.refl r
    case _ r1 => cases r1
  case pi Γ A K1 K2 B j1 j2 ih1 ih2 =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 =>
      rw [<-r1]; constructor; apply ih1 (Or.inl rfl) r2
      apply ih2 (Or.inl rfl) (.tail r2)
    case _ r1 =>
      cases r1
      case _ A' r1 =>
        constructor; apply ih1 (Or.inr r1) r2
        apply ih2 (Or.inl rfl) (.head r1 r2)
      case _ B' r1 =>
        constructor; apply ih1 (Or.inl rfl) r2
        apply ih2 (Or.inr r1) (.tail r2)
  case lam Γ A K1 K2 B t j1 j2 j3 ih1 ih2 ih3 =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 =>
      rw [<-r1]; constructor
      apply ih1 (Or.inl rfl) r2
      apply ih2 (Or.inl rfl) (.tail r2)
      apply ih3 (Or.inl rfl) (.tail r2)
    case _ r1 =>
      cases r1
      case _ t' r1 =>
        constructor; apply ih1 (Or.inl rfl) r2
        apply ih2 (Or.inl rfl) (.tail r2)
        apply ih3 (Or.inr r1) (.tail r2)
  case app Γ f A B a B' j1 j2 j3 ih1 ih2 =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 =>
      rw [<-r1]; constructor; apply ih1 (Or.inl rfl) r2
      apply ih2 (Or.inl rfl) r2; apply j3
    case _ r1 =>
      cases r1
      case _ A' b =>
        replace ih1 := ih1 (Or.inl rfl) r2
        replace ih2 := ih2 (Or.inl rfl) r2
        have lem := lam_destruct_lemma ih1; simp at lem
        replace lem := lem A b B rfl Red.Conv.refl
        cases lem; case _ A' lem =>
        cases lem.1.2; case _ K1 lem2 =>
        cases lem.2; case _ k2 lem3 =>
        cases lem3; case _ D lem3 =>
          have ih2' : Γ' ⊢ a : A' := by
            apply Judgment.conv; apply ih2
            apply lem2; apply lem.1.1
          have lem4 := Proof.beta lem3.2.2 ih2'; simp at *; rw [j3]
          have lem5 := classification ih1
          cases lem5 <;> simp at *; case _ lem5 =>
          cases lem5; case _ K3 lem5 =>
            have lem6 := all_destruct_lemma lem5; simp at lem6
            replace lem6 := lem6 A B K3 rfl rfl Red.Conv.refl
            replace lem6 := Proof.beta lem6 ih2; simp at lem6
            apply Judgment.conv; apply lem4; apply lem6
            apply Red.Conv.subst_same; apply Red.Conv.sym; apply lem3.1
      case _ f' r1 =>
        constructor; apply ih1 (Or.inr r1) r2
        apply ih2 (Or.inl rfl) r2; apply j3
      case _ a' r1 =>
        replace j1 := ih1 (Or.inl rfl) r2
        replace j2 := ih2 (Or.inl rfl) r2
        have lem1 := classification j1
        cases lem1 <;> simp at *; case _ lem1 =>
          cases lem1; case _ K lem1 =>
            have lem2 := all_destruct_lemma lem1; simp at lem2
            replace lem2 := lem2 A B K rfl rfl Red.Conv.refl
            have lem3 := Proof.beta lem2 j2; simp at lem3
            apply @Judgment.conv _ _ (B β[a']) _ K
            constructor; apply j1; apply ih2 (Or.inr r1) r2; rfl
            rw [j3]; apply lem3; rw [j3]; simp
            apply Red.Conv.subst
            intro n t h1; cases n <;> simp at *; subst h1
            exists a'; apply And.intro
            apply Star.refl; apply Star.step Star.refl r1
            intro n k h1; cases n <;> simp at *; apply h1
            apply Red.Conv.refl
  case prod Γ A B j1 j2 ih1 ih2 =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 =>
      rw [<-r1]; constructor; apply ih1 (Or.inl rfl) r2
      apply ih2 (Or.inl rfl) r2
    case _ r1 =>
      cases r1
      case _ A' r1 => constructor; apply ih1 (Or.inr r1) r2; apply ih2 (Or.inl rfl) r2
      case _ B' r1 => constructor; apply ih1 (Or.inl rfl) r2; apply ih2 (Or.inr r1) r2
  case pair Γ a A b B j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 =>
      rw [<-r1]; constructor; apply ih1 (Or.inl rfl) r2
      apply ih2 (Or.inl rfl) r2; apply ih3 (Or.inl rfl) r2
      apply ih4 (Or.inl rfl) r2
    case _ r1 =>
      cases r1
      case _ a' r1 =>
        constructor; apply ih1 (Or.inr r1) r2; apply ih2 (Or.inl rfl) r2
        apply ih3 (Or.inl rfl) r2; apply ih4 (Or.inl rfl) r2
      case _ b' r1 =>
        constructor; apply ih1 (Or.inl rfl) r2; apply ih2 (Or.inr r1) r2
        apply ih3 (Or.inl rfl) r2; apply ih4 (Or.inl rfl) r2
  case fst Γ t A B j ih =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 => rw [<-r1]; constructor; apply ih (Or.inl rfl) r2
    case _ r1 =>
      cases r1
      case _ s =>
        replace ih := ih (Or.inl rfl) r2
        have lem := pair_destruct_lemma ih; simp at lem
        replace lem := lem t' s A B rfl rfl Red.Conv.refl
        have lem2 := classification ih; simp at lem2
        cases lem2; case _ K lem2 =>
        cases lem.1; case _ C lem =>
          replace lem2 := times_destruct_lemma lem2; simp at lem2
          replace lem2 := lem2 A B K rfl rfl Red.Conv.refl
          apply Judgment.conv; apply lem.2.1; apply lem2.1
          apply Red.Conv.sym; apply lem.1
      case _ t' r1 => constructor; apply ih (Or.inr r1) r2
  case snd Γ t A B j ih =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 => rw [<-r1]; constructor; apply ih (Or.inl rfl) r2
    case _ r1 =>
      cases r1
      case _ s =>
        replace ih := ih (Or.inl rfl) r2
        have lem := pair_destruct_lemma ih; simp at lem
        replace lem := lem s t' A B rfl rfl Red.Conv.refl
        have lem2 := classification ih; simp at lem2
        cases lem2; case _ K lem2 =>
        cases lem.2; case _ C lem =>
          replace lem2 := times_destruct_lemma lem2; simp at lem2
          replace lem2 := lem2 A B K rfl rfl Red.Conv.refl
          apply Judgment.conv; apply lem.2.1; apply lem2.2
          apply Red.Conv.sym; apply lem.1
      case _ t' r1 => constructor; apply ih (Or.inr r1) r2
  case unit Γ j ih =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 => rw [<-r1]; constructor; apply (ih r2).1
    case _ r1 => cases r1
  case unit_ty Γ j ih =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 => rw [<-r1]; constructor; apply (ih r2).1
    case _ r1 => cases r1
  case unit_rec Γ u t A j1 j2 j3 ih1 ih2 ih3 =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 =>
      rw [<-r1]; constructor; apply ih1 (Or.inl rfl) r2
      apply ih2 (Or.inl rfl) r2; apply ih3 (Or.inl rfl) r2
    case _ r1 =>
      cases r1
      case _ => apply ih2 (Or.inl rfl) r2
      case _ u' r1 =>
        constructor; apply ih1 (Or.inr r1) r2
        apply ih2 (Or.inl rfl) r2; apply ih3 (Or.inl rfl) r2
      case _ t' r1 =>
        constructor; apply ih1 (Or.inl rfl) r2
        apply ih2 (Or.inr r1) r2; apply ih3 (Or.inl rfl) r2
  case conv j1 j2 j3 ih1 ih2 =>
    intro t' Γ' r1 r2
    constructor; apply ih1 r1 r2; apply ih2 (Or.inl rfl) r2
    apply j3

  theorem preservation_term : Γ ⊢ t : A -> t -β>* t' -> Γ ⊢ t' : A := by
  intro j r; induction r
  case _ => apply j
  case _ _ r2 ih => apply preservation1 ih (Or.inr r2) CtxRed.refl

  theorem preservation_ctx : Γ ⊢ t : A -> @Star (Ctx Term) CtxRed Γ Γ' -> Γ' ⊢ t : A := by
  intro j r; induction r
  case _ => apply j
  case _ r2 ih => apply preservation1 ih (Or.inl rfl) r2

  theorem preservation_type : Γ ⊢ t : A -> A -β>* A' -> Γ ⊢ t : A' := by
  intro j r
  have lem := classification j
  cases lem
  case _ h =>
    subst h
    have lem := Red.red_const_forces_const r
    subst lem; apply j
  case _ h =>
    cases h; case _ K h =>
      apply Judgment.conv; apply j
      apply preservation_term; apply h; apply r
      exists A'; apply And.intro; apply r; apply Star.refl

  theorem preservation_wf : ⊢ Γ -> @Star (Ctx Term) CtxRed Γ Γ' -> ⊢ Γ' := by
  intro j r
  induction r
  case _ => apply j
  case _ r2 ih => apply (preservation1 ih r2).1

  theorem preservation :
    Γ ⊢ t : A ->
    @Star (Ctx Term) CtxRed Γ Γ' ->
    t -β>* t' ->
    A -β>* A' ->
    Γ' ⊢ t' : A'
  := by
  intro j r1 r2 r3
  replace j := preservation_ctx j r1
  replace j := preservation_term j r2
  replace j := preservation_type j r3
  apply j

end Fomega.Proof
