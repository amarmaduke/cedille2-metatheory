
import Cedille2.Proof
import Cedille2.Basic
import Fomega.Basic.Derivations
import Cedille2.FomegaModel.Interpretation

namespace FomegaModel

  @[simp]
  abbrev KindSoundnessLemmaType : (v : Cedille2.JudgmentVariant) -> Cedille2.JudgmentIndex v -> Prop
  | .prf => λ (t, A) => A = (□ : Cedille2.Term) -> ∀ Δ, ⊢ω Δ -> Δ ⊢ 𝒱 t : □
  | .wf => λ _ => True

  theorem kind_soundness_lemma : Cedille2.Judgment v Γ ix -> KindSoundnessLemmaType v ix := by
  intro j
  induction j <;> simp at *
  case _ => intro Δ wf; constructor; apply wf
  case _ j1 j2 ih =>
    intro e Δ wf; subst e; rw [<-j2] at j1
    exfalso; apply Cedille2.Proof.kind_not_proof j1
  case _ Γ A m K B j1 j2 ih1 ih2 =>
    intro e Δ wf
    cases m <;> simp at *
    case _ =>
      split
      case _ h =>
        have lem := Cedille2.Proof.classify_kind j1 h
        injection lem with e; subst e; simp at *
        have lem1 := ih1 _ wf
        have lem2 : ⊢ω (𝒱 A :: Δ) := by
          constructor; apply wf; apply lem1
        constructor; apply lem1
        apply ih2 _ lem2
        constructor
      case _ h =>
        cases K <;> simp at *
        case _ =>
          have lem := Cedille2.Proof.is_kind_forces_classify j1 rfl
          exfalso; apply h lem
        case _ =>
          have lem2 : ⊢ω (★ :: Δ) := by
            constructor; apply wf; constructor; apply wf
          constructor; constructor; apply wf
          apply ih2 _ lem2
          constructor
  case _ j1 j2 j3 ih1 ih2 =>
    intro e Δ wf; subst e
    -- by: classification, inversion on `∀(m)[A][B], substitution, □ not a subexpr
    sorry
  case _ =>
    -- by: classification and □ not a subexpr
    sorry
  case _ =>
    -- by: classification and □ not a subexpr
    sorry
  case _ j1 j2 j3 ih1 ih2 =>
    intro h Δ wf; subst h
    exfalso; apply Cedille2.Proof.kind_not_proof j2
  case _ j1 j2 j3 ih1 ih1 =>
    intro h Δ wf; subst h
    exfalso; apply Cedille2.Proof.kind_not_proof j2

  theorem kind_soundness :
    Γ ⊢c t : □ ->
    ∀ Δ, ⊢ω Δ -> Δ ⊢ 𝒱 t : □
  := by
  intro j
  apply kind_soundness_lemma j rfl

  @[simp]
  abbrev TypeSoundnessLemmaType (Γ : Ctx Cedille2.Term) : (v : Cedille2.JudgmentVariant) -> Cedille2.JudgmentIndex v -> Prop
  | .prf => λ (t, A) => Γ ⊢c A : □ -> γ' Γ ⊢ 𝒯 t : 𝒱 A
  | .wf => λ _ => True

  theorem type_soundness_lemma : Cedille2.Judgment v Γ ix -> TypeSoundnessLemmaType Γ v ix := by
  intro j; induction j <;> simp
  case _ =>
    intro j; exfalso
    apply Cedille2.Proof.kind_not_proof j
  case _ Γ x K T j1 j2 ih =>
    intro j3; cases K <;> simp at *
    case _ =>

      sorry
    case _ =>

      sorry
  case _ Γ A m K B j1 j2 ih1 ih2 =>
    intro j3; cases m <;> simp at *
    case _ =>
      have lem1 := Cedille2.Proof.is_type_forces_classify j1 j3
      replace ih1 := ih1 j3
      replace ih2 := ih2 (Cedille2.Proof.weaken j1 j3)
      rw [lem1]; rw [lem1] at ih2; simp at *
      sorry
    case _ => sorry
    case _ =>
      exfalso; apply Cedille2.Proof.kind_not_proof j3
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ =>
    intro j; cases j
    case _ j =>
      exfalso; apply Cedille2.Proof.kind_not_proof j
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ =>
    intro j; cases j
    case _ j =>
      exfalso; apply Cedille2.Proof.kind_not_proof j
  case _ => sorry
  case _ =>
    intro j; cases j
    case _ j =>
      exfalso; apply Cedille2.Proof.kind_not_proof j
  case _ => sorry
  case _ => sorry

  theorem type_soundness :
    Γ ⊢c t : A ->
    Γ ⊢c A : □ ->
    γ' Γ ⊢ 𝒯 t : 𝒱 A
  := by sorry

  theorem term_soundness :
    Γ ⊢c t : A ->
    γ Γ ⊢ 𝓉 t : 𝒯 A
  := by sorry

end FomegaModel
