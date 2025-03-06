
import Cedille2.Proof
import Fomega.Basic.Derivations
import Cedille2.FomegaModel.Interpretation
import Cedille2.FomegaModel.Normalization

namespace FomegaModel

  @[simp]
  abbrev KindSoundnessLemmaType : (v : Cedille2.JudgmentVariant) -> Cedille2.JudgmentIndex v -> Prop
  | .prf => λ (t, A) => A = (□ : Cedille2.Term) -> ∀ Δ, ⊢ω Δ -> Δ ⊢ 𝒱 t : □
  | .wf => λ _ => True

  theorem kind_soundness_lemma : Cedille2.Judgment v Γ ix -> KindSoundnessLemmaType v ix := by
  intro j
  induction j <;> simp at *
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry

  theorem kind_soundness :
    Γ ⊢c t : □ ->
    ∀ Δ, ⊢ω Δ -> Δ ⊢ 𝒱 t : □
  := by
  intro j
  apply kind_soundness_lemma j rfl

  theorem type_soundness :
    Γ ⊢c t : A ->
    Γ ⊢c A : □ ->
    γ Γ ⊢ 𝒯 t : 𝒱 A
  := by sorry

  theorem term_soundness :
    Γ ⊢c t : A ->
    γ Γ ⊢ 𝓉 t : 𝒯 A
  := by sorry

end FomegaModel
