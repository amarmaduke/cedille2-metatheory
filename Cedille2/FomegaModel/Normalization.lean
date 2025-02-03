
import WCCC.Proof
import Fomega.Basic.Derivations
import WCCC.FomegaModel.Interpretation

namespace FomegaModel

  theorem red_preserved :
    Γ ⊢c t : A ->
    let ℓ := Γ.length
    t -β> s ->
    ∃ z, 𝓉 ℓ t -β>+ z ∧ 𝓉 ℓ s -β>* z
  := by
  intro j ℓ r
  induction r
  case beta => sorry
  case iproj1 =>
    simp at *; sorry
  case iproj2 => sorry
  case proj1 => sorry
  case proj2 => sorry
  case substelim => sorry
  case phi => sorry
  case unit_rec => sorry
  case conv_beta => sorry
  case conv_fst => sorry
  case conv_snd => sorry
  case conv_subst => sorry
  case conv_phi => sorry
  case conv_conv =>
    simp at *; sorry
  case lam_congr1 => sorry
  case lam_congr2 => sorry
  case app_congr1 => sorry
  case app_congr2 => sorry
  case all_congr1 => sorry
  case all_congr2 => sorry
  case inter_congr1 => sorry
  case inter_congr2 => sorry
  case inter_congr3 => sorry
  case pair_congr1 => sorry
  case pair_congr2 => sorry
  case fst_congr => sorry
  case snd_congr => sorry
  case inter_ty_congr1 => sorry
  case inter_ty_congr2 => sorry
  case times_congr1 => sorry
  case times_congr2 => sorry
  case refl_congr1 => sorry
  case refl_congr2 => sorry
  case subst_congr1 => sorry
  case subst_congr2 => sorry
  case phi_congr1 => sorry
  case phi_congr2 => sorry
  case phi_congr3 => sorry
  case phi_congr4 => sorry
  case eq_congr1 => sorry
  case eq_congr2 => sorry
  case eq_congr3 => sorry
  case conv_congr1 => sorry
  case conv_congr2 => sorry
  case unit_rec_congr1 => sorry
  case unit_rec_congr2 => sorry

  theorem fomega_sn_implies_sn :
    Γ ⊢c t : A ->
    let ℓ := Γ.length
    z -β>* 𝓉 ℓ t ->
    Term.SNPlus z ->
    Term.SN t
  := by
  intro j ℓ r h
  induction h generalizing t
  case _ s h ih =>
    constructor; intro y r2
    have lem := red_preserved j r2
    cases lem; case _ z lem =>

      sorry
  -- generalize sdef : 𝓉 ℓ t = s at *
  -- induction h generalizing t
  -- case _ s h ih =>
  --   rw [<-sdef] at ih
  --   constructor; intro t' r
  --   have lem := red_preserved j r
  --   cases lem; case _ z lem =>

  --     sorry
    --
    -- -- step here requires preservation (as expected)
    -- apply ih (𝓉 ℓ t') lem sorry rfl

  axiom fomega_sn {Γ : Ctx} {t A : Term} : Γ ⊢ω t : A -> Term.SN t

  theorem sn_term : Γ ⊢c t : A -> Term.SN t := by
  intro j; apply fomega_sn_implies_sn j
  let ℓ := Γ.length
  have lem1 : (γ Γ) ⊢ω (𝓉 ℓ t) : (𝒯 ℓ A) := by sorry
  have lem2 := fomega_sn lem1
  have lem3 : Γ.length = ℓ := by unfold ℓ; simp
  rw [lem3]; apply Term.sn_implies_snplus; apply lem2

end FomegaModel
