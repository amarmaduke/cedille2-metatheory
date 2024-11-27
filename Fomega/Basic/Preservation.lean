import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification

namespace Fomega.Proof

  theorem conv_ctx : t ⊢ Γ -> Γ ⊢ t : A ->
    (∀ n, Γ d@ n =β= Δ d@ n) ->
    t ⊢ Δ ∧ Δ ⊢ t : A
  := by
  intro cj j h
  sorry

  theorem preservation1 : Γ ⊢ t : A -> t -β> t' -> Γ ⊢ t' : A := by
  intro j r
  induction j generalizing t'
  case ax => cases r
  case var => cases r
  case pi => sorry
  case tpi => sorry
  case lam => sorry
  case app Γ f A' B a B' j1 j2 j3 ih1 ih2 =>
    cases r
    case beta C d => sorry
    case app_congr1 => sorry
    case app_congr2 => sorry
  case conv j1 j2 j3 ih1 ih2 =>
    apply Proof.conv; apply ih1 r
    apply j2; apply j3

  theorem preservation : Γ ⊢ t : A -> t -β>* t' -> Γ ⊢ t' : A := by
  intro j r
  induction r generalizing Γ A
  case _ => exact j
  case _ r1 _r2 ih => apply ih (preservation1 j r1)

  theorem preservation_type : Γ ⊢ t : A -> A -β>* A' -> Γ ⊢ t : A' := by sorry

end Fomega.Proof
