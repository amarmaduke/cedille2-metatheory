
import Common
import Cedille2.Proof
import Fomega.Basic.Derivations
import Cedille2.FomegaModel.Interpretation

namespace FomegaModel

  theorem red_preserved :
    Γ ⊢c t : A ->
    t -β> s ->
    𝓉 t -β>+ 𝓉 s
  := by
  intro j r; sorry

  theorem fomega_sn_implies_sn :
    Γ ⊢c t : A ->
    @SNPlus _ Fomega.Red (𝓉 t) ->
    @SN _ Cedille2.Red t
  := by
  sorry

  axiom fomega_sn {Γ : Ctx Fomega.Term} {t A : Fomega.Term} : Γ ⊢ω t : A -> @SN _ Fomega.Red t

  theorem sn_term : Γ ⊢c t : A -> @SN _ Cedille2.Red t := by
  intro j; apply fomega_sn_implies_sn j
  have lem1 : (γ Γ) ⊢ω (𝓉 t) : (𝒯 A) := by sorry
  have lem2 := fomega_sn lem1
  apply sn_implies_snplus; apply lem2

end FomegaModel
