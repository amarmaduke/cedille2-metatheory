
import Cedille2.Proof
import Fomega.Basic.Derivations
import Cedille2.FomegaModel.Interpretation
import Cedille2.FomegaModel.Normalization

namespace FomegaModel

  def ctt : Cedille2.Term := λτ[★] λf[#!0] λf[#!1] #1
  def cff : Cedille2.Term := λτ[★] λf[#!0] λf[#!1] #0

  theorem logical_consistency
    : ¬ ([] ⊢c t : cFalse)
  := by sorry

  theorem equational_consistency
    : ¬ ([] ⊢c t : .eq ctt cff)
  := by sorry

end FomegaModel
