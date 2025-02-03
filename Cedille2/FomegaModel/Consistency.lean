
import WCCC.Proof
import WCCC.Proof.Derivations
import Fomega.Basic.Derivations
import WCCC.FomegaModel.Interpretation
import WCCC.FomegaModel.Normalization

namespace FomegaModel

  theorem equational_consistency
    : ¬ ([] ⊢c t : .eq cBool ctt cff)
  := by sorry

  theorem logical_consistency
    : ¬ ([] ⊢c t : cFalse)
  := by sorry


end FomegaModel
