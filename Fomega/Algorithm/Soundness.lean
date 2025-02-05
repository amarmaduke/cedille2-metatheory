import Fomega.Proof
import Fomega.Basic
import Fomega.Algorithm

namespace Fomega

  theorem infer_kind_sound :
    infer_kind Γ t = .some A ->
    ⊢ Γ ->
    Γ ⊢ t : A
  := by
    intro h1 h2
    induction Γ, t using infer_kind.induct generalizing A
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry

end Fomega
