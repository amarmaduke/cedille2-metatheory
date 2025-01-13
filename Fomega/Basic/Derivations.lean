import Common
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification

namespace Fomega

  @[simp]
  def uid (t : Term) : Term := .unit_rec .unit t

  -- ⊢ (X : ★) -> X
  @[simp]
  def Bot : Term := ∀f[★] 0!!

end Fomega
