import Common
import Fomega.Term
import Fomega.Proof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification

namespace Fomega

  @[simp]
  def uid (t : Term) : Term := .unit_rec (u) t

  -- ⊢ (X : ★) -> X
  @[simp]
  def Bot : Term := Π[★] #0

end Fomega
