import Common
import Fomega.Term
import Fomega.Proof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification

namespace Fomega

  def uid (t : Term) : Term := .unit_rec (u) (u) t

  def uid2 (t1 t2 : Term) : Term := .unit_rec t2 (u) t1

  -- ⊢ (X : ★) -> X
  @[simp]
  def Bot : Term := Π[★] #0

end Fomega
