import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification

namespace Fomega

  @[simp]
  def PairTy (A B : Term) : Term := .all mf ★ ()

end Fomega
