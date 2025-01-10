import Common
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification

namespace Fomega

  -- ⊢ (X : ★) -> X -> X
  @[simp]
  def IdTy : Term := .all mf ★ (.all mf (.bound .kind 0) (.bound .kind 1))

  -- ⊢ λ X:★. λ x:X. x
  @[simp]
  def id : Term := .lam mf ★ (.lam mf (.bound .kind 0) (.bound .type 0))

  -- ⊢ (X : ★) -> X
  @[simp]
  def Bot : Term := .all mf ★ (.bound .kind 0)

end Fomega
