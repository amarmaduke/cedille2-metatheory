import Common
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification

namespace Fomega

  -- A, B ⊢ (X : ★) -> (A -> B -> X) -> X
  @[simp]
  def PairTy (A B : Term) : Term := .all mf ★ (.all mf
    (.all mf A (.all mf B (.bound .kind 2)))
    (.bound .kind 0))

  -- A, B, a, b ⊢ λ X : ★. λ ctor : (A -> B -> X). ctor a b
  @[simp]
  def pair (A B a b : Term) : Term := .lam mf ★
    (.lam mf (.all mf A (.all mf B (.bound .kind 2)))
      (.app mf (.app mf (.bound .type 0) a) b))

  -- A B p ⊢ p A (λ a b. a)
  @[simp]
  def fst (A B p : Term) : Term := .app mf
    (.app mf p A)
    (.lam mf A (.lam mf B (.bound .type 1)))

  -- A B p ⊢ p A (λ a b. b)
  @[simp]
  def snd (A B p : Term) : Term := p `@f A `@f (.lam mf A (.lam mf B (.bound .type 0)))

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
