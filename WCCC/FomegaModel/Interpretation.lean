
import WCCC.Proof
import Fomega.Basic.Derivations

namespace FomegaModel

  @[simp]
  def 𝒱 : Term -> Term
  | □ | ★ => ★
  | .all _ A B =>
    if A.classify = .kind then .all mf (𝒱 A) (𝒱 B)
    else 𝒱 B
  | _ => .none

  -- 𝓉
  @[simp]
  def 𝒯 : Term -> Term
  | □ | ★ => .bound .kind 0
  | .bound .kind x => .bound .kind x
  | .all _ A B =>
    if A.classify = .kind then
      .all mf (𝒱 A) (.all mf (𝒯 A) (𝒯 B))
    else if A.classify = .type then
      .all mf ★ (.all mf (𝒯 A) (𝒯 B))
    else .none
  | .lam .type A t =>
    if A.classify = .kind then .lam mf (𝒱 A) (𝒯 t)
    else if A.classify = .type then 𝒯 t
    else .none
  | .app .type f a =>
    if a.classify = .type then .app mf (𝒯 f) (𝒯 a)
    else if a.classify = .term then 𝒯 f
    else .none
  | .prod A B => Fomega.PairTy A B
  | .eq _ _ _ => Fomega.IdTy
  | _ => .none

  @[simp]
  def γ : Ctx -> Ctx
  | [] => ★ :: Fomega.Bot :: []
  | .cons A Γ =>
    if A.classify = .kind then (𝒯 A) :: (𝒱 A) :: (γ Γ)
    else (𝒯 A) :: (𝒯 A) :: (γ Γ)

  def g0 (ℓ : Nat) : Term := .bound .kind (ℓ - 2)
  def gBot (ℓ : Nat) : Term := .bound .type (ℓ - 1)

  @[simp]
  def canon (ℓ : Nat) : Term -> Term
  | ★ => g0 ℓ
  | .all mf A B =>
    if B.classify = .kind then .lam mf A (canon ℓ B)
    else (gBot ℓ) `@τ (.all mf A B)
  | B => (gBot ℓ) `@τ B

  @[simp]
  def 𝓉 (ℓ : Nat) : Term -> Term -> Term
  | ★, _ => c zr
  | .bound .type x, _ => .bound .kind (2*x)
  | .bound .kind x, _ => .bound .type (2*x + 1)
  | .all _ A B, _ =>
    if A.classify = .kind then
      c (∀f[zr] ∀f[zr] zr) `@f 𝓉' A `@f (𝓉' B) β[c (𝒯 A)] β[c (𝒱 A)]
    else
      c (∀f[zr] ∀f[zr] zr) `@f 𝓉' A `@f (𝓉' B) β[c (𝒯 A)] β[zr]
  | .lam _ A t, _ =>
    if A.classify = .kind then
      (λf[zr] λf[𝒱 A] λf[𝒯 A] 𝓉' t) `@f 𝓉' A
    else
      (λf[zr] λf[★] λf[𝒯 A] 𝓉' t) `@f 𝓉' A
  | .app _ f a, _ =>
    if a.classify = .type then 𝓉' f `@f 𝒯 a `@f 𝓉' a
    else 𝓉' f `@f zr `@f 𝓉' a
  | .prod A B, _ => sorry
  | .pair _ B' t s, .prod A B => sorry
  | .fst t, _ => sorry
  | _, _ => .none
  where
    𝓉' : Term -> Term
    | t => 𝓉 ℓ t .none
    c : Term -> Term
    | t => canon ℓ t
    zr := g0 ℓ
    bot := gBot ℓ

end FomegaModel
