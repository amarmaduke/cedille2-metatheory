
import WCCC.Proof
import Fomega.Basic.Derivations

namespace FomegaModel

  notation:170 Γ:170 " ⊢c " t:170 " : " A:170 => WCCC.Judgment WCCC.JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢c " Γ:170 => WCCC.Judgment WCCC.JudgmentVariant.wf Γ ()

  notation:170 Γ:170 " ⊢ω " t:170 " : " A:170 => Fomega.Judgment Fomega.JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢ω " Γ:170 => Fomega.Judgment Fomega.JudgmentVariant.wf Γ ()

  def uid := Fomega.uid

  @[simp]
  def 𝒱 : Term -> Term
  | □ | ★ => ★
  | .all _ A B =>
    if A.classify = .kind then .all mf (𝒱 A) (𝒱 B)
    else 𝒱 B
  | _ => .none

  def g0 (ℓ : Nat) : Term := .bound .kind (ℓ - 2)
  def gBot (ℓ : Nat) : Term := .bound .type (ℓ - 1)

  @[simp]
  def 𝒯 (ℓ : Nat) : Term -> Term
  | □ | ★ => .bound .kind 0
  | .bound .kind x => .bound .kind x
  | .all _ A B =>
    if A.classify = .kind then ∀f[𝒱 A] ∀f[𝒯 (ℓ + 1) A] 𝒯 (ℓ + 2) B
    else ∀f[★] ∀f[𝒯 (ℓ + 1) A] 𝒯 (ℓ + 2) B
  | .lam .type A t =>
    if A.classify = .kind then λf[𝒱 A] 𝒯 (ℓ + 1) t
    else 𝒯 ℓ t
  | .app .type f a =>
    if a.classify = .type then (𝒯 ℓ f) `@f (𝒯 ℓ a)
    else  𝒯 ℓ f
  | .inter_ty A B => .times A B
  | .eq _ _ _ => .unit_ty
  | _ => .none

  @[simp]
  def γ : Ctx -> Ctx
  | [] => ★ :: Fomega.Bot :: []
  | .cons A Γ =>
    let ℓ := Γ.length
    if A.classify = .kind then (𝒯 ℓ A) :: (𝒱 A) :: (γ Γ)
    else (𝒯 ℓ A) :: (𝒯 ℓ A) :: (γ Γ)

  @[simp]
  def canon (ℓ : Nat) : Term -> Term
  | ★ => g0 ℓ
  | .all mf A B =>
    if B.classify = .kind then λf[A] (canon ℓ B)
    else (gBot ℓ) `@τ (.all mf A B)
  | B => (gBot ℓ) `@τ B

  @[simp]
  def 𝓉 (ℓ : Nat) : Term -> Term
  | ★ => c zr
  | .bound .type x => .bound .kind (2*x)
  | .bound .kind x => .bound .type (2*x + 1)
  | .all _ A B =>
    if A.classify = .kind then
      c (∀f[zr] ∀f[zr] zr) `@f 𝓉 ℓ A `@f (𝓉 ℓ B) β[c (𝒯 ℓ A)] β[c (𝒱 A)]
    else
      c (∀f[zr] ∀f[zr] zr) `@f 𝓉 ℓ A `@f (𝓉 ℓ B) β[c (𝒯 ℓ A)] β[zr]
  | .lam _ A t =>
    if A.classify = .kind then
      (λf[zr] λf[𝒱 A] λf[𝒯 ℓ A] 𝓉 ℓ t) `@f 𝓉 ℓ A
    else
      (λf[zr] λf[★] λf[𝒯 ℓ A] 𝓉 ℓ t) `@f 𝓉 ℓ A
  | .app _ (.conv n (.all _ A1 B) (.lam _ A2 b)) t => sorry
  | .app _ f a =>
    if a.classify = .type then 𝓉 ℓ f `@f 𝒯 ℓ a `@f 𝓉 ℓ a
    else 𝓉 ℓ f `@f zr `@f 𝓉 ℓ a
  | .inter_ty A B => c (∀f[zr] ∀f[zr] zr) `@f 𝓉 ℓ A `@f (𝓉 ℓ B) β[c (𝒯 ℓ A)]
  | .inter _ B t s => (λf[zr] .pair (𝓉 ℓ t) (𝓉 ℓ s)) `@f (𝓉 ℓ B) β[𝓉 ℓ t]
  | .fst t => .fst (𝓉 ℓ t)
  | .snd t => .snd (𝓉 ℓ t)
  | .eq A a b => c (∀f[zr] ∀f[𝒯 ℓ A] ∀f[𝒯 ℓ A] zr) `@f 𝓉 ℓ A `@f 𝓉 ℓ a `@f 𝓉 ℓ b
  | .refl A t => (λf[zr] λf[𝒯 ℓ A] .unit) `@f 𝓉 ℓ A `@f 𝓉 ℓ t
  | .subst Pr e => sorry
  | .phi A a b e =>
    (λf[zr] λf[𝒯 ℓ A] .unit_rec (𝓉 ℓ e) (𝓉 ℓ b))
    `@f 𝓉 ℓ A
    `@f 𝓉 ℓ a
  | .conv _ A t => (λf[zr] uid (𝓉 ℓ t)) `@f 𝓉 ℓ A
  | _ => .none
  where
    c : Term -> Term
    | t => canon ℓ t
    zr := g0 ℓ
    bot := gBot ℓ

end FomegaModel
