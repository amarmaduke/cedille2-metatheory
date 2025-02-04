
import Cedille2.Proof
import Cedille2.Term.Classify
import Fomega.Basic.Derivations

namespace FomegaModel

  notation:170 Γ:170 " ⊢c " t:170 " : " A:170 => Cedille2.Judgment Cedille2.JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢c " Γ:170 => Cedille2.Judgment Cedille2.JudgmentVariant.wf Γ ()

  notation:170 Γ:170 " ⊢ω " t:170 " : " A:170 => Fomega.Judgment Fomega.JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢ω " Γ:170 => Fomega.Judgment Fomega.JudgmentVariant.wf Γ ()

  def uid := Fomega.uid

  @[simp]
  def 𝒱 : Cedille2.Term -> Fomega.Term
  | □ | ★ => ★
  | .all _ A B =>
    if A.classify = .kind then .all (𝒱 A) (𝒱 B)
    else 𝒱 B
  | _ => □

  @[simp]
  def 𝒯 : Cedille2.Term -> Fomega.Term
  | □ | ★ => (U)
  | .var .kind x => #x
  | .all _ A B =>
    if A.classify = .kind then Π[𝒱 A] Π[𝒯 A] 𝒯 B
    else Π[★] Π[𝒯 A] 𝒯 B
  | .lam .type A t =>
    if A.classify = .kind then `λ[𝒱 A] 𝒯 t
    else 𝒯 t
  | .app .type f a =>
    if a.classify = .type then (𝒯 f) `@ (𝒯 a)
    else  𝒯 f
  | .inter_ty A B => (𝒯 A) ⊗ (𝒯 B)
  | .eq _ _ => (U)
  | _ => □

  @[simp]
  def γ : Ctx Cedille2.Term -> Ctx Fomega.Term
  | [] => []
  | .cons A Γ =>
    if A.classify = .kind then (𝒯 A) :: (𝒱 A) :: (γ Γ)
    else (𝒯 A) :: (𝒯 A) :: (γ Γ)

  @[simp]
  def canon : Cedille2.Term -> Fomega.Term
  | ★ => (U)
  | .all mf A B =>
    if B.classify = .kind then `λ[𝒯 A] (canon B)
    else .unit_rec (𝒯 (.all mf A B)) (u) (u)
  | B => .unit_rec (𝒯 B) (u) (u)

  @[simp]
  def 𝓉 : Cedille2.Term -> Fomega.Term
  | ★ => (u)
  | .var .type x => #(2*x)
  | .var .kind x => #(2*x + 1)
  | .all _ A B =>
    if A.classify = .kind then
      .uid2 (𝓉 A) (.uid2 ((𝓉 B) β[.uid2 (𝒯 A) (u)] β[.uid2 (𝒱 A) (u)]) (u))
    else
      c (∀f[zr] ∀f[zr] zr) `@f 𝓉 A `@f (𝓉 B) β[c (𝒯 A)] β[zr]
  | .lam _ A t =>
    if A.classify = .kind then
      (λf[zr] λf[𝒱 A] λf[𝒯 A] 𝓉 t) `@f 𝓉 A
    else
      (λf[zr] λf[★] λf[𝒯 A] 𝓉 t) `@f 𝓉 A
  | .app _ (.conv n (.all _ A1 B) (.lam _ A2 b)) t => sorry
  | .app _ f a =>
    if a.classify = .type then 𝓉 f `@f 𝒯 a `@f 𝓉 a
    else 𝓉 f `@f zr `@f 𝓉 a
  | .inter_ty A B => c (∀f[zr] ∀f[zr] zr) `@f 𝓉 A `@f (𝓉 B) β[c (𝒯 A)]
  | .inter _ B t s => (λf[zr] .pair (𝓉 t) (𝓉 s)) `@f (𝓉 B) β[𝓉 t]
  | .fst t => .fst (𝓉 t)
  | .snd t => .snd (𝓉 t)
  | .eq A a b => c (∀f[zr] ∀f[𝒯 A] ∀f[𝒯 A] zr) `@f 𝓉 A `@f 𝓉 a `@f 𝓉 b
  | .refl A t => (λf[zr] λf[𝒯 A] .unit) `@f 𝓉 A `@f 𝓉 t
  | .subst Pr e => sorry
  | .phi A a b e =>
    (λf[zr] λf[𝒯 A] .unit_rec (𝓉 e) (𝓉 b))
    `@f 𝓉 A
    `@f 𝓉 a
  | .conv _ A t => (λf[zr] uid (𝓉 t)) `@f 𝓉 A
  | _ => .none

end FomegaModel
