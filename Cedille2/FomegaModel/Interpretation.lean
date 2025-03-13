
import Cedille2.Proof
import Cedille2.Term.Classify
import Fomega.Basic.Derivations

namespace FomegaModel

  notation:170 Γ:170 " ⊢c " t:170 " : " A:170 => Cedille2.Judgment Cedille2.JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢c " Γ:170 => Cedille2.Judgment Cedille2.JudgmentVariant.wf Γ ()

  notation:170 Γ:170 " ⊢ω " t:170 " : " A:170 => Fomega.Judgment Fomega.JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢ω " Γ:170 => Fomega.Judgment Fomega.JudgmentVariant.wf Γ ()

  def drop1 : Fomega.Term -> Fomega.Term -> Fomega.Term
  | d, t => .unit_rec d (u) t

  def drop2 : Fomega.Term -> Fomega.Term -> Fomega.Term -> Fomega.Term
  | d1, d2, t => drop1 d1 (drop1 d2 t)

  @[simp]
  def 𝒱 : Cedille2.Term -> Fomega.Term
  | □ | ★ => ★
  | .all _ A B =>
    if A.classify = .kind then .all (𝒱 A) (𝒱 B)
    else .all ★ (𝒱 B)
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
    else `λ[★] 𝒯 t
  | .app .type f a =>
    if a.classify = .type then (𝒯 f) `@ (𝒯 a)
    else  (𝒯 f) `@ (U)
  | .inter_ty A B => (𝒯 A) ⊗ (𝒯 (B β[□]))
  | .eq _ _ => (U)
  | _ => □

  @[simp]
  def γ : Ctx Cedille2.Term -> Ctx Fomega.Term
  | [] => []
  | .cons A Γ =>
    if A.classify = .kind then (𝒱 A) :: (𝒯 A) :: (γ Γ)
    else ★ :: (𝒯 A) :: (γ Γ)

  @[simp]
  def γ' : Ctx Cedille2.Term -> Ctx Fomega.Term
  | Γ => Fomega.Term.Bot :: γ Γ

  def canτ : Cedille2.Term -> Fomega.Term
  | B => #0 `@ 𝒯 B

  def canκ : Cedille2.Term -> Fomega.Term
  | ★ => (U)
  | .all mf A B => `λ[𝒯 A] (canκ B)
  | _ => □

  @[simp]
  def 𝓉 : Cedille2.Term -> Fomega.Term
  | ★ => (u)
  | .var .type x => #(2*x + 1)
  | .var .kind x => #(2*x + 2)
  | .all _ A B => (`λ[(U)] `λ[(U)] (u)) `@ (𝓉 A) `@ (𝓉 B β[canκ A] β[canτ A])
  | .lam _ A t =>
    if A.classify = .kind then
      (`λ[(U)] `λ[𝒱 A] `λ[𝒯 A] 𝓉 t) `@ 𝒯 A
    else
      (`λ[(U)] `λ[★] `λ[𝒯 A] 𝓉 t) `@ 𝒯 A
  | .app _ f a =>
    if a.classify = .type then
      𝓉 f `@ 𝒯 a `@ 𝓉 a
    else
      𝓉 f `@ (U) `@ 𝓉 a
  | .inter_ty A B => (`λ[(U)] `λ[(U)] (u)) `@ (𝓉 A) `@ (𝓉 B)
  | .inter _ _ B t s => (`λ[(U)] .pair (𝓉 t) (𝓉 s)) `@ (𝓉 B)
  | .fst t => .fst (𝓉 t)
  | .snd t => .snd (𝓉 t)
  | .eq a b => drop2 (𝓉 a) (𝓉 b) (u)
  | .refl t => drop1 (𝓉 t) (u)
  | .subst Pr e t => .unit_rec (𝓉 Pr) (𝓉 e) (𝓉 t)
  | .phi a b e => .unit_rec (𝓉 a) (𝓉 e) (𝓉 b)
  | .conv _ _ A t => drop1 (𝓉 A) (𝓉 t)
  | _ => □

end FomegaModel
