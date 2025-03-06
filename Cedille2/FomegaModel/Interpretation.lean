
import Cedille2.Proof
import Cedille2.Term.Classify
import Fomega.Basic.Derivations

namespace FomegaModel

  notation:170 Γ:170 " ⊢c " t:170 " : " A:170 => Cedille2.Judgment Cedille2.JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢c " Γ:170 => Cedille2.Judgment Cedille2.JudgmentVariant.wf Γ ()

  notation:170 Γ:170 " ⊢ω " t:170 " : " A:170 => Fomega.Judgment Fomega.JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢ω " Γ:170 => Fomega.Judgment Fomega.JudgmentVariant.wf Γ ()

  @[simp]
  def drop1 : Fomega.Term -> Fomega.Term -> Fomega.Term
  | d, t => .unit_rec d (u) t

  @[simp]
  def drop2 : Fomega.Term -> Fomega.Term -> Fomega.Term -> Fomega.Term
  | d1, d2, t => drop1 d1 (drop1 d2 t)

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
  | .all _ A B => □
    -- if A.classify = .kind then
    --   uid2 (𝓉 A) (uid2 ((𝓉 B) β[uid2 (𝒯 A) (u)] β[uid2 (𝒱 A) (u)]) (u))
    -- else
    --   c (∀f[zr] ∀f[zr] zr) `@f 𝓉 A `@f (𝓉 B) β[c (𝒯 A)] β[zr]
  | .lam _ A t => □
    -- if A.classify = .kind then
    --   (λf[zr] λf[𝒱 A] λf[𝒯 A] 𝓉 t) `@f 𝓉 A
    -- else
    --   (λf[zr] λf[★] λf[𝒯 A] 𝓉 t) `@f 𝓉 A
  | .app _ f a =>
    if a.classify = .type then 𝓉 f `@ 𝒯 a `@ 𝓉 a
    else 𝓉 f `@ (U) `@ 𝓉 a
  | .inter_ty A B => □
  | .inter _ _ B t s => □
  | .fst t => .fst (𝓉 t)
  | .snd t => .snd (𝓉 t)
  | .eq a b => □
  | .refl t => drop1 (𝓉 t) (u)
  | .subst Pr e t => □
  | .phi a b e => □
  | .conv _ _ A t => □
  | _ => □

end FomegaModel
