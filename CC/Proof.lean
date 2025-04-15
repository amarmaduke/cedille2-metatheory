import Common
import CC.Term

namespace CC

  inductive ParProofVariant : Type
  | prf | wf

  @[simp, inline]
  abbrev ParProofIndex : ParProofVariant -> Type
  | .prf => Term × Term × Term
  | .wf => Unit

  inductive ParProof : (v : ParProofVariant) -> Ctx Term -> ParProofIndex v -> Prop where
  | nil : ParProof .wf [] ()
  | cons :
    ParProof .prf Γ (A, A', .const K) ->
    ParProof .wf (A :: Γ) ()
  | ax :
    ParProof .wf Γ () ->
    ParProof .prf Γ (★, ★, □)
  | var :
    ParProof .wf Γ () ->
    Γ d@ n = T ->
    ParProof .prf Γ (#n, #n, T)
  | lam :
    ParProof .prf Γ (A, A', .const K1) ->
    ParProof .prf (A::Γ) (B, B', .const K2) ->
    ParProof .prf (A::Γ) (t, t', B) ->
    ParProof .prf Γ (`λ[A] t, `λ[A'] t', Π[A] B)
  | app :
    ParProof .prf Γ (a, a', A) ->
    ParProof .prf Γ (A, A', .const K1) ->
    ParProof .prf Γ (f, f', Π[A] B) ->
    ParProof .prf (A::Γ) (B, B', .const K2) ->
    ParProof .prf Γ (f `@[B] a, f' `@[B'] a', B β[a])
  | pi :
    ParProof .prf Γ (A, A', .const K1) ->
    ParProof .prf (A::Γ) (B, B', .const K2) ->
    ParProof .prf Γ (Π[A] B, Π[A'] B', .const K2)
  | beta :
    ParProof .prf Γ (t, t', A) ->
    ParProof .prf Γ (A, A', .const K1) ->
    ParProof .prf (A::Γ) (t, t', B) ->
    ParProof .prf (A::Γ) (B, B', .const K2) ->
    ParProof .prf Γ ((`λ[A] b) `@[B] t, b' β[t'] , B β[t])
  | fconv :
    ParProof .prf Γ (t, t', B) ->
    ParProof .prf Γ (B, B', .const K) ->
    ParProof .prf Γ (t, t', B')
  | bconv :
    ParProof .prf Γ (t, t', B') ->
    ParProof .prf Γ (B, B', .const K) ->
    ParProof .prf Γ (t, t', B)

end CC
