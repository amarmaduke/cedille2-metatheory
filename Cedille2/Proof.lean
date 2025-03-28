
import Common
import Erased
import Cedille2.Term
import Cedille2.Term.Erasure
import Cedille2.Reduction

namespace Cedille2

  @[simp]
  def dom (m : Mode) (K : Const) : Const :=
    match m with
    | mf => .type
    | mt => K
    | m0 => K

  @[simp]
  def codom (m : Mode) : Const :=
    match m with
    | mf => .type
    | mt => .kind
    | m0 => .type

  inductive JudgmentVariant : Type
  | prf | wf

  @[simp, inline]
  abbrev JudgmentIndex : JudgmentVariant -> Type
  | .prf => Term × Term
  | .wf => Unit

  inductive Judgment : (v : JudgmentVariant) -> Ctx Term -> JudgmentIndex v -> Prop where
  | nil : Judgment .wf [] ()
  | cons :
    Judgment .wf Γ () ->
    Judgment .prf Γ (A, .const K) ->
    Judgment .wf (A::Γ) ()
  | ax :
    Judgment .wf Γ () ->
    Judgment .prf Γ (★, □)
  | var :
    Judgment .prf Γ (Γ d@ x, .const K) ->
    T = Γ d@ x ->
    Judgment .prf Γ (.var K x, T)
  | pi :
    Judgment .prf Γ (A, .const (dom m K)) ->
    Judgment .prf (A::Γ) (B, .const (codom m)) ->
    Judgment .prf Γ (`∀(m)[A] B, .const (codom m))
  | lam :
    Judgment .prf Γ (A, .const (dom m K)) ->
    Judgment .prf (A::Γ) (B, .const (codom m)) ->
    Judgment .prf (A::Γ) (t, B) ->
    (m = m0 -> ∀ v1 v2 σ, [v1 :: σ]t.erase = [v2 :: σ]t.erase) ->
    Judgment .prf Γ (`λ(m)[A] t, `∀(m)[A] B)
  | app :
    Judgment .prf Γ (f, `∀(m)[A] B) ->
    Judgment .prf Γ (a, A) ->
    B' = B β[a] ->
    Judgment .prf Γ (f `@(m) a, B')
  | inter_ty :
    Judgment .prf Γ (A, ★) ->
    Judgment .prf (A::Γ) (B, ★) ->
    Judgment .prf Γ ([A]∩ B, ★)
  | inter :
    Judgment .prf Γ (t, A) ->
    Judgment .prf Γ (A, ★) ->
    Judgment .prf (A::Γ) (B, ★) ->
    Judgment .prf Γ (s, B β[t]) ->
    t.erase ≡β[g1;g2]≡ s.erase ->
    Judgment .prf Γ (.inter g1 g2 B t s, [A]∩ B)
  | fst :
    Judgment .prf Γ (t, [A]∩ B) ->
    Judgment .prf Γ (t.!1, A)
  | snd :
    Judgment .prf Γ (t, [A]∩ B) ->
    B' = B β[t.!1] ->
    Judgment .prf Γ (t.!2, B')
  | eq :
    Judgment .prf Γ (a, A) ->
    Judgment .prf Γ (b, A) ->
    Judgment .prf Γ (A, ★) ->
    Judgment .prf Γ (.eq a b, ★)
  | refl :
    Judgment .prf Γ (a, A) ->
    Judgment .prf Γ (b, A) ->
    Judgment .prf Γ (A, ★) ->
    a.erase ≡β[g1;g2]≡ b.erase ->
    Judgment .prf Γ (.refl g1 g2 a b, .eq a b)
  | subst :
    Judgment .prf Γ (e, .eq a b) ->
    Judgment .prf Γ (a, A) ->
    Judgment .prf Γ (Pr, ∀τ[A] ∀τ[.eq #0 ([S]b)] ★) ->
    Judgment .prf Γ (t, Pr `@τ a `@τ (.refl 0 0 a a)) ->
    Judgment .prf Γ (.subst Pr e t, Pr `@τ b `@τ e)
  | phi :
    Judgment .prf Γ (a, A) ->
    Judgment .prf Γ (b, [A]∩ B) ->
    Judgment .prf Γ (e, .eq a b.!1) ->
    Judgment .prf Γ (.phi a b e, [A]∩ B)
  | iconv :
    Judgment .prf Γ (t, A) ->
    Judgment .prf Γ (B, .const K) ->
    A =β= B ->
    Judgment .prf Γ (t, B)
  | econv :
    Judgment .prf Γ (t, A) ->
    Judgment .prf Γ (B, ★) ->
    A.erase ≡β[g1;g2]≡ B.erase ->
    Judgment .prf Γ (.conv g1 g2 B t, B)

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Judgment JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢ " Γ:170 => Judgment JudgmentVariant.wf Γ ()

  theorem judgment_ctx_wf : Judgment v Γ idx -> ⊢ Γ := by
  intro j
  induction j
  case nil => constructor
  case cons j1 j2 _ _ => constructor; apply j1; apply j2
  all_goals try simp [*]

end Cedille2
