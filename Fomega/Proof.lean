
import Common
import Fomega.Term
import Fomega.Reduction

namespace Fomega

  def dom (K1 : Const) : Const -> Const
  | .type => K1
  | .kind => .kind

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
    Judgment .wf Γ () ->
    T = Γ d@ x ->
    Judgment .prf Γ (#x, T)
  | pi :
    Judgment .prf Γ (A, .const (dom K1 K2)) ->
    Judgment .prf (A::Γ) (B, .const K2) ->
    Judgment .prf Γ (Π[A] B, .const K2)
  | lam :
    Judgment .prf Γ (A, .const (dom K1 K2)) ->
    Judgment .prf (A::Γ) (B, .const K2) ->
    Judgment .prf (A::Γ) (t, B) ->
    Judgment .prf Γ (`λ t, Π[A] B)
  | app :
    Judgment .prf Γ (f, Π[A] B) ->
    Judgment .prf Γ (a, A) ->
    B' = B β[a] ->
    Judgment .prf Γ (f `@ a, B')
  | prod :
    Judgment .prf Γ (A, ★) ->
    Judgment .prf Γ (B, ★) ->
    Judgment .prf Γ (A ⊗ B, ★)
  | pair :
    Judgment .prf Γ (a, A) ->
    Judgment .prf Γ (b, B) ->
    Judgment .prf Γ (A, ★) ->
    Judgment .prf Γ (B, ★) ->
    Judgment .prf Γ (.pair a b, A ⊗ B)
  | fst :
    Judgment .prf Γ (t, A ⊗ B) ->
    Judgment .prf Γ (t.fst, A)
  | snd :
    Judgment .prf Γ (t, A ⊗ B) ->
    Judgment .prf Γ (t.snd, B)
  | unit_ty :
    Judgment .wf Γ () ->
    Judgment .prf Γ ((U), ★)
  | unit :
    Judgment .wf Γ () ->
    Judgment .prf Γ ((u), (U))
  | unit_rec :
    Judgment .prf Γ (u, (U)) ->
    Judgment .prf Γ (t, A) ->
    Judgment .prf Γ (A, ★) ->
    Judgment .prf Γ (.unit_rec u t, A)
  | conv :
    Judgment .prf Γ (t, A) ->
    Judgment .prf Γ (B, .const K) ->
    A =β= B ->
    Judgment .prf Γ (t, B)

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Judgment JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢ " Γ:170 => Judgment JudgmentVariant.wf Γ ()

  theorem judgment_ctx_wf : Judgment v Γ idx -> ⊢ Γ := by
  intro j
  induction j
  case nil => constructor
  case cons j1 j2 _ _ => constructor; apply j1; apply j2
  all_goals try simp [*]

end Fomega
