
import Common
import Fomega.Ctx

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

  inductive Judgment : (v : JudgmentVariant) -> Ctx -> JudgmentIndex v -> Prop
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
    Judgment .prf Γ (.bound K x, T)
  | pi :
    Judgment .prf Γ (A, .const (dom K1 K2)) ->
    Judgment .prf (A::Γ) (B, .const K2) ->
    Judgment .prf Γ (.all mf A B, .const K2)
  | lam :
    Judgment .prf Γ (A, .const (dom K1 K2)) ->
    Judgment .prf (A::Γ) (B, .const K2) ->
    Judgment .prf (A::Γ) (t, B) ->
    Judgment .prf Γ (.lam mf A t, .all mf A B)
  | app :
    Judgment .prf Γ (f, .all mf A B) ->
    Judgment .prf Γ (a, A) ->
    B' = (B β[a]) ->
    Judgment .prf Γ (.app mf f a, B')
  | conv :
    Judgment .prf Γ (t, A) ->
    Judgment .prf Γ (B, .const K) ->
    A =β= B ->
    Judgment .prf Γ (t, B)

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Judgment JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢ " Γ:170 => Judgment JudgmentVariant.wf Γ ()

end Fomega
