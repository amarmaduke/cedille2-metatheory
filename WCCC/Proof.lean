
import Common
import WCCC.Mode
import WCCC.Ctx

namespace WCCC

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
    Judgment .prf Γ (A, Mode.dom m K) ->
    Judgment .prf (A::Γ) (B, Mode.codom m) ->
    Judgment .prf Γ (.all m A B, Mode.codom m)
  | lam :
    Judgment .prf Γ (.all m A B, Mode.codom m) ->
    Judgment .prf (A::Γ) (t, B) ->
    Judgment .prf Γ (.lam m A t, .all m A B)
  | app :
    Judgment .prf Γ (f, .all m A B) ->
    Judgment .prf Γ (a, A) ->
    Judgment .prf Γ (.app m f a, B β[a])
  | prod :
    Judgment .prf Γ (A, ★) ->
    Judgment .prf (A::Γ) (B, ★) ->
    Judgment .prf Γ (.prod A B, ★)
  | pair :
    Judgment .prf (A::Γ) (B, ★) ->
    Judgment .prf Γ (t, A) ->
    Judgment .prf Γ (s, B β[t]) ->
    t.erase =β{n}= s.erase ->
    Judgment .prf Γ (.pair n B t s, .prod A B)
  | fst :
    Judgment .prf Γ (t, .prod A B) ->
    Judgment .prf Γ (.fst t, A)
  | snd :
    Judgment .prf Γ (t, .prod A B) ->
    Judgment .prf Γ (.snd t, B β[.fst t])
  | eq :
    Judgment .prf Γ (A, ★) ->
    Judgment .prf Γ (a, A) ->
    Judgment .prf Γ (b, A) ->
    Judgment .prf Γ (.eq A a b, ★)
  | refl :
    Judgment .prf Γ (t, A) ->
    Judgment .prf Γ (.refl t, .eq A t t)
  | subst :
    Judgment .prf Γ (e, .eq A a b) ->
    Judgment .prf Γ (Pr, .all mt A ★) ->
    Judgment .prf Γ (.subst Pr e, .all mf (.app mt Pr a) (.app mt Pr b))
  | phi :
    Judgment .prf Γ (a, A) ->
    Judgment .prf Γ (b, .prod A B) ->
    Judgment .prf Γ (e, .eq A a (.fst b)) ->
    Judgment .prf Γ (.phi a b e, .prod A B)
  | iconv :
    Judgment .prf Γ (t, A) ->
    Judgment .prf Γ (B, .const K) ->
    A =β= B ->
    Judgment .prf Γ (t, B)
  | econv :
    Judgment .prf Γ (t, A) ->
    Judgment .prf Γ (B, .const K) ->
    A.erase =β{n}= B.erase ->
    Judgment .prf Γ (.conv n B t, B)

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Judgment JudgmentVariant.prf Γ (t, A)
  notation:170 "⊢ " Γ:170 => Judgment JudgmentVariant.wf Γ ()

end WCCC
