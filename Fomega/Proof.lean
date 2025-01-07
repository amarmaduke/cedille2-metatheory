
import Common
import Fomega.Ctx

namespace Fomega

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
    Judgment .prf Γ (A, .const K) ->
    Judgment .prf (A::Γ) (B, ★) ->
    Judgment .prf Γ (.all mf A B, ★)
  | tpi :
    Judgment .prf Γ (A, □) ->
    Judgment .prf (A::Γ) (B, □) ->
    Judgment .prf Γ (.all mf A B, □)
  | lam :
    Judgment .prf Γ (.all mf A B, .const K) ->
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

  @[simp]
  abbrev all_inversion_idx A B T : JudgmentIndex v :=
    match v with
    | .prf => (.all mf A B, T)
    | .wf => ()

  theorem all_destruct :
    Γ ⊢ .all mf A B : T ->
    T =β= .const K ->
    Γ ⊢ .all mf A B : .const K ∧ (∃ K, Γ ⊢ A : .const K) ∧ (A::Γ) ⊢ B : .const K
  := by
  intro j hc
  generalize tdef : Term.all mf A B = t at *
  induction j generalizing A B K
  case ax => simp at tdef
  case var => simp at tdef
  case pi Γ' A' K' B' j1 j2 ih1 ih2 =>
    injection tdef with e1 e2 e3
    subst e2; subst e3
    cases K
    case _ =>
      apply And.intro; constructor; apply j1; apply j2
      apply And.intro; exists K'
      apply j2
    case _ => exfalso; apply Term.RedConv.type_not_conv_to_kind hc
  case tpi Γ' A' B' j1 j2 ih1 ih2 =>
    injection tdef with e1 e2 e3
    subst e2; subst e3
    cases K
    case _ => exfalso; apply Term.RedConv.type_not_conv_to_kind (Term.RedConv.sym hc)
    case _ =>
      apply And.intro; constructor; apply j1; apply j2
      apply And.intro; exists .kind
      apply j2
  case lam => simp at tdef
  case app => simp at tdef
  case econv Γ t' A' B' _K' h1 _h2 _h3 ih1 _ih2 =>
    cases t' <;> simp at tdef
  case iconv Γ t' A' B' _K' h1 _h2 h3 ih1 _ih2 =>
    cases t' <;> simp at tdef
    case all m C D =>
      apply ih1 (Term.RedConv.trans h3 hc)
      rw [tdef.1, tdef.2.1, tdef.2.2]

end Fomega
