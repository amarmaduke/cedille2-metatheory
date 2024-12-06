
import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken

namespace Fomega.Proof

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
  case conv Γ t' A' B' _K' h1 _h2 h3 ih1 _ih2 =>
    cases t' <;> simp at tdef
    case _ m r1 r2 =>
      cases tdef
      case _ e1 tdef =>
      cases tdef
      case _ e2 e3 =>
        subst e1; subst e2; subst e3
        apply @ih1 A B K (Term.RedConv.trans h3 hc) rfl

  theorem lam_destruct_conv :
    Γ ⊢ .lam mf A t : T ->
    T =β= .all mf C D ->
    ∃ B, A =β= C ∧ B =β= D ∧ Γ ⊢ .lam mf A t : .all mf A B
  := by
  intro j hc
  generalize sdef : Term.lam mf A t = s at *
  induction j generalizing A C D t
  case ax => simp at sdef
  case var => simp at sdef
  case pi => simp at sdef
  case tpi => simp at sdef
  case lam A' B' K' t' j3 j4 ih1 ih2 =>
    replace hc := Term.RedConv.all_congr hc
    injection sdef with e1 e2 e3
    subst e2; subst e3; exists B'
    apply And.intro hc.2.1
    apply And.intro hc.2.2
    constructor; apply j3; apply j4
  case app => simp at sdef
  case conv Γ t' A' B' _K' h1 _h2 h3 ih1 _ih2 =>
    cases t' <;> simp at sdef
    case _ m r1 r2 =>
      cases sdef
      case _ e1 sdef =>
      cases sdef
      case _ e2 e3 =>
        subst e1; subst e2; subst e3
        apply @ih1 A t C D (Term.RedConv.trans h3 hc) rfl

  theorem lam_destruct_body :
    Γ ⊢ .lam mf A t : T ->
    Γ ⊢ .all mf A B : .const K ->
    T =β= .all mf A B ->
    (A::Γ) ⊢ t : B
  := by
  intro j1 j2 hc
  generalize sdef : Term.lam mf A t = s at *
  induction j1 generalizing A B t K
  case ax => simp at sdef
  case var => simp at sdef
  case pi => simp at sdef
  case tpi => simp at sdef
  case lam Γ' A' B' K' t' j3 j4 ih1 ih2 =>
    injection sdef with e1 e2 e3
    subst e2; subst e3
    replace j3 := all_destruct j2 Term.RedConv.refl
    have lem := Term.RedConv.all_congr hc
    apply Proof.conv; apply j4
    apply j3.2.2; apply lem.2.2
  case app => simp at sdef
  case conv Γ t' A' B' _K' h1 _h2 h3 ih1 _ih2 =>
    cases t' <;> simp at sdef
    case _ m r1 r2 =>
      cases sdef
      case _ e1 sdef =>
      cases sdef
      case _ e2 e3 =>
        subst e1; subst e2; subst e3
        apply @ih1 A t B K j2 (Term.RedConv.trans h3 hc) rfl

end Fomega.Proof
