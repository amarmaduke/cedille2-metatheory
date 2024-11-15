
import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Conv
import Fomega.Basic.Weaken

namespace Fomega.Proof

  theorem all_destruct :
    Γ ⊢ .all mf A B : T ->
    T === .const K ->
    (A::Γ) ⊢ B : T
  := by
  intro j hc
  generalize tdef : Term.all mf A B = t at *
  induction j generalizing A B
  case ax => simp at tdef
  case var => simp at tdef
  case pi => sorry
  case tpi => sorry
  case lam => simp at tdef
  case app => simp at tdef
  case conv Γ t' A' B' K' h1 h2 h3 ih1 ih2 =>
    cases t' <;> simp at tdef
    case _ m r1 r2 =>
      cases tdef
      case _ e1 h' =>
        cases h'
        case _ e2 e3 =>
          subst e1; subst e2; subst e3
          have ih3 := @ih1 A B sorry rfl
          apply Proof.conv; exact ih3
          sorry
          exact h3
          exact K


end Fomega.Proof
