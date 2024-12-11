import Common
import FomegaMut.Ctx
import FomegaMut.Proof
import FomegaMut.PreProof
import FomegaMut.Basic.Weaken
import FomegaMut.Basic.Substitution
import FomegaMut.Basic.Inversion

namespace FomegaMut.Proof

  theorem proof_classification : Γ ⊢ t : A -> A = □ ∨ (∃ K, Γ ⊢ A : .const K) := by
  intro j
  generalize tydef : JudKind.prf = ty at j
  induction j <;> cases tydef
  case ax => apply Or.inl; rfl
  case var Γ K x h _ih =>
    cases h
    case _ h =>
      apply Or.inr; apply Exists.intro; apply h
  case pi h _ _ _ =>
    replace h := ctx_wf h
    cases h
    case _ f h =>
      apply Or.inr; exists .kind; constructor
      constructor; apply h; apply Term.none
  case tpi => apply Or.inl; rfl
  case lam h1 _h2 _ih1 _ih2 => apply Or.inr; apply Exists.intro; apply h1
  case app _h1 h2 h3 ih1 _ih2 =>
    replace ih1 := ih1 rfl
    cases ih1 <;> simp at *
    case _ h =>
      cases h
      case _ K h =>
        cases h
        case _ K q1 q2 =>
          have h := Proof.beta q2 h2; simp at h
          apply Or.inr; exists .type
          subst h3; exact h
        case _ K q1 q2 =>
          have h := Proof.beta q2 h2; simp at h
          apply Or.inr; exists .kind
          subst h3; exact h
        case _ C K' q1 q2 q3 =>
          replace q1 := all_destruct q1 q2
          have h := Proof.beta (q1.2.2) h2
          simp at h; apply Or.inr; exists K
          subst h3; apply h
  case iconv K _h1 h2 _h3 _ih1 _ih2 =>
    apply Or.inr; exists K
  case econv K _h1 h2 _h3 _ih1 _ih2 =>
    apply Or.inr; exists K

end FomegaMut.Proof
