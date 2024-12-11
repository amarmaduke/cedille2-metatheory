import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion

namespace Fomega.Proof

  theorem proof_classification : t ⊢ Γ -> Γ ⊢ t : A -> A = □ ∨ (∃ K, Γ ⊢ A : .const K) := by
  intro j1 j2
  induction j2
  case ax => apply Or.inl; rfl
  case var Γ K x =>
    apply Or.inr; cases j1
    case _ j => exists K
  case pi =>
    apply Or.inr
    exists .kind; constructor
  case tpi => apply Or.inl; rfl
  case lam h1 _h2 _ih1 _ih2 => apply Or.inr; apply Exists.intro; apply h1
  case app _h1 h2 h3 ih1 _ih2 =>
    cases j1
    case _ j1 j2 =>
      replace ih1 := ih1 j1
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

end Fomega.Proof
