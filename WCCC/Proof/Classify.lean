
import Common
import WCCC.Proof

namespace WCCC

  theorem classify_proof
    : Γ ⊢[m] t : A ->
      (A = □) ∨ (Γ ⊢[mt] A : □) ∨ (Γ ⊢[mt] A : ★)
  := by {
    intro j
    induction j
    case ax =>
      sorry
    case var =>
      sorry
    case lam Γ A m K t B C j1 j2 j3 ih1 ih2 ih3 =>
      cases m
      case _ =>
        simp at *; apply Or.inr
        constructor
        case h.K => exact K
        all_goals simp [*]
      case _ =>
        simp at *; apply Or.inr
        constructor
        case h.K => exact K
        all_goals simp [*]
      case _ =>
        simp at *; apply Or.inl
        constructor
        case h.K => exact K
        all_goals simp [*]
    case pi =>
      sorry
    case app Γ m1 f m2 A B a j1 j2 ih1 ih2 =>
      cases m2
      case _ =>
        apply Or.inr; apply Or.inr
        cases ih1
        case _ ih1 => injection ih1
        case _ ih1 =>
          cases ih1
          case _ ih1 => cases ih1
          case _ ih1 =>
            cases ih1
            case _ K j3 j4 =>
              simp at j4;
              sorry
      case _ =>
        sorry
      case _ =>
        sorry
    case prod =>
      sorry
    case pair =>
      sorry
    case fst =>
      sorry
    case snd =>
      sorry
    case eq =>
      sorry
    case refl =>
      sorry
    case subst =>
      sorry
    case conv =>
      sorry
  }

  theorem term_classify_is_sound
    : Γ ⊢[m] t : A -> (A = □ -> Term.classify t = .kind)
      ∧ (Γ ⊢[mt] A : □ -> Term.classify t = .type)
      ∧ (Γ ⊢[mt] A : ★ -> Term.classify t = .term)
  := by sorry

end WCCC
