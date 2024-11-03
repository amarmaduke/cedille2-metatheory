import Common
import WCCC.Proof

namespace WCCC

  theorem proof_mode_inclusion : m1 ∈ m2 -> Γ ⊢[m1] t : A -> Γ ⊢[m2] t : A := by {
    intro jm j
    induction j generalizing m2
    case ax Γ => cases jm; constructor
    case var Γ x m3 A K m4 j1 j2 j3 _ih3 =>
      constructor; exact j1; exact j2
      apply Mode.mem_trans j3 jm
    case pi Γ A m K B j1 j2 _ih1 _ih2 =>
      cases jm; constructor; exact j1; exact j2
    case lam Γ A m4 K m3 t B j1 _j2 j3 _ih1 ih2 _ih3 =>
      constructor; apply j1; apply ih2 jm; apply j3
    case app Γ m3 f m4 A B a _j1 _j2 ih1 ih2 =>
      constructor; apply ih1 jm
      replace jm := Mode.mem_mul m4 jm
      apply ih2 jm
    case prod Γ A B j1 j2 _ih1 _ih2 =>
      cases jm; constructor; apply j1; apply j2
    case pair Γ B A m t s j1 _j2 j3 _ih1 ih2 _ih3 =>
      constructor; apply j1; apply ih2 jm; apply j3
    case fst Γ m t A B _j ih =>
      constructor; apply ih jm
    case snd Γ t A B m j1 j2 _ih1 =>
      constructor; exact j1; apply Mode.mem_trans j2 jm
    case eq Γ A a b j1 j2 j3 _ih1 _ih2 _ih3 =>
      cases jm; constructor; apply j1; apply j2; apply j3
    case phi Γ m a A b B e _j1 j2 j3 ih1 _ih2 _ih3 =>
      constructor; apply ih1 jm; exact j2; exact j3
    case refl Γ t A m j _ih =>
      constructor; apply j
    case subst Γ m e A a b P _j1 j2 ih1 _ih2 =>
      constructor; apply ih1 jm; apply j2
    case conv Γ m t A B K c _j1 j2 cv ih1 _ih2 =>
      constructor; apply ih1 jm; apply j2; apply cv
  }

end WCCC
