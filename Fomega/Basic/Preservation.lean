import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification

namespace Fomega.Proof

  theorem wf_type : t ⊢ Γ -> Γ ⊢ t : A -> A ⊢ Γ := by
  intro j1 j2
  induction j2
  case ax => constructor
  case var => cases j1; simp [*]
  case pi => constructor
  case tpi => constructor
  case lam _ih1 ih2 =>
    cases j1
    case _ j1 j2 =>
      constructor; apply j1; apply ih2 j2
  case app _j1 j2' sh ih1 _ih2 =>
    cases j1
    case _ j1 j2 =>
      replace ih1 := ih1 j1
      cases ih1
      case _ j3 j4 =>
        subst sh; apply beta_wf;
        apply j4; apply j2'; apply j2
  case econv => cases j1; simp [*]
  case iconv =>  sorry

  theorem preservation1 : t ⊢ Γ -> Γ ⊢ t : A -> t -β> t' -> Γ ⊢ t' : A := by
  intro cj j r
  induction j generalizing t'
  case ax => cases r
  case var => cases r
  case pi => sorry
  case tpi => sorry
  case lam Γ A B K t j1 j2 ih1 ih2 =>
    cases r
    case lam_congr1 A' r =>
      constructor; apply Proof.lam
    case lam_congr2 => sorry
  case app Γ f A' B a B' j1 j2 j3 ih1 ih2 =>
    cases r
    case beta C d => sorry
    case app_congr1 f' r => sorry
    case app_congr2 => sorry
  case econv j1 j2 j3 ih1 ih2 => sorry
  case iconv => sorry

  theorem preservation_wf1 : t ⊢ Γ -> Γ ⊢ t : A -> t -β> t' -> t' ⊢ Γ := by
  intro j1 j2 r
  induction j2 generalizing t'
  case ax => cases r
  case var => cases r
  case pi => sorry
  case tpi => sorry
  case lam => sorry
  case app j2 j3 j4 ih1 ih2 =>
    cases j1
    case _ cj1 cj2 =>
    cases r
    case beta =>
      cases cj1
      case _ cj1 cj3 =>
        sorry
    case app_congr1 => sorry
    case app_congr2 => sorry
  case econv ih1 ih2 => sorry
  case iconv => sorry


  -- theorem preservation : Γ ⊢ t : A -> t -β>* t' -> Γ ⊢ t' : A := by
  -- intro j r
  -- induction r generalizing Γ A
  -- case _ => exact j
  -- case _ r1 _r2 ih => apply ih (preservation1 j r1)

  theorem preservation_type : Γ ⊢ t : A -> A -β>* A' -> Γ ⊢ t : A' := by sorry

end Fomega.Proof
