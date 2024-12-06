import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification

namespace Fomega.Proof

  -- theorem wf_type_conv : A ⊢ Γ -> A =β= B -> Γ ⊢ B : .const K -> B ⊢ Γ := by
  -- intro wf cv j
  -- induction wf generalizing B K

  -- theorem wf_type2 : t ⊢ Γ -> Γ ⊢ t : A -> A ⊢ Γ := by
  -- intro j1 j2
  -- induction j1 generalizing A
  -- case ax => sorry
  -- case var Γ x K j3 j4 ih =>
  --   generalize sdef : Term.bound K x = s at *
  --   induction s generalizing K x
  --   all_goals try cases sdef
  --   case _ K i =>
  -- case pi => sorry
  -- case lam => sorry
  -- case app => sorry

  theorem wf_type : t ⊢ Γ -> Γ ⊢ t : A -> A ⊢ Γ := by
  intro j1 j2
  induction j2
  case ax => constructor
  case var => cases j1; simp [*]
  case pi => constructor
  case tpi => constructor
  case lam => sorry
  case app => sorry
  case conv j2 cv ih _ => sorry

  theorem preservation1 : t ⊢ Γ -> Γ ⊢ t : A -> t -β> t' -> Γ ⊢ t' : A := by
  intro cj j r
  induction j generalizing t'
  case ax => cases r
  case var => cases r
  case pi => sorry
  case tpi => sorry
  case lam Γ A K t B j1 j2 ih1 ih2 =>
    cases r
    case lam_congr1 A' r => sorry
    case lam_congr2 => sorry
  case app Γ f A' B a B' j1 j2 j3 ih1 ih2 =>
    cases r
    case beta C d =>
      have j4 := lam_destruct_conv j1 Term.RedConv.refl
      cases j4
      case _ B2 j4 =>
      cases cj
      case _ cj1 cj2 =>
        have cl := proof_classification cj1 j4.2.2
        cases cl
        case _ h => cases h
        case _ h =>
        cases h
        case _ K j5 =>
          have j6 := lam_destruct_body j4.2.2 j5 Term.RedConv.refl
          have cl2 := proof_classification cj1 j1
          cases cl2
          case _ h => cases h
          case _ h =>
          cases h
          case _ K2 j7 =>
            have lem1 : Γ ⊢ a : C := by
              replace j5 := all_destruct j5 Term.RedConv.refl
              cases j5.2.1
              case _ K3 j8 =>
                apply Proof.conv; apply j2; apply j8
                apply Term.RedConv.sym j4.1
            have lem2 : B2 β[a] =β= B β[a] := by
              apply Term.RedConv.subst; apply j4.2.1
            have lem3 : Γ ⊢ (B β[a]) : Term.const K2 := by
              replace j7 := all_destruct j7 Term.RedConv.refl
              have j8 := beta j7.2.2 j2
              apply j8
            replace j6 := beta j6 lem1
            apply Proof.conv; apply j6; rw [j3]; apply lem3
            rw [j3]; apply lem2
    case app_congr1 => sorry
    case app_congr2 => sorry
  case conv j1 j2 j3 ih1 ih2 =>
    apply Proof.conv; apply ih1 cj r
    apply j2; apply j3

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
  case conv ih1 ih2 => apply ih1 j1 r


  -- theorem preservation : Γ ⊢ t : A -> t -β>* t' -> Γ ⊢ t' : A := by
  -- intro j r
  -- induction r generalizing Γ A
  -- case _ => exact j
  -- case _ r1 _r2 ih => apply ih (preservation1 j r1)

  theorem preservation_type : Γ ⊢ t : A -> A -β>* A' -> Γ ⊢ t : A' := by sorry

end Fomega.Proof
