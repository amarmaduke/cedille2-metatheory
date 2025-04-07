
import Common
import Cedille2.Proof
import Fomega.Basic.Derivations
import Cedille2.FomegaModel.Interpretation
import Cedille2.FomegaModel.Soundness

namespace FomegaModel

  theorem drop1_red_congr1 : d -β>+ d' -> drop1 d t -β>+ drop1 d' t := by sorry
  theorem drop1_red_congr2 : t -β>+ t' -> drop1 d t -β>+ drop1 d t' := by sorry

  theorem drop1_red : drop1 d t -β> t := by
  unfold drop1; simp; constructor

  theorem beta_type b t :
    𝓉 (t β[b]) = (𝓉 t) β[(U)] β[𝓉 b]
  := by sorry

  theorem red_preserved :
    Γ ⊢c t : T ->
    t -β> s ->
    𝓉 t -β>+ 𝓉 s
  := by
  intro j r
  induction r generalizing Γ T <;> simp at *
  -- Steps
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  -- Conv Steps
  case _ g1 g2 m1 A B m2 C t =>
    have lem1 : A.classify = .type := by sorry
    rw [lem1]; simp; apply Plus.stepr_from_star drop1_red
    generalize zdef : [.su (.conv g2 g1 C #0) :: I]t = z
    cases z
    case lam m3 W w =>
      have lem2 : ∃ (U V : Cedille2.Term), B = (`∀(m3)[U] V) := by sorry
      cases lem2; case _ U lem2 =>
      cases lem2; case _ V lem2 =>
      rw [lem2]; simp
      have lem3 := beta_type (.conv g2 g1 C #0) t; simp at lem3
      have lem4 : 𝓉 (t β[.conv g2 g1 C #0]) = 𝓉 (`λ(m3)[W]w) := by sorry
      rw [lem3] at lem4; simp at lem4
      have lem5 : W.classify = .type := by sorry
      rw [lem5] at lem4; simp at lem4
      sorry
    case inter => sorry
    case refl => sorry
    all_goals
      sorry
  case _ => sorry
  case _ g1 g2 a b h1 h2 u v =>
    apply Plus.stepr drop1_red
    apply Plus.stepr drop1_red
    apply Plus.stepr_from_star drop1_red
    apply Star.refl
  -- Congruences
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ t1 t1' g1 g2 t2 r ih =>
    have lem1 : Γ ⊢c t1 : T := by sorry
    have lem2 := ih lem1
    cases t2
    case lam => sorry
    case inter => sorry
    case refl h1 h2 u v =>
      have lem3 : ∃ a b, t1 = .eq a b := by sorry
      cases lem3; case _ a lem3 =>
      cases lem3; case _ b lem3 =>
        subst lem3; cases r <;> simp
        case _ a' r =>

          sorry
        case _ b' r => sorry
    all_goals
      simp; apply drop1_red_congr1 lem2
  case _ => sorry

  theorem fomega_sn_implies_sn :
    Γ ⊢c t : A ->
    @SNPlus _ Fomega.Red (𝓉 t) ->
    @SN _ Cedille2.Red t
  := by
  sorry

  axiom fomega_sn {Γ : Ctx Fomega.Term} {t A : Fomega.Term} : Γ ⊢ω t : A -> @SN _ Fomega.Red t

  theorem sn_term : Γ ⊢c t : A -> @SN _ Cedille2.Red t := by
  intro j; apply fomega_sn_implies_sn j
  have lem1 : (γ Γ) ⊢ω (𝓉 t) : (𝒯 A) := term_soundness j
  have lem2 := fomega_sn lem1
  apply sn_implies_snplus; apply lem2

end FomegaModel
