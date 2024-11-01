
import Common
import WCCC.Proof

namespace WCCC.Conv

  theorem refl : (CvTerm.refl t) : t === t := by {
    induction t
    all_goals try (simp; constructor <;> simp [*])
  }

  theorem subst : c : t === s -> ([▸σ]c) : [σ]t === [σ]s := by {
    intro h
    induction h generalizing σ <;> simp
    case sym c t2 t1 h ih => constructor; apply ih
    case trans c1 t1 t2 c2 t3 h1 h2 ih1 ih2 => constructor; apply ih1; apply ih2
    case bound K x =>
      unfold Term.subst_term_to_subst_cvterm <;> simp
      cases (σ x) <;> simp
      case _ => constructor
      case _ => apply refl
    case app_beta c b t t2 m A h ih =>
      constructor; simp at *; apply ih
    case all_congr c1 A1 A2 c2 B1 B2 m h1 h2 ih1 ih2 =>
      replace ih2 := @ih2 ^σ; simp at ih2
      constructor; apply ih1; apply ih2
    case lam_eta c m A t1 t2 h ih =>
      constructor; simp at *

    case pair_erased c t1 t2 T1 s1 h ih =>
      constructor; apply ih
    repeat sorry
  }

end WCCC.Conv
