import Common
import WCCC.Proof

namespace WCCC.Proof

  -- TODO: ctx needs to be generalized to Γ2 ++ (m, A) :: Γ1
  --       not clear how substitution works in that setup on Γ2
  theorem subst_head :
    Γ ⊢[m1] a : A ->
    ((m1, A) :: Γ) ⊢[m2] t : T ->
    Γ ⊢[m2] (t β[a]) : (T β[a])
  := by {
    intro h j
    generalize Δdef : ((m1, A) :: Γ) = Δ at *
    induction j generalizing m1 A Γ a
    case var Γ' x m1' T K m2 j1 j2 j3 ih =>
      subst Δdef; simp at *
      cases x <;> simp at *
      case _ =>
        cases j1
        case _ h1 h2 =>
          subst h1; subst h2
          sorry
      case _ x =>
        sorry
    case pi Γ' A' m K B j1 j2 ih1 ih2 =>
      sorry
    repeat sorry
  }

end WCCC.Proof
