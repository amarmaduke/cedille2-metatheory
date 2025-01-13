import Common.Term
import Common.Term.Substitution
import Common.Reduction.Definition
import Common.Reduction.Basic

namespace RedPlus

  theorem destruct : x -β>+ z -> ∃ y, x -β> y ∧ y -β>* z := by
  intro r; induction r
  case _ a b r =>
    exists b; apply And.intro r Red.refl
  case _ a b c _ _ ih1 ih2 =>
    cases ih1; case _ u ih1 =>
    cases ih2; case _ v ih2 =>
      exists u; apply And.intro ih1.1
      replace ih2 := RedStar.step ih2.1 ih2.2
      apply Red.trans ih1.2 ih2

end RedPlus
