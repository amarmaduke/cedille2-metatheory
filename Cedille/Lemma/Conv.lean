
import Cedille.Def 
import Cedille.Lemma.Erasure
import Cedille.Lemma.Red
import Cedille.Lemma.Confluence

namespace Cedille.BetaConv

  lemma refl : A =β= A := by {
    apply BetaConv.conv RedStar.refl RedStar.refl
  }

  lemma symm : A =β= B -> B =β= A := by {
    intros e; cases e; case _ t r1 r2 =>
    apply BetaConv.conv r2 r1
  }

  lemma trans : A =β= B -> B =β= C -> A =β= C := by {
    intro e1 e2
    cases e1; case _ t1 r1 r2 =>
    cases e2; case _ t2 w1 w2 =>
    have r := confluence r2 w1
    casesm* ∃ _, _, _ ∧ _; case _ Z q1 q2 =>
    have r1' := RedStar.trans r1 q1
    have r2' := RedStar.trans w2 q2
    apply BetaConv.conv r1' r2'
  }

end Cedille.BetaConv

namespace Cedille.Conv

  lemma red_b : a === b -> a' -β>* a -> a' === b := by {
    intros e step
    induction step
    case refl t => simp [*]
    case step t1 t2 t3 s1 _s2 ih => {
      have lem := ih e
      cases lem
      case _ c d s3 e2 s4 =>
      have lem := RedStar.step s1 s3
      apply Conv.conv lem s4 e2
    }
  }

  lemma refl : A === A := Conv.conv RedStar.refl RedStar.refl (λ _ => BetaConv.refl)

  lemma symm : A === B -> B === A := by {
    intros e; cases e; case _ u1 u2 r1 e r2 =>
    apply Conv.conv r2 r1 _
    intro x
    apply BetaConv.symm (e x)
  }

  lemma by_beta (S : FvSet!) : (∀ x, erase x a =β= erase x b) -> a === b := by {
    intro h
    apply Conv.conv RedStar.refl RedStar.refl h
  }

end Cedille.Conv
