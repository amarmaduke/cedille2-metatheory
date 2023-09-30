
import Cedille.Def

namespace Cedille.Conv

  lemma red_b : a =β= b -> a' -β>* a -> a' =β= b := by {
    intros e step
    induction step
    case refl t => simp [*]
    case step t1 t2 t3 s1 _s2 ih => {
      have lem := ih e
      cases lem
      case _ c d S s3 e2 s4 =>
      have lem := RedStar.step s1 s3
      apply Conv.conv _ lem s4 e2
    }
  }

  lemma refl : A =β= A := Conv.conv [] RedStar.refl RedStar.refl (λ _ _ => rfl)

  lemma symm : A =β= B -> B =β= A := by {
    intros e; cases e; case _ u1 u2 S r1 e r2 =>
    apply Conv.conv S r2 r1 _
    intro x xn
    rw [e x xn]
  }

end Cedille.Conv
