
import Cedille.Def
import Cedille.Lemma.Red
import Cedille.Lemma.RedErasure
import Cedille.Lemma.Confluence

namespace Cedille.Conv

  lemma red_f : a =β= b -> a -β>* a' -> a' =β= b := by {
    intros h step
    cases h; case _ t1 t2 s1 s2 e =>
    have confl := confluence s1 step
    casesm* ∃ _, _, _ ∧ _; case _ z r1 r2 =>
    have lem := red_erasure s2 r1
    casesm* ∃ _, _, _ ∧ _; case _ w r3 e2 =>
    have r4 := RedStar.trans e r3
    apply Conv.conv r2 r4 e2
  }

  lemma red_b : a =β= b -> a' -β>* a -> a' =β= b := by {
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
  lemma refl : A =β= A := Conv.conv RedStar.refl RedStar.refl rfl

  lemma symm : A =β= B -> B =β= A := by {
    intros e; cases e; case _ u1 u2 r1 e r2 =>
    apply Conv.conv r2 r1 (by rewrite [e]; simp)
  }

  lemma trans : A =β= B -> B =β= C -> A =β= C := by {
    intros e1 e2
    cases e1; case _ u1 u2 r1 e1 r2 =>
    cases e2; case _ v1 v2 s1 e2 s2 =>
    have confl := confluence r2 s1
    casesm* ∃ _, _, _ ∧ _; case _ z rz1 rz2 =>
    have lem1 := red_erasure (Eq.symm e1) rz1
    have lem2 := red_erasure e2 rz2
    casesm* ∃ _, _, _ ∧ _; case _ w1 w2 wr1 we1 wr2 we2 =>
    have l := RedStar.trans r1 wr1
    have r := RedStar.trans s2 wr2
    have eq : erase w1 = erase w2 := by rewrite [<-we1, <-we2]; rfl
    apply Conv.conv l r eq
  }

  -- lemma red_ff : a =β= b -> a -β>* a' -> b -β>* b' -> a' =β= b' := by {
  --   intros e s1 s2
  --   apply red_f _ s1
  --   apply symm (red_f (symm e) s2)
  -- }

  -- lemma red_bb : a =β= b -> a' -β>* a -> b' -β>* b -> a' =β= b' := by {
  --   intros e s1 s2
  --   apply red_b _ s1
  --   apply symm (red_b (symm e) s2)
  -- }

  -- lemma red_fb : a =β= b -> a -β>* a' -> b' -β>* b -> a' =β= b' := sorry

  -- lemma red_bf : a =β= b -> a' -β>* a -> b -β>* b' -> a' =β= b' := sorry


  lemma subst : t =β= s ∧ A =β= B <-> [_:= t]A =β= [_:= s]B := sorry

  lemma subst1 : t =β= t' ∧ A =β= [_:= t]B <-> A =β= [_:= t']B := sorry

  lemma pi : a1 =β= a2 ∧ b1 =β= b2 <-> pi m a1 b1 =β= pi m a2 b2 := sorry

  lemma inter : a1 =β= a2 ∧ b1 =β= b2 <-> inter a1 b1 =β= inter a2 b2 := sorry

  lemma fst : t1 =β= t2 <-> fst t1 =β= fst t2 := sorry

  lemma eq : A1 =β= A2 ∧ t1 =β= t2 ∧ s1 =β= s2 <-> eq A1 t1 s1 =β= eq A2 t2 s2 := sorry

end Cedille.Conv
