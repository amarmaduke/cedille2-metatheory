
import Cedille.Def
import Cedille.Lemma.Erasure
import Cedille.Lemma.Red
import Cedille.Lemma.BetaConv
import Cedille.Lemma.RedErasure
import Cedille.Lemma.Confluence

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

  lemma by_beta : (∀ x, erase x a =β= erase x b) -> a === b := by {
    intro h
    apply Conv.conv RedStar.refl RedStar.refl h
  }

  lemma red_f :
    PseObj a ->
    a === b ->
    a -β>* a' ->
    a' === b
  := by {
    sorry
    -- intro h cv step
    -- cases cv; case _ u v r1 e r2 =>
    -- have lem1 := confluence step r1
    -- casesm* ∃ _, _, _ ∧ _; case _ z r3 r4 =>
    -- have lem2 := preservation_of_sanity h r1
    -- replace e := erase_red_f lem2 e r4
    -- constructor; exact r3; exact r2; exact e
  }

  lemma trans :
    PseObj B ->
    A === B ->
    B === C ->
    A === C
  := by {
    sorry
    -- intro h c1 c2
    -- cases c1; case _ u1 u2 r1 e1 r2 =>
    -- cases c2; case _ v1 v2 r3 e2 r4 =>
    -- have lem := confluence r2 r3
    -- casesm* ∃ _, _, _ ∧ _; case _ B' rr1 rr2 =>
    -- constructor; exact r1; exact r4
    -- intro x
    -- have h2 : PseObj u2 := preservation_of_sanity h r2
    -- have h3 : PseObj v1 := preservation_of_sanity h r3
    -- replace e1 := erase_red_f h2 (λ x => BetaConv.symm (e1 x)) rr1
    -- replace e2 := erase_red_f h3 e2 rr2
    -- have lem := BetaConv.trans (BetaConv.symm (e1 x)) (e2 x)
    -- exact lem
  }

  lemma to_beta (S : FvSet!) : PseObj a -> PseObj b -> a === b -> (∀ x, erase x a =β= erase x b)
  := by {
    intro h1 h2 cv
    cases cv; case _ a' b' r1 e r2 =>
    intro x;
    replace e := erase_red_b h1 e r1
    replace e := erase_red_b h2 (λ x => BetaConv.symm (e x)) r2
    apply BetaConv.symm (e x)
  }

end Cedille.Conv
