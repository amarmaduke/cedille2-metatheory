
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

  lemma bind :
    A =β= A' ->
    B =β= B' ->
    Syntax.bind k A B =β= Syntax.bind k A' B'
  := by {
    intro c1 c2
    cases c1; case _ Az r1 r2 =>
    cases c2; case _ Bz r3 r4 =>
    apply BetaConv.conv _ _; exact Syntax.bind k Az Bz
    apply red_bind r1 r3
    apply red_bind r2 r4
  }

  lemma ctor :
    A =β= A' ->
    B =β= B' ->
    C =β= C' ->
    Syntax.ctor k A B C =β= Syntax.ctor k A' B' C'
  := by {
    intro c1 c2 c3
    cases c1; case _ Az a1 a2 =>
    cases c2; case _ Bz b1 b2 =>
    cases c3; case _ Cz c1 c2 =>
    apply BetaConv.conv _ _; exact Syntax.ctor k Az Bz Cz
    apply red_ctor a1 b1 c1
    apply red_ctor a2 b2 c2
  }

  lemma red_f : A =β= B -> A -β>* A' -> A' =β= B := by {
    intro cv step
    have cv2 : A' =β= A := BetaConv.symm (BetaConv.conv step RedStar.refl)
    apply BetaConv.trans cv2 cv
  }

  -- lemma open_if (x : Name) : t =β= t' -> {_|-> x}t =β= {_|-> x}t' := by {
  --   intro h
  --   cases h; case _ z r1 r2 =>
  --   sorry
  -- }

  -- lemma bind' {S : FvSet!} :
  --   A =β= A' ->
  --   ((x : Name) -> x ∉ S -> {_|-> x}B =β= {_|-> x}B') ->
  --   Syntax.bind k A B =β= Syntax.bind k A' B'
  -- := by {
  --   sorry
  -- }

end Cedille.BetaConv
