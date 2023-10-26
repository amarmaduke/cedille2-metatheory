
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

    lemma bind (x : Name) :
    A =β= A' ->
    x ∉ fv B ++ fv B' ->
    {_|-> x}B =β= {_|-> x}B' ->
    Syntax.bind k A B =β= Syntax.bind k A' B'
  := by {
    intro s1 xn s2
    simp at *
    replace xn := demorgan xn
    cases xn; case _ xn1 xn2 =>
    cases s1; case _ Az a1 a2 =>
    cases s2; case _ Bz b1 b2 =>
    apply BetaConv.conv _ _; exact Syntax.bind k Az ({_<-| x}Bz)
    apply red_bind x a1 _ _
    simp; intro h
    cases h
    case _ z => apply xn1 z
    case _ z => apply var_not_in_close z
    simp [*]
    apply red_bind x a2 _ _
    simp; intro h
    cases h
    case _ z => apply xn2 z
    case _ z => apply var_not_in_close z
    simp [*]
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

  -- lemma bind' {S : FvSet!} :
  --   A =β= A' ->
  --   ((x : Name) -> x ∉ S -> {_|-> x}B =β= {_|-> x}B') ->
  --   Syntax.bind k A B =β= Syntax.bind k A' B'
  -- := by {
  --   sorry
  -- }

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
