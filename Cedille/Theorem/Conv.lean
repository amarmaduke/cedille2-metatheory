
import Cedille.Def
import Cedille.Lemma

namespace Cedille

  lemma trans :
    Γ1 ⊢ A : T1 ->
    Γ2 ⊢ B : T2 ->
    Γ3 ⊢ C : T3 ->
    A =β= B ->
    B =β= C ->
    A =β= C
  := by {
    intros j1 j2 j3 e1 e2
    cases e1; case _ u1 u2 S1 r1 e1 r2 =>
    cases e2; case _ v1 v2 S2 s1 e2 s2 =>
    have confl := confluence r2 s1
    casesm* ∃ _, _, _ ∧ _; case _ z rz1 rz2 =>
    have j4 := preservation_of_infer j2 r2
    have j5 := preservation_of_infer j2 s1
    have j6 := preservation_of_infer j1 r1
    have j7 := preservation_of_infer j3 s2
    casesm* ∃ _, _; case _ T1 wj1 T2 wj2 T3 wj3 T4 wj4 =>
    have j8 := preservation_of_infer wj1 rz1
    cases j8; case _ T5 wj5 =>
    have lem1 := red_erasure S1 wj1 wj3 (λ x xn => Eq.symm (e1 x xn)) rz1
    have lem2 := red_erasure S2 wj2 wj4 e2 rz2
    casesm* ∃ _, _, _ ∧ _; case _ w1 w2 wr1 we1 wr2 we2 =>
    have l := RedStar.trans r1 wr1
    have r := RedStar.trans s2 wr2
    apply Conv.conv (S1 ++ S2) l r _
    intro x xn; simp at xn
    replace xn := demorgan xn
    cases xn; case _ xn1 xn2 =>
    rw [<-we1 x xn1, <-we2 x xn2]
  }

  lemma red_f :
    Γ1 ⊢ a : A ->
    Γ2 ⊢ b : B ->
    a =β= b ->
    a -β>* a' ->
    a' =β= b
  := by {
    intros aproof bproof h step
    have lem1 : a =β= a' := Conv.conv [] step (@RedStar.refl a') (by simp)
    have lem2 := preservation_of_infer aproof step
    cases lem2; case _ A' j =>
    apply trans j aproof bproof (Conv.symm lem1) h
  }

  @[simp] lemma kindu_not_conv_eq : ¬ (kindu =β= eq A a b) := sorry
  @[simp] lemma typeu_not_conv_eq : ¬ (typeu =β= eq A a b) := sorry
  @[simp] lemma pi_codomain_not_conv_eq : ¬ (Mode.pi_codomain m =β= eq A a b) := sorry
  @[simp] lemma pi_not_conv_eq : ¬ (pi m A1 B1 =β= eq A2 a b) := sorry
  @[simp] lemma inter_not_conv_eq : ¬ (inter A1 B1 =β= eq A2 a b) := sorry

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


  -- lemma subst : t =β= s ∧ A =β= B <-> [_:= t]A =β= [_:= s]B := sorry

  -- lemma subst1 : t =β= t' ∧ A =β= [_:= t]B <-> A =β= [_:= t']B := sorry

  -- lemma pi : a1 =β= a2 ∧ b1 =β= b2 <-> pi m a1 b1 =β= pi m a2 b2 := sorry

  -- lemma inter : a1 =β= a2 ∧ b1 =β= b2 <-> inter a1 b1 =β= inter a2 b2 := sorry

  -- lemma fst : t1 =β= t2 <-> fst t1 =β= fst t2 := sorry

  -- lemma eq : A1 =β= A2 ∧ t1 =β= t2 ∧ s1 =β= s2 <-> eq A1 t1 s1 =β= eq A2 t2 s2 := sorry

end Cedille
