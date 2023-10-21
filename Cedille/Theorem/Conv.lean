
import Cedille.Def
import Cedille.Lemma

namespace Cedille

  lemma trans : Γ ⊢ b : B -> a === b -> b === c -> a === c := by {
    intro j e1 e2
    cases e1; case _ u1 u2 r1 e1 r2 =>
    cases e2; case _ v1 v2 r3 e2 r4 =>
    have confl := confluence r2 r3
    casesm* ∃ _, _, _ ∧ _; case _ z w1 w2 =>
    have e3 := BetaConv.conv w1 w2
    apply Conv.conv r1 r4
    intro x
    simp at *
    replace e1 := e1 x
    replace e2 := e2 x
    have ju2 := preservation_of_infer j r2
    have jv1 := preservation_of_infer j r3
    casesm* ∃ _, _; case _ _ ju2 _ jv1 =>
    replace e3 : u2 === v1 := by {
      cases e3; case _ z r1 r2 =>
      apply Conv.conv r1 r2 _
      intro x; apply BetaConv.refl
    }
    replace e3 := conv_by_erase ju2 jv1 e3
    have e4 := BetaConv.trans e1 (e3 x)
    have e5 := BetaConv.trans e4 e2
    simp [*]
  }

  lemma red_f :
    Γ ⊢ a : A ->
    a === b ->
    a -β>* a' ->
    a' === b
  := by {
    intros j h step
    have lem1 : a === a' := Conv.conv step (@RedStar.refl a') (λ _ => BetaConv.refl)
    apply trans j (Conv.symm lem1) h
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
