
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Inversion
import Cedille.Lemma.Syntax
import Cedille.Lemma.Substitution

namespace Cedille

  -- lemma red_open_forced_step : {_|-> x}t1 -β> t2 -> ∃ z, t2 = {_|-> x}z ∧ x ∉ fv z := sorry
  -- lemma red_open_forced : {_|-> x}t1 -β>* t2 -> ∃ z, t2 = {_|-> x}z ∧ x ∉ fv z := sorry

  -- lemma red_open_erase : {_|-> x}(erase t) -β> s -> erase ({_|-> x}t) -β> s := sorry

  -- lemma red_strictify_erasure :
  --   erase ({_|-> Name.fresh S1}t) -β> s ->
  --   erase ({_|-> Name.fresh (S1 ++ S2)}t) -β> s
  -- := sorry

  -- lemma red_open_close_step : x ∉ fv t1 -> {_|-> x}t1 -β> t2 -> t1 -β> {_<-| x}t2 := by {
  --   intros xnin step
  --   generalize h : {_|-> x}t1 = t at *
  --   induction step
  --   sorry
  -- }

  -- lemma red_open_close : x ∉ fv t1 -> {_|-> x}t1 -β>* t2 -> t1 -β>* {_<-| x}t2 := by {
  --   intros xnin step
  --   generalize h : {_|-> x}t1 = t at *
  --   induction step generalizing t1
  --   case refl t' => {
  --     rewrite [<-h]; simp
  --     rw [close_open_cancel xnin]
  --     apply RedStar.refl
  --   }
  --   case step u1 u2 u3 s1 _s2 ih => {
  --     rewrite [<-h] at s1
  --     have u2step := red_open_close_step xnin s1
  --     have lem := @ih ({_<-| x}u2) var_not_in_close (by simp)
  --     apply RedStar.step u2step lem
  --   }
  -- }

  lemma red_fv_step : t1 -β> t2 -> fv t2 ⊆ fv t1 := by {
    intros h
    induction h <;> simp [*]
    case beta m z1 z2 z3 x xn => {
      apply FvSet.subset_right _
      apply FvSet.subset_comm _
      apply @fv_subst x z3 z2
    }
    case snd z1 z2 z3 => {
      apply FvSet.subset_right; apply FvSet.subset_left; simp
    }
    case eqind z1 z2 z3 z4 z5 z6 => {
      apply And.intro _ _
      apply FvSet.subset_right; apply FvSet.subset_right; apply FvSet.subset_right;
      apply FvSet.subset_right; apply FvSet.subset_right; simp
      apply FvSet.subset_right; apply FvSet.subset_right; apply FvSet.subset_right;
      apply FvSet.subset_right; apply FvSet.subset_left; simp
    }
    case bind1 z1 z2 k z3 h ih => {
      apply FvSet.subset_left; simp [*]
    }
    case bind2 z1 z2 k z3 h ih => {
      apply FvSet.subset_right; simp [*]
    }
    case ctor1 z1 z2 k z4 z5 h ih => {
      apply FvSet.subset_left; simp [*]
    }
    case ctor2 z1 z2 k z4 z5 h ih => {
      apply And.intro _ _
      apply FvSet.subset_right; apply FvSet.subset_left; simp [*]
      apply FvSet.subset_right; apply FvSet.subset_right; simp
    }
    case ctor3 z1 z2 k z4 z5 h ih => {
      apply And.intro _ _
      apply FvSet.subset_right; apply FvSet.subset_left; simp
      apply FvSet.subset_right; apply FvSet.subset_right; simp [*]
    }
  }

  lemma red_fv : t1 -β>* t2 -> fv t2 ⊆ fv t1 := by {
    intros step
    induction step
    case refl => simp
    case step z1 z2 z3 s1 _s2 ih => {
      have lem1 := red_fv_step s1
      apply subset_trans ih lem1
    }
  }

  -- lemma red_rename_step : t1 -β> t2 -> {_|-> y}{_<-| x}t1 -β> {_|-> y}{_<-| x}t2 := by {
  --   intro step
  --   cases Name.decEq x y
  --   case isFalse h => {
  --     induction step <;> simp
  --     case beta m u1 u2 u3 => apply Red.beta
  --     case fst => apply Red.fst
  --     case snd => apply Red.snd
  --     case eqind => apply Red.eqind
  --     case promote => apply Red.promote
  --     case phi t1 t2 t3 => apply Red.phi
  --     case bind1 u1 u1' k u2 _ ih => {
  --       apply Red.bind1
  --       apply ih
  --     }
  --     case bind2 u2 u2' k u1 S _ ih => {
  --       apply Red.bind2 _; exact (S ++ [x])
  --       intro z zn
  --       simp at zn
  --       replace zn := demorgan zn
  --       cases zn; case _ zn1 zn2 =>
  --       rw [rename_open_commute zn2, rename_open_commute zn2]
  --       apply ih z zn1
  --     }
  --     case ctor1 t1 t1' c t2 t3 _ ih => apply Red.ctor1; apply ih
  --     case ctor2 t2 t2' c t1 t3 _ ih => apply Red.ctor2; apply ih
  --     case ctor3 t3 t3' c t1 t3 _ ih => apply Red.ctor3; apply ih
  --   }
  --   case isTrue h => subst h; simp [*]
  -- }

  -- lemma red_rename : t1 -β>* t2 -> {_|-> y}{_<-| x}t1 -β>* {_|-> y}{_<-| x}t2 := by {
  --   intro step
  --   induction step
  --   case refl => apply RedStar.refl
  --   case step u u' v s1 _s2 ih => {
  --     have lem := @red_rename_step _ _ _ y x s1
  --     apply RedStar.step lem ih
  --   }
  -- }

  -- lemma red_subst_step (x) (t : Term 0) : t1 -β> t2 -> [x := t]t1 -β> [x := t]t2 := by {
  --   intro step
  --   induction step
  --   repeat sorry
  -- }

  -- lemma red_subst (x) (t : Term 0) : t1 -β>* t2 -> [x := t]t1 -β>* [x := t]t2 := by {
  --   intro step
  --   induction step
  --   case refl => apply RedStar.refl
  --   case step u1 u2 u3 s1 _s2 ih => {
  --     have s3  := red_subst_step x t s1
  --     apply RedStar.step s3 ih
  --   }
  -- }

  -- lemma red_open_generalize_step :
  --   x ∉ fv t1 ->
  --   x ∉ fv t2 ->
  --   {_|-> x}t1 -β> {_|-> x}t2 ->
  --   ∀ y, {_|-> y}t1 -β> {_|-> y}t2
  -- := by {
  --   intro xn1 xn2 step y
  --   have step2 := @red_rename_step _ _ _ y x step
  --   rw [close_open_cancel xn1, close_open_cancel xn2] at step2
  --   apply step2
  -- }

  -- lemma red_open_generalize :
  --   x ∉ fv t1 ->
  --   x ∉ fv t2 ->
  --   {_|-> x}t1 -β>* {_|-> x}t2 ->
  --   ∀ y, {_|-> y}t1 -β>* {_|-> y}t2
  -- := by {
  --   intro xn1 xn2 step y
  --   have step2 := @red_rename _ _ _ y x step
  --   rw [close_open_cancel xn1, close_open_cancel xn2] at step2
  --   apply step2
  -- }

  namespace RedStar
    lemma trans : a -β>* b -> b -β>* c -> a -β>* c := by {
      intros h1 h2
      induction h1 generalizing c
      case refl a' => simp [*]
      case step t1 t2 t3 s1 _s2 ih => {
        have lem := ih h2
        apply RedStar.step s1 lem
      }
    }
  end RedStar

  lemma red_bind1 : A -β>* A' -> Syntax.bind k A B -β>* Syntax.bind k A' B := by {
    intro h
    induction h
    case refl A => apply RedStar.refl
    case step A A' C s1 _s2 ih => {
      apply RedStar.step _ ih
      apply Red.bind1 s1
    }
  }

  lemma red_bind2 : B -β>* B' -> Syntax.bind k A B -β>* Syntax.bind k A B' := by {
    intro h
    induction h
    case refl A => apply RedStar.refl
    case step A A' C s1 _s2 ih => {
      apply RedStar.step _ ih
      apply Red.bind2 s1
    }
  }

  lemma red_bind :
    A -β>* A' ->
    B -β>* B' ->
    Syntax.bind k A B -β>* Syntax.bind k A' B'
  := by {
    intro s1 s2
    apply RedStar.trans _ _; exact Syntax.bind k A' B
    apply red_bind1 s1
    apply red_bind2 s2
  }

  lemma red_bind_rev :
    Syntax.bind k A B -β>* Syntax.bind k A' B' ->
    A -β>* A' ∧ B -β>* B'
  := by {
    intro step
    generalize lhsdef : Syntax.bind k A B = lhs at *
    generalize rhsdef : Syntax.bind k A' B' = rhs at *
    induction step generalizing A B A' B'
    case refl => {
      rw [<-lhsdef] at rhsdef; injection rhsdef with _ e1 e2
      subst e1; subst e2
      apply And.intro RedStar.refl RedStar.refl
    }
    case step t1 t2 t3 step r ih => {
      rw [<-lhsdef] at step
      cases step
      case bind1 T step => {
        replace ih := @ih T B A' B' rfl rhsdef
        have lem := RedStar.step step ih.1
        simp [*]
      }
      case bind2 T step => {
        replace ih := @ih A T A' B' rfl rhsdef
        have lem := RedStar.step step ih.2
        simp [*]
      }
    }
  }

  lemma red_ctor1 : A -β>* A' -> Syntax.ctor k A B C -β>* Syntax.ctor k A' B C := by {
    intro step
    induction step
    case refl => apply RedStar.refl
    case step A A' z s1 _s2 ih => {
      apply RedStar.step _ _; exact Syntax.ctor k A' B C
      apply Red.ctor1 s1; apply ih
    }
  }

  lemma red_ctor2 : B -β>* B' -> Syntax.ctor k A B C -β>* Syntax.ctor k A B' C := by {
    intro step
    induction step
    case refl => apply RedStar.refl
    case step B B' z s1 _s2 ih => {
      apply RedStar.step _ _; exact Syntax.ctor k A B' C
      apply Red.ctor2 s1; apply ih
    }
  }


  lemma red_ctor3 : C -β>* C' -> Syntax.ctor k A B C -β>* Syntax.ctor k A B C' := by {
    intro step
    induction step
    case refl => apply RedStar.refl
    case step C C' z s1 _s2 ih => {
      apply RedStar.step _ _; exact Syntax.ctor k A B C'
      apply Red.ctor3 s1; apply ih
    }
  }

  lemma red_ctor :
    A -β>* A' ->
    B -β>* B' ->
    C -β>* C' ->
    Syntax.ctor k A B C -β>* Syntax.ctor k A' B' C'
  := by {
    intro s1 s2 s3
    apply RedStar.trans _ _; exact Syntax.ctor k A' B C
    apply red_ctor1 s1; apply RedStar.trans _ _; exact Syntax.ctor k A' B' C
    apply red_ctor2 s2; apply red_ctor3 s3
  }

  lemma red_ctor_rev :
    (∀ i md, k ∉ [Constructor.proj i, Constructor.app md, Constructor.eqind, Constructor.promote]) ->
    Syntax.ctor k A B C -β>* Syntax.ctor k A' B' C' ->
    A -β>* A' ∧ B -β>* B' ∧ C -β>* C'
  := by {
    intro h step
    generalize lhsdef : Syntax.ctor k A B C = lhs at *
    generalize rhsdef : Syntax.ctor k A' B' C' = rhs at *
    induction step generalizing A B C A' B' C'
    case refl => {
      rw [<-lhsdef] at rhsdef; injection rhsdef with _ e1 e2 e3
      subst e1; subst e2; subst e3
      apply And.intro RedStar.refl _
      apply And.intro RedStar.refl RedStar.refl
    }
    case step t1 t2 t3 r1 r2 ih => {
      rw [<-lhsdef] at r1
      cases r1
      case beta md _ _ _ _ => exfalso; apply h 1 md; simp
      case fst => exfalso; apply h 1 m0; simp
      case snd => exfalso; apply h 2 m0; simp
      case eqind => exfalso; apply h 1 m0; simp
      case promote k u => exfalso; apply h k m0; simp
      case phi => exfalso; apply h 1 m0; simp
      case ctor1 T step => {
        replace ih := @ih T B C A' B' C' (by simp) rhsdef
        have lem := RedStar.step step ih.1
        simp [*]
      }
      case ctor2 T step => {
        replace ih := @ih A T C A' B' C' (by simp) rhsdef
        have lem := RedStar.step step ih.2.1
        simp [*]
      }
      case ctor3 T step => {
        replace ih := @ih A B T A' B' C' (by simp) rhsdef
        have lem := RedStar.step step ih.2.2
        simp [*]
      }
    }
  }


  -- lemma red_pi
  --   : A -β>* A' -> x ∉ fv B ++ fv B' -> {_|-> x}B -β>* {_|-> x}B' -> pi m A B -β>* pi m A' B'
  -- := by apply red_bind

  -- lemma red_pi' {S : FvSet!}
  --   : A -β>* A' -> ((x : Name) -> x ∉ S -> {_|-> x}B -β>* {_|-> x}B') -> pi m A B -β>* pi m A' B'
  -- := by apply red_bind'

  -- lemma red_lam
  --   : A -β>* A' -> x ∉ fv B ++ fv B' -> {_|-> x}B -β>* {_|-> x}B' -> lam m A B -β>* lam m A' B'
  -- := by apply red_bind

  -- lemma red_lam' {S : FvSet!}
  --   : A -β>* A' -> ((x : Name) -> x ∉ S -> {_|-> x}B -β>* {_|-> x}B') -> lam m A B -β>* lam m A' B'
  -- := by apply red_bind'

  -- lemma red_inter
  --   : A -β>* A' -> x ∉ fv B ++ fv B' -> {_|-> x}B -β>* {_|-> x}B' -> pi m A B -β>* pi m A' B'
  -- := by apply red_bind

  -- lemma red_inter' {S : FvSet!}
  --   : A -β>* A' -> ((x : Name) -> x ∉ S -> {_|-> x}B -β>* {_|-> x}B') -> inter A B -β>* inter A' B'
  -- := by apply red_bind'

  -- lemma red_app : f -β>* f' -> a -β>* a' -> app m f a -β>* app m f' a'
  -- := by intro h1 h2; apply red_ctor h1 h2 RedStar.refl

  -- lemma red_pair : t -β>* t' -> s -β>* s' -> a -β>* a' -> pair t s a -β>* pair t' s' a'
  -- := by apply red_ctor

  -- lemma red_fst : t -β>* t' -> fst t -β>* fst t'
  -- := by intro h; apply red_ctor h RedStar.refl RedStar.refl

  -- lemma red_snd : t -β>* t' -> snd t -β>* snd t'
  -- := by intro h; apply red_ctor h RedStar.refl RedStar.refl

  -- lemma red_eq : A -β>* A' -> a -β>* a' -> b -β>* b' -> eq A a b -β>* eq A' a' b'
  -- := by apply red_ctor

  -- lemma red_promote : t -β>* t' -> promote t -β>* promote t'
  -- := by intro h; apply red_ctor h RedStar.refl RedStar.refl

  -- lemma red_phi : a -β>* a' -> b -β>* b' -> e -β>* e' -> phi a b e -β>* phi a' b' e'
  -- := by apply red_ctor

  -- lemma red_open : t -β> t' -> {i |-> x}t -β> {i |-> x}t' := by {
  --   intro step
  --   induction step <;> simp at *
  --   case beta md t1 t2 t3 => {
  --     have r1 := @Red.beta _ md ({_|-> x}t1) ({_|-> x}t2) ({_|-> x}t3)
  --     sorry
  --   }
  --   case fst => sorry
  --   case snd => sorry
  --   case eqind => sorry
  --   case promote => sorry
  --   case phi => sorry
  --   case bind1 => sorry
  --   case bind2 t2 t2' k t1 S step ih => {
  --     apply Red.bind2; swap; exact S; intro y yn
  --     sorry
  --   }
  --   case ctor1 => sorry
  --   case ctor2 => sorry
  --   case ctor3 => sorry
  -- }

  lemma red_norm : A -β>* A' -> (∀ z, ¬ A -β> z) -> A = A' := by {
    intro step norm
    induction step
    case refl => simp
    case step u u' v s1 _s2 _ih => {
      exfalso; apply norm u' s1
    }
  }

  lemma red_force_mode_pi_domain : Mode.pi_domain m K -β>* A -> A = Mode.pi_domain m K := by {
    intro step
    cases m <;> simp at * <;> cases step <;> try simp [*]
    case _ _ step _ => cases step
    case _ _ step _ => cases step
    case _ _ step _ => cases step
  }

  lemma red_force_mode_pi_codomain : Mode.pi_codomain m -β>* A -> A = Mode.pi_codomain m := by {
    intro step
    cases m <;> simp at * <;> cases step <;> try simp [*]
    case _ _ step _ => cases step
    case _ _ step _ => cases step
    case _ _ step _ => cases step
  }

  lemma red_force_const : const K -β>* A -> A = const K := by {
    intro step
    cases step <;> try simp [*]
    case _ _ step _ => cases step
  }

  -- @[simp] lemma red_inv_pi_not_pi_domain : ¬ pi m1 A B -β>* Mode.pi_domain m2 K := by {
  --   intro h
  --   generalize lhsdef : pi m1 A B = lhs at *
  --   generalize rhsdef : Mode.pi_domain m2 K = rhs at *
  --   induction h generalizing m1 A B
  --   case refl => {
  --     subst lhsdef
  --     cases m2 <;> simp at *
  --   }
  --   case step u u' z s1 s2 ih => {
  --     subst lhsdef; cases s1 <;> simp at *
  --     case bind1 A' step => apply @ih m1 A' B rfl rhsdef
  --     case bind2 B' S step => apply @ih m1 A B' rfl rhsdef
  --   }
  -- }

  -- @[simp] lemma red_inv_inter_not_pi_domain : ¬ inter A B -β>* Mode.pi_domain m K := by {
  --   intro h
  --   generalize lhsdef : inter A B = lhs at *
  --   generalize rhsdef : Mode.pi_domain m K = rhs at *
  --   induction h generalizing m A B
  --   case refl => {
  --     subst lhsdef
  --     cases m <;> simp at *
  --   }
  --   case step u u' z s1 s2 ih => {
  --     subst lhsdef; cases s1 <;> simp at *
  --     case bind1 A' step => apply @ih A' B m rfl rhsdef
  --     case bind2 B' S step => apply @ih A B' m rfl rhsdef
  --   }
  -- }

  -- ALl cases but lam are by IH
  -- lemma preservation_of_pseobj_step : PseObj a -> a -β> a' -> PseObj a' := by {
  --   intro h step
  --   induction h generalizing a'
  --   case ax => cases step
  --   case var => cases step
  --   case bind => sorry
  --   case lam => sorry
  --   case pair t1 t2 t3 h1 h2 h3 e ih1 ih2 ih3 => {
  --     cases step <;> simp
  --     case ctor1 t1' ih => {
  --       apply PseObj.pair (ih1 ih) h2 h3
  --       sorry
  --     }
  --     case ctor2 => sorry
  --     case ctor3 => sorry
  --   }
  --   case ctor k t1 t2 t3 n h1 h2 h3 ih1 ih2 ih3 => {
  --     cases step
  --     case beta m u v => {
  --       cases h1; case _ S h4 h5 h6 => apply subst_pseobj h2 h6
  --       case _ S h4 h5 h6 => apply subst_pseobj h2 h5
  --     }
  --     case fst => cases h1 <;> simp [*]
  --     case snd => cases h1 <;> simp [*]
  --     case eqind => {
  --       cases h3; case _ n2 h4 h5 h6 =>
  --       cases h4; case _ n3 h4 h7 h8 =>
  --       constructor <;> simp [*]
  --     }
  --     case promote => {
  --       cases h1; case _ h _ _ =>
  --       cases h; case _ =>
  --       constructor <;> simp [*]
  --     }
  --     case phi => cases h1; simp [*]
  --     case ctor1 t1' ih => apply PseObj.ctor n (ih1 ih) h2 h3
  --     case ctor2 t2' ih => apply PseObj.ctor n h1 (ih2 ih) h3
  --     case ctor3 t3' ih => apply PseObj.ctor n h1 h2 (ih3 ih)
  --   }
  -- }

  -- lemma preservation_of_pseobj : PseObj a -> a -β>* a' -> PseObj a' := by {
  --   intro h step
  --   induction step
  --   case refl => simp [*]
  --   case step t1 t2 _ r1 _ ih => {
  --     have lem := preservation_of_pseobj_step h r1
  --     apply ih lem
  --   }
  -- }

  -- lemma ctt_normal : ¬ (ctt -β> t) := sorry
  -- lemma cff_normal : ¬ (cff -β> t) := sorry
  -- lemma cbool_normal : ¬ (cbool -β> t) := sorry

end Cedille
