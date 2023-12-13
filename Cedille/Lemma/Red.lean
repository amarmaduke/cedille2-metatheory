
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Inversion
import Cedille.Lemma.Syntax
import Cedille.Lemma.Substitution

namespace Cedille

  -- lemma red_open : t -β> t' -> {_|-> x}t -β> {_|-> x}t' := by {
  --   intro step
  --   induction step <;> simp
  --   case beta m u1 u2 u3 => {
  --     have s1 := @Red.beta _ m u1 u2 u3
  --     have s2 := @Red.beta _ m ({_|-> x}u1) ({_|-> x}u2) ({_|-> x}u3)

  --   }
  --   repeat sorry
  -- }


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
    case beta t1 t2 t3 => {
      apply FvSet.subset_right _
      apply FvSet.subset_comm _
      apply @fv_subst _ t3 t2
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
    case bind2 z1 z2 k z3 S h ih => {
      have fresh := @Name.fresh_is_fresh (S ++ fv z2)
      generalize _xdef : Name.fresh (S ++ fv z2) = x at *
      have xn1 := FvSet.not_mem_left fresh
      have xn2 := FvSet.not_mem_right fresh
      have lem := ih x xn1; simp at lem
      replace lem := fv_open_shrink xn2 lem
      apply FvSet.subset_right; exact lem
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

  lemma red_rename_step : t1 -β> t2 -> {_|-> y}{_<-| x}t1 -β> {_|-> y}{_<-| x}t2 := by {
    intro step
    cases Name.decEq x y
    case isFalse h => {
      induction step <;> simp
      case beta m u1 u2 u3 => apply Red.beta
      case fst => apply Red.fst
      case snd => apply Red.snd
      case eqind => apply Red.eqind
      case promote => apply Red.promote
      case phi t1 t2 t3 => apply Red.phi
      case bind1 u1 u1' k u2 _ ih => {
        apply Red.bind1
        apply ih
      }
      case bind2 u2 u2' k u1 S _ ih => {
        apply Red.bind2 _; exact (S ++ [x])
        intro z zn
        simp at zn
        replace zn := demorgan zn
        cases zn; case _ zn1 zn2 =>
        rw [rename_open_commute zn2, rename_open_commute zn2]
        apply ih z zn1
      }
      case ctor1 t1 t1' c t2 t3 _ ih => apply Red.ctor1; apply ih
      case ctor2 t2 t2' c t1 t3 _ ih => apply Red.ctor2; apply ih
      case ctor3 t3 t3' c t1 t3 _ ih => apply Red.ctor3; apply ih
    }
    case isTrue h => subst h; simp [*]
  }

  lemma red_rename : t1 -β>* t2 -> {_|-> y}{_<-| x}t1 -β>* {_|-> y}{_<-| x}t2 := by {
    intro step
    induction step
    case refl => apply RedStar.refl
    case step u u' v s1 _s2 ih => {
      have lem := @red_rename_step _ _ y x s1
      apply RedStar.step lem ih
    }
  }

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

  lemma red_open_generalize_step :
    x ∉ fv t1 ->
    x ∉ fv t2 ->
    {_|-> x}t1 -β> {_|-> x}t2 ->
    ∀ y, {_|-> y}t1 -β> {_|-> y}t2
  := by {
    intro xn1 xn2 step y
    have step2 := @red_rename_step _ _ y x step
    rw [close_open_cancel xn1, close_open_cancel xn2] at step2
    apply step2
  }

  lemma red_open_generalize :
    x ∉ fv t1 ->
    x ∉ fv t2 ->
    {_|-> x}t1 -β>* {_|-> x}t2 ->
    ∀ y, {_|-> y}t1 -β>* {_|-> y}t2
  := by {
    intro xn1 xn2 step y
    have step2 := @red_rename _ _ y x step
    rw [close_open_cancel xn1, close_open_cancel xn2] at step2
    apply step2
  }

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

  lemma red_bind2 (x : Name) :
    x ∉ fv B ++ fv B' ->
    {_|-> x}B -β>* {_|-> x}B' ->
    Syntax.bind k A B -β>* Syntax.bind k A B'
  := by {
    intro xn h
    generalize C1def : {_|-> x}B = C at *
    generalize C2def : {_|-> x}B' = C' at *
    induction h generalizing B B'
    case refl t => {
      simp at xn
      replace xn := demorgan xn
      cases xn; case _ xn1 xn2 =>
      replace C1def := open_to_close xn1 C1def
      replace C2def := open_to_close xn2 C2def
      subst C1def; subst C2def
      apply RedStar.refl
    }
    case step u v u' s1 _s2 ih => {
      simp at xn
      replace xn := demorgan xn
      cases xn; case _ xn1 xn2 =>
      apply RedStar.step _ _; exact Syntax.bind k A ({_<-| x}v)
      apply Red.bind2 _; exact []; intro y yn
      rw [<-C1def] at s1
      have lem := @red_rename_step _ _ y x s1
      rw [close_open_cancel xn1] at lem
      exact lem
      have xn3 : x ∉ fv ({_<-| x}v) ++ fv B' := by {
        simp; intro h
        cases h
        case _ h => {
          have lem := @var_not_in_close x _ v
          apply lem h
        }
        case _ h => apply xn2 h
      }
      apply @ih ({_<-| x}v) B' xn3 (by simp) C2def
    }
  }

  lemma red_bind2' {S : FvSet!} :
    ((x : Name) -> x ∉ S -> {_|-> x}B -β>* {_|-> x}B') ->
    Syntax.bind k A B -β>* Syntax.bind k A B'
  := by {
    intro h
    have fresh := @Name.fresh_is_fresh (S ++ fv B ++ fv B')
    generalize _xdef : Name.fresh (S ++ fv B ++ fv B') = x at *
    simp at fresh
    replace fresh := demorgan fresh
    cases fresh; case _ xn1 xn2' =>
    have xn2 := demorgan xn2'
    cases xn2; case _ xn2 xn3 =>
    have h2 := h x xn1
    apply red_bind2 x (by simp; exact xn2') h2
  }

  lemma red_bind (x : Name) :
    A -β>* A' ->
    x ∉ fv B ++ fv B' ->
    {_|-> x}B -β>* {_|-> x}B' ->
    Syntax.bind k A B -β>* Syntax.bind k A' B'
  := by {
    intro s1 xn s2
    apply RedStar.trans _ _; exact Syntax.bind k A' B
    apply red_bind1 s1
    apply red_bind2 x xn s2
  }

  lemma red_bind' {S : FvSet!} :
    A -β>* A' ->
    ((x : Name) -> x ∉ S -> {_|-> x}B -β>* {_|-> x}B') ->
    Syntax.bind k A B -β>* Syntax.bind k A' B'
  := by {
    intro s1 s2
    apply RedStar.trans _ _; exact Syntax.bind k A' B
    apply red_bind1 s1
    apply red_bind2' s2
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

  lemma red_pi
    : A -β>* A' -> x ∉ fv B ++ fv B' -> {_|-> x}B -β>* {_|-> x}B' -> pi m A B -β>* pi m A' B'
  := by apply red_bind

  lemma red_pi' {S : FvSet!}
    : A -β>* A' -> ((x : Name) -> x ∉ S -> {_|-> x}B -β>* {_|-> x}B') -> pi m A B -β>* pi m A' B'
  := by apply red_bind'

  lemma red_lam
    : A -β>* A' -> x ∉ fv B ++ fv B' -> {_|-> x}B -β>* {_|-> x}B' -> lam m A B -β>* lam m A' B'
  := by apply red_bind

  lemma red_lam' {S : FvSet!}
    : A -β>* A' -> ((x : Name) -> x ∉ S -> {_|-> x}B -β>* {_|-> x}B') -> lam m A B -β>* lam m A' B'
  := by apply red_bind'

  lemma red_inter
    : A -β>* A' -> x ∉ fv B ++ fv B' -> {_|-> x}B -β>* {_|-> x}B' -> pi m A B -β>* pi m A' B'
  := by apply red_bind

  lemma red_inter' {S : FvSet!}
    : A -β>* A' -> ((x : Name) -> x ∉ S -> {_|-> x}B -β>* {_|-> x}B') -> inter A B -β>* inter A' B'
  := by apply red_bind'

  lemma red_app : f -β>* f' -> a -β>* a' -> app m f a -β>* app m f' a'
  := by intro h1 h2; apply red_ctor h1 h2 RedStar.refl

  lemma red_pair : t -β>* t' -> s -β>* s' -> a -β>* a' -> pair t s a -β>* pair t' s' a'
  := by apply red_ctor

  lemma red_fst : t -β>* t' -> fst t -β>* fst t'
  := by intro h; apply red_ctor h RedStar.refl RedStar.refl

  lemma red_snd : t -β>* t' -> snd t -β>* snd t'
  := by intro h; apply red_ctor h RedStar.refl RedStar.refl

  lemma red_eq : A -β>* A' -> a -β>* a' -> b -β>* b' -> eq A a b -β>* eq A' a' b'
  := by apply red_ctor

  lemma red_promote : t -β>* t' -> promote t -β>* promote t'
  := by intro h; apply red_ctor h RedStar.refl RedStar.refl

  lemma red_phi : a -β>* a' -> b -β>* b' -> e -β>* e' -> phi a b e -β>* phi a' b' e'
  := by apply red_ctor

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

  lemma red_force_typeu : typeu -β>* A -> A = typeu := by {
    intro step
    cases step <;> try simp [*]
    case _ _ step _ => cases step
  }

  @[simp] lemma red_inv_pi_not_pi_domain : ¬ pi m1 A B -β>* Mode.pi_domain m2 K := by {
    intro h
    generalize lhsdef : pi m1 A B = lhs at *
    generalize rhsdef : Mode.pi_domain m2 K = rhs at *
    induction h generalizing m1 A B
    case refl => {
      subst lhsdef
      cases m2 <;> simp at *
    }
    case step u u' z s1 s2 ih => {
      subst lhsdef; cases s1 <;> simp at *
      case bind1 A' step => apply @ih m1 A' B rfl rhsdef
      case bind2 B' S step => apply @ih m1 A B' rfl rhsdef
    }
  }

  @[simp] lemma red_inv_inter_not_pi_domain : ¬ inter A B -β>* Mode.pi_domain m K := by {
    intro h
    generalize lhsdef : inter A B = lhs at *
    generalize rhsdef : Mode.pi_domain m K = rhs at *
    induction h generalizing m A B
    case refl => {
      subst lhsdef
      cases m <;> simp at *
    }
    case step u u' z s1 s2 ih => {
      subst lhsdef; cases s1 <;> simp at *
      case bind1 A' step => apply @ih A' B m rfl rhsdef
      case bind2 B' S step => apply @ih A B' m rfl rhsdef
    }
  }

  -- ALl cases but lam are by IH
  lemma preservation_of_sanity_step : Sane a -> a -β> a' -> Sane a' := by {
    intro h step
    induction h generalizing a'
    case ax => cases step
    case var => cases step
    case pi => sorry
    case lam A t m S Ah th e aih tih => {
      cases step
      case bind1 A' step => {
        simp; replace aih := aih step
        constructor; exact aih; exact th; exact e
      }
      case bind2 t' S' step => {
        simp
        sorry -- Need a lemma saying reduction doesn't move erased to non-eraed
        -- otherwise straightforward
      }
    }
    case app f b m h1 h2 ih1 ih2 => {
      cases step
      case beta u v => {
        cases h1; case _ S ih2 ih3 ih4 =>
        apply sanity_subst h2 ih3
      }
      case ctor1 => sorry
      case ctor2 => sorry
      case ctor3 => sorry
    }
    case inter => sorry
    case pair => sorry
    case fst t h ih => {
      cases step
      case fst u v => cases h; simp [*]
      case phi u v => cases h; simp [*]
      case ctor1 t' step => {
        simp; replace ih := ih step
        constructor; exact ih
      }
      case ctor2 _ step => cases step
      case ctor3 _ step => cases step
    }
    case snd t h ih => {
      cases step
      case snd u v => cases h; simp [*]
      case ctor1 u step => {
        simp; replace ih := ih step
        constructor; exact ih
      }
      case ctor2 _ step => cases step
      case ctor3 _ step => cases step
    }
    case eq => sorry
    case refl => sorry
    case eqind A P x y r w Ah Ph xh yh rh wh Aih Pih xih yih rih wih => {
      cases step
      case eqind t => {
        constructor; exact wh
        cases rh; case _ h => exact h
      }
      case ctor1 => sorry
      case ctor2 => sorry
      case ctor3 => sorry
    }
    case promote e h ih => {
      cases step
      case promote t => {
        cases h; case _ h =>
        cases h; case _ h =>
        constructor; exact h
      }
      case ctor1 e' step => {
        simp; replace ih := ih step
        constructor; exact ih
      }
      case ctor2 _ step => cases step
      case ctor3 _ step => cases step
    }
    case phi a f e ah fh eh aih fih eih => {
      cases step
      case ctor1 => sorry
      case ctor2 => sorry
      case ctor3 => sorry
    }
    case delta e h ih => {
      cases step
      case ctor1 => sorry
      case ctor2 _ step => cases step
      case ctor3 _ step => cases step
    }
  }

  lemma preservation_of_sanity : Sane a -> a -β>* a' -> Sane a' := by {
    intro h step
    induction step
    case refl => simp [*]
    case step t1 t2 _ r1 _ ih => {
      have lem := preservation_of_sanity_step h r1
      apply ih lem
    }
  }

  -- lemma ctt_normal : ¬ (ctt -β> t) := sorry
  -- lemma cff_normal : ¬ (cff -β> t) := sorry
  -- lemma cbool_normal : ¬ (cbool -β> t) := sorry

end Cedille
