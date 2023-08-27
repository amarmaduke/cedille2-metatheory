
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Syntax

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


  lemma red_open_forced_step : {_|-> x}t1 -β> t2 -> ∃ z, t2 = {_|-> x}z ∧ x ∉ fv z := sorry
  lemma red_open_forced : {_|-> x}t1 -β>* t2 -> ∃ z, t2 = {_|-> x}z ∧ x ∉ fv z := sorry


  lemma red_pi : A -β>* A' -> {_|-> x}B -β>* {_|-> x}B' -> pi m A B -β>* pi m A' B' := by {
    intro s1 s2
    induction s1
    case refl A => {
      generalize Cdef1 : {_|-> x}B = C at *    
      generalize Cdef2 : {_|-> x}B' = C' at *    
      induction s2 generalizing x B B'
      case refl => sorry
      case step v1 v2 v3 vs s2 ih2 => {
        rw [<-Cdef1] at vs
        have e := red_open_forced_step vs
        casesm* ∃ _, _, _ ∧ _; case _ z ze zn =>
        have ze : {_|-> x}z = v2 := by rw [ze]
        have lem := ih2 ze Cdef2
        rw [<-ze] at vs
        sorry
      }
    }
    case step u1 u2 u3 us s1 ih1 => {
      have s3 : pi m u1 B -β> pi m u2 B := by {
        unfold pi; apply Red.bind1 us
      }
      apply RedStar.step s3 ih1
    }
  }

  lemma red_lam : A -β>* A' -> {_|-> x}B -β>* {_|-> x}B' -> lam m A B -β>* lam m A' B' := sorry

  lemma red_app : f -β>* f' -> a -β>* a' -> app m f a -β>* app m f' a' := sorry

  lemma red_inter : A -β>* A' -> {_|-> x}B -β>* {_|-> x}B' -> inter A B -β>* inter A' B' := sorry

  lemma red_pair : t -β>* t' -> s -β>* s' -> a -β>* a' -> pair t s a -β>* pair t' s' a' := sorry

  lemma red_fst : t -β>* t' -> fst t -β>* fst t' := sorry

  lemma red_snd : t -β>* t' -> snd t -β>* snd t' := sorry

  lemma red_eq : A -β>* A' -> a -β>* a' -> b -β>* b' -> eq A a b -β>* eq A' a' b' := sorry

  lemma red_promote : t -β>* t' -> promote t -β>* promote t' := sorry

  lemma red_phi : a -β>* a' -> b -β>* b' -> e -β>* e' -> phi a b e -β>* phi a' b' e' := sorry

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
      apply And.intro _ _
      apply subset_right; apply subset_right; simp
      apply subset_right; apply subset_left; simp
    }
    case snd z1 z2 z3 => {
      apply subset_right; apply subset_left; simp
    }
    case eqind z1 z2 z3 z4 z5 z6 => {
      apply And.intro _ _
      apply subset_right; apply subset_right; apply subset_right;
      apply subset_right; apply subset_right; simp
      apply subset_right; apply subset_right; apply subset_right;
      apply subset_right; apply subset_left; simp
    }
    case phi z1 z2 z3 => {
      apply subset_right; apply subset_left; simp
    }
    case bind1 z1 z2 k z3 h ih => {
      apply subset_left; simp [*]
    }
    case bind2 z1 z2 k z3 S h ih => {
      have fresh := @Name.fresh_is_fresh (S ++ fv z2)
      generalize _xdef : Name.fresh (S ++ fv z2) = x at *
      have xn1 := FvSet.not_mem_left fresh
      have xn2 := FvSet.not_mem_right fresh
      have lem := ih x xn1; simp at lem
      apply subset_right; apply subset_cons xn2 lem
    }
    case ctor1 z1 z2 k z4 z5 h ih => {
      apply subset_left; simp [*]
    }
    case ctor2 z1 z2 k z4 z5 h ih => {
      apply And.intro _ _
      apply subset_right; apply subset_left; simp [*]
      apply subset_right; apply subset_right; simp
    }
    case ctor3 z1 z2 k z4 z5 h ih => {
      apply And.intro _ _
      apply subset_right; apply subset_left; simp
      apply subset_right; apply subset_right; simp [*]
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
      case phi h => {
        apply Red.phi
        apply erase_rename h
      }
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
  --   intro yn step
  --   cases Name.decEq x y
  --   case isFalse h => {
  --     induction step <;> simp
  --     case beta m u1 u2 u3 => apply Red.beta
  --     case fst => apply Red.fst
  --     case snd => apply Red.snd
  --     case eqind => apply Red.eqind
  --     case promote => apply Red.promote
  --     case phi h => {
  --       apply Red.phi
  --       apply erase_rename h
  --     }
  --     case bind1 u1 u1' k u2 _ ih => {
  --       simp at yn
  --       replace yn := demorgan yn
  --       cases yn; case _ yn1 yn2 =>
  --       apply Red.bind1
  --       apply ih yn1
  --     }
  --     case bind2 u2 u2' k u1 S _ ih => {
  --       simp at yn
  --       replace yn := demorgan yn
  --       cases yn; case _ yn1 yn2 =>
  --       apply Red.bind2 _; exact (S ++ [x] ++ [y])
  --       intro z zn
  --       simp at zn
  --       replace zn := demorgan zn
  --       cases zn; case _ zn1 zn2 =>
  --       replace zn2 := demorgan zn2
  --       cases zn2; case _ zn2 zn3 =>
  --       rw [rename_open_commute zn2, rename_open_commute zn2]
  --       apply ih z zn1 _
  --       simp; intro h; cases h
  --       case _ h => subst h; apply zn3 rfl
  --       case _ h => apply yn2 h
  --     }
  --     case ctor1 t1 t1' c t2 t3 _ ih => {
  --       simp at yn
  --       replace yn := demorgan yn; cases yn; case _ yn1 yn2 =>
  --       replace yn2 := demorgan yn2; cases yn2; case _ yn2 yn3 =>
  --       apply Red.ctor1; apply ih yn1
  --     }
  --     case ctor2 t2 t2' c t1 t3 _ ih => {
  --       simp at yn
  --       replace yn := demorgan yn; cases yn; case _ yn1 yn2 =>
  --       replace yn2 := demorgan yn2; cases yn2; case _ yn2 yn3 =>
  --       apply Red.ctor2; apply ih yn2
  --     }
  --     case ctor3 t3 t3' c t1 t3 _ ih => {
  --       simp at yn
  --       replace yn := demorgan yn; cases yn; case _ yn1 yn2 =>
  --       replace yn2 := demorgan yn2; cases yn2; case _ yn2 yn3 =>
  --       apply Red.ctor3; apply ih yn3
  --     }
  --   }
  --   case isTrue h => subst h; simp [*]
  -- }


  lemma red_subst_step (x) (t : Term 0) : t1 -β> t2 -> [x := t]t1 -β> [x := t]t2 := by {
    intro step
    induction step
    repeat sorry
  }

  lemma red_subst (x) (t : Term 0) : t1 -β>* t2 -> [x := t]t1 -β>* [x := t]t2 := by {
    intro step
    induction step
    case refl => apply RedStar.refl
    case step u1 u2 u3 s1 _s2 ih => {
      have s3  := red_subst_step x t s1
      apply RedStar.step s3 ih
    }
  }

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

    -- intro xn1 xn2 step y yn1 yn2
    -- generalize z1def : {_|-> x}t1 = z1 at *    
    -- generalize z2def : {_|-> x}t2 = z2 at *
    -- induction step generalizing t1 t2 x y
    -- case beta => sorry
    -- case fst u1 u2 u3 => {
    --   cases t1 <;> unfold fst at z1def <;> simp at *
    --   case bound => sorry
    --   case ctor k v1 v2 v3 => {
    --     unfold fst at z1def; injection z1def with _ e1 e2 e3 e4
    --     have e3 : v2 = kindu := sorry
    --     have e4 : v3 = kindu := sorry
    --     subst e1; subst e3; subst e4; simp
    --     cases v1 <;> simp at *
    --     case bound => sorry
    --     case ctor k2 w1 w2 w3 h => {
    --       sorry
    --       -- unfold pair at e2; injection e2 with _ e1 e2 e3 e4
    --       -- subst e1; simp
    --       -- rw [<-e2] at z2def
    --       -- have e5 : t2 = w1 := sorry
    --       -- subst e5
    --       -- exists []; intro y yn
    --       -- apply Red.fst
    --     }
    --   }
    -- }
    -- case snd => sorry
    -- case eqind => sorry
    -- case promote => sorry
    -- case phi => sorry
    -- case bind1 => sorry
    -- case bind2 u1 u2 k u3 S h ih => {
    --   cases t1 <;> simp at *
    --   case bound => sorry
    --   case bind b v1 v2 => {
    --     cases t2 <;> simp at *
    --     case bound => sorry
    --     case bind b' w1 w2 => {
    --       replace xn1 := demorgan xn1
    --       replace xn2 := demorgan xn2
    --       replace yn1 := demorgan yn1
    --       replace yn2 := demorgan yn2
    --       casesm* ∃ _, _, _ ∧ _; case _ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 =>
    --       subst e1; subst e2
    --       have e11' := open_to_close e3 e11
    --       have e13' := open_to_close e5 e13
    --       rw [e11', e13']
    --       apply Red.bind2 _
    --       exact S
    --       intro z zn
    --       have lem := @ih z zn z ({_|-> y}v2) ({_|-> y}w2) sorry sorry z sorry sorry
    --       --have lem := @ih z zn z ({_|-> x}v2) ({_|-> x}w2) sorry sorry (by congr) (by congr)
    --       --cases lem; case _ S' lem =>



    --       -- casesm* ∃ _, _, _ ∧ _; case _ e1 e2 e3 e4 e5 e6 =>
    --       -- subst e1; subst e2
    --       -- exists S; intro y yn
    --       -- have e1' : v2 = {_<-| x}u1 := sorry
    --       -- have e2' : w2 = {_<-| x}u2 := sorry
    --       -- rw [e1', e2']
    --       -- apply Red.bind2 _
    --       -- trivial; intro z zn


    --     }
    --   }
    -- }
    -- case ctor1 => sorry
    -- case ctor2 => sorry
    -- case ctor3 => sorry
  }

  lemma red_open_generalize (S : FvSet!) :
    x ∉ fv t1 ->
    x ∉ fv t2 ->
    {_|-> x}t1 -β>* {_|-> x}t2 ->
    ∀ y, y ∉ S -> {_|-> y}t1 -β>* {_|-> y}t2
  := by {
    intro xn1 xn2 step
    generalize z1def : {_|-> x}t1 = z1 at *    
    generalize z2def : {_|-> x}t2 = z2 at *
    induction step generalizing t1 t2 x
    case refl t => {
      sorry
    }
    case step u1 u2 u3 s1 s2 ih => {
      rw [<-z1def] at s1
      have s1' := red_open_forced_step s1
      casesm* ∃ _, _, _ ∧ _; case _ z ze zn =>
      rw [ze] at s1
      have lem := ih zn xn2 (by rw [ze]) z2def
      sorry
    }
  }

  lemma red_pi2 : x ∉ fv B ++ fv B' -> {_|-> x}B -β> {_|-> x}B' -> pi m A B -β> pi m A B' := by {
    intro xn h
    simp at xn
    replace xn := demorgan xn
    cases xn; case _ xn1 xn2 =>
    apply Red.bind2 _
    exact (fv B ++ fv B')
    intro y yn
    simp at yn
    replace yn := demorgan yn
    cases yn; case _ yn1 yn2 =>
    have g := red_open_generalize_step xn1 xn2 h
    apply g y yn1 yn2
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

  -- lemma ctt_normal : ¬ (ctt -β> t) := sorry
  -- lemma cff_normal : ¬ (cff -β> t) := sorry
  -- lemma cbool_normal : ¬ (cbool -β> t) := sorry

end Cedille
