
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Inversion
import Cedille.Lemma.Syntax
import Cedille.Lemma.Substitution
import Cedille.Lemma.Red

-- based heavily off https://plfa.inf.ed.ac.uk/Confluence/

namespace Cedille

  def parp (t : Term) : Term :=
    match t with
    | Syntax.const k => const k
    | Syntax.bound i => bound i
    | Syntax.free x => free x
    | Syntax.ctor (Constructor.app _)
      (Syntax.bind (Binder.lam _) _t1 t2)
      t3
      (Syntax.const Constant.kindU)
      =>
      let x := @Name.fresh (fv t2);
      [x := parp t3]{0 <-| x}(parp t2)
    | Syntax.ctor (Constructor.proj 1)
      (Syntax.ctor Constructor.pair u1 _u2 _u3)
      (Syntax.const Constant.kindU)
      (Syntax.const Constant.kindU)
      => parp u1
    | Syntax.ctor (Constructor.proj 1)
      (Syntax.ctor Constructor.phi u1 _u2 _u3)
      (Syntax.const Constant.kindU)
      (Syntax.const Constant.kindU)
      => parp u1
    | Syntax.ctor (Constructor.proj 2)
      (Syntax.ctor Constructor.pair _u1 u2 _u3)
      (Syntax.const Constant.kindU)
      (Syntax.const Constant.kindU)
      => parp u2
    | Syntax.ctor Constructor.eqind
      _t1
      _t2
      (Syntax.ctor Constructor.jω
        (Syntax.ctor Constructor.refl
          v1
          (Syntax.const Constant.kindU)
          (Syntax.const Constant.kindU))
        u2
        (Syntax.const Constant.kindU))
      => app m0 (parp u2) (parp v1)
    | Syntax.ctor Constructor.promote
      (Syntax.ctor Constructor.refl
        (Syntax.ctor (Constructor.proj _)
          v1
          (Syntax.const Constant.kindU)
          (Syntax.const Constant.kindU))
        (Syntax.const Constant.kindU)
        (Syntax.const Constant.kindU))
      (Syntax.const Constant.kindU)
      (Syntax.const Constant.kindU)
      => refl (parp v1)
    | Syntax.bind k t1 t2 => Syntax.bind k (parp t1) (parp t2)
    | Syntax.ctor k t1 t2 t3 => Syntax.ctor k (parp t1) (parp t2) (parp t3)

  inductive ParRed : Term -> Term -> Prop where
  | beta {x m t1 t2 t3 t1' t2' t3'} :
    x ∉ fv t2' ->
    ParRed t1 t1' ->
    ParRed t2 t2' ->
    ParRed t3 t3' ->
    ParRed (app m (lam m t1 t2) t3) ([x := t3']{0 |-> x}t2')
  | fst :
    ParRed t1 t1' ->
    ParRed t2 t2' ->
    ParRed t3 t3' ->
    ParRed (proj 1 (pair t1 t2 t3)) t1'
  | snd :
    ParRed t1 t1' ->
    ParRed t2 t2' ->
    ParRed t3 t3' ->
    ParRed (proj 2 (pair t1 t2 t3)) t2'
  | eqind :
    ParRed t1 t1' ->
    ParRed t2 t2' ->
    ParRed t3 t3' ->
    ParRed t4 t4' ->
    ParRed t5 t5' ->
    ParRed t6 t6' ->
    ParRed (J t1 t2 t3 t4 (refl t5) t6) (t6' @0 t5')
  | promote :
    ParRed t t' ->
    ParRed (promote (refl (proj i t))) (refl t')
  | phi :
    ParRed t1 t1' ->
    ParRed t2 t2' ->
    ParRed t3 t3' ->
    ParRed (proj 1 (phi t1 t2 t3)) t1'
  | bind :
    ParRed t1 t1' ->
    ParRed t2 t2' ->
    ParRed (Syntax.bind k t1 t2) (Syntax.bind k t1' t2')
  | ctor :
    ParRed t1 t1' ->
    ParRed t2 t2' ->
    ParRed t3 t3' ->
    ParRed (Syntax.ctor k t1 t2 t3) (Syntax.ctor k t1' t2' t3')
  | const : ParRed (const K) (const K)
  | free : ParRed (free x) (free x)
  | bound : ParRed (bound i) (bound i)

  notation:150 t1:150 " -p> " t2:150 => ParRed t1 t2

  inductive ParRedStar : Term -> Term -> Prop where
  | refl : ParRedStar t t
  | step : t1 -p> t2 -> ParRedStar t2 t3 -> ParRedStar t1 t3

  notation:150 t1:150 " -p>* " t2:150 => ParRedStar t1 t2

  namespace ParRed

    lemma refl_bind_open (x : Name)
      : x ∉ fv t -> ParRed t t -> ParRed ({i |-> x}t) ({i |-> x}t)
    := by {
      sorry
    }

    lemma refl_n : ParRed t t := by {
      induction t
      case bound => apply ParRed.bound
      case free => apply ParRed.free
      case const => apply ParRed.const
      case bind b t1 t2 ih1 ih2 => {
        apply ParRed.bind; apply ih1; apply ih2
      }
      case ctor k t1 t2 t3 ih1 ih2 ih3 => {
        apply ParRed.ctor; apply ih1; apply ih2; apply ih3
      }
    }

    lemma refl : t -p> t := refl_n

  end ParRed

  lemma red_implies_par_step : t -β> s -> t -p> s := by {
    intro step
    induction step
    case beta m t1 t2 t3 x xn => {
      apply @ParRed.beta x m t1 t2 t3 t1 t2 t3 xn; apply ParRed.refl
      apply ParRed.refl
      apply ParRed.refl
    }
    case fst => {
      apply ParRed.fst
      apply ParRed.refl; apply ParRed.refl; apply ParRed.refl
    }
    case snd => {
      apply ParRed.snd
      apply ParRed.refl; apply ParRed.refl; apply ParRed.refl
    }
    case eqind => {
      apply ParRed.eqind
      apply ParRed.refl; apply ParRed.refl; apply ParRed.refl
      apply ParRed.refl; apply ParRed.refl; apply ParRed.refl
    }
    case promote => {
      apply ParRed.promote; apply ParRed.refl
    }
    case phi => {
      apply ParRed.phi
      apply ParRed.refl; apply ParRed.refl; apply ParRed.refl
    }
    case bind1 t1 t1' k t2 _ ih => {
      apply ParRed.bind; exact ih; apply ParRed.refl
    }
    case bind2 t2 t2' k t1 _ ih => {
      apply ParRed.bind; apply ParRed.refl; exact ih
    }
    case ctor1 t1 t1' k t2 t3 _ ih => {
      apply ParRed.ctor; exact ih
      apply ParRed.refl; apply ParRed.refl
    }
    case ctor2 t2 t2' k t1 t3 _ ih => {
      apply ParRed.ctor; apply ParRed.refl
      exact ih; apply ParRed.refl
    }
    case ctor3 t3 t3' k t1 t2 _ ih => {
      apply ParRed.ctor; apply ParRed.refl
      apply ParRed.refl; exact ih
    }
  }

  lemma red_implies_par : t -β>* s -> t -p>* s := by {
    intro step
    induction step
    case refl => apply ParRedStar.refl
    case step t1 t2 t3 r1 _r2 ih => {
      have lem := red_implies_par_step r1
      apply ParRedStar.step lem ih
    }
  }

  lemma par_implies_red_step : t -p> s -> t -β>* s := by {
    sorry
    -- intro step
    -- induction step
    -- case beta t1 t1' t2 t2' t3 t3' m S h1 ih1 h2 ih2 h3 ih3 => {
    --   have r1 : app m (lam m t1 t2) t3 -β>* app m (lam m t1 t2') t3' := by {
    --     have xfresh := @Name.fresh_is_fresh (S ++ fv t2 ++ fv t2')
    --     generalize xdef : @Name.fresh (S ++ fv t2 ++ fv t2') = x at *
    --     simp at *; replace xfresh := demorgan3 xfresh
    --     casesm* _ ∧ _; case _ xn1 xn2 xn3 =>
    --     apply red_ctor
    --     apply red_bind2 x
    --     simp [*]
    --     apply h3 x xn1; apply ih3; apply RedStar.refl
    --   }
    --   have r2 := RedStar.step (@Red.beta _ m t1 t2' t3') RedStar.refl
    --   apply RedStar.trans r1 r2
    -- }
    -- case fst t1 t1' t2 t2' t3 t3' h1 h2 h3 ih1 ih2 ih3 => {
    --   have r1 : fst (pair t1 t2 t3) -β>* fst (pair t1' t2 t3) := by {
    --     sorry
    --   }
    --   have r2 := RedStar.step (@Red.fst _ t1' t2 t3) RedStar.refl
    --   apply RedStar.trans r1 r2
    -- }
    -- case snd => sorry
    -- case eqind => sorry
    -- case promote => sorry
    -- case phi => sorry
    -- case bind t1 t1' t2 t2' k S s1 ih1 s2 ih2 => {
    --   have xfresh := @Name.fresh_is_fresh (S ++ fv t2 ++ fv t2')
    --   generalize xdef : @Name.fresh (S ++ fv t2 ++ fv t2') = x at *
    --   simp at *; replace xfresh := demorgan3 xfresh
    --   casesm* _ ∧ _; case _ xn1 xn2 xn3 =>
    --   apply red_bind x
    --   apply s2
    --   simp [*]
    --   apply ih2 x xn1
    -- }
    -- case ctor t1 t1' t2 t2' t3 t3' k h1 h2 h3 ih1 ih2 ih3 => {
    --   apply red_ctor ih1 ih2 ih3
    -- }
    -- case const => apply RedStar.refl
    -- case free => apply RedStar.refl
    -- case bound i => apply RedStar.refl
  }

  lemma par_implies_red : t -p>* s -> t -β>* s := by {
    intro step
    induction step
    case refl => apply RedStar.refl
    case step t1 t2 t3 r1 _r2 ih => {
      have lem := par_implies_red_step r1
      apply RedStar.trans lem ih
    }
  }

  @[simp] lemma parp_kindu : parp kindu = kindu := by {
    unfold parp; unfold kindu; simp
  }

  -- lemma parp_open {n} (t : Term) : {_|-> x}parp t = parp ({_|-> x}t) := by {
  --   sorry
  -- }

  lemma par_subst :
    t -p> t' ->
    s -p> s' ->
    [x := t]s -p> [x := t']s'
  := by {
    sorry
    -- intro r1 r2
    -- have xfresh := @Name.fresh_is_fresh (S ++ fv s ++ fv s')
    -- generalize xdef : @Name.fresh (S ++ fv s ++ fv s') = x at *
    -- simp at xfresh; replace xfresh := demorgan3 xfresh
    -- casesm* _ ∧ _; case _ xn1 xn2 xn3 =>
    -- have r3 := r2 x xn1
    -- generalize zdef : {_|-> x}s = z at *
    -- generalize zpdef : {_|-> x}s' = z' at *
    -- induction r3 generalizing t t' s s'
    -- case beta t1 t1' t2 t2' t3 t3' m S' h1 h2 h3 ih1 ih2 ih3 => {
    --   replace zdef := open_to_close xn2 zdef; simp at zdef
    --   replace zpdef := open_to_close xn3 zpdef
    --   subst zdef; subst zpdef; simp
    --   rw [subst_hsubst_commute]
    --   apply ParRed.beta; apply ParRed.refl
    --   repeat sorry
    -- }
    -- case fst t1 t1' t2 t2' t3 t3' h1 h2 h3 ih1 ih2 ih3 => {
    --   replace zdef := open_to_close xn2 zdef; simp at zdef
    --   replace zpdef := open_to_close xn3 zpdef; simp at zpdef
    --   subst zdef; subst zpdef; simp
    --   sorry
    -- }
    -- case snd => sorry
    -- case eqind => sorry
    -- case promote => sorry
    -- case phi => sorry
    -- case bind => sorry
    -- case ctor => sorry
    -- case const => sorry
    -- case free => sorry
    -- case bound => sorry
  }

  lemma par_triangle : t -p> s -> s -p> (parp t) := by {
    sorry
    -- intro step
    -- induction step
    -- case beta t1 t1' t2 t2' t3 t3' m S h1 h2 h3 ih1 ih2 ih3 => {
    --   unfold app; unfold lam; unfold parp; unfold kindu; simp
    --   have lem : ∀ x ∉ S, {_|-> x}t2' -p> {_|-> x}(parp t2) := by {
    --     intro x xn; rw [parp_open]
    --     apply ih2 x xn
    --   }
    --   apply par_subst S ih3 lem
    -- }
    -- case fst t1 t1' t2 t2' t3 t3' h1 h2 h3 ih1 ih2 ih3 => exact ih1
    -- case snd t1 t1' t2 t2' t3 t3' h1 h2 h3 ih1 ih2 ih3 => exact ih2
    -- case eqind t1 t1' t2 t2' t3 t3' t4 t4' t5 t5' t6 t6'
    --   h1 h2 h3 h4 h5 h6 ih1 ih2 ih3 ih4 ih5 ih6 =>
    -- {
    --   apply ParRed.ctor; exact ih6; exact ih5
    --   apply ParRed.refl
    -- }
    -- case promote t t' h ih => {
    --   apply ParRed.ctor; exact ih
    --   apply ParRed.refl; apply ParRed.refl
    -- }
    -- case phi t1 t1' t2 t2' t3 t3' h1 h2 h3 ih1 ih2 ih3 => exact ih1
    -- case bind t1 t1' t2 t2' k S h1 h2 ih1 ih2 => {
    --   cases k <;> simp
    --   case lam m => {
    --     sorry
    --   }
    --   case pi m => sorry
    --   case inter => sorry
    -- }
    -- case ctor t1 t1' t2 t2' t3 t3' k h1 h2 h3 ih1 ih2 ih3 => {
    --   cases k
    --   case app => sorry
    --   case pair => {
    --     unfold parp; simp
    --     apply ParRed.ctor; apply ih1; apply ih2; apply ih3
    --   }
    --   case fst => {
    --     generalize H : (parp (Syntax.ctor Constructor.fst t1 t2 t3)) = t
    --     unfold parp at H
    --     split at H
    --     all_goals injections
    --     case _ t' u1 u2 u3 e1 e2 e3 e4 => {
    --       subst e2; subst e3; subst e4; simp at *
    --       cases h2; case _ =>
    --       cases h3; case _ =>
    --       simp at *
    --       unfold pair at ih1; unfold parp at ih1
    --       cases t1' <;> try cases ih1
    --       case ctor k v1 v2 v3 => {
    --         cases k <;> try cases h1
    --         case _ h1 h2 h3 => {
    --           cases ih1; case _ h4 h5 h6 =>
    --           simp; rw [<-H]; apply ParRed.fst
    --           apply h4; apply h5; apply h6
    --         }
    --       }
    --     }
    --     case _ => sorry
    --     case _ t' k u1 u2 u3 m1 m2 m3 m4 m5 h e1 e2 e3 e4 e5 => {
    --       subst e2; subst e3; subst e4; subst e5; simp at *
    --       rw [<-H]; apply ParRed.ctor; exact ih1; exact ih2; exact ih3
    --     }
    --   }
    --   case snd => sorry
    --   case eq => sorry
    --   case refl => sorry
    --   case eqind => sorry
    --   case j0 => sorry
    --   case jω => sorry
    --   case promote => sorry
    --   case delta => sorry
    --   case phi => sorry
    -- }
    -- case const => unfold parp; unfold const; simp; apply ParRed.refl
    -- case free => unfold parp; unfold free; simp; apply ParRed.refl
    -- case bound i => unfold parp; unfold free; simp; apply ParRed.refl
  }

  lemma par_diamond : t -p> t1 -> t -p> t2 -> ∃ k, t1 -p> k ∧ t2 -p> k := by {
    intro r1 r2
    exists (parp t)
    apply And.intro _ _
    apply par_triangle r1
    apply par_triangle r2
  }

  lemma par_strip : t -p> t1 -> t -p>* t2 -> ∃ z, t1 -p>* z ∧ t2 -p> z := by {
    intro r1 r2
    induction r2 generalizing t1
    case refl t' => {
      exists t1; apply And.intro _ _
      apply ParRedStar.refl; apply r1
    }
    case step u1 u2 u3 s1 _s2 ih => {
      have lem := par_triangle s1
      replace ih := ih lem
      have lem2 := par_triangle r1
      casesm* ∃ _, _, _ ∧ _; case _ z rr1 rr2 =>
      exists z; apply And.intro _ rr2
      apply ParRedStar.step lem2 rr1
    }
  }

  lemma par_confluence : t -p>* t1 -> t -p>* t2 -> ∃ z, t1 -p>* z ∧ t2 -p>* z := by {
    intro r1 r2
    induction r1 generalizing t2
    case refl t' => {
      exists t2; apply And.intro r2 _
      apply ParRedStar.refl
    }
    case step u1 u2 u3 s1 _s2 ih => {
      have lem1 := par_strip s1 r2
      casesm* ∃ _, _, _ ∧ _; case _ z1 rr1 rr2 =>
      replace ih := ih rr1
      casesm* ∃ _, _, _ ∧ _; case _ z2 rr3 rr4 =>
      exists z2; apply And.intro rr3
      apply ParRedStar.step rr2 rr4
    }
  }

  theorem confluence : t -β>* t1 -> t -β>* t2 -> ∃ z, t1 -β>* z ∧ t2 -β>* z := by {
    intro r1 r2
    have p1 := red_implies_par r1
    have p2 := red_implies_par r2
    have lem := par_confluence p1 p2
    casesm* ∃ _, _, _ ∧ _; case _ z p3 p4 =>
    have r3 := par_implies_red p3
    have r4 := par_implies_red p4
    exists z
  }

end Cedille
