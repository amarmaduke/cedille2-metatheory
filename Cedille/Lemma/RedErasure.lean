
import Common
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Inversion
import Cedille.Lemma.Red
import Cedille.Lemma.Substitution
import Cedille.Lemma.BetaConv

namespace Cedille

  lemma erase_betaconv_open_if
    : erase x ({_|-> y}t) =β= erase x ({_|-> y}t') ->
      erase x t =β= erase x t'
  := by sorry

  lemma erase_betaconv_open_only_if
    : erase x t =β= erase x t' ->
      erase x ({_|-> y}t) =β= erase x ({_|-> y}t')
  := by sorry

  lemma erase_subst_noop {v : Term n} (S : FvSet!)
    : (∀ x ∉ S, x ∉ fv (erase x ({_|-> x}t))) ->
      erase x ([_:= v]t) = erase x ({_|-> x}t)
  := by sorry

  lemma erase_pseobj_red : PseObj t -> t -β> t' -> ∀ x, erase x t =β= erase x t' := by {
    intro obj step
    induction obj generalizing t'
    case ax => cases step
    case var => cases step
    case bind k A B S hn p1 p2 ih1 ih2 => {
      cases k
      case' lam md => cases md
      case lam.erased => exfalso; apply hn (by simp)
      all_goals {
        cases step
        simp at *
        case bind1 A' step => {
          replace ih1 := ih1 step
          intro x; try apply BetaConv.refl
          try apply BetaConv.bind1 (ih1 x)
        }
        case bind2 B' S' step => {
          intro x; simp
          have yfresh := @Name.fresh_is_fresh (S ++ S' ++ fv B ++ fv B')
          generalize ydef : @Name.fresh (S ++ S' ++ fv B ++ fv B') = y at *
          simp at yfresh; have yn := demorgan4 yfresh
          casesm* _ ∧ _; case _ yn1 yn2 yn3 yn4 =>
          have yn' : y ∉ fv (erase x B) ++ fv (erase x B') := by {
            simp; intro h; cases h
            case _ h => apply yn3 (erase_fv x h)
            case _ h => apply yn4 (erase_fv x h)
          }
          replace ih2 := ih2 y yn1 (step y yn2) x
          replace ih2 := erase_betaconv_open_if ih2
          replace ih2 := BetaConv.open_if y ih2
          apply BetaConv.bind; apply BetaConv.refl; exact yn'; exact ih2
        }
      }
    }
    case lam A t S p1 p2 h ih1 ih2 => {
      cases step
      case bind1 A' step => simp; intro x; apply BetaConv.refl
      case bind2 t' S' step => {
        simp; intro x
        have yfresh := @Name.fresh_is_fresh (S ++ S' ++ fv t ++ fv t')
        generalize ydef : @Name.fresh (S ++ S' ++ fv t ++ fv t') = y at *
        simp at yfresh; have yn := demorgan4 yfresh
        casesm* _ ∧ _; case _ yn1 yn2 yn3 yn4 =>
          have yn' : y ∉ fv (erase x t) ++ fv (erase x t') := by {
            simp; intro h; cases h
            case _ h => apply yn3 (erase_fv x h)
            case _ h => apply yn4 (erase_fv x h)
          }
          replace ih2 := ih2 y yn1 (step y yn2) x
          replace ih2 := erase_betaconv_open_if ih2
          replace ih2 := BetaConv.open_if x ih2
          rw [erase_open_commute_same, erase_open_commute_same]
          exact ih2
      }
    }
    case pair t s T th sh Th e tih sih Tih => {
      cases step <;> simp at *
      case ctor1 t' step => apply tih step
      case ctor2 => intro x; apply BetaConv.refl
      case ctor3 => intro x; apply BetaConv.refl
    }
    case ctor k t1 t2 t3 ne h1 h2 h3 ih1 ih2 ih3 => {
      cases k <;> simp at *
      case app md => {
        cases step
        case beta t1' t2' => {
          cases md
          case free => {
            intro x; rw [erase_app_mf_unfolded, erase_lam_mf]
            constructor
            apply RedStar.step Red.beta RedStar.refl
            rw [subst_erase]
            apply RedStar.refl
          }
          case type => sorry
          case erased => {
            intro x
            cases h1 <;> simp at *
            case lam S' p1 p2 he =>
            rw [erase_subst_noop S' he]
            apply BetaConv.refl
          }
        }
        case ctor1 => sorry
        case ctor2 => sorry
        case ctor3 => sorry
      }
      case fst => {
        cases step <;> simp at *
        any_goals intro x; apply BetaConv.refl
        case ctor1 t1' step => apply ih1 step
      }
      case snd => {
        cases step <;> simp at *
        case snd t1 t3 => {
          intro x; cases h1
          case pair _ _ e _ => exact e x
          case ctor n _ _ _ => exfalso; apply n (by simp)
        }
        case ctor1 t1' step => intro x; apply ih1 step x
        case ctor2 => intro x; apply BetaConv.refl
        case ctor3 => intro x; apply BetaConv.refl
      }
      case eq => {
        cases step <;> simp at *
        case ctor1 t1' step => {
          intro x; replace ih1 := ih1 step x
          apply BetaConv.ctor ih1 BetaConv.refl BetaConv.refl
        }
        case ctor2 t2' step => {
          intro x; replace ih2 := ih2 step x
          apply BetaConv.ctor BetaConv.refl ih2 BetaConv.refl
        }
        case ctor3 t3' step => {
          intro x; replace ih3 := ih3 step x
          apply BetaConv.ctor BetaConv.refl BetaConv.refl ih3
        }
      }
      case refl => cases step <;> (simp at *; intro x; apply BetaConv.refl)
      case eqind => {
        cases step
        case eqind t1 t2 t3 t4 t5 t6 => {
          simp at *; intro x
          have r1 : lam mf kindu (bound 0) @ω erase x t6 -β> erase x t6 := by sorry
          have r2 := RedStar.step r1 RedStar.refl
          sorry
          -- intro x; apply RedStar.step _ RedStar.refl
          -- rw [erase_Jω, erase_refl, erase_app_m0]
          -- apply Red.beta
        }
        case ctor1 => intro x; apply BetaConv.refl
        case ctor2 => intro x; apply BetaConv.refl
        case ctor3 t3' step => intro x; apply ih3 step x
      }
      case j0 => cases step <;> (simp at *; intro x; apply BetaConv.refl)
      case jω => {
        cases step <;> simp at *
        case ctor1 t1' step => {
          intro x; replace ih1 := ih1 step x
          apply BetaConv.ctor ih1 BetaConv.refl BetaConv.refl
        }
        case ctor2 t2' step => {
          intro x; replace ih2 := ih2 step x
          apply BetaConv.ctor BetaConv.refl ih2 BetaConv.refl
        }
        case ctor3 => intro x; apply BetaConv.refl
      }
      case promote => {
        cases step <;> simp at *
        case promote => intro x; apply BetaConv.refl
        case ctor1 t1' step => intro x; apply ih1 step x
        case ctor2 => intro x; apply BetaConv.refl
        case ctor3 => intro x; apply BetaConv.refl
      }
      case delta => {
        cases step <;> simp at *
        case ctor1 t1' step => intro x; apply ih1 step x
        case ctor2 => intro x; apply BetaConv.refl
        case ctor3 => intro x; apply BetaConv.refl
      }
      case phi => {
        cases step <;> simp at *
        case ctor1 t1' step => intro x; apply ih1 step x
        case ctor2 => intro x; apply BetaConv.refl
        case ctor3 => intro x; apply BetaConv.refl
      }
    }
  }

  lemma erase_red_f_step :
    PseObj a ->
    (∀ x, erase x a =β= erase x b) ->
    a -β> a' ->
    (∀ x, erase x a' =β= erase x b)
  := by {
    intro j e step
    induction j generalizing a' b
    case ax => cases step
    case var => cases step
    case bind => sorry
    case lam => sorry
    case pair t s T th sh Th e2 tih sih Tih => {
      simp at *
      cases step <;> simp
      case ctor1 t' step => apply tih e step
      case ctor2 => simp [*]
      case ctor3 => simp [*]
    }
    case ctor k t1 t2 t3 ne h1 h2 h3 ih1 ih2 ih3 => {
      cases k <;> simp at *
      case app md => sorry
      case fst => {
        cases step <;> simp at *
        any_goals apply e
        case ctor1 t1' step => apply ih1 e step
      }
      case snd => {
        cases step <;> simp at *
        any_goals apply e
        case snd t1 t3 => {
          cases h1;
          case _ p1 p2 h p3 => {
            intro x
            apply BetaConv.trans (BetaConv.symm (h x)) (e x)
          }
          case _ ne _ _ _ => exfalso; apply ne (by simp)
        }
        case ctor1 t1' step => apply ih1 e step
      }
      case eq => {
        cases step <;> simp at *
        case ctor1 t1' step => {
          intro x
          have lem := erase_pseobj_red h1 step
          have lem2 := @BetaConv.ctor _ _ _ (erase x t2) _ (erase x t3) _ Constructor.eq
            (lem x) BetaConv.refl BetaConv.refl
          apply BetaConv.trans (BetaConv.symm lem2) (e x)
        }
        case ctor2 => sorry -- Like ctor1
        case ctor3 => sorry -- Like ctor2
      }
      case refl => cases step <;> simp at * <;> simp [*]
      case eqind => {
        cases step <;> simp at *
        case eqind t1 t2 t3 t4 t5 t6 => sorry
        case ctor1 => sorry
        case ctor2 => sorry
        case ctor3 => sorry
      }
      case j0 => cases step <;> simp at * <;> apply e
      case jω => {
        cases step <;> simp at *
        case ctor1 t1' step => sorry
        case ctor2 t2' step => sorry
        case ctor3 t3' step => apply e
      }
      case promote => cases step <;> simp at * <;> simp [*]
      case delta => cases step <;> simp at * <;> simp [*]
      case phi => cases step <;> simp at * <;> simp [*]
    }
  }

  lemma erase_red_f :
    PseObj a ->
    (∀ x, erase x a =β= erase x b) ->
    a -β>* a' ->
    (∀ x, erase x a' =β= erase x b)
  := by {
    sorry
    -- intro j e step
    -- induction step
    -- case refl => simp [*]
    -- case step t1 t2 _t3 r1 _r2 ih => {
    --   have lem1 := preservation_of_pseobj_step j r1
    --   have lem2 := erase_red_f_step j e r1
    --   apply ih lem1 lem2
    -- }
  }

  lemma erase_red_b_step :
    PseObj a ->
    (∀ x, erase x a' =β= erase x b) ->
    a -β> a' ->
    (∀ x, erase x a =β= erase x b)
  := by {
    intro h e step
    induction h generalizing b
    case ax => sorry
    case var => sorry
    case bind => sorry
    case lam => sorry
    case pair => sorry
    case ctor => sorry
  }

  lemma erase_red_b :
    PseObj a ->
    (∀ x, erase x a' =β= erase x b) ->
    a -β>* a' ->
    (∀ x, erase x a =β= erase x b)
  := by {
    sorry
    -- intro h e step
    -- induction step
    -- case refl t => simp [*]
    -- case step u v w r1 _r2 ih => {
    --   have h2 := preservation_of_pseobj_step h r1
    --   have lem := ih h2 e
    --   apply erase_red_b_step h lem r1
    -- }
  }
  -- lemma erase_free_red :
  --   ((x : Name) -> x ∉ fv t -> x ∉ (fv ∘ erase x) ({_|-> x}t)) ->
  --   (∃ x, {_|-> x}t -β>* {_|-> x}t') ->
  --   (x : Name) -> x ∉ fv t' -> x ∉ (fv ∘ erase x) ({_|-> x}t')
  -- := sorry

  -- lemma red_erasure_step_lam_mf :
  --   erase t1 = lam mf kindu (erase t2) ->
  --   t1 -β> z1 ->
  --   ∃ z2, t2 -β>* z2 ∧ erase z1 = lam mf kindu (erase z2)
  -- := sorry

  -- lemma red_erasure_step_lam_mt {n} {t1 t2 z1 : Term n} {t2' : Term (n + 1)} :
  --   erase t1 = lam mt (erase t2) (erase t2') ->
  --   t1 -β> z1 ->
  --   ∃ z2 z2', t2 -β>* z2 ∧ t2' -β>* z2' ∧ erase z1 = lam mt (erase z2) (erase z2')
  -- := λ h step => @Nat.rec
  --   (λ n =>
  --     ∀ m (t1 t2 z1 : Term m) (t2' : Term (m + 1)),
  --     size t1 ≤ n ->
  --     erase t1 = lam mt (erase t2) (erase t2') ->
  --     t1 -β> z1 ->
  --     ∃ z2 z2', t2 -β>* z2 ∧ t2' -β>* z2' ∧ erase z1 = lam mt (erase z2) (erase z2'))
  --   sorry
  --   (by {
  --     intros n ih m t1 t2 z1 t2' h e step
  --     cases t1 <;> simp at * <;> simp
  --     case const => cases step
  --     case bind k u1 u2 => {
  --       cases k <;> simp at *
  --       case lam m =>
  --       cases m <;> simp at *
  --       case erased => {
  --         generalize xdef : Name.fresh (fv u2) = x at *
  --         cases step <;> simp at * <;> simp
  --         case bind1 u1' step => {
  --           exists t2; apply And.intro RedStar.refl _
  --           exists t2'; apply And.intro RedStar.refl _
  --           simp [*]
  --         }
  --         case bind2 u2' S step => {
  --           have step : u2 -β> u2' := sorry
  --           sorry
  --         }
  --       }
  --       case type => {
  --         sorry
  --       }
  --     }
  --     case ctor => {
  --       sorry
  --     }
  --   })
  --   (size t1)
  --   n
  --   t1
  --   t2
  --   z1
  --   t2'
  --   (by simp)
  --   h
  --   step

  -- lemma red_erasure_step2 :
  --   Γ1 ⊢ t1 : A1 ->
  --   Γ2 ⊢ t2 : A2 ->
  --   erase t1 = erase t2 ->
  --   t1 -β> z1 ->
  --   ∃ z2, t2 -β>* z2 ∧ erase z1 = erase z2
  -- := λ j1 j2 h step => @Nat.rec
  --   (λ n =>
  --     ∀ Γ1 t1 A1 Γ2 t2 A2 z1,
  --     size t2 ≤ n ->
  --     Γ1 ⊢ t1 : A1 ->
  --     Γ2 ⊢ t2 : A2 ->
  --     erase t1 = erase t2 ->
  --     t1 -β> z1 ->
  --     ∃ z2, t2 -β>* z2 ∧ erase z1 = erase z2)
  --   sorry
  --   (by {
  --     intros n ih Γ1 t1 A1 Γ2 t2 A2 z1 h j1 j2 e step
  --     cases t2 <;> simp at * <;> simp
  --     case bound i => apply ih Γ1 t1 A1 Γ2 (bound i) A2 z1 (by simp) j1 j2 e step
  --     case free x => apply ih Γ1 t1 A1 Γ2 (free x) A2 z1 (by simp) j1 j2 e step
  --     case const k => apply ih Γ1 t1 A1 Γ2 (const k) A2 z1 (by simp) j1 j2 e step
  --     case bind k1 u1 u2 => {
  --       cases k1
  --       case lam m => {
  --         cases m <;> simp at * <;> simp
  --         case free => {
  --           sorry
  --           -- have lem := red_erasure_step_lam_mf e step
  --           -- casesm* ∃ _, _, _ ∧ _; case _ w step2 e2 =>
  --           -- exists lam mf u1 w; apply And.intro _ _
  --           -- apply red_lam RedStar.refl step2
  --           -- simp [*]
  --         }
  --         case type => {
  --           sorry
  --           -- have lem := red_erasure_step_lam_mt e step
  --           -- casesm* ∃ _, _, _ ∧ _; case _ w1 w2 wstep1 wstep2 e2 =>
  --           -- exists lam mt w1 w2; apply And.intro _ _
  --           -- apply red_lam wstep1 wstep2
  --           -- simp [*]
  --         }
  --         case erased => {
  --           cases j2; case _ K B S g1 g2 g3 =>
  --           have fresh := @Name.fresh_is_fresh (S ++ fv u2)
  --           generalize xdef : Name.fresh (S ++ fv u2) = x at *
  --           have xn1 := FvSet.not_mem_left fresh
  --           have xn2 := FvSet.not_mem_right fresh
  --           replace g3 := g3 x xn1
  --           have g2r := erase_free_rename (g2 rfl)
  --           have su2 : size ({_|-> x}u2) ≤ n := by {
  --             have lem1 := Nat.le_of_succ_le_succ h
  --             have lem2 := nat_add_le lem1
  --             casesm* _ ∧ _; case _ l r =>
  --             simp [*]
  --           }
  --           have e2 : erase t1 = erase ({_|-> x}u2) := by
  --             rw [g2r x (Name.fresh (fv u2)) xn2 Name.fresh_is_fresh]; simp [*]
  --           have lem := ih Γ1 t1 A1 (Γ2 ++ [x:u1]) ({_|-> x}u2) ({_|-> x}B) z1 su2 j1 g3 e2 step
  --           casesm* ∃ _, _, _ ∧ _; case _ u2' ustep ue =>
  --           have ustep2 := red_open_forced ustep
  --           cases ustep2; case _ z zh =>
  --           cases zh; case _ ze zn =>
  --           subst ze
  --           exists (lam m0 u1 z); apply And.intro _ _
  --           apply red_lam RedStar.refl ustep; simp
  --           have yfresh := @Name.fresh_is_fresh (fv z)
  --           generalize ydef : Name.fresh (fv z) = y at *
  --           have g2r2 := erase_free_rename (erase_free_red (g2 rfl) (Exists.intro x ustep))
  --           have fv1 : fv z ⊆ fv u2 := fv_open_shrink zn (red_fv ustep)
  --           have xn3 := contra (@subset_mem x (fv z) (fv u2) fv1) xn2
  --           have e3 := g2r2 x y xn3 yfresh; simp at e3
  --           rw [<-e3, ue]
  --         }
  --       }
  --       case pi m => {
  --         sorry
  --       }
  --       case inter => {
  --         sorry
  --       }
  --     }
  --     case ctor k u1 u2 u3 => {
  --       cases k <;> simp at * <;> simp
  --       case app => sorry
  --       case pair => sorry
  --       case fst => sorry
  --       case snd => sorry
  --       case eq => sorry
  --       case refl => sorry
  --       case eqind => sorry
  --       case promote => sorry
  --       case delta => sorry
  --       case phi => {
  --         cases j2; case _ A B g1 g2 g3 g4 g5 =>
  --         cases g1; case _ A' g eq =>
  --         have lem := ih Γ1 t1 A1 Γ2 u1 A' z1 sorry j1 g e step
  --         casesm* ∃ _, _, _ ∧ _; case _ w step e =>
  --         exists (phi w u2 u3); apply And.intro _ _
  --         apply red_phi step RedStar.refl RedStar.refl
  --         simp [*]
  --       }
  --     }
  --   })
  --   (size t2)
  --   Γ1
  --   t1
  --   A1
  --   Γ2
  --   t2
  --   A2
  --   z1
  --   (by simp)
  --   j1
  --   j2
  --   h
  --   step

  -- lemma red_erasure_step {n} {t1 t2 z1 : Term n} :
  --   erase t1 = erase t2 ->
  --   t1 -β> z1 ->
  --   ∃ z2, t2 -β>* z2 ∧ erase z1 = erase z2
  -- := λ h step => @Nat.rec
  --   (λ n =>
  --     ∀ m (t1 t2 z1 : Term m),
  --     size t1 ≤ n ->
  --     erase t1 = erase t2 ->
  --     t1 -β> z1 ->
  --     ∃ z2, t2 -β>* z2 ∧ erase z1 = erase z2)
  --   sorry
  --   (by {
  --     intros n ih m t1 t2 z1 h e step
  --     cases t1
  --     case bound => cases step
  --     case free => cases step
  --     case const => cases step
  --     case bind k u1 u2 => {
  --       cases k
  --       case lam m => {
  --         cases m; simp at *
  --         case free => {
  --           cases step <;> simp
  --           case bind1 v1 step => {
  --             exists t2; simp [*]
  --             apply RedStar.refl
  --           }
  --           case bind2 v2 S step => {
  --             have fresh := @Name.fresh_is_fresh S
  --             generalize xdef : Name.fresh S = x at *
  --             replace step := step x fresh
  --             have lem := ih m ({_|-> x}u2) (t2) ({_|-> x}v2) sorry sorry step

  --           }
  --         }
  --         case type => {

  --         }
  --         case erased => {

  --         }
  --       }
  --       case pi m => {

  --       }
  --       case inter => {

  --       }
  --     }
  --     case ctor => {

  --     }
  --   })
  --   (size t1)
  --   n
  --   t1
  --   t2
  --   z1
  --   (by simp)
  --   h
  --   step

  -- lemma typed_fv_erase :
  --   Γ ⊢ a : A ->
  --   x ∉ fv (erase x a)
  -- := sorry

  -- lemma typed_fv_erase_bind (S : FvSet!) :
  --   (∀ x, x ∉ S -> (Γ ++ [x:C]) ⊢ {_|-> x}a >: A) ->
  --   x ∉ fv (erase x a)
  -- := sorry

  -- lemma red_erase_step :
  --   Γ ⊢ a : A ->
  --   a -β> b ->
  --   (∀ x, erase x a =β= erase x b)
  -- := λ j step => @Infer.rec
  --   (λ Γ a A j => ∀ b,
  --     a -β> b ->
  --     (∀ x, erase x a =β= erase x b))
  --   (λ Γ a A j => ∀ b,
  --     a -β> b ->
  --     (∀ x, erase x a =β= erase x b))
  --   (λ Γ a A j => ∀ b,
  --     a -β> b ->
  --     (∀ x, erase x a =β= erase x b))
  --   (λ Γ wf => True)
  --   (by {
  --     intro Γ wf _ b step
  --     cases step
  --   })
  --   (by {
  --     intro Γ y C wf yn _ b step
  --     cases step
  --   })
  --   sorry
  --   sorry
  --   sorry
  --   (by {
  --     simp at *
  --     intro Γ C B S j1 j2 ih1 ih2 b step
  --     cases step
  --     case bind1 C' step => {
  --       simp at *
  --       replace ih1 := ih1 C' step
  --       intro x
  --       apply BetaConv.bind x (ih1 x) _ BetaConv.refl
  --       intro h; simp at h
  --       apply typed_fv_erase_bind S j2 h
  --     }
  --     case bind2 B' S' step => {
  --       sorry
  --     }
  --   })
  --   sorry
  --   (by {
  --     simp
  --     intro Γ t A B j ih b r x
  --     cases r <;> simp
  --     case fst => apply BetaConv.refl
  --     case phi t2 t3 => apply BetaConv.refl
  --     case ctor1 => sorry
  --     case ctor2 => sorry
  --     case ctor3 => sorry
  --   })
  --   (by {
  --     simp
  --     intro Γ t C B j ih b r
  --     cases r
  --     case snd t1 t3 => {
  --       cases j; case _ _ j _ =>
  --       cases j; case _ S2 _ e _ _ _ =>
  --       simp [*]
  --     }
  --     case ctor1 => sorry
  --     case ctor2 => sorry
  --     case ctor3 => sorry
  --   })
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   (by {
  --     simp at *
  --     intro Γ f A B a e j1 j2 j3 j4 ih1 ih2 ih3 b r x
  --     cases r <;> simp
  --     case ctor1 a' r => apply ih2 a' r x
  --     case ctor2 f' r => apply BetaConv.refl
  --     case ctor3 => apply BetaConv.refl
  --   })
  --   (by {
  --     simp
  --     intro Γ e j ih b r x
  --     cases r <;> simp
  --     case ctor1 e' r => apply ih e' r x
  --     case ctor2 _ r => cases r
  --     case ctor3 _ r => cases r
  --   })
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   Γ
  --   a
  --   A
  --   j
  --   b
  --   step

  -- lemma red_erase :
  --   Γ ⊢ a : A ->
  --   a -β>* b ->
  --   (∀ x, erase x a =β= erase x b)
  -- := by {
  --   intro j step x
  --   induction step generalizing Γ A
  --   case refl => apply BetaConv.refl
  --   case step t1 t2 t3 step _ ih => {
  --     have jt2 := preservation_of_infer_step j step
  --     cases jt2; case _ U j2 =>
  --     replace ih := ih j2
  --     have lem := red_erase_step j step
  --     apply BetaConv.trans (lem x) ih
  --   }
  -- }

  -- theorem conv_by_erase :
  --   Γ1 ⊢ a : A ->
  --   Γ2 ⊢ b : B ->
  --   a === b ->
  --   (∀ x, erase x a =β= erase x b)
  -- := by {
  --   intro ja jb cv x
  --   cases cv; case _ u v r1 e r2 =>
  --   have lem1 := red_erase ja r1
  --   have lem2 := red_erase jb r2
  --   have e2 := BetaConv.trans (lem1 x) (e x)
  --   apply BetaConv.trans e2
  --   apply BetaConv.symm (lem2 x)
  -- }

  -- lemma red_erasure (S : FvSet!) :
  --   Γ1 ⊢ t1 : A1 ->
  --   Γ2 ⊢ t2 : A2 ->
  --   ((x : Name) -> x ∉ S -> erase x t1 = erase x t2) ->
  --   t1 -β>* z1 ->
  --   ∃ z2, t2 -β>* z2 ∧ (∀ x, x ∉ S -> erase x z1 = erase x z2)
  -- := by sorry
  -- -- := by {
  -- --   intro h step
  -- --   induction step generalizing t2
  -- --   case refl t' => {
  -- --     exists t2; simp [*]
  -- --     apply RedStar.refl
  -- --   }
  -- --   case step u1 u2 u3 s1 _s2 e => {
  -- --     have lem := red_erasure_step h s1
  -- --     casesm* ∃ _, _, _ ∧ _; case _ w step e2 =>
  -- --     have lem := @e w e2
  -- --     casesm* ∃ _, _, _ ∧ _; case _ w' step' e3 =>
  -- --     exists w'; simp [*]
  -- --     apply RedStar.trans step step'
  -- --   }
  -- -- }

end Cedille
