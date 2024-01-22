
import Common
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Inversion
import Cedille.Lemma.Red
import Cedille.Lemma.Substitution
import Cedille.Lemma.BetaConv
import Cedille.Lemma.Rule

namespace Cedille

  -- lemma erase_betaconv_open_if
  --   : erase x ({_|-> y}t) =β= erase x ({_|-> y}t') ->
  --     erase x t =β= erase x t'
  -- := by sorry

  -- lemma erase_betaconv_open_only_if
  --   : erase x t =β= erase x t' ->
  --     erase x ({_|-> y}t) =β= erase x ({_|-> y}t')
  -- := by sorry

  -- lemma erase_subst_noop {v : Term n} (S : FvSet!)
  --   : (∀ x ∉ S, x ∉ fv (erase x ({_|-> x}t))) ->
  --     erase x ([_:= v]t) = erase x ({_|-> x}t)
  -- := by sorry

  lemma erase_open_conv
    : erase ({i |-> x}t) =β= erase ({i |-> x}t') -> erase t =β= erase t'
  := by sorry

  lemma erase_pseobj_red : PseObj t -> t -β> t' -> erase t =β= erase t' := by {
    intro obj step
    induction obj generalizing t'
    case ax => cases step
    case var => cases step
    case bind k A B hn p1 S p2 ih1 ih2 => {
      cases k
      case' lam md => cases md
      case lam.erased => exfalso; apply hn (by simp)
      all_goals {
        cases step
        simp at *
        case bind1 A' step => {
          replace ih1 := ih1 step
          try apply BetaConv.refl
          try apply BetaConv.bind ih1 BetaConv.refl
        }
        case bind2 B' step => {
          have yfresh := @Name.fresh_is_fresh S
          generalize ydef : @Name.fresh S = y at *
          replace step : {0 |-> y}B -β> {0 |-> y}B' := by sorry
          replace ih2 := ih2 y yfresh step
          simp; try apply BetaConv.refl
          try apply BetaConv.bind BetaConv.refl (erase_open_conv ih2)
        }
      }
    }
    case lam A t p1 S1 p2 S2 p3 ih1 ih2 => {
      cases step
      case bind1 A' step => simp; apply BetaConv.refl
      case bind2 t' step => {
        have yfresh := @Name.fresh_is_fresh S1
        generalize ydef : @Name.fresh S1 = y at *
        replace step : {0 |-> y}t -β> {0 |-> y}t' := by sorry
        replace ih2 := ih2 y yfresh step
        simp; exact (erase_open_conv ih2)
      }
    }
    case pair t s T th sh Th e tih sih Tih => {
      cases step <;> simp at *
      case ctor1 t' step => apply tih step
      case ctor2 => apply BetaConv.refl
      case ctor3 => apply BetaConv.refl
    }
    case ctor k t1 t2 t3 ne h1 h2 h3 ih1 ih2 ih3 => {
      cases k <;> simp at *
      case app md => {
        cases step
        case beta t1' t2' => {
          cases md
          case free => {
            sorry
            -- rw [erase_app_mf_unfolded, erase_lam_mf]
            -- constructor
            -- apply RedStar.step Red.beta RedStar.refl
            -- rw [subst_erase]
            -- apply RedStar.refl
          }
          case type => sorry
          case erased => {
            cases h1 <;> simp at *
            case lam p1 p2 he =>
            sorry
          }
        }
        case ctor1 => sorry
        case ctor2 => sorry
        case ctor3 => sorry
      }
      case proj i => {
        cases i
        case first => {
          cases step <;> simp at *
          any_goals apply BetaConv.refl
          case ctor1 t1' step => apply ih1 step
        }
        case second => {
          cases step <;> simp at *
          case snd t1 t3 => {
            cases h1
            case pair _ _ e _ => exact e
            case ctor n _ _ _ => exfalso; apply n (by simp)
          }
          case ctor1 t1' step => apply ih1 step
          case ctor2 => apply BetaConv.refl
          case ctor3 => apply BetaConv.refl
        }
      }
      case eq => {
        cases step <;> simp at *
        case ctor1 t1' step => {
          replace ih1 := ih1 step
          apply BetaConv.ctor ih1 BetaConv.refl BetaConv.refl
        }
        case ctor2 t2' step => {
          replace ih2 := ih2 step
          apply BetaConv.ctor BetaConv.refl ih2 BetaConv.refl
        }
        case ctor3 t3' step => {
          replace ih3 := ih3 step
          apply BetaConv.ctor BetaConv.refl BetaConv.refl ih3
        }
      }
      case refl => cases step <;> (simp at *; apply BetaConv.refl)
      case subst => sorry
      case promote => {
        cases step <;> simp at *
        case promote => apply BetaConv.refl
        case ctor1 t1' step => apply ih1 step
        case ctor2 => apply BetaConv.refl
        case ctor3 => apply BetaConv.refl
      }
      case delta => {
        cases step <;> simp at *
        case ctor1 t1' step => apply ih1 step
        case ctor2 => apply BetaConv.refl
        case ctor3 => apply BetaConv.refl
      }
      case phi => {
        cases step <;> simp at *
        case ctor1 t1' step => apply ih1 step
        case ctor2 => apply BetaConv.refl
        case ctor3 => apply BetaConv.refl
      }
    }
  }

  lemma erase_red_f_step :
    PseObj a ->
    erase a =β= erase b ->
    a -β> a' ->
    erase a' =β= erase b
  := by {
    intro p c1 step
    have lem := erase_pseobj_red p step
    apply BetaConv.trans (BetaConv.symm lem) c1
    -- intro j e step
    -- induction j generalizing a' b
    -- case ax => cases step
    -- case var => cases step
    -- case bind k A B S hn p1 p2 ih1 ih2 => {
    --   cases k <;> simp at *
    --   case lam md => sorry
    --   case pi md => sorry
    --   case inter => {
    --     cases step <;> simp at *
    --     case bind1 A' step => {
    --       sorry
    --     }
    --     case bind2 B' step => {
    --       sorry
    --     }
    --   }
    -- }
    -- case lam => sorry
    -- case pair t s T th sh Th e2 tih sih Tih => {
    --   simp at *
    --   cases step <;> simp
    --   case ctor1 t' step => apply tih e step
    --   case ctor2 => simp [*]
    --   case ctor3 => simp [*]
    -- }
    -- case ctor k t1 t2 t3 ne h1 h2 h3 ih1 ih2 ih3 => {
    --   cases k <;> simp at *
    --   case app md => sorry
    --   case proj i => {
    --     sorry
    --     -- cases step <;> simp at *
    --     -- any_goals apply e
    --     -- case ctor1 t1' step => apply ih1 e step
    --   }
    --   -- case snd => {
    --   --   cases step <;> simp at *
    --   --   any_goals apply e
    --   --   case snd t1 t3 => {
    --   --     cases h1;
    --   --     case _ p1 p2 h p3 => {
    --   --       intro x
    --   --       apply BetaConv.trans (BetaConv.symm (h x)) (e x)
    --   --     }
    --   --     case _ ne _ _ _ => exfalso; apply ne (by simp)
    --   --   }
    --   --   case ctor1 t1' step => apply ih1 e step
    --   -- }
    --   case eq => {
    --     cases step <;> simp at *
    --     case ctor1 t1' step => {
    --       sorry
    --       -- intro x
    --       -- have lem := erase_pseobj_red h1 step
    --       -- have lem2 := @BetaConv.ctor _ _ _ (erase x t2) _ (erase x t3) _ Constructor.eq
    --       --   (lem x) BetaConv.refl BetaConv.refl
    --       -- apply BetaConv.trans (BetaConv.symm lem2) (e x)
    --     }
    --     case ctor2 => sorry -- Like ctor1
    --     case ctor3 => sorry -- Like ctor2
    --   }
    --   case refl => cases step <;> simp at * <;> simp [*]
    --   case eqind => {
    --     cases step <;> simp at *
    --     case eqind t1 t2 t3 t4 t5 t6 => sorry
    --     case ctor1 => sorry
    --     case ctor2 => sorry
    --     case ctor3 => sorry
    --   }
    --   case j0 => cases step <;> simp at * <;> apply e
    --   case jω => {
    --     cases step <;> simp at *
    --     case ctor1 t1' step => sorry
    --     case ctor2 t2' step => sorry
    --     case ctor3 t3' step => apply e
    --   }
    --   case promote => cases step <;> simp at * <;> simp [*]
    --   case delta => cases step <;> simp at * <;> simp [*]
    --   case phi => cases step <;> simp at * <;> simp [*]
    -- }
  }

  theorem preservation_of_pseobj_step : PseObj t -> t -β> t' -> PseObj t' := by {
    intro p step
    induction p generalizing t'
    case ax => cases step
    case var => cases step
    case bind => sorry
    case lam A t p1 p2 e ih1 ih2 => {
      cases step <;> simp
      case bind1 A' step => sorry
      case bind2 B' step => sorry
    }
    case pair t s T p1 p2 p3 e ih1 ih2 ih3 => {
      cases step <;> simp
      case ctor1 t' step => {
        replace ih1 := ih1 step; constructor
        simp [*]; simp [*]; simp [*]
        apply erase_red_f_step p1 e step
      }
      case ctor2 s' step => {
        replace ih2 := ih2 step; constructor
        simp [*]; simp [*]; simp [*]
        have lem := erase_red_f_step p2 (BetaConv.symm e) step
        apply BetaConv.symm lem
      }
      case ctor3 T' step => {
        replace ih3 := ih3 step; constructor
        all_goals simp [*]
      }
    }
    case ctor k t1 t2 t3 hn p1 p2 p3 ih1 ih2 ih3 => {
      cases k
      case app => sorry
      case pair => exfalso; apply hn (by simp)
      case proj i => {
        cases i
        case first => {
          cases step <;> simp at *
          case fst t2 t3 => cases p1 <;> simp [*]
          case ctor1 => sorry
          case ctor2 => sorry
          case ctor3 => sorry
        }
        case second => sorry
      }
      case eq => sorry
      case refl => sorry
      case subst => sorry
      case promote => sorry
      case delta => sorry
      case phi => sorry
    }
  }

  lemma erase_red_f :
    PseObj a ->
    erase a =β= erase b ->
    a -β>* a' ->
    erase a' =β= erase b
  := by {
    intro j e step
    induction step
    case refl => simp [*]
    case step t1 t2 _t3 r1 _r2 ih => {
      replace e := erase_red_f_step j e r1
      have p := preservation_of_pseobj_step j r1
      apply ih p e
    }
  }

  theorem preservation_of_pseobj : PseObj t -> t -β>* t' -> PseObj t' := by {
    intro p step
    induction step
    case refl => simp [*]
    case step t1 t2 _t3 r1 _r2 ih => {
      apply ih (preservation_of_pseobj_step p r1)
    }
  }

  lemma erase_red_b_step :
    PseObj a ->
    erase a' =β= erase b ->
    a -β> a' ->
    erase a =β= erase b
  := by {
    intro h e step
    have lem := erase_pseobj_red h step
    apply BetaConv.trans lem e
  }

  lemma erase_red_b :
    PseObj a ->
    erase a' =β= erase b ->
    a -β>* a' ->
    erase a =β= erase b
  := by {
    intro h e step
    induction step
    case refl t => simp [*]
    case step u v w r1 _r2 ih => {
      have h2 := preservation_of_pseobj_step h r1
      have lem := ih h2 e
      apply erase_red_b_step h lem r1
    }
  }

  lemma infer_implies_pseobj_type : Γ ⊢ t : A -> PseObj A := by sorry
  -- := λ j => @Infer.rec
  --   (λ Γ t A _ => PseObj A)
  --   (λ Γ t A _ => PseObj A)
  --   (λ Γ t A _ => PseObj A)
  --   (λ _ _ => True)
  --   (by { intro Γ _ _; constructor })
  --   (by {
  --     intro Γ x A wf xn _
  --     have lem := get_ctx_wf wf xn
  --     casesm* ∃ _, _; case _ Δ K lem =>
  --     cases lem; case _ D lem r =>
  --     apply infer_implies_pseobj lem
  --   })
  --   (by {
  --     intros _ _ m
  --     cases m <;> (simp; intros; constructor)
  --   })
  --   (by {
  --     intros Γ A m K t B j1 j2 e ih1 ih2; simp at *
  --     cases j1; case _ _ j1 _ =>
  --     have lem := infer_implies_pseobj j1
  --     sorry
  --     --apply PseObj.bind _ lem ih2; simp
  --   })
  --   (by {
  --     intros x B Γ f m A a xn j1 j2 ih1 ih2
  --     cases ih1; case _ S hn _ ih2 =>
  --     sorry
  --   })
  --   (by { intros; constructor })
  --   (by {
  --     intros Γ T A B t s j1 j2 j3 e ih1 ih2 ih3; simp at *
  --     cases ih1; case _ S' _ p1 p2 =>
  --     apply PseObj.bind _ p1 p2; simp
  --   })
  --   (by {
  --     intros Γ t A B j ih
  --     cases ih; case _ _ _ ih _ => exact ih
  --   })
  --   (by {
  --     intros x B Γ t A xn j ih
  --     cases ih; case _ _ _ ih =>
  --     replace ih := ih x xn
  --     sorry
  --   })
  --   (by { intros; constructor })
  --   (by {
  --     intros Γ t A j ih
  --     have lem := infer_implies_pseobj j
  --     apply PseObj.ctor _ ih lem lem; simp
  --   })
  --   (by {
  --     intros Γ A P x y r w j1 j2 j3 j4 j5 j6 ih1 ih2 ih3 ih4 ih5 ih6
  --     constructor; simp; constructor; simp; constructor; simp
  --     cases j2; case _ _ _ j2 _ _ => apply infer_implies_pseobj j2
  --     cases j3; case _ _ _ j3 _ _ => apply infer_implies_pseobj j3
  --     constructor; cases j4; case _ _ _ j4 _ _ => apply infer_implies_pseobj j4
  --     constructor; cases j5; case _ _ _ j5 _ _ => apply infer_implies_pseobj j5
  --     constructor
  --   })
  --   (by {
  --     intros Γ e T i a j b A B j1 j2 j3 ih1 ih2 ih3
  --     cases j2; case _ _ j2 _ =>
  --     cases j3; case _ _ _ j3 _ _ =>
  --     have lem1 := infer_implies_pseobj j2
  --     have lem2 := infer_implies_pseobj j3
  --     apply PseObj.ctor _ ih2 lem1 lem2; simp
  --   })
  --   (by {
  --     intros A B Γ f a e h j1 j2 j3 fve ih1 ih2 ih3
  --     cases ih1; case _ S _ _ ih1 =>
  --     have lem : ∀ x ∉ fv B, PseObj ({0 |-> x}B) := by {
  --       have yfresh := @Name.fresh_is_fresh (fv (inter A B))
  --       generalize ydef : @Name.fresh (fv (inter A B)) = y at *
  --       simp at *; replace ih1 := ih1 y yfresh
  --       intro x xn; unfold inter at ih1
  --       rw [Syntax.open_vanish] at ih1
  --       cases ih1; case _ S' _ _ ih1 => {
  --         rw [Syntax.open_vanish h.2] at ih1
  --         apply ih1 x xn
  --       }
  --       apply h.1
  --     }
  --     apply PseObj.bind _ ih2 lem; simp
  --   })
  --   (by {
  --     intros; constructor; simp; constructor
  --     simp; intro x; constructor
  --   })
  --   (by {
  --     intros Γ t A B j step ih
  --     apply preservation_of_pseobj ih step
  --   })
  --   (by {
  --     intros Γ t A B K j1 j2 cv ih1 ih2
  --     cases j2; case _ _ j2 _ =>
  --     apply infer_implies_pseobj j2
  --   })
  --   (by simp)
  --   (by simp)
  --   Γ
  --   t
  --   A
  --   j


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
