
import Cedille.Def
import Cedille.Lemma.Refold

namespace Cedille

  lemma infer_implies_wf : Γ ⊢ t : A -> ⊢ Γ := λ j => @Infer.rec
    (λ Γ t A _ => ⊢ Γ)
    (λ Γ t A _ => ⊢ Γ)
    (λ Γ t A _ => ⊢ Γ)
    (λ Γ _ => ⊢ Γ)
    (by simp)
    (by simp)
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by intros; simp [*])
    (by apply Wf.nil)
    (by {
      intro x Γ A K j1 j2 j3 _ _
      apply Wf.append j1 j2 j3
    })
    Γ
    t
    A
    j

  lemma get_ctx_wf : ⊢ Γ -> (x, A) ∈ Γ -> ∃ Γ K, Γ ⊢ A >: const K := λ wf inn => @Wf.rec
    (λ _ _ _ _ => True)
    (λ _ _ _ _ => True)
    (λ _ _ _ _ => True)
    (λ Γ _ => ∀ x A, (x, A) ∈ Γ -> ∃ Γ K, Γ ⊢ A >: const K)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by { intro x A inn; cases inn })
    (by {
      intro x Γ A K _ _ j ih _ x' A' inn
      simp at inn; cases inn
      case _ h => apply ih x' A' h
      case _ h => {
        cases h
        case _ => exists Γ; exists K
        case _ h => exfalso; cases h
      }
    })
    Γ
    wf
    x
    A
    inn

  lemma infer_implies_cinfer : Γ ⊢ t : A -> Γ ⊢ t >: A := by {
    intro j; apply ConInfer.infer j RedStar.refl
  }

  lemma infer_implies_pseobj : Γ ⊢ t : A -> PseObj t := by sorry
  -- := λ j => @Infer.rec
  --   (λ Γ t A _ => PseObj t)
  --   (λ Γ t A _ => PseObj t)
  --   (λ Γ t A _ => PseObj t)
  --   (λ _ _ => True)
  --   (by { intro Γ _ _; constructor })
  --   (by {
  --     intro _ _ _ _ _ _
  --     constructor
  --   })
  --   (by {
  --     intro Γ A m K B _j1 j2 ih1 ih2; simp at *
  --     constructor; simp; apply ih1
  --     apply ih2
  --   })
  --   (by {
  --     intro Γ A m K t B j1 j2 j3 ih1 ih2; simp at *
  --     cases m
  --     case free => {
  --       apply PseObj.bind; simp
  --       apply ih1; intro x xn
  --       have yfresh := @Name.fresh_is_fresh (fv t ++ fv B)
  --       generalize ydef : @Name.fresh (fv t ++ fv B) = y at *
  --       simp at *; replace ih2 := ih2 y yfresh
  --       sorry
  --     }
  --     case type => {
  --       apply PseObj.bind; simp
  --       apply ih1; sorry
  --     }
  --     case erased => {
  --       apply PseObj.lam; apply ih1
  --       repeat sorry
  --     }
  --   })
  --   (by {
  --     intro x B Γ f m A a _xn _j1 _j2 ih1 ih2
  --     constructor; simp; apply ih1; apply ih2
  --     constructor
  --   })
  --   (by {
  --     intro Γ A B _j1 j2 ih1 ih2; simp at *
  --     constructor; simp; apply ih1
  --     apply ih2
  --   })
  --   (by {
  --     intro Γ T A B t s _j1 _j2 j3 e p1 p2 p3
  --     simp at *; have xfresh := @Name.fresh_is_fresh (fv B)
  --     generalize _xdef : @Name.fresh (fv B) = x at *
  --     replace p3 := p3 x xfresh
  --     apply PseObj.pair p2 p3 p1 e
  --   })
  --   (by {
  --     intros; constructor; simp; simp [*]
  --     constructor; constructor
  --   })
  --   (by {
  --     intros; constructor; simp; simp [*]
  --     constructor; constructor
  --   })
  --   (by {
  --     intros; constructor <;> simp [*]
  --   })
  --   (by {
  --     intros; constructor; simp; simp [*]
  --     constructor; constructor
  --   })
  --   (by {
  --     intros; constructor; simp
  --     constructor; simp; simp [*]; simp [*]; constructor
  --     constructor; simp; simp [*]; simp [*]; constructor
  --     constructor; simp; simp [*]; simp [*]; constructor
  --   })
  --   (by {
  --     intros; constructor; simp; simp [*]
  --     constructor; constructor
  --   })
  --   (by {
  --     intros; constructor; simp
  --     all_goals simp [*]
  --   })
  --   (by {
  --     intros; constructor; simp; simp [*]
  --     constructor; constructor
  --   })
  --   (by simp)
  --   (by {
  --     intro Γ t A B K _j1 _j2 _cv ih1 _ih2
  --     simp [*]
  --   })
  --   (by simp)
  --   (by simp)
  --   Γ
  --   t
  --   A
  --   j

    lemma cinfer_implies_pseobj : Γ ⊢ t >: A -> PseObj t := by {
      intro j; cases j; case _ _ j _ =>
      apply infer_implies_pseobj j
    }

  -- lemma infer_implies_check : Γ ⊢ t : A -> Γ ⊢ t =: A := by {
  --   intro j; apply Check.check j _ _
  -- }

  -- lemma cinfer_implies_check : Γ ⊢ t >: A -> Γ ⊢ t =: A := by {
  --   intro j; cases j
  --   case _ A' j step =>
  --   apply Check.check j _
  --   apply Conv.red_b Conv.refl step
  -- }

  -- lemma check_from_cinfer :
  --   Γ ⊢ t >: A ->
  --   A =β= B ->
  --   Γ ⊢ t =: B
  -- := by {
  --   intros j e
  --   cases j
  --   case _ C j step =>
  --   have lem := Conv.red_b e step
  --   apply Check.check j lem
  -- }

  -- lemma rename_ctx_invariant {Γ : Map! Term} :
  --   (y : Name) ->
  --   x ∉ Map.fv Γ ->
  --   [x |-> y]Γ = Γ
  -- := sorry

  -- lemma rename_term_invariant {A : Term n} :
  --   (y : Name) ->
  --   x ∉ fv A ->
  --   {_|-> y}{_<-| x}A = A
  -- := sorry

  -- lemma rename_infer (x : Name) :
  --   Γ ⊢ t : A ->
  --   y ∉ (Map.fv Γ ++ fv t ++ fv A) ->
  --   [x |-> y]Γ ⊢ {_|-> y}{_<-| x}t : {_|-> y}{_<-| x}A
  -- := sorry

end Cedille
