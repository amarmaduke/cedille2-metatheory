
import Cedille.Def
import Cedille.Lemma.Conv

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

  lemma infer_implies_cinfer : Γ ⊢ t : A -> Γ ⊢ t >: A := by {
    intro j; apply ConInfer.infer j RedStar.refl
  }

  lemma infer_implies_sane : Γ ⊢ t : A -> Sane t := λ j => @Infer.rec
    (λ Γ t A _ => Sane t)
    (λ Γ t A _ => Sane t)
    (λ Γ t A _ => Sane t)
    (λ Γ _ => True)
    (by intros; constructor)
    (by intros; constructor)
    (by {
      intro Γ A m K B S j1 j2 ih1 ih2
      simp at *
      constructor; exact ih1; exact ih2
    })
    (by {
      intros Γ A m K t B S j1 j2 j3 ih1 ih2
      simp at *
      constructor; exact ih1; exact ih2; exact j3
    })
    (by {
      intro Γ f m A B a S j1 j2 ih1 ih2
      constructor; exact ih1; exact ih2
    })
    (by {
      intro Γ A B S j1 j2 ih1 ih2
      simp at *
      constructor; exact ih1; exact ih2
    })
    (by {
      intro Γ T A B t s S j1 j2 j3 j4 ih1 ih2 ih3
      constructor; exact ih1; exact ih2; exact ih3; exact j4
    })
    (by {
      intro Γ t A B j ih
      constructor; exact ih
    })
    (by {
      intro Γ t A B j ih
      constructor; exact ih
    })
    (by {
      intro Γ A a b j1 j2 j3 ih1 ih2 ih3
      constructor; exact ih1; exact ih2; exact ih3
    })
    (by {
      intro Γ t A j ih
      constructor; exact ih
    })
    (by {
      intro Γ A P x y r w j1 j2 j3 j4 j5 j6 ih1 ih2 ih3 ih4 ih5 ih6
      constructor; exact ih1; exact ih2; exact ih3
      exact ih4; exact ih5; exact ih6
    })
    (by {
      intro Γ e T a b A B j1 j2 j3 j4 ih1 ih2 ih3
      constructor; exact ih1
    })
    (by {
      intro Γ f A B a e j1 j2 j3 j4 ih1 ih2 ih3
      constructor; exact ih2; exact ih1; exact ih3
    })
    (by {
      intro Γ e j ih
      constructor; exact ih
    })
    (by intros; simp [*])
    (by intros; simp [*])
    (by simp)
    (by simp)
    Γ
    t
    A
    j

  lemma chck_type_red : Γ ⊢ t =: A -> A -β>* B -> Γ ⊢ t =: B := by {
    intro j step
    cases j; case _ C K j1 cv j2 =>
    sorry
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

  lemma rename_ctx_invariant {Γ : Map! Term n} :
    (y : Name) ->
    x ∉ Map.fv Γ ->
    [x |-> y]Γ = Γ
  := sorry

  lemma rename_term_invariant {A : Term n} :
    (y : Name) ->
    x ∉ fv A ->
    {_|-> y}{_<-| x}A = A
  := sorry

  lemma rename_infer (x : Name) :
    Γ ⊢ t : A ->
    y ∉ (Map.fv Γ ++ fv t ++ fv A) ->
    [x |-> y]Γ ⊢ {_|-> y}{_<-| x}t : {_|-> y}{_<-| x}A
  := sorry

end Cedille
