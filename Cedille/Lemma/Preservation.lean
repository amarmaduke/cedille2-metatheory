
import Common
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Inversion
import Cedille.Lemma.Red
import Cedille.Lemma.Conv
import Cedille.Lemma.Rule

namespace Cedille

  inductive CtxRed : (Map! (Term 0)) -> (Map! (Term 0)) -> Prop where
  | head (x:Name) A : CtxRed Γ Δ -> CtxRed (Γ ++ [x:A]) (Δ ++ [x:A])
  | tail (x:Name) Γ : A -β> B -> CtxRed (Γ ++ [x:A]) (Γ ++ [x:B])

  -- lemma preservation_of_proof :
  --   Γ ⊢ t : A ->
  --   (∀ t', t -β> t' -> ∃ A', A -β>* A' ∧ Γ ⊢ t' : A')
  --   ∧ (∀ Γ', CtxRed Γ Γ' -> ∃ A', A -β>* A' ∧ Γ' ⊢ t : A')
  -- := λ j => @Infer.rec
  --   (λ Γ t A j =>
  --     (∀ t', t -β> t' -> ∃ A', A -β>* A' ∧ Γ ⊢ t' : A')
  --     ∧ (∀ Γ', CtxRed Γ Γ' -> ∃ A', A -β>* A' ∧ Γ' ⊢ t : A'))
  --   (λ Γ t A j =>
  --     (∀ t', t -β> t' -> ∃ A', A -β>* A' ∧ Γ ⊢ t' : A')
  --     ∧ (∀ Γ', CtxRed Γ Γ' -> ∃ A', A -β>* A' ∧ Γ' ⊢ t : A'))
  --   (λ Γ t A j =>
  --     (∀ t', t -β> t' -> ∃ A', A -β>* A' ∧ Γ ⊢ t' : A')
  --     ∧ (∀ Γ', CtxRed Γ Γ' -> ∃ A', A -β>* A' ∧ Γ' ⊢ t : A'))
  --   (λ Γ wf => ∀ Γ', CtxRed Γ Γ' -> ⊢ Γ')
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   (by {
  --     intro Γ t A B K j1 j2 j3 ih1 ih2
  --     sorry
  --   })
  --   sorry
  --   sorry
  --   Γ
  --   t
  --   A
  --   j



  -- lemma preservation_of_cinfr :
  --   Γ ⊢ A >: typeu ->
  --   (∀ B, A -β> B -> Γ ⊢ B >: typeu) ∧ (∀ Δ, CtxRed Γ Δ -> Δ ⊢ A >: typeu)
  -- := λ j => @ConInfer.rec
  --   (λ Γ A K j => K = typeu -> (∀ B, A -β> B -> Γ ⊢ B : K) ∧ (∀ Δ, CtxRed Γ Δ -> Δ ⊢ A : K))
  --   (λ Γ A K j => K = typeu -> (∀ B, A -β> B -> Γ ⊢ B >: K) ∧ (∀ Δ, CtxRed Γ Δ -> Δ ⊢ A >: K))
  --   (λ Γ A K j => (∀ B, A -β> B -> Γ ⊢ B =: K) ∧ (∀ Δ, CtxRed Γ Δ -> Δ ⊢ A =: K))
  --   (λ Γ j => ∀ Δ, CtxRed Γ Δ -> ⊢ Δ)
  --   (by {
  --     intro Γ wf ih eq
  --     sorry -- EASY
  --   })
  --   (by {
  --     intro Γ x A wf xin ih eq
  --     apply And.intro _ _
  --     intro B step; cases step
  --     intro Δ step; replace ih := ih Δ step
  --     sorry -- EASY
  --   })
  --   (by {
  --     intro Γ A m K C S j1 j2 ih1 ih2 eq; simp at *
  --     sorry
  --   })
  --   (by {
  --     intro Γ A m K t B S j1 j2 j3 ih1 ih2 eq
  --     sorry
  --   })
  --   (by {
  --     intro Γ f m A B a S j1 j2 ih1 ih2
  --     sorry
  --   })
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   (by {
  --     intro Γ A a b j1 j2 j3 ih1 ih2 ih3 _
  --     apply And.intro _ _
  --     intro B step
  --     cases step
  --     case ctor1 => sorry
  --     case ctor2 => sorry
  --     case ctor3 _ b' step => {
  --       simp at *
  --       sorry
  --     }
  --     sorry
  --   })
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   (by {
  --     intro Γ t A B j1 j2 ih
  --     sorry
  --   })
  --   (by {
  --     intro Γ t A B K j1 j2 j3 ih1 ih2
  --     apply And.intro _ _
  --     intro t' step
  --     sorry
  --     sorry
  --   })
  --   sorry
  --   sorry
  --   Γ
  --   A
  --   typeu
  --   j
  --   (by simp)

  lemma preservation :
    Γ ⊢ t >: A ->
    (∀ s, t -β> s -> Γ ⊢ s >: A)
    ∧ (∀ B, A -β>* B -> Γ ⊢ t >: B)
    ∧ (∀ Δ, CtxRed Γ Δ -> Δ ⊢ t >: A)
  := λ j => @ConInfer.rec
    (λ Γ t A j => (∀ s, t -β> s -> Γ ⊢ s >: A)
      ∧ (∀ B, A -β>* B -> Γ ⊢ t >: B)
      ∧ (∀ Δ, CtxRed Γ Δ -> Δ ⊢ t >: A))
    (λ Γ t A j => (∀ s, t -β> s -> Γ ⊢ s >: A)
      ∧ (∀ B, A -β>* B -> Γ ⊢ t >: B)
      ∧ (∀ Δ, CtxRed Γ Δ -> Δ ⊢ t >: A))
    (λ Γ t A j => (∀ s, t -β> s -> Γ ⊢ s =: A)
      ∧ (∀ B, A -β>* B -> Γ ⊢ t =: B)
      ∧ (∀ Δ, CtxRed Γ Δ -> Δ ⊢ t =: A))
    (λ Γ j => ∀ Δ, CtxRed Γ Δ -> ⊢ Δ)
    (by {
      sorry
    })
    (by {
      sorry
    })
    (by {
      sorry
    })
    (by {
      sorry
    })
    (by {
      intro Γ f m A B a S j1 j2 ih1 ih2
      sorry
    })
    sorry
    (by {
      intro Γ T A B t s S j1 j2 j3 j4 ih1 ih2 ih3
      casesm* _ ∧ _; case _ ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 ih9 =>
      apply And.intro _ _
      {
        intro q step
        cases step <;> simp
        case ctor1 t' step => {
          constructor; constructor; exact S
          exact j1; apply ih2 t' step
          have lem : [_:= t]B -β>* [_:= t']B := sorry
          repeat sorry
        }
        case ctor2 => sorry
        case ctor3 => sorry
      }
      apply And.intro _ _
      {
        intro Q step
        sorry
        -- cases step <;> simp
        -- case bind1 A' step => {
        --   constructor; constructor; exact S
        --   exact j1; exact j2; exact j3; exact j4
        --   apply red_bind1 (RedStar.step step RedStar.refl)
        -- }
        -- case bind2 B' S' step => {
        --   constructor; constructor; exact (S ++ S')
        --   exact j1; exact j2; exact j3; exact j4
        --   have xfresh := @Name.fresh_is_fresh (S ++ S' ++ fv B ++ fv B')
        --   generalize xdef : @Name.fresh (S ++ S' ++ fv B ++ fv B') = x at *
        --   simp at *
        --   replace xfresh := demorgan4 xfresh
        --   casesm* _ ∧ _; case _ xn1 xn2 xn3 xn4 =>
        --   have xn5 : x ∉ (fv B ++ fv B') := by simp [*]
        --   have step2 := RedStar.step (step x xn2) RedStar.refl
        --   apply red_bind2 x xn5 step2
        -- }
      }
      intro Δ step
      constructor; constructor; exact S
      apply ih5 Δ step; apply ih7 Δ step; apply ih9 Δ step; exact j4
      apply RedStar.refl
    })
    sorry
    sorry
    (by {
      intro Γ A a b j1 j2 j3 ih1 ih2 ih3
      casesm* _ ∧ _; case _ ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 ih9 =>
      apply And.intro _ _
      {
        intro s step
        cases step <;> simp
        case ctor1 A' step => {
          have steps := RedStar.step step RedStar.refl
          constructor; constructor
          apply ih1 A' step; apply ih6 A' steps; apply ih8 A' steps
          apply RedStar.refl
        }
        case ctor2 a' step => {
          constructor; constructor
          apply j1; apply ih2 a' step; apply j3
          apply RedStar.refl
        }
        case ctor3 b' step => {
          constructor; constructor
          apply j1; apply j2; apply ih3 b' step
          apply RedStar.refl
        }
      }
      apply And.intro _ _
      {
        intro B' step
        cases step
        case refl => {
          constructor; constructor
          exact j1; exact j2; exact j3; exact RedStar.refl
        }
        case step _ step _ => cases step
      }
      intro Δ step
      constructor; constructor
      apply ih5 Δ step; apply ih7 Δ step; apply ih9 Δ step
      apply RedStar.refl
    })
    sorry
    sorry
    sorry
    sorry
    sorry
    (by {
      intro Γ t A B j1 j2 ih
      sorry
    })
    (by {
      intro Γ t A B K j1 j2 j3 ih1 ih2
      casesm* _ ∧ _; case _ ih1 ih2 ih3 ih4 ih5 ih6 => {
        apply And.intro _ _
        {
          intro s step
          replace ih1 := ih1 s step
          cases ih1; case _ T j step2 =>
          constructor; exact j; exact j2
          apply Conv.red_b j3 step2
        }
        apply And.intro _ _
        {
          sorry
          -- intro B' step
          -- replace ih2 := ih2 B' step
          -- constructor; exact j1; exact ih2
          -- have lem : A === B' := by {
          --   have lem1 := Conv.symm j3
          --   cases j2; case _ j2 _ =>
          --   have h := infer_implies_sane j2
          --   have lem2 := Conv.red_f h lem1 (RedStar.step step RedStar.refl)
          --   apply Conv.symm lem2
          -- }
          -- exact lem
        }
        intro Δ step
        replace ih6 := ih6 Δ step
        replace ih4 := ih4 Δ step
        cases ih4; case _ T j step2 =>
        constructor; exact j; exact ih6
        apply Conv.red_b j3 step2
      }
    })
    sorry
    sorry
    Γ
    t
    A
    j


  -- lemma preservation_of_infer_step_subst :
  --   Γ ⊢ lam m u1 u2 >: pi m A B ->
  --   Γ ⊢ u3 =: A ->
  --   ∃ B, Γ ⊢ [_:= u3]u2 : B
  -- := by sorry

  -- lemma preservation_step_of_infer_ctx (S : FvSet!) :
  --   ((x : Name) -> x ∉ S → (Γ ++ [x:A]) ⊢ {_|-> x}t : {_|-> x}B) ->
  --   A -β> A' ->
  --   ∃ B, ((x : Name) -> x ∉ S → (Γ ++ [x:A']) ⊢ {_|-> x}t : {_|-> x}B)
  -- := by sorry

  -- lemma preservation_step_of_cinfer_ctx (S : FvSet!) :
  --   ((x : Name) -> x ∉ S → (Γ ++ [x:A]) ⊢ {_|-> x}t >: {_|-> x}B) ->
  --   A -β> A' ->
  --   ((x : Name) -> x ∉ S → (Γ ++ [x:A']) ⊢ {_|-> x}t >: {_|-> x}B)
  -- := by sorry

  -- lemma preservation_step_of_cinfer_ctx_const (S : FvSet!) :
  --   ((x : Name) -> x ∉ S → (Γ ++ [x:A]) ⊢ {_|-> x}t >: const K) ->
  --   A -β> A' ->
  --   ((x : Name) -> x ∉ S → (Γ ++ [x:A']) ⊢ {_|-> x}t >: const K)
  -- := by sorry

  -- lemma rule_cinfer_red : Γ ⊢ t >: A -> A -β>* B -> Γ ⊢ t >: B := by {
  --   intro j step
  --   cases j; case _ D j step2 =>
  --   replace step := RedStar.trans step2 step
  --   apply ConInfer.infer j step
  -- }

  -- lemma rule_inv_inter1_kind : ¬ (Γ ⊢ t >: inter (const K) B) := λ j => @Nat.rec
  --   (λ s => ∀ Γ t K B,
  --     size t ≤ s ->
  --     ¬ Γ ⊢ t >: inter (const K) B)
  --   sorry
  --   (by {
  --     intro s ih Γ t K B sh j
  --     cases t <;> simp at *
  --     case bound => apply ih _ (bound _) _ _ (by simp) j
  --     case free => apply ih _ (free _) _ _ (by simp) j
  --     case const => apply ih _ (const _) _ _ (by simp) j
  --     case bind b u1 u2 => {
  --       cases b <;> simp at *
  --       case lam m => {
  --         sorry
  --       }
  --       case pi m => sorry
  --       case inter => sorry
  --     }
  --     case ctor => sorry
  --   })
  --   (size t)
  --   Γ
  --   t
  --   K
  --   B
  --   (by simp)
  --   j

  -- lemma preservation_step_of_cinfer_const :
  --   Γ ⊢ t >: const K ->
  --   t -β> s ->
  --   Γ ⊢ s >: const K
  -- := λ j step => @ConInfer.rec
  --   (λ Γ t A j => ∀ s K, A -β>* const K -> t -β> s -> Γ ⊢ s : A)
  --   (λ Γ t A j => ∀ s K, A = const K -> t -β> s -> Γ ⊢ s >: A)
  --   (λ Γ t A j => ∀ s K, A = const K -> t -β> s -> Γ ⊢ s =: A)
  --   (λ Γ wf => True)
  --   (by {
  --     intro Γ wf _ s K e step
  --     cases step
  --   })
  --   (by {
  --     intro Γ x A wf xn _ s K e step
  --     cases step
  --   })
  --   (by {
  --     intro Γ A m K B S j1 j2 ih1 ih2 s K' e step; simp at *
  --     cases step <;> simp at *
  --     case bind1 A' step => {
  --       cases m <;> simp at *
  --       case free => {
  --         have lem1 := ih1 A' Constant.typeU rfl step
  --         have lem2 := preservation_step_of_cinfer_ctx_const S j2 step
  --         apply @Infer.pi _ _ mf Constant.typeU _ _ lem1 lem2
  --       }
  --       case erased => {
  --         have lem1 := ih1 A' K rfl step
  --         have lem2 := preservation_step_of_cinfer_ctx_const S j2 step
  --         apply @Infer.pi _ _ m0 K _ _ lem1 lem2
  --       }
  --       case type => {
  --         have lem1 := ih1 A' K rfl step
  --         have lem2 := preservation_step_of_cinfer_ctx_const S j2 step
  --         apply @Infer.pi _ _ mt K _ _ lem1 lem2
  --       }
  --     }
  --     case bind2 B' S' step => {
  --       cases m <;> simp at *
  --       case free => {
  --         have lem2 : ∀ x, x ∉ (S ++ S') -> (Γ ++ [x:A]) ⊢ {_|-> x}B' >: typeu := by {
  --           intro x xn; simp at xn
  --           replace xn := demorgan xn
  --           cases xn; case _ xn1 xn2 =>
  --           apply ih2 x xn1 ({_|-> x}B') Constant.typeU rfl _
  --           apply step x xn2
  --         }
  --         apply @Infer.pi _ _ mf Constant.typeU _ (S ++ S') j1 lem2
  --       }
  --       case erased => {
  --         have lem2 : ∀ x, x ∉ (S ++ S') -> (Γ ++ [x:A]) ⊢ {_|-> x}B' >: typeu := by {
  --           intro x xn; simp at xn
  --           replace xn := demorgan xn
  --           cases xn; case _ xn1 xn2 =>
  --           apply ih2 x xn1 ({_|-> x}B') Constant.typeU rfl _
  --           apply step x xn2
  --         }
  --         apply @Infer.pi _ _ m0 K _ (S ++ S') j1 lem2
  --       }
  --       case type => {
  --         have lem2 : ∀ x, x ∉ (S ++ S') -> (Γ ++ [x:A]) ⊢ {_|-> x}B' >: kindu := by {
  --           intro x xn; simp at xn
  --           replace xn := demorgan xn
  --           cases xn; case _ xn1 xn2 =>
  --           apply ih2 x xn1 ({_|-> x}B') Constant.kindU rfl _
  --           apply step x xn2
  --         }
  --         apply @Infer.pi _ _ mt K _ (S ++ S') j1 lem2
  --       }
  --     }
  --   })
  --   sorry
  --   sorry
  --   sorry
  --   (sorry)
  --   (by {
  --     intro Γ t A B j ih s K e step
  --     sorry
  --   })
  --   sorry
  --   (by {
  --     intro Γ A a b j1 j2 j3 ih1 ih2 ih3 s K e step
  --     cases step <;> simp at *
  --     case ctor1 => sorry
  --     case ctor2 a' step => {
  --       sorry
  --     }
  --     case ctor3 => sorry
  --   })
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   (by {
  --     intro Γ t A B j step ih s K e step'
  --     subst e
  --     have lem := ih s K step step'
  --     apply ConInfer.infer lem step
  --   })
  --   (by {
  --     intro Γ t A B K' j1 j2 conv ih1 ih2 s K e step
  --     subst e;
  --     cases conv; case _ A' K'' S s1 er s2 =>
  --     cases s2
  --     case refl => {
  --       clear ih2
  --       sorry
  --     }
  --     case step _ step _ => cases step
  --   })
  --   (by simp)
  --   (by simp)
  --   Γ
  --   t
  --   (const K)
  --   j
  --   s
  --   K
  --   rfl
  --   step


  -- lemma preservation_step_of_cinfer_pi_domain :
  --   Γ ⊢ t >: Mode.pi_domain m K ->
  --   t -β> s ->
  --   Γ ⊢ s >: Mode.pi_domain m K
  -- := λ j step => @Nat.rec
  --   (λ si => ∀ Γ t m K s,
  --     size t ≤ si ->
  --     Γ ⊢ t >: Mode.pi_domain m K ->
  --     t -β> s ->
  --     Γ ⊢ s >: Mode.pi_domain m K)
  --   sorry
  --   (by {
  --     intro si ih Γ t m K s sh j step
  --     cases t <;> simp at *
  --     case bound => cases step
  --     case free => cases step
  --     case const => cases step
  --     case bind b u1 u2 => {
  --       have s1 : size u1 ≤ si := by linarith
  --       have s2 : size u2 ≤ si := by linarith
  --       cases b <;> simp at *
  --       case lam m' => {
  --         cases j; case _ D j step2 =>
  --         cases j; case _ K2 B2 S2 j1 j2 j3 =>
  --         exfalso; apply red_inv_pi_not_pi_domain step2
  --       }
  --       case pi m' => {
  --         cases j; case _ D j step2 =>
  --         cases j; case _ K2 S2 j1 j2 =>
  --         have e := red_force_mode_pi_codomain step2; rw [e]
  --         cases step <;> simp
  --         case bind1 u1' step => {
  --           cases m' <;> simp at *
  --           case free => {
  --             have lem := @ih Γ u1 mf Constant.typeU u1' s1 j1 step; simp at lem
  --             apply ConInfer.infer _ _; exact typeu
  --             apply @Infer.pi _ _ mf Constant.typeU _ S2 lem
  --             simp; apply preservation_step_of_cinfer_ctx_const S2 j2 step
  --             apply RedStar.refl
  --           }
  --           case erased => sorry
  --           case type => sorry
  --         }
  --         case bind2 => sorry
  --       }
  --       case inter => {
  --         cases j; case _ D j step2 =>
  --         cases j; case _ S2 j1 j2 =>
  --         have e := red_force_typeu step2; rw [e]
  --         cases step <;> simp
  --         case bind1 u1' step => {
  --           have lem := @ih Γ u1 mf K u1' s1 j1 step; simp at lem
  --           sorry
  --         }
  --         case bind2 => sorry
  --       }
  --     }
  --     case ctor c u1 u2 u3 => {
  --       have s1 : size u1 ≤ si := by linarith
  --       have s2 : size u2 ≤ si := by linarith
  --       have s3 : size u3 ≤ si := by linarith
  --       cases c <;> simp at *
  --       case app m => sorry
  --       case pair => {
  --         cases j; case _ D j step2 =>
  --         cases j; case _ A B j1 j2 j3 j4 =>
  --         exfalso; apply red_inv_inter_not_pi_domain step2
  --       }
  --       case fst => {
  --         cases j; case _ D j step2 =>
  --         cases j; case _ B j =>
  --         have step2 : inter D B -β>* inter (Mode.pi_domain m K) B := by {
  --           apply red_inter' step2 (λ _ _ => RedStar.refl); exact []
  --         }
  --         replace j := rule_cinfer_red j step2
  --         cases m <;> simp at *
  --         case free => exfalso; apply rule_inv_inter1_kind j
  --         case erased => exfalso; apply rule_inv_inter1_kind j
  --         case type => exfalso; apply rule_inv_inter1_kind j
  --       }
  --       case snd => sorry
  --       case eq => sorry
  --       case refl => sorry
  --       case eqind => sorry
  --       case j0 => sorry
  --       case jω => sorry
  --       case promote => sorry
  --       case delta => sorry
  --       case phi => sorry
  --     }
  --   })
  --   (size t)
  --   Γ
  --   t
  --   m
  --   K
  --   s
  --   (by simp)
  --   j
  --   step


  -- lemma preservation_of_infer_step4 : Γ ⊢ t : A -> t -β> s -> Γ ⊢ s : A := by {
  --   intro j step
  --   induction step generalizing Γ A
  --   case beta m u1 u2 u3 => {
  --     cases j; case _ A B S j1 j2 =>
  --     sorry
  --   }
  --   case fst u1 u2 u3 => {
  --     cases j; case _ B j =>
  --     cases j; case _ T j step =>
  --     sorry
  --   }
  --   case snd => sorry
  --   case eqind => sorry
  --   case promote => sorry
  --   case phi => sorry
  --   case bind1 => sorry
  --   case bind2 => sorry
  --   case ctor1 => sorry
  --   case ctor2 => sorry
  --   case ctor3 => sorry
  -- }

  -- lemma preservation_of_infer_step : Γ ⊢ t : A -> t -β> s -> ∃ B, Γ ⊢ s : B := by {
  --   intro tproof step
  --   induction step generalizing Γ A
  --   case beta m u1 u2 u3 => {
  --     cases tproof; case _ A B S j1 j2 =>
  --     apply preservation_of_infer_step_subst j1 j2
  --   }
  --   case fst u1 u2 u3 => {
  --     cases tproof; case _ B j =>
  --     cases j; case _ P j step =>
  --     cases j; case _ A2 B2 j1 j2 j3 j4 =>
  --     cases j1; case _ A3 j5 j6 =>
  --     sorry
  --   }
  --   case snd u1 u2 u3 => {
  --     cases tproof; case _ A1 B1 j =>
  --     cases j; case _ P j1 s1 =>
  --     cases j1; case _ A2 B2 j1 j2 j3 j4 =>
  --     cases j3; case _ A3 j5 c1 =>
  --     sorry
  --   }
  --   case eqind u1 u2 u3 u4 u5 u6 => {
  --     cases tproof
  --     case eqind j1 j2 j3 j4 j5 j6 => {
  --       cases j5; case _ D j5 c1 =>
  --       cases j5; case _ A j =>
  --       sorry
  --     }
  --   }
  --   case promote u => {
  --     cases tproof; case _ T a b A B j1 j2 =>
  --     cases j2; case _ A2 j2 s1 =>
  --     cases j2; case _ A3 j2 =>
  --     cases j2; case _ B2 j2 =>
  --     cases j2; case _ T j s2 =>
  --     exists eq T u u
  --     apply Infer.refl; simp [*]
  --   }
  --   case phi => sorry
  --   case bind1 u1 u2 k u3 s1 ih => {
  --     cases k <;> simp at *
  --     case lam m => {
  --       cases tproof; case _ K B S j1 j2 j3 =>
  --       cases j1; case _ T j1 step2 =>
  --       have lem := ih j1
  --       cases lem; case _ D jlem =>
  --       have cj1 : Γ ⊢ u1 >: Mode.pi_domain m K := ConInfer.infer j1 step2
  --       have lem1 := preservation_step_of_cinfer_pi_domain cj1 s1
  --       have lem2 := @preservation_step_of_infer_ctx Γ u1 u3 B u2 S j3 s1
  --       cases lem2; case _ B' lem2 =>
  --       exists (pi m u2 B')
  --       apply Infer.lam lem1 lem2 j2
  --     }
  --     case pi m => sorry
  --     case inter => sorry
  --   }
  --   case bind2 u1 u2 k u3 S1 s1 ih => {
  --     cases k <;> simp at *
  --     case lam m => {
  --       cases tproof; case _ K B S2 j1 j2 j3 =>
  --       have xfresh := @Name.fresh_is_fresh (S1 ++ S2)
  --       generalize xdef : Name.fresh (S1 ++ S2) = x at *
  --       simp at *
  --       replace xfresh := demorgan xfresh
  --       cases xfresh; case _ xn1 xn2 =>
  --       have lem1 := ih x xn1 (j3 x xn2)
  --       cases lem1; case _ D lem1 =>
  --       have lem2 := to_open D x
  --       cases lem2; case _ D' lem2 =>
  --       subst lem2
  --       exists pi m u3 D'
  --       apply Infer.lam j1 _ _
  --       exact S2; intro y yn
  --       sorry


  --       sorry
  --     }
  --     case pi m => sorry
  --     case inter => sorry
  --   }
  --   case ctor1 => sorry
  --   case ctor2 => sorry
  --   case ctor3 => sorry
  -- }

  -- lemma preservation_of_infer_step3 : Γ ⊢ t : A -> t -β> s -> ∃ B, Γ ⊢ s : B
  --   := λ j step => @Infer.rec
  --     (λ Γ t A j' => ∀ s, t -β> s -> ∃ B, Γ ⊢ s : B)
  --     (λ Γ t A j' => ∀ s, t -β> s -> ∃ B, Γ ⊢ s >: B)
  --     (λ Γ t A j' => ∀ s, t -β> s -> ∃ B, Γ ⊢ s =: B)
  --     (λ Γ wf => True)
  --   sorry
  --   sorry
  --   sorry
  --   (by {
  --     intro Γ A m K t B S j1 j2 j3 ih1 ih2 s step; simp at *
  --     cases step <;> simp
  --     case bind1 A' step => {
  --       sorry
  --     }
  --     case bind2 => sorry
  --   })
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   sorry
  --   (by {
  --     intro Γ t A B j step ih s step2
  --     have lem := ih s step2
  --     cases lem; case _ D j2 =>
  --     sorry
  --   })
  --   (by {
  --     intro Γ t A B j c ih s step
  --     sorry
  --   })
  --   sorry
  --   sorry
  --   Γ
  --   t
  --   A
  --   j
  --   s
  --   step

  -- theorem preservation_of_infer : Γ ⊢ t : A -> t -β>* s -> ∃ B, Γ ⊢ s : B := sorry

end Cedille
