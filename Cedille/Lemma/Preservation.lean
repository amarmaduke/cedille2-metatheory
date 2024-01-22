
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

  inductive ParCtxRed : (Map! Term) -> (Map! Term) -> Prop where
  | empty : ParCtxRed [] []
  | step : ParCtxRed Γ Γ' -> A -β>* A' -> ParCtxRed (Γ ++ [x : A]) (Γ' ++ [x : A'])

  inductive CtxRed : (Map! Term) -> (Map! Term) -> Prop where
  | head (x:Name) A : CtxRed Γ Δ -> CtxRed (Γ ++ [x:A]) (Δ ++ [x:A])
  | tail (x:Name) Γ : A -β> B -> CtxRed (Γ ++ [x:A]) (Γ ++ [x:B])

  inductive CtxRedStar : (Map! Term) -> (Map! Term) -> Prop where
  | refl : CtxRedStar t t
  | step : CtxRed t1 t2 -> CtxRedStar t2 t3 -> CtxRedStar t1 t3

  @[simp] lemma ctx_red_not_empty : ¬ CtxRed [] Γ := by sorry

  lemma ctx_red_append {A B : Term} :
    CtxRed (Γ ++ [x:A]) (Δ ++ [y:B]) ->
    (CtxRed Γ Δ ∧ x = y ∧ A = B) ∨ (A -β> B ∧ x = y ∧ Γ = Δ)
  := by {
    intro step
    generalize lhsdef : Γ ++ [x:A] = lhs at *
    generalize rhsdef : Δ ++ [y:B] = rhs at *
    cases step
    case head Γ' Δ' x' A' step => {
      have lem1 := append_eq lhsdef
      have lem2 := append_eq rhsdef
      casesm* _ ∧ _; case _ e1 e2 e3 e4 =>
      subst e1; subst e3
      have lem1 := pair_eq e2
      have lem2 := pair_eq e4
      casesm* _ ∧ _; case _ e5 e6 e7 e8 =>
      subst e5; subst e6; subst e7; subst e8
      simp; apply Or.inl step
    }
    case tail A' B' x' Γ' step => {
      have lem1 := append_eq lhsdef
      have lem2 := append_eq rhsdef
      casesm* _ ∧ _; case _ e1 e2 e3 e4 =>
      subst e1; subst e3
      have lem1 := pair_eq e2
      have lem2 := pair_eq e4
      casesm* _ ∧ _; case _ e5 e6 e7 e8 =>
      subst e5; subst e6; subst e7; subst e8
      simp; apply Or.inr step
    }
  }

  lemma ctx_red_fv : CtxRed Γ Δ -> Map.fv Δ ⊆ Map.fv Γ := by sorry

  lemma ctx_red_in {A : Term} :
    CtxRed Γ Δ ->
    (x, A) ∈ Γ ->
    ((x, A) ∈ Δ) ∨ (∃ B, A -β> B ∧ (x, B) ∈ Δ)
  := by sorry

  lemma preservation_of_cinfr_type : Γ ⊢ t >: A -> A -β>* B -> Γ ⊢ t >: B := by {
    intro j step
    cases j; case _ D j r =>
    replace step := RedStar.trans r step
    constructor; exact j; simp [*]
  }

  -- lemma infr_red_b_step : Γ ⊢ s : B -> t -β> s -> ∃ A, A -β>* B ∧ Γ ⊢ t : A := λ j step => @Infer.rec
  --   (λ Γ s B _ => ∀ t, t -β> s -> ∃ A, A -β>* B ∧ Γ ⊢ t : A)
  --   (λ Γ s B _ => ∀ t, t -β> s -> Γ ⊢ t >: B)
  --   (λ Γ s B _ => ∀ t, t -β> s -> Γ ⊢ t =: B)
  --   (λ Γ _ => True)
  --   (by {
  --     intro Γ wf _ s step

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
  --   sorry
  --   sorry
  --   sorry
  --   (by {
  --     intro Γ t A B j step ih
  --     intro s step2
  --     have lem1 := ih s step2
  --     cases lem1; case _ T lem1 =>
  --     constructor; exact lem1.2
  --     apply RedStar.trans lem1.1 step
  --   })
  --   (by {
  --     intro Γ t A B K j1 j2 cv ih1 ih2
  --     intro s step
  --     have lem1 := ih1 s step
  --     cases lem1; case _ T lem1 =>
  --     constructor; exact lem1.2; exact j2
  --     apply Conv.red_b cv lem1.1
  --   })
  --   (by simp)
  --   (by simp)
  --   Γ
  --   s
  --   B
  --   j
  --   t
  --   step

  -- lemma cinfr_red_b_step : Γ ⊢ s >: A -> t -β> s -> Γ ⊢ t >: A := by {
  --   intro j step
  --   cases j; case _ D j r =>
  --   have lem := infr_red_b_step j step
  --   casesm* ∃ _, _, _ ∧ _; case _ T r2 j2 =>
  --   have r3 := RedStar.trans r2 r
  --   constructor; exact j2; exact r3
  -- }

  -- lemma cinfr_red_b : Γ ⊢ s >: A -> t -β>* s -> Γ ⊢ t >: A := by {
  --   intro j step
  --   induction step
  --   case refl => simp [*]
  --   case step t1 t2 t3 step _ ih => {
  --     replace j := ih j
  --     apply cinfr_red_b_step j step
  --   }
  -- }

  -- lemma chck_type_red_b : Γ ⊢ t =: B -> A -β>* B -> Γ ⊢ t =: A := by {
  --   intro j r
  --   cases j; case _ D K j1 cv j2 =>
  --   have lem1 := Conv.symm (Conv.red_b (Conv.symm cv) r)
  --   have lem2 : Γ ⊢ A >: const K := cinfr_red_b j2 r
  --   constructor; exact j1; exact lem2; exact lem1
  -- }

  lemma preservation_infer_step :
    Γ ⊢ t : A -> t -p> s -> ParCtxRed Γ Δ -> ∃ B, A -p> B ∧ Δ ⊢ s : B
  := λ j => @Infer.rec
    (λ Γ t A j => ∀ Δ s, t -p> s -> ParCtxRed Γ Δ -> ∃ B, A -p> B ∧ Δ ⊢ s : B)
    (λ Γ t A j => ∀ Δ s, t -p> s -> ParCtxRed Γ Δ -> ∃ B, A -p> B ∧ Δ ⊢ s >: B)
    (λ Γ t A j => ∀ Δ s, t -p> s -> ParCtxRed Γ Δ -> Δ ⊢ s =: A)
    (λ Γ j => ∀ Δ, ParCtxRed Γ Δ -> ⊢ Δ)
    (by {
      intro Γ wf ih Δ s step1 step2
      cases step1; case _ =>
      exists kindu; apply And.intro _ _
      constructor; simp
      replace ih := ih _ step2
      constructor; exact ih
    })
    (by {
      intro Γ x A wf xin ih s Δ step
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
      sorry
    })
    (by {
      sorry
    })
    sorry
    sorry
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
      sorry
    })
    (by {
      sorry
    })
    (by {
      intro Γ t A B j1 step ih Δ s step1 step2
      replace ih := ih _ _ step1 step2
      casesm* ∃ _, _, _ ∧ _; case _ A' step3 j2 =>
      have lem1 : ∃ B', A' -β>* B' ∧ B -p> B' := sorry
      casesm* ∃ _, _, _ ∧ _; case _ B' r1 r2 =>
      exists B'; apply And.intro r2 _
      constructor; exact j2; apply r1
    })
    (by {
      intro Γ t A B K j1 j2 cv ih1 ih2 Δ s step1 step2
      replace ih1 := ih1 _ _ step1 step2
      casesm* ∃ _, _, _ ∧ _; case _ A' step3 j3 =>
      have lem1 : A -β>* A' := sorry
      replace ih2 := ih2 Δ B (ParRed.refl) step2
      casesm* ∃ _, _, _ ∧ _; case _ T step4 j4 =>
      cases step4; case _ =>
      constructor; exact j3; exact j4
      apply Conv.red_f (infer_implies_pseobj_type j1) cv lem1
    })
    (by {
      intro Δ step
      sorry
    })
    (by {
      sorry
    })
    Γ
    t
    A
    j
    Δ
    s

  -- lemma preservation_chck_step :
  --   Γ ⊢ t =: A ->
  --   (∀ s, t -β> s -> Γ ⊢ s =: A)
  --   ∧ (∀ Δ, CtxRed Γ Δ -> Δ ⊢ t =: A)
  -- := by {
  --   intro j
  --   cases j; case _ T K j cv j2 =>
  --   have lem := preservation_infer_step j
  --   cases lem; case _ lem1 lem2 =>
  --   apply And.intro _ _
  --   {
  --     intro s step
  --     replace lem1 := lem1 s step
  --     casesm* ∃ _, _, _ ∧ _; case _ D r j3 =>
  --     constructor; exact j3; exact j2
  --     apply Conv.red_f _ cv r
  --     apply infer_implies_pseobj_type j
  --   }
  --   {
  --     intro Δ step
  --     replace lem2 := lem2 Δ step
  --     casesm* ∃ _, _, _ ∧ _; case _ D r j3 =>
  --     sorry
  --   }
  -- }

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
