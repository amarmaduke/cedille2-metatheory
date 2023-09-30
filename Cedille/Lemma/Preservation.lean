
import Common
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Inversion
import Cedille.Lemma.Red

namespace Cedille

  lemma preservation_of_infer_step_subst :
    Γ ⊢ lam m u1 u2 >: pi m A B ->
    Γ ⊢ u3 =: A ->
    ∃ B, Γ ⊢ [_:= u3]u2 : B
  := by sorry

  lemma preservation_step_of_infer_ctx (S : FvSet!) :
    ((x : Name) -> x ∉ S → (Γ ++ [x:A]) ⊢ {_|-> x}t : {_|-> x}B) ->
    A -β> A' ->
    ∃ B, ((x : Name) -> x ∉ S → (Γ ++ [x:A']) ⊢ {_|-> x}t : {_|-> x}B)
  := by sorry

  lemma preservation_step_of_cinfer_ctx (S : FvSet!) :
    ((x : Name) -> x ∉ S → (Γ ++ [x:A]) ⊢ {_|-> x}t >: {_|-> x}B) ->
    A -β> A' ->
    ((x : Name) -> x ∉ S → (Γ ++ [x:A']) ⊢ {_|-> x}t >: {_|-> x}B)
  := by sorry

  lemma preservation_step_of_cinfer_ctx_const (S : FvSet!) :
    ((x : Name) -> x ∉ S → (Γ ++ [x:A]) ⊢ {_|-> x}t >: const K) ->
    A -β> A' ->
    ((x : Name) -> x ∉ S → (Γ ++ [x:A']) ⊢ {_|-> x}t >: const K)
  := by sorry

  lemma rule_cinfer_red : Γ ⊢ t >: A -> A -β>* B -> Γ ⊢ t >: B := by {
    intro j step
    cases j; case _ D j step2 =>
    replace step := RedStar.trans step2 step
    apply ConInfer.infer j step
  }

  lemma rule_inv_inter1_kind : ¬ (Γ ⊢ t >: inter (const K) B) := λ j => @Nat.rec
    (λ s => ∀ Γ t K B,
      size t ≤ s ->
      ¬ Γ ⊢ t >: inter (const K) B)
    sorry
    (by {
      intro s ih Γ t K B sh j
      cases t <;> simp at *
      case bound => apply ih _ (bound _) _ _ (by simp) j
      case free => apply ih _ (free _) _ _ (by simp) j
      case const => apply ih _ (const _) _ _ (by simp) j
      case bind b u1 u2 => {
        cases b <;> simp at *
        case lam m => {
          sorry
        }
        case pi m => sorry
        case inter => sorry
      }
      case ctor => sorry
    })
    (size t)
    Γ
    t
    K
    B
    (by simp)
    j

  lemma preservation_step_of_cinfer_const :
    Γ ⊢ t >: const K ->
    t -β> s ->
    Γ ⊢ s >: const K
  := λ j step => @ConInfer.rec
    (λ Γ t A j => ∀ s K, A -β>* const K -> t -β> s -> Γ ⊢ s : A)
    (λ Γ t A j => ∀ s K, A = const K -> t -β> s -> Γ ⊢ s >: A)
    (λ Γ t A j => ∀ s K, A = const K -> t -β> s -> Γ ⊢ s =: A)
    (λ Γ wf => True)
    (by {
      intro Γ wf _ s K e step
      cases step
    })
    (by {
      intro Γ x A wf xn _ s K e step
      cases step
    })
    (by {
      intro Γ A m K B S j1 j2 ih1 ih2 s K' e step; simp at *
      cases step <;> simp at *
      case bind1 A' step => {
        cases m <;> simp at *
        case free => {
          have lem1 := ih1 A' Constant.typeU rfl step
          have lem2 := preservation_step_of_cinfer_ctx_const S j2 step
          apply @Infer.pi _ _ mf Constant.typeU _ _ lem1 lem2
        }
        case erased => {
          have lem1 := ih1 A' K rfl step
          have lem2 := preservation_step_of_cinfer_ctx_const S j2 step
          apply @Infer.pi _ _ m0 K _ _ lem1 lem2
        }
        case type => {
          have lem1 := ih1 A' K rfl step
          have lem2 := preservation_step_of_cinfer_ctx_const S j2 step
          apply @Infer.pi _ _ mt K _ _ lem1 lem2
        }
      }
      case bind2 B' S' step => {
        cases m <;> simp at *
        case free => {
          have lem2 : ∀ x, x ∉ (S ++ S') -> (Γ ++ [x:A]) ⊢ {_|-> x}B' >: typeu := by {
            intro x xn; simp at xn
            replace xn := demorgan xn
            cases xn; case _ xn1 xn2 =>
            apply ih2 x xn1 ({_|-> x}B') Constant.typeU rfl _
            apply step x xn2
          }
          apply @Infer.pi _ _ mf Constant.typeU _ (S ++ S') j1 lem2
        }
        case erased => {
          have lem2 : ∀ x, x ∉ (S ++ S') -> (Γ ++ [x:A]) ⊢ {_|-> x}B' >: typeu := by {
            intro x xn; simp at xn
            replace xn := demorgan xn
            cases xn; case _ xn1 xn2 =>
            apply ih2 x xn1 ({_|-> x}B') Constant.typeU rfl _
            apply step x xn2
          }
          apply @Infer.pi _ _ m0 K _ (S ++ S') j1 lem2
        }
        case type => {
          have lem2 : ∀ x, x ∉ (S ++ S') -> (Γ ++ [x:A]) ⊢ {_|-> x}B' >: kindu := by {
            intro x xn; simp at xn
            replace xn := demorgan xn
            cases xn; case _ xn1 xn2 =>
            apply ih2 x xn1 ({_|-> x}B') Constant.kindU rfl _
            apply step x xn2
          }
          apply @Infer.pi _ _ mt K _ (S ++ S') j1 lem2
        }
      }
    })
    sorry
    sorry
    sorry
    (sorry)
    (by {
      intro Γ t A B j ih s K e step
      sorry
    })
    sorry
    (by {
      intro Γ A a b j1 j2 j3 ih1 ih2 ih3 s K e step
      cases step <;> simp at *
      case ctor1 => sorry
      case ctor2 a' step => {
        sorry
      }
      case ctor3 => sorry
    })
    sorry
    sorry
    sorry
    sorry
    sorry
    (by {
      intro Γ t A B j step ih s K e step'
      subst e
      have lem := ih s K step step'
      apply ConInfer.infer lem step
    })
    (by {
      intro Γ t A B K' j1 j2 conv ih1 ih2 s K e step
      subst e;
      cases conv; case _ A' K' S s1 er s2 =>
      cases s2
      case refl => {
        clear ih2
        sorry
      }
      case step _ step _ => cases step
    })
    (by simp)
    (by simp)
    Γ
    t
    (const K)
    j
    s
    K
    rfl
    step


  lemma preservation_step_of_cinfer_pi_domain :
    Γ ⊢ t >: Mode.pi_domain m K ->
    t -β> s ->
    Γ ⊢ s >: Mode.pi_domain m K
  := λ j step => @Nat.rec
    (λ si => ∀ Γ t m K s,
      size t ≤ si ->
      Γ ⊢ t >: Mode.pi_domain m K ->
      t -β> s ->
      Γ ⊢ s >: Mode.pi_domain m K)
    sorry
    (by {
      intro si ih Γ t m K s sh j step
      cases t <;> simp at *
      case bound => cases step
      case free => cases step
      case const => cases step
      case bind b u1 u2 => {
        have s1 : size u1 ≤ si := by linarith 
        have s2 : size u2 ≤ si := by linarith
        cases b <;> simp at *
        case lam m' => {
          cases j; case _ D j step2 =>
          cases j; case _ K2 B2 S2 j1 j2 j3 =>
          exfalso; apply red_inv_pi_not_pi_domain step2
        }
        case pi m' => {
          cases j; case _ D j step2 =>
          cases j; case _ K2 S2 j1 j2 =>
          have e := red_force_mode_pi_codomain step2; rw [e]
          cases step <;> simp
          case bind1 u1' step => {
            cases m' <;> simp at *
            case free => {
              have lem := @ih Γ u1 mf Constant.typeU u1' s1 j1 step; simp at lem
              apply ConInfer.infer _ _; exact typeu
              apply @Infer.pi _ _ mf Constant.typeU _ S2 lem
              simp; apply preservation_step_of_cinfer_ctx_const S2 j2 step
              apply RedStar.refl
            }
            case erased => sorry
            case type => sorry
          }
          case bind2 => sorry
        }
        case inter => {
          cases j; case _ D j step2 =>
          cases j; case _ S2 j1 j2 =>
          have e := red_force_typeu step2; rw [e]
          cases step <;> simp
          case bind1 u1' step => {
            have lem := @ih Γ u1 mf K u1' s1 j1 step; simp at lem
            sorry
          }
          case bind2 => sorry
        }
      }
      case ctor c u1 u2 u3 => {
        have s1 : size u1 ≤ si := by linarith 
        have s2 : size u2 ≤ si := by linarith
        have s3 : size u3 ≤ si := by linarith
        cases c <;> simp at *
        case app m => sorry
        case pair => {
          cases j; case _ D j step2 =>
          cases j; case _ A B j1 j2 j3 j4 =>
          exfalso; apply red_inv_inter_not_pi_domain step2
        }
        case fst => {
          cases j; case _ D j step2 =>
          cases j; case _ B j =>
          have step2 : inter D B -β>* inter (Mode.pi_domain m K) B := by {
            apply red_inter' step2 (λ _ _ => RedStar.refl); exact []
          }
          replace j := rule_cinfer_red j step2
          cases m <;> simp at *
          case free => exfalso; apply rule_inv_inter1_kind j
          case erased => exfalso; apply rule_inv_inter1_kind j
          case type => exfalso; apply rule_inv_inter1_kind j
        }
        case snd => sorry
        case eq => sorry
        case refl => sorry
        case eqind => sorry
        case promote => sorry
        case delta => sorry
        case phi => sorry
      }
    })
    (size t)
    Γ
    t
    m
    K
    s
    (by simp)
    j
    step


  lemma preservation_of_infer_step4 : Γ ⊢ t : A -> t -β> s -> Γ ⊢ s : A := by {
    intro j step
    induction step generalizing Γ A
    case beta m u1 u2 u3 => {
      cases j; case _ A B S j1 j2 =>
      sorry
    }
    case fst u1 u2 u3 => {
      cases j; case _ B j =>
      cases j; case _ T j step =>
      sorry
    }
    case snd => sorry
    case eqind => sorry
    case promote => sorry
    case phi => sorry
    case bind1 => sorry
    case bind2 => sorry
    case ctor1 => sorry
    case ctor2 => sorry
    case ctor3 => sorry
  }

  lemma preservation_of_infer_step : Γ ⊢ t : A -> t -β> s -> ∃ B, Γ ⊢ s : B := by {
    intro tproof step
    induction step generalizing Γ A
    case beta m u1 u2 u3 => {
      cases tproof; case _ A B S j1 j2 =>
      apply preservation_of_infer_step_subst j1 j2
    }
    case fst u1 u2 u3 => {
      cases tproof; case _ B j =>
      cases j; case _ P j step =>
      cases j; case _ A2 B2 j1 j2 j3 j4 =>
      cases j1; case _ A3 j5 j6 =>
      sorry
    }
    case snd u1 u2 u3 => {
      cases tproof; case _ A1 B1 j =>
      cases j; case _ P j1 s1 =>
      cases j1; case _ A2 B2 j1 j2 j3 j4 =>
      cases j3; case _ A3 j5 c1 =>
      sorry
    }
    case eqind u1 u2 u3 u4 u5 u6 => {
      cases tproof
      case app A1 B1 S1 j1 j2 => {
        cases j1; case _ D1 j1 s1 =>
        cases j1; case _ A2 B2 S2 j4 j5 =>
        cases j4; case _ D2 j4 s2 =>
        cases j4; case _ A3 B3 S3 j6 j7 =>
        cases j6; case _ D3 j6 s3 =>
        cases j6; case _ A4 B4 S4 j8 j9 =>
        cases j8; case _ D4 j8 s4 =>
        cases j8; case _ A5 B5 S5 j8 j11 =>
        cases j8; case _ D5 j8 s5 =>
        cases j8; case _ A6 B6 S6 j8 j13 =>
        cases j8; case _ D6 j8 s6 => 
        cases j8
      }
      case eqind j1 j2 j3 j4 j5 j6 => {
        cases j5; case _ D j5 c1 =>
        cases j5; case _ A j =>
        sorry
      }
    }
    case promote u => {
      cases tproof; case _ T a b A B j1 j2 =>
      cases j2; case _ A2 j2 s1 =>
      cases j2; case _ A3 j2 =>
      cases j2; case _ B2 j2 =>
      cases j2; case _ T j s2 =>
      exists eq T u u
      apply Infer.refl; simp [*]
    }
    case phi u1 u2 u3 S er => {
      cases tproof; case _ A B S j1 j2 f1 f2 j3 =>
      cases j2; case _ T j2 s1 =>
      exists T
    }
    case bind1 u1 u2 k u3 s1 ih => {
      cases k <;> simp at *
      case lam m => {
        cases tproof; case _ K B S j1 j2 j3 =>
        cases j1; case _ T j1 step2 =>
        have lem := ih j1
        cases lem; case _ D jlem =>
        have cj1 : Γ ⊢ u1 >: Mode.pi_domain m K := ConInfer.infer j1 step2
        have lem1 := preservation_step_of_cinfer_pi_domain cj1 s1
        have lem2 := @preservation_step_of_infer_ctx Γ u1 u3 B u2 S j3 s1
        cases lem2; case _ B' lem2 =>
        exists (pi m u2 B')
        apply Infer.lam lem1 lem2 j2
      }
      case pi m => sorry
      case inter => sorry
    }
    case bind2 u1 u2 k u3 S1 s1 ih => {
      cases k <;> simp at *
      case lam m => {
        cases tproof; case _ K B S2 j1 j2 j3 =>
        have xfresh := @Name.fresh_is_fresh (S1 ++ S2)
        generalize xdef : Name.fresh (S1 ++ S2) = x at *
        simp at *
        replace xfresh := demorgan xfresh
        cases xfresh; case _ xn1 xn2 =>
        have lem1 := ih x xn1 (j3 x xn2)
        cases lem1; case _ D lem1 =>
        have lem2 := to_open D x
        cases lem2; case _ D' lem2 =>
        subst lem2
        exists pi m u3 D'
        apply Infer.lam j1 _ _
        exact S2; intro y yn
        sorry


        sorry
      }
      case pi m => sorry
      case inter => sorry
    }
    case ctor1 => sorry
    case ctor2 => sorry
    case ctor3 => sorry
  }

  lemma preservation_of_infer_step3 : Γ ⊢ t : A -> t -β> s -> ∃ B, Γ ⊢ s : B
    := λ j step => @Infer.rec
      (λ Γ t A j' => ∀ s, t -β> s -> ∃ B, Γ ⊢ s : B)
      (λ Γ t A j' => ∀ s, t -β> s -> ∃ B, Γ ⊢ s >: B)
      (λ Γ t A j' => ∀ s, t -β> s -> ∃ B, Γ ⊢ s =: B)
      (λ Γ wf => True)
    sorry
    sorry
    sorry
    (by {
      intro Γ A m K t B S j1 j2 j3 ih1 ih2 s step; simp at *
      cases step <;> simp
      case bind1 A' step => {
        sorry
      }
      case bind2 => sorry
    })
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    (by {
      intro Γ t A B j step ih s step2
      have lem := ih s step2
      cases lem; case _ D j2 =>
      sorry
    })
    (by {
      intro Γ t A B j c ih s step
      sorry
    })
    sorry
    sorry
    Γ
    t
    A
    j
    s
    step

  theorem preservation_of_infer : Γ ⊢ t : A -> t -β>* s -> ∃ B, Γ ⊢ s : B := sorry 

end Cedille
