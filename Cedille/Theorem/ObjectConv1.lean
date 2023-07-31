
import Cedille.Def
import Cedille.Lemma
import Cedille.Theorem.Preservation

namespace Cedille

  lemma object_red_to_proof_red_step_lam_mf_bind2_case {S S' : FvSet} :
    ((x : Name) -> x ∉ S -> (s : _) ->
      erase ({_|-> x}B) -β> s ->
      ∃ k, {_|-> x}B -β>* k ∧ erase k = s) ->
    ((x : Name) -> x ∉ S' -> {_|-> x}erase B -β> {_|-> x}B') ->
    ∃ k, lam mf A B -β>* k ∧ erase k = lam mf kindu B'
  := by {
    intros ih step
    have xfresh := @Name.fresh_is_fresh (S ++ S')
    let x := Name.fresh (S ++ S')
    have xe : Name.fresh (S ++ S') = x := by simp
    have xn1 : x ∉ S := FvSet.not_mem_left xfresh
    have xn2 : x ∉ S' := FvSet.not_mem_right xfresh
    have step := step x xn2
    have step := red_open_erase step
    have lem := ih x xn1 ({_|-> x}B') step
    casesm* ∃ _ , _ , _ ∧ _
    case _ k kstep e => {
      exists (lam mf A ({_<-| x}k)); simp [*]
      have e2 := erase_close_open e
      rewrite [e2]; simp [*]
      apply (red_lam2 kstep)
    }
  }

  lemma object_red_to_proof_red_step_bind2_case {S S' : FvSet} :
    (ctor : (A : Term) -> (B : Term 1) -> Term) ->
    (ctore : {A : Term} -> {B : Term 1} -> erase (ctor A B) = ctor (erase A) (erase B)) ->
    (ctorr : {x A B B' : _} -> {_|-> x}B -β>* B' -> ctor A B -β>* ctor A ({_<-| x}B')) ->
    ((x : Name) -> x ∉ S -> (s : _) ->
      erase ({_|-> x}B) -β> s ->
      ∃ k, {_|-> x}B -β>* k ∧ erase k = s) ->
    ((x : Name) -> x ∉ S' -> {_|-> x}erase B -β> {_|-> x}B') ->
    ∃ k, ctor A B -β>* k ∧ erase k = ctor (erase A) B'
  := by {
    intros ctor ctore ctorr ih step
    have xfresh := @Name.fresh_is_fresh (S ++ S')
    let x := Name.fresh (S ++ S')
    have xe : Name.fresh (S ++ S') = x := by simp
    have xn1 : x ∉ S := FvSet.not_mem_left xfresh
    have xn2 : x ∉ S' := FvSet.not_mem_right xfresh
    have step := step x xn2
    have step := red_open_erase step
    have lem := ih x xn1 ({_|-> x}B') step
    casesm* ∃ _ , _ , _ ∧ _
    case _ k kstep e => {
      exists (ctor A ({_<-| x}k)); simp [*]
      have e2 := erase_close_open e
      rewrite [e2]
      rfl
    }
  }

  lemma object_red_to_proof_red_step_app_case :
    Γ ⊢ a =: A ->
    ((s : _) -> erase f -β> s -> ∃ k, f -β>* k ∧ erase k = s) ->
    ((s : _) -> erase a -β> s -> ∃ k, a -β>* k ∧ erase k = s) ->
    (s : _) ->
    Γ ⊢ f >: pi mf A B ->
    erase (f @ω a) -β> s ->
    ∃ k, f @ω a -β>* k ∧ erase k = s
  := by {
    intros _ ih1 ih2 s j2 step
    simp at step
    refine (@Red.rec
      (λ x y _ => x = erase f @ω erase a -> y = s -> ∃ k, f @ω a -β>* k ∧ erase k = y)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (erase f @ω erase a) s step rfl rfl
    ) <;> intros <;> intros <;> simp at *
    case _ m t1 t2 t3 e1 e2 => {
      cases m <;> simp at e1
      injection e1 with _ _ h1 h2 _
      have h1 := erase_forces_lam_mf (symm h1)
      casesm* ∃ _, _, _ ∧ _
      case _ t1' t2' t1e t2e fe => {
        have step2 : f @ω a -β> [_:= a]t2' := by subst fe; apply Red.beta
        rewrite [fe] at step; simp at step
        cases step
        case beta => {
          exists ([_:= a]t2'); simp [*]
          rewrite [fe] at step2
          apply (RedStar.step step2 RedStar.refl)
        }
        case ctor1 s step => {
          rewrite [e2]; simp at *
          rewrite [fe] at ih1; simp at ih1
          have lem := ih1 s step
          casesm* ∃ _, _, _ ∧ _
          case _ k kstep ke =>
          rewrite [<-fe] at kstep; simp
          exists (k @ω a); simp [*]; rewrite [<-fe]
          apply (red_app1 kstep)
        }
        case ctor2 s step => {
          rewrite [e2]; simp at *
          have lem := ih2 s step
          casesm* ∃ _, _, _ ∧ _
          case _ k kstep ke =>
          exists (f @ω k); simp; rewrite [fe, ke]; simp; rewrite [<-fe]
          apply (red_app2 kstep)
        }
        case ctor3 s step => cases step
      }
    }
    case _ t1 t2 t3 t4 t5 t6 e1 _e2 => {
      injection e1 with _ _ e1 e3 _
      have lem := erase_no_eqind (symm e1)
      contradiction
    }
    case _ t1 t1' c t2 t2' step _ e1 _e2 => {
      injection e1 with _ ce t1e t2e t2'e; rewrite [ce, t2e, t2'e]; simp
      have lem := ih1 t1' (by subst t1e; apply step)
      casesm* ∃ _, _, _ ∧ _
      case _ k kstep ke =>
      exists (k @ω a); simp [*]
      apply (red_app1 kstep)
    }
    case _ t1 t1' c t2 t2' step _ e1 _e2 => {
      injection e1 with _ ce t1e t2e t2'e; rewrite [ce, t1e, t2'e]; simp
      have lem := ih2 t1' (by subst t2e; apply step)
      casesm* ∃ _, _, _ ∧ _
      case _ k kstep ke =>
      exists (f @ω k); simp [*]
      apply (red_app2 kstep)
    }
    case _ t1 t1' c t2 t2' step _ e1 _e2 => {
      injection e1 with _ _ _ _ e; subst e; cases step
    }
  }

  lemma object_red_to_proof_red_step_tapp_case :
    Γ ⊢ a =: A ->
    ((s : _) -> erase f -β> s -> ∃ k, f -β>* k ∧ erase k = s) ->
    ((s : _) -> erase a -β> s -> ∃ k, a -β>* k ∧ erase k = s) ->
    (s : _) ->
    Γ ⊢ f >: pi mt A B ->
    erase (f @τ a) -β> s ->
    ∃ k, f @τ a -β>* k ∧ erase k = s
  := by {
    intros _ ih1 ih2 s j2 step
    simp at step
    refine (@Red.rec
      (λ x y _ => x = erase f @τ erase a -> y = s -> ∃ k, f @τ a -β>* k ∧ erase k = y)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (erase f @τ erase a) s step rfl rfl
    ) <;> intros <;> intros <;> simp at *
    case _ m t1 t2 t3 e1 e2 => {
      cases m; simp at e1
      have lem := app_m0_not_app_mt e1; contradiction
      injection e1 with _ _ h1 h2 _
      have h1 := erase_forces_lam_mt (symm h1)
      casesm* ∃ _, _, _ ∧ _
      case _ t1' t2' t1e t2e fe => {
        have step2 : f @τ a -β> [_:= a]t2' := by subst fe; apply Red.beta
        rewrite [fe] at step; simp at step
        cases step
        case beta => {
          exists ([_:= a]t2'); simp [*]
          rewrite [fe] at step2
          apply (RedStar.step step2 RedStar.refl)
        }
        case ctor1 s step => {
          rewrite [e2]; simp at *
          rewrite [fe] at ih1; simp at ih1
          have lem := ih1 s step
          casesm* ∃ _, _, _ ∧ _
          case _ k kstep ke =>
          rewrite [<-fe] at kstep; simp
          exists (k @τ a); simp [*]; rewrite [<-fe]
          apply (red_app1 kstep)
        }
        case ctor2 s step => {
          rewrite [e2]; simp at *
          have lem := ih2 s step
          casesm* ∃ _, _, _ ∧ _
          case _ k kstep ke =>
          exists (f @τ k); simp; rewrite [fe, ke]; simp; rewrite [<-fe]
          apply (red_app2 kstep)
        }
        case ctor3 s step => cases step
      }
    }
    case _ t1 t1' c t2 t2' step _ e1 _e2 => {
      injection e1 with _ ce t1e t2e t2'e; rewrite [ce, t2e, t2'e]; simp
      have lem := ih1 t1' (by subst t1e; apply step)
      casesm* ∃ _, _, _ ∧ _
      case _ k kstep ke =>
      exists (k @τ a); simp [*]
      apply (red_app1 kstep)
    }
    case _ t1 t1' c t2 t2' step _ e1 _e2 => {
      injection e1 with _ ce t1e t2e t2'e; rewrite [ce, t1e, t2'e]; simp
      have lem := ih2 t1' (by subst t2e; apply step)
      casesm* ∃ _, _, _ ∧ _
      case _ k kstep ke =>
      exists (f @τ k); simp [*]
      apply (red_app2 kstep)
    }
    case _ t1 t1' c t2 t2' step _ e1 _e2 => {
      injection e1 with _ _ _ _ e; subst e; cases step
    }
  }

  lemma object_red_to_proof_red_step_elam_case {S : FvSet} :
    Γ ⊢ A >: const K ->
    ((x : Name) -> x ∉ S -> (Γ ++ [x:A]) ⊢ {_|-> x}t : {_|-> x}B) ->
    ((s : _) -> erase A -β> s → ∃ k, A -β>* k ∧ erase k = s) ->
    ((x : Name) -> ¬x ∈ S → (s : _) ->
      erase ({_|-> x}t) -β> s ->
      ∃ k, {_|-> x}t -β>* k ∧ erase k = s) ->
    (s : _) ->
    ((x : Name) -> x ∉ fv t -> x ∉ (fv ∘ erase) ({_|-> x}t)) ->
    (erase (lam m0 A t) -β> s) ->
    ∃ k, lam m0 A t -β>* k ∧ erase k = s
  := by {
    intros j1 j2 ih1 ih2 s ih3 step
    simp at step
    let x := Name.fresh ((fv t) ++ S)
    have xe : Name.fresh ((fv t) ++ S) = x := by simp
    have xfresh := @Name.fresh_is_fresh ((fv t) ++ S)
    have xn1 := FvSet.not_mem_right xfresh
    have xn2 := FvSet.not_mem_left xfresh
    have fn := ih3 (Name.fresh (fv t)) Name.fresh_is_fresh
    have lem := erase_free_invariant fn x xn2
    rewrite [lem] at step
    have lem := ih2 x xn1 s step
    casesm* ∃ _, _, _ ∧ _
    case _ k kstep ke =>
    exists (lam m0 A ({_<-| x}k)); simp; rewrite [xe]
    generalize ydef : Name.fresh (fv ({_<-| x}k)) = y
    have fn2 : y ∉ (fv ∘ erase) ({_|-> y}{_<-| x}k) := sorry
    have xn3 : x ∉ fv ({_<-| x}k) := sorry
    have e2 := erase_free_invariant fn2 x xn3; simp at e2
    rewrite [e2]; simp [*]
    apply (red_lam2 kstep)
  }

  lemma object_red_to_proof_red_step :
    Γ ⊢ t : A ->
    (erase t) -β> s ->
    ∃ k, t -β>* k ∧ (erase k) = s
  := λ j step => @Infer.rec
    (λ Γ t A _ => (s : _) -> (erase t) -β> s -> ∃ k, t -β>* k ∧ (erase k) = s)
    (λ Γ t A _ => (s : _) -> (erase t) -β> s -> ∃ k, t -β>* k ∧ (erase k) = s)
    (λ Γ t A _ => (s : _) -> (erase t) -β> s -> ∃ k, t -β>* k ∧ (erase k) = s)
    (λ Γ _ => True)
    (by {
      intro Γ _ _ s step
      simp at step
      cases step
    })
    (by {
      intros _ _ x _ _ _ _ _ s step
      simp at step
      cases step
    })
    (by {
      intro Γ A m K B S _ h2 ih1 ih2 s step
      simp at step
      cases step
      case bind1 A' step => {
        have lem1 := ih1 A' step
        casesm* ∃ _ , _ , _ ∧ _
        case _ k kstep e => {
          exists (pi m k B); simp
          rewrite [<-e]
          refine (And.intro ?_ rfl)
          apply (red_pi1 kstep)
        }
      }
      case bind2 B' S' step => {
        simp at ih2
        apply (object_red_to_proof_red_step_bind2_case
          (pi m) erase_pi red_pi2 ih2 step)
      }
    })
    (by {
      intro Γ A K t B m S h1 h2 ih1 ih2 ih3 s step; simp at ih3
      cases m
      case erased => {
        simp at step
        apply (object_red_to_proof_red_step_elam_case h1 h2 ih2 ih3 s (ih1 rfl) step)
      }
      case free => {
        simp at step
        cases step
        case bind1 _ step => cases step
        case bind2 t' S' step => {
          apply (object_red_to_proof_red_step_lam_mf_bind2_case ih3 step)
        }
      }
      case type => {
        simp at step
        cases step
        case bind1 A' step => {
          have lem1 := ih2 A' step
          casesm* ∃ _ , _ , _ ∧ _
          case _ k kstep e => {
            exists (lam mt k t); simp [*]
            apply (red_lam1 kstep)
          }
        }
        case bind2 B' S' step => {
          apply (object_red_to_proof_red_step_bind2_case
            (lam mt) erase_lam_mt red_lam2 ih3 step)
        }
      }
    })
    (by {
      intros Γ f m A B a _ h1 h2 ih1 ih2 s step
      cases m
      case erased => {
        simp at step
        have lem1 := ih1 s step
        casesm* ∃ _ , _ , _ ∧ _
        case _ k kstep e =>
        exists (k @0 a); simp [*]
        apply (Cedille.red_app1 kstep)
      }
      case free => {
        apply (object_red_to_proof_red_step_app_case
          h2 ih1 ih2 s h1 step)
      }
      case type => {
        apply (object_red_to_proof_red_step_tapp_case
          h2 ih1 ih2 s h1 step)
      }
    })
    (by {
      intros _ A B S _ _ ih1 ih2 s step; simp at ih2
      simp at step
      cases step
      case bind1 t' step => {
        have lem := ih1 t' step
        casesm* ∃ _, _, _ ∧ _
        case _ k kstep ke =>
        exists (inter k B); simp [*]
        apply (red_inter1 kstep)
      }
      case bind2 B' S' step => {
        simp at ih2
        apply (object_red_to_proof_red_step_bind2_case
          inter erase_inter red_inter2 ih2 step)
      }
    })
    (by {
      sorry
      -- intros _ t _ s _ _ _ _ ih1 _ s' step
      -- simp at step
      -- have lem := ih1 s' step
      -- casesm* ∃ _, _, _ ∧ _
      -- case _ k kstep ke =>
      -- exists (pair k s); simp [*]
      -- apply (red_pair1 kstep)
    })
    (by {
      intros _ t _ _ _ ih s step
      simp at step
      have lem := ih s step
      casesm* ∃ _, _, _ ∧ _
      case _ k kstep e =>
      exists (fst k); simp [*]
      apply (red_fst kstep)
    })
    (by {
      intros _ t _ _ _ ih s step
      simp at step
      have lem := ih s step
      casesm* ∃ _, _, _ ∧ _
      case _ k kstep e =>
      exists (snd k); simp [*]
      apply (red_snd kstep)
    })
    (by {
      intros _ a _ b _ _ ih1 ih2 s step
      simp at step
      cases step <;> simp
      case ctor1 t1 step => {
        have lem := ih1 t1 step
        casesm* ∃ _, _, _ ∧ _
        case _ k kstep ke =>
        exists (eq k b); simp [*]
        apply (red_eq1 kstep)
      }
      case ctor2 t2 step => {
        have lem := ih2 t2 step
        casesm* ∃ _, _, _ ∧ _
        case _ k kstep ke =>
        exists (eq a k); simp [*]
        apply (red_eq2 kstep)
      }
      case ctor3 t3 step => cases step
    })
    (by {
      intros _ t _ _ _ s step
      simp at step
      cases step
      case bind1 t' step => cases step
      case bind2 t' S step => {
        let x := Name.fresh S
        have xfresh := @Name.fresh_is_fresh S
        have lem := step x xfresh
        rewrite [open_bound_0] at lem
        cases lem
      }
    })
    (by {
      intros _ s step
      simp at step; cases step
      case bind1 t' step => cases step
      case bind2 t' S step => {
        let x := Name.fresh S
        have xfresh := @Name.fresh_is_fresh S
        have lem := step x xfresh
        rewrite [open_bound_0] at lem
        cases lem
      }
    })
    (by {
      intros _ e _ _ _ ih s step
      simp at step
      have lem := ih s step
      casesm* ∃ _, _, _ ∧ _
      case _ k kstep ke =>
      exists (promote k); simp [*]
      apply (red_promote kstep)
    })
    (by {
      intros _ b _ _ a e _ _ _ _ _ _ ih2 _ s step
      simp at step
      have lem := ih2 s step
      casesm* ∃ _, _, _ ∧ _
      case _ k kstep ke =>
      exists (phi k b e); simp [*]
      apply (red_phi kstep)
    })
    (by {
      intros _ r _ _ _ _ ih s step
      simp at step
      have lem := ih s step
      casesm* ∃ _, _, _ ∧ _
      case _ k kstep ke =>
      exists (delta k); simp [*]
      apply (red_delta kstep)
    })
    (by {
      intros _ e _ ih s step
      simp at step
      have lem := ih s step
      casesm* ∃ _, _, _ ∧ _
      case _ k kstep ke =>
      exists (delta k); simp [*]
      apply (red_delta kstep)
    })
    (by {
      intros _ _ _ _ _ _ ih s step
      apply ih s step
    })
    (by {
      intros _ _ _ _ _ _ ih s step
      apply ih s step
    })
    (by simp)
    (by simp)
    Γ
    t
    A
    j
    s
    step

  lemma object_red_to_proof_red :
    Γ ⊢ t : A ->
    (erase t) -β>* s ->
    ∃ k, t -β>* k ∧ (erase k) = s
  := λ j step => @RedStar.rec
    (λ a b _ => (A t : _) -> erase t = a -> Γ ⊢ t : A -> ∃ k, t -β>* k ∧ (erase k) = b)
    (by {
      intros a _A t e _
      exists t; simp [*]
      apply RedStar.refl
    })
    (by {
      intros a b c step _ ih A t e j
      subst e
      have lem1 := object_red_to_proof_red_step j step
      casesm* ∃ _, _, _ ∧ _
      case _ k kstep ke =>
      have j2 := preservation (infer_implies_check j) kstep
      cases j2
      case check D j2 e2 =>
      have lem2 := ih D k ke j2
      casesm* ∃ _, _, _ ∧ _
      case _ k2 k2step k2e =>
      exists k2; simp [*]
      apply (RedStar.transitive kstep k2step)
    })
    (erase t)
    s
    step
    A
    t
    rfl
    j

  theorem object_conv :
    Γ ⊢ t : A ->
    Γ ⊢ s : B ->
    (erase t) =β= (erase s) ->
    t =β= s
  := by {
    intros j1 j2 e
    cases e
    case conv t1 t2 r1 e r2 =>
    have lem1 := object_red_to_proof_red j1 r1
    have lem2 := object_red_to_proof_red j2 r2
    casesm* ∃ _ , _, _ ∧ _
    case _ k1 k2 r1' e1 r2' e2 =>
    subst e1 e2
    simp at e -- idempotency of erasure
    apply (Conv.conv r1' r2' e)
  }

end Cedille
