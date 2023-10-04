
import Cedille.Def
import Cedille.Lemma
-- import Cedille.Theorem.Preservation

namespace Cedille

--   lemma object_red_to_proof_red_step_lam_mf_bind2_case {S S' : FvSet} :
--     ((x : Name) -> x ∉ S -> (s : _) ->
--       erase ({_|-> x}B) -β> s ->
--       ∃ k, {_|-> x}B -β>* k ∧ erase k = s) ->
--     ((x : Name) -> x ∉ S' -> {_|-> x}erase B -β> {_|-> x}B') ->
--     ∃ k, lam mf A B -β>* k ∧ erase k = lam mf kindu B'
--   := by {
--     intros ih step
--     have xfresh := @Name.fresh_is_fresh (S ++ S')
--     let x := Name.fresh (S ++ S')
--     have xe : Name.fresh (S ++ S') = x := by simp
--     have xn1 : x ∉ S := FvSet.not_mem_left xfresh
--     have xn2 : x ∉ S' := FvSet.not_mem_right xfresh
--     have step := step x xn2
--     have step := red_open_erase step
--     have lem := ih x xn1 ({_|-> x}B') step
--     casesm* ∃ _ , _ , _ ∧ _
--     case _ k kstep e => {
--       exists (lam mf A ({_<-| x}k)); simp [*]
--       have e2 := erase_close_open e
--       rewrite [e2]; simp [*]
--       apply (red_lam2 kstep)
--     }
--   }

--   lemma object_red_to_proof_red_step_bind2_case {S S' : FvSet} :
--     (ctor : (A : Term) -> (B : Term 1) -> Term) ->
--     (ctore : {A : Term} -> {B : Term 1} -> erase (ctor A B) = ctor (erase A) (erase B)) ->
--     (ctorr : {x A B B' : _} -> {_|-> x}B -β>* B' -> ctor A B -β>* ctor A ({_<-| x}B')) ->
--     ((x : Name) -> x ∉ S -> (s : _) ->
--       erase ({_|-> x}B) -β> s ->
--       ∃ k, {_|-> x}B -β>* k ∧ erase k = s) ->
--     ((x : Name) -> x ∉ S' -> {_|-> x}erase B -β> {_|-> x}B') ->
--     ∃ k, ctor A B -β>* k ∧ erase k = ctor (erase A) B'
--   := by {
--     intros ctor ctore ctorr ih step
--     have xfresh := @Name.fresh_is_fresh (S ++ S')
--     let x := Name.fresh (S ++ S')
--     have xe : Name.fresh (S ++ S') = x := by simp
--     have xn1 : x ∉ S := FvSet.not_mem_left xfresh
--     have xn2 : x ∉ S' := FvSet.not_mem_right xfresh
--     have step := step x xn2
--     have step := red_open_erase step
--     have lem := ih x xn1 ({_|-> x}B') step
--     casesm* ∃ _ , _ , _ ∧ _
--     case _ k kstep e => {
--       exists (ctor A ({_<-| x}k)); simp [*]
--       have e2 := erase_close_open e
--       rewrite [e2]
--       rfl
--     }
--   }

--   lemma object_red_to_proof_red_step_app_case :
--     Γ ⊢ a =: A ->
--     ((s : _) -> erase f -β> s -> ∃ k, f -β>* k ∧ erase k = s) ->
--     ((s : _) -> erase a -β> s -> ∃ k, a -β>* k ∧ erase k = s) ->
--     (s : _) ->
--     Γ ⊢ f >: pi mf A B ->
--     erase (f @ω a) -β> s ->
--     ∃ k, f @ω a -β>* k ∧ erase k = s
--   := by {
--     intros _ ih1 ih2 s j2 step
--     simp at step
--     refine (@Red.rec
--       (λ x y _ => x = erase f @ω erase a -> y = s -> ∃ k, f @ω a -β>* k ∧ erase k = y)
--       ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
--       (erase f @ω erase a) s step rfl rfl
--     ) <;> intros <;> intros <;> simp at *
--     case _ m t1 t2 t3 e1 e2 => {
--       cases m <;> simp at e1
--       injection e1 with _ _ h1 h2 _
--       have h1 := erase_forces_lam_mf (symm h1)
--       casesm* ∃ _, _, _ ∧ _
--       case _ t1' t2' t1e t2e fe => {
--         have step2 : f @ω a -β> [_:= a]t2' := by subst fe; apply Red.beta
--         rewrite [fe] at step; simp at step
--         cases step
--         case beta => {
--           exists ([_:= a]t2'); simp [*]
--           rewrite [fe] at step2
--           apply (RedStar.step step2 RedStar.refl)
--         }
--         case ctor1 s step => {
--           rewrite [e2]; simp at *
--           rewrite [fe] at ih1; simp at ih1
--           have lem := ih1 s step
--           casesm* ∃ _, _, _ ∧ _
--           case _ k kstep ke =>
--           rewrite [<-fe] at kstep; simp
--           exists (k @ω a); simp [*]; rewrite [<-fe]
--           apply (red_app1 kstep)
--         }
--         case ctor2 s step => {
--           rewrite [e2]; simp at *
--           have lem := ih2 s step
--           casesm* ∃ _, _, _ ∧ _
--           case _ k kstep ke =>
--           exists (f @ω k); simp; rewrite [fe, ke]; simp; rewrite [<-fe]
--           apply (red_app2 kstep)
--         }
--         case ctor3 s step => cases step
--       }
--     }
--     case _ t1 t2 t3 t4 t5 t6 e1 _e2 => {
--       injection e1 with _ _ e1 e3 _
--       have lem := erase_no_eqind (symm e1)
--       contradiction
--     }
--     case _ t1 t1' c t2 t2' step _ e1 _e2 => {
--       injection e1 with _ ce t1e t2e t2'e; rewrite [ce, t2e, t2'e]; simp
--       have lem := ih1 t1' (by subst t1e; apply step)
--       casesm* ∃ _, _, _ ∧ _
--       case _ k kstep ke =>
--       exists (k @ω a); simp [*]
--       apply (red_app1 kstep)
--     }
--     case _ t1 t1' c t2 t2' step _ e1 _e2 => {
--       injection e1 with _ ce t1e t2e t2'e; rewrite [ce, t1e, t2'e]; simp
--       have lem := ih2 t1' (by subst t2e; apply step)
--       casesm* ∃ _, _, _ ∧ _
--       case _ k kstep ke =>
--       exists (f @ω k); simp [*]
--       apply (red_app2 kstep)
--     }
--     case _ t1 t1' c t2 t2' step _ e1 _e2 => {
--       injection e1 with _ _ _ _ e; subst e; cases step
--     }
--   }

--   lemma object_red_to_proof_red_step_tapp_case :
--     Γ ⊢ a =: A ->
--     ((s : _) -> erase f -β> s -> ∃ k, f -β>* k ∧ erase k = s) ->
--     ((s : _) -> erase a -β> s -> ∃ k, a -β>* k ∧ erase k = s) ->
--     (s : _) ->
--     Γ ⊢ f >: pi mt A B ->
--     erase (f @τ a) -β> s ->
--     ∃ k, f @τ a -β>* k ∧ erase k = s
--   := by {
--     intros _ ih1 ih2 s j2 step
--     simp at step
--     refine (@Red.rec
--       (λ x y _ => x = erase f @τ erase a -> y = s -> ∃ k, f @τ a -β>* k ∧ erase k = y)
--       ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
--       (erase f @τ erase a) s step rfl rfl
--     ) <;> intros <;> intros <;> simp at *
--     case _ m t1 t2 t3 e1 e2 => {
--       cases m; simp at e1
--       have lem := app_m0_not_app_mt e1; contradiction
--       injection e1 with _ _ h1 h2 _
--       have h1 := erase_forces_lam_mt (symm h1)
--       casesm* ∃ _, _, _ ∧ _
--       case _ t1' t2' t1e t2e fe => {
--         have step2 : f @τ a -β> [_:= a]t2' := by subst fe; apply Red.beta
--         rewrite [fe] at step; simp at step
--         cases step
--         case beta => {
--           exists ([_:= a]t2'); simp [*]
--           rewrite [fe] at step2
--           apply (RedStar.step step2 RedStar.refl)
--         }
--         case ctor1 s step => {
--           rewrite [e2]; simp at *
--           rewrite [fe] at ih1; simp at ih1
--           have lem := ih1 s step
--           casesm* ∃ _, _, _ ∧ _
--           case _ k kstep ke =>
--           rewrite [<-fe] at kstep; simp
--           exists (k @τ a); simp [*]; rewrite [<-fe]
--           apply (red_app1 kstep)
--         }
--         case ctor2 s step => {
--           rewrite [e2]; simp at *
--           have lem := ih2 s step
--           casesm* ∃ _, _, _ ∧ _
--           case _ k kstep ke =>
--           exists (f @τ k); simp; rewrite [fe, ke]; simp; rewrite [<-fe]
--           apply (red_app2 kstep)
--         }
--         case ctor3 s step => cases step
--       }
--     }
--     case _ t1 t1' c t2 t2' step _ e1 _e2 => {
--       injection e1 with _ ce t1e t2e t2'e; rewrite [ce, t2e, t2'e]; simp
--       have lem := ih1 t1' (by subst t1e; apply step)
--       casesm* ∃ _, _, _ ∧ _
--       case _ k kstep ke =>
--       exists (k @τ a); simp [*]
--       apply (red_app1 kstep)
--     }
--     case _ t1 t1' c t2 t2' step _ e1 _e2 => {
--       injection e1 with _ ce t1e t2e t2'e; rewrite [ce, t1e, t2'e]; simp
--       have lem := ih2 t1' (by subst t2e; apply step)
--       casesm* ∃ _, _, _ ∧ _
--       case _ k kstep ke =>
--       exists (f @τ k); simp [*]
--       apply (red_app2 kstep)
--     }
--     case _ t1 t1' c t2 t2' step _ e1 _e2 => {
--       injection e1 with _ _ _ _ e; subst e; cases step
--     }
--   }

--   lemma object_red_to_proof_red_step_elam_case {S : FvSet} :
--     Γ ⊢ A >: const K ->
--     ((x : Name) -> x ∉ S -> (Γ ++ [x:A]) ⊢ {_|-> x}t : {_|-> x}B) ->
--     ((s : _) -> erase A -β> s → ∃ k, A -β>* k ∧ erase k = s) ->
--     ((x : Name) -> ¬x ∈ S → (s : _) ->
--       erase ({_|-> x}t) -β> s ->
--       ∃ k, {_|-> x}t -β>* k ∧ erase k = s) ->
--     (s : _) ->
--     ((x : Name) -> x ∉ fv t -> x ∉ (fv ∘ erase) ({_|-> x}t)) ->
--     (erase (lam m0 A t) -β> s) ->
--     ∃ k, lam m0 A t -β>* k ∧ erase k = s
--   := by {
--     intros j1 j2 ih1 ih2 s ih3 step
--     simp at step
--     let x := Name.fresh ((fv t) ++ S)
--     have xe : Name.fresh ((fv t) ++ S) = x := by simp
--     have xfresh := @Name.fresh_is_fresh ((fv t) ++ S)
--     have xn1 := FvSet.not_mem_right xfresh
--     have xn2 := FvSet.not_mem_left xfresh
--     have fn := ih3 (Name.fresh (fv t)) Name.fresh_is_fresh
--     have lem := erase_free_invariant fn x xn2
--     rewrite [lem] at step
--     have lem := ih2 x xn1 s step
--     casesm* ∃ _, _, _ ∧ _
--     case _ k kstep ke =>
--     exists (lam m0 A ({_<-| x}k)); simp; rewrite [xe]
--     generalize ydef : Name.fresh (fv ({_<-| x}k)) = y
--     have fn2 : y ∉ (fv ∘ erase) ({_|-> y}{_<-| x}k) := sorry
--     have xn3 : x ∉ fv ({_<-| x}k) := sorry
--     have e2 := erase_free_invariant fn2 x xn3; simp at e2
--     rewrite [e2]; simp [*]
--     apply (red_lam2 kstep)
--   }

-- this + proof normalization gives object normalization
-- |t| ->  s0  ->  s1  ->  s2  -> ...
--  =      =       =       =
--  t ->+  k0 ->+  k1 ->+  k2 ->+ ...
-- Every step in the erased sequence can be matched below with a proof step
-- but the proof step must be terminating, so if you assume the erased
-- reduction is infinite you arrive at a contradiction

  theorem object_red_to_proof_red_step (S : FvSet!) :
    Γ ⊢ t : A ->
    (∀ x, x ∉ S -> (erase x t) -β> s) ->
    ∃ k, t -β>+ k ∧ (∀ x, x ∉ S -> (erase x k) = s)
  := λ j step => @Infer.rec
    (λ Γ t A _ => ∀ s,
      (∀ x, x ∉ S -> (erase x t) -β> s) ->
      ∃ k, t -β>+ k ∧ (∀ x, x ∉ S -> (erase x k) = s))
    (λ Γ t A _ => ∀ s,
      (∀ x, x ∉ S -> (erase x t) -β> s) ->
      ∃ k, t -β>+ k ∧ (∀ x, x ∉ S -> (erase x k) = s))
    (λ Γ t A _ => ∀ s,
      (∀ x, x ∉ S -> (erase x t) -β> s) ->
      ∃ k, t -β>+ k ∧ (∀ x, x ∉ S -> (erase x k) = s))
    (λ Γ _ => True)
    (by {
      intro Γ wf _ s step
      have xfresh := @Name.fresh_is_fresh S
      generalize Name.fresh S = x at *
      cases (step x xfresh)
    })
    (by {
      intro Γ x A wf xin _ s step
      have xfresh := @Name.fresh_is_fresh S
      generalize Name.fresh S = x at *
      cases (step x xfresh)
    })
    sorry
    sorry
    (by {
      intro Γ f m A B a S2 j1 j2 ih1 ih2 s step
      sorry
    })
    sorry
    sorry
    (by {
      intro Γ t A B j ih s step
      simp at step
      have lem := ih s step
      casesm* ∃ _, _, _ ∧ _
      case _ w1 s1 w2 s2 s3 =>
      exists (fst w1)
      apply And.intro _ _
      exists (fst w2)
      apply And.intro _ _
      apply Red.ctor1 s2
      apply red_ctor1 s3
      simp; apply s1
    })
    sorry
    sorry
    sorry
    (by {
      intro Γ A P x y r w j1 j2 j3 j4 j5 j6 ih1 ih2 ih3 ih4 ih5 ih6 s step
      simp at step
      -- either r -> r' or w -> w' (strucutral, easy)
      -- or r looks like a lambda, but this means it is refl, so it must be identity
      -- thus you perform the J reduction, followed by potentially a w -> w'
      sorry
    })
    sorry
    (by {
      intro Γ b A B a e S2 j1 j2 j3 f1 f2 ih1 ih2 ih3 s step
      simp at step
      have lem := ih2 s step
      casesm* ∃ _, _, _ ∧ _
      case _ w1 s1 w2 s2 s3 =>
      exists (phi w1 b e)
      apply And.intro _ _
      exists (phi w2 b e)
      apply And.intro _ _
      apply Red.ctor1 s2
      apply red_ctor1 s3
      simp; apply s1
    })
    (by {
      intro Γ e a ih s step
      simp at step
      have lem := ih s step
      casesm* ∃ _, _, _ ∧ _
      case _ w1 e1 w2 s1 s2 =>
      exists (delta w1)
      apply And.intro _ _
      exists (delta w2)
      apply And.intro _ _
      apply Red.ctor1 s1
      apply red_ctor1 s2
      simp; apply e1
    })
    (by {
      intro Γ t A B j s1 ih s s2
      apply ih s s2
    })
    (by {
      intro Γ t A B K j1 j2 c1 ih1 ih2 s step
      apply ih1 s step
    })
    (by simp)
    (by simp)
    Γ
    t
    A
    j
    s
    step
    


--   lemma object_red_to_proof_red :
--     Γ ⊢ t : A ->
--     (erase t) -β>* s ->
--     ∃ k, t -β>* k ∧ (erase k) = s
--   := λ j step => @RedStar.rec
--     (λ a b _ => (A t : _) -> erase t = a -> Γ ⊢ t : A -> ∃ k, t -β>* k ∧ (erase k) = b)
--     (by {
--       intros a _A t e _
--       exists t; simp [*]
--       apply RedStar.refl
--     })
--     (by {
--       intros a b c step _ ih A t e j
--       subst e
--       have lem1 := object_red_to_proof_red_step j step
--       casesm* ∃ _, _, _ ∧ _
--       case _ k kstep ke =>
--       have j2 := preservation (infer_implies_check j) kstep
--       cases j2
--       case check D j2 e2 =>
--       have lem2 := ih D k ke j2
--       casesm* ∃ _, _, _ ∧ _
--       case _ k2 k2step k2e =>
--       exists k2; simp [*]
--       apply (RedStar.transitive kstep k2step)
--     })
--     (erase t)
--     s
--     step
--     A
--     t
--     rfl
--     j

--   theorem object_conv :
--     Γ ⊢ t : A ->
--     Γ ⊢ s : B ->
--     (erase t) =β= (erase s) ->
--     t =β= s
--   := by {
--     intros j1 j2 e
--     cases e
--     case conv t1 t2 r1 e r2 =>
--     have lem1 := object_red_to_proof_red j1 r1
--     have lem2 := object_red_to_proof_red j2 r2
--     casesm* ∃ _ , _, _ ∧ _
--     case _ k1 k2 r1' e1 r2' e2 =>
--     subst e1 e2
--     simp at e -- idempotency of erasure
--     apply (Conv.conv r1' r2' e)
--   }

end Cedille
