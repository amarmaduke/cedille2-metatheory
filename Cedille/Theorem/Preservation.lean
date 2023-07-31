
import Cedille.Def
import Cedille.Lemma

namespace Cedille

  lemma preservation_ctx {A : Term} :
    (Γ ++ [x : A]) ⊢ t >: B ->
    A -β> A' ->
    (Γ ++ [x : A']) ⊢ t >: B
  := sorry

  lemma preservation_subst :
    Γ ⊢ t =: [_:= s]A ->
    s -β> s' ->
    Γ ⊢ t =: [_:= s']A
  := sorry

  lemma preservation_check_type :
    Γ ⊢ t =: A ->
    A =β= B ->
    Γ ⊢ t =: B
  := sorry


  -- lemma preservation_cinfer_type :
  --   Γ ⊢ t >: A ->
  --   A -β> A' ->
  --   Γ ⊢ t >: A'
  -- := sorry

  theorem preservation_step : Γ ⊢ t =: A -> t -β> s -> Γ ⊢ s =: A
  := λ j step => @Check.rec
    (λ Γ t A j => (s : _) -> t -β> s -> Γ ⊢ s =: A)
    (λ Γ t A j => (s : _) -> t -β> s -> Γ ⊢ s =: A)
    (λ Γ t A j => (s : _) -> t -β> s -> Γ ⊢ s =: A)
    (λ Γ j => True)
    (by {
      intros Γ wf ih s step; cases step
    })
    (by {
      intros Γ Γ1 x Γ2 A wf e ih s step
      cases step
    })
    (by {
      intros Γ A m K B S j1 j2 ih1 ih2 s step; simp at ih2
      cases step <;> simp
      case bind1 A' step => {
        cases (ih1 A' step); case _ D j e =>
        
        apply infer_implies_check _
        apply Infer.pi (ih1 A' step) _
        exact S
        intros x xn
        have lem := j2 x xn
        apply preservation_ctx lem step
      }
      case bind2 B' S' step => {
        apply infer_implies_check _
        apply Infer.pi j1 _
        exact (S ++ S')
        intros x xn
        have xn1 := FvSet.not_mem_right xn
        have xn2 := FvSet.not_mem_left xn
        replace step := step x xn1
        apply ih2 x xn2 ({_|-> x}B') step
      }
    })
    (by {
      intros Γ A K t B m S j1 j2 j3 ih1 ih2 s step; simp at *
      cases step <;> simp
      case bind1 A' step => {
        have fresh := @Name.fresh_is_fresh (S ++ Map.fv Γ ++ fv A')
        have xn1 := FvSet.not_mem_left fresh
        have xn2 := FvSet.not_mem_left xn1
        have xn3 := FvSet.not_mem_right xn1
        have xn4 := FvSet.not_mem_right fresh
        generalize h : Name.fresh (S ++ Map.fv Γ ++ fv A') = x at *
        have lem1 := ih1 A' step
        have lem2 := preservation_ctx (infer_implies_cinfer (j2 x xn2)) step
        cases lem2
        case _ D j4 step2 =>
        apply (Check.check _ _); exact (pi m A' ({_<-| x}D))
        apply (Infer.lam lem1 _ j3); exact (Map.fv (Γ ++ [x:A']) ++ fv ({_|-> x}t) ++ fv D)
        intros y yn
        have lem2 := rename_infer x j4 yn; simp at lem2
        rewrite [rename_term_invariant y xn4] at lem2
        rewrite [rename_ctx_invariant y xn3] at lem2; exact lem2
        replace step2 := red_open_close step2
        apply Conv.pi.1 _; apply And.intro _ _
        apply Conv.red_ff Conv.refl (RedStar.step step RedStar.refl) RedStar.refl
        apply Conv.red_ff Conv.refl RedStar.refl step2
      }
      case bind2 B' S' step => {

        sorry
      }
    })
    sorry
    (by {
      -- almost exactly the same as pi case
      intros Γ A B S j1 j2 ih1 ih2 s step; simp at ih2
      cases step <;> simp
      case bind1 A' step => {
        apply infer_implies_cinfer _
        apply Infer.inter (ih1 A' step) _
        exact S
        intros x xn
        have lem := j2 x xn
        apply preservation_ctx lem step
      }
      case bind2 B' S' step => {
        apply infer_implies_cinfer _
        apply Infer.inter j1 _
        exact (S ++ S')
        intros x xn
        have xn1 := FvSet.not_mem_right xn
        have xn2 := FvSet.not_mem_left xn
        replace step := step x xn1
        apply ih2 x xn2 ({_|-> x}B') step
      }
    })
    (by {
      intros Γ T A B t s j1 j2 j3 e ih1 ih2 ih3 s' step
      cases step <;> simp
      case ctor1 t' step => {
        apply Check.check _ _; exact inter A B
        apply Infer.pair j1 (ih2 t' step) _ _
        apply preservation_subst j3 step
        apply Conv.red_ff e (RedStar.step step RedStar.refl) RedStar.refl
        apply Conv.refl
      }
      case ctor2 s' step => {
        apply Check.check _ _; exact inter A B
        apply Infer.pair j1 j2 (ih3 s' step) _
        apply Conv.red_ff e RedStar.refl (RedStar.step step RedStar.refl)
        apply Conv.refl
      }
      case ctor3 T' step => {
        apply Check.check _ _; exact inter A B
        apply Infer.pair (ih1 T' step) j2 j3 e
        apply Conv.refl
      }
    })
    (by {
      intros Γ t A B j ih s step
      cases step <;> simp
      case fst t T => {
        cases j; case infer D j step =>
        cases j; case pair A' B' j1 e j2 j3 =>
        have lem : inter A' B' =β= inter A B :=
          Conv.red_bb Conv.refl step RedStar.refl
        have lem := (Conv.inter.2 lem).1
        cases j1; case _ D j e2 =>
        apply Check.check j _
        apply Conv.trans e2 lem
      }
      case ctor1 t' step => {
        apply Check.check _ _; exact A
        apply Infer.fst _; exact B
        apply ih t' step
        apply Conv.refl
      }
      case ctor2 step => cases step
      case ctor3 step => cases step
    })
    (by {
      intros Γ t A B j ih s step
      cases step <;> simp
      case snd t T => {
        cases j; case _ D j step =>
        cases j; case _ A' B' j1 e j2 j3 =>
        have lem := Conv.red_bb Conv.refl step RedStar.refl
        have lem := (Conv.inter.2 lem).2
        cases j2; case _ D j e2 =>
        apply Check.check j _
        apply Conv.subst1.1 _; exact t; apply And.intro _ _
        apply Conv.conv _ _ _; exact t; exact t
        apply RedStar.refl; apply (RedStar.step Red.fst RedStar.refl); simp
        apply Conv.trans e2 _
        apply Conv.subst.1 _
        apply And.intro Conv.refl lem
      }
      case ctor1 t' step => {
        apply Check.check _ _; exact ([_:= fst t']B)
        apply Infer.snd _; exact A
        apply ih t' step
        apply Conv.subst.1 _; apply And.intro _ _
        have lem : t' =β= t :=
          Conv.red_ff Conv.refl (RedStar.step step RedStar.refl) RedStar.refl
        apply Conv.fst.1 lem
        apply Conv.refl
      }
      case ctor2 step => cases step
      case ctor3 step => cases step
    })
    (by {
      intros Γ a A b j1 j2 ih1 ih2 s step
      cases step <;> simp
      case ctor1 a' step => {
        sorry
        -- apply Check.check _ _; exact typeu
        -- have lem := ih1 a' step
        -- cases lem; case _ D j1 e => {
        --   apply Infer.eq j1 _
        --   apply preservation_check_type j2 (Conv.symm e)
        -- }
        -- apply Conv.refl
      }
      case ctor2 b' step => {
        sorry
        -- apply Check.check _ _; exact typeu
        -- apply Infer.eq j1 _
        -- apply ih2 b' step
        -- apply Conv.refl
      }
      case ctor3 step => sorry
    })
    (by {
      intros Γ t A j ih s step
      cases step <;> simp
      case ctor1 t' step => {
        sorry
        -- apply Check.check _ _; exact eq t' t'
        -- have lem := ih t' step
        -- cases lem; case _ D j e => apply Infer.refl j
        -- have e : t' =β= t := 
        --   Conv.conv RedStar.refl (RedStar.step step RedStar.refl) rfl
        -- apply Conv.eq.1 (And.intro e e)
      }
      case ctor2 step => cases step
      case ctor3 step => cases step
    })
    sorry
    sorry
    sorry
    (by {
      intros Γ r A a b j e ih s step
      cases step <;> simp
      case delta t => {
        unfold idt
        cases j; case _ _ j _=>
        have wf := infer_implies_wf j
        apply Check.check _ Conv.refl
        apply Infer.lam _ _ _; exact Constant.kindU; exact Map.fv Γ
        apply ConInfer.infer (Infer.ax wf) RedStar.refl
        intros x xn; simp
        apply Infer.lam _ _ _; exact Constant.typeU; exact (Map.fv Γ ++ [x])
        apply ConInfer.infer _ RedStar.refl
        apply @Infer.var (Γ ++ [x:typeu]) Γ x [] typeu _ _
        apply @Wf.append x Γ typeu Constant.kindU xn wf
        apply ConInfer.infer (Infer.ax wf) RedStar.refl; simp
        intros y yn; simp; rewrite [<-List.append_assoc]
        apply @Infer.var (Γ ++ [x:typeu] ++ [y:free x]) (Γ ++ [x:typeu]) y [] (free x) _ _
        have lem := @Wf.append x Γ typeu Constant.kindU xn wf
          (ConInfer.infer (Infer.ax wf) RedStar.refl)
        apply Wf.append _ _ _; exact Constant.typeU
        rewrite [Map.fv_append, Map.fv_single]; exact yn; exact lem
        apply ConInfer.infer _ RedStar.refl
        apply @Infer.var (Γ ++ [x:typeu]) Γ x [] typeu _ _; exact lem; simp; simp
        intros f; contradiction
        intros _ x xn; simp
      }
      case ctor1 r' step => {
        have lem := ih r' step
        apply Check.check _ Conv.refl
        apply Infer.deltatop lem e
      }
      case ctor2 step => cases step
      case ctor3 step => cases step
    })
    (by {
      intros Γ e j ih s step
      cases step <;> simp
      case ctor1 e' step => {
        have lem := ih e' step
        apply Check.check _ Conv.refl
        apply Infer.deltabot lem
      }
      case ctor2 step => cases step
      case ctor3 step => cases step
    })
    (by {
      intros Γ t A B j step ih s step2
      have lem := ih s step2
      cases lem; case _ D j2 e =>
      have lem : A =β= B := Conv.red_b Conv.refl step
      have e := Conv.trans e lem
      apply Check.check j2 e
    })
    (by {
      intros Γ t A B j e ih s step
      have lem := ih s step
      cases lem; case _ D j2 step =>
      have lem2 := Conv.trans step e
      apply Check.check j2 lem2
    })
    (by simp)
    (by simp)
    Γ
    t
    A
    j
    s
    step

  theorem preservation : Γ ⊢ t =: A -> t -β>* s -> Γ ⊢ s =: A := sorry

end Cedille
