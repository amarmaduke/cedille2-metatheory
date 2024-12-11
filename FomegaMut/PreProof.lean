
import Common
import FomegaMut.Proof

namespace FomegaMut

  theorem wf_switch_dummy : Jud .wf Γ t x -> Jud .wf Γ t ξ := by
  intro j
  generalize tydef : JudKind.wf = ty at j
  induction j <;> cases tydef
  all_goals (try simp at *; constructor <;> simp [*])
  case wf_ax h ih => constructor; apply h

  theorem proof_is_wf : Γ ⊢ t : A -> t ⊢ Γ := by
  intro j
  generalize tydef : JudKind.prf = ty at j
  induction j <;> cases tydef
  all_goals (try simp at *)
  case ax h _ =>
    cases h
    case _ f h =>
      constructor; apply h
  case var h _ => apply wf_switch_dummy; apply h
  case pi ih1 ih2 => constructor; apply ih1; apply ih2
  case tpi ih1 ih2 => constructor; apply ih1; apply ih2
  case lam ih1 ih2 =>
    replace ih1 := ih1
    cases ih1
    case _ cj1 cj2 =>
      constructor; apply cj1; apply ih2
  case app ih1 ih2 => constructor; apply ih1; apply ih2
  case econv ih1 ih2 => constructor; apply ih2; apply ih1
  case iconv ih1 _ih2 => apply ih1

  theorem ctx_wf : Jud jk Γ t A -> ∃ (f:Nat -> Const), ∀ x, Γ ⊢ (Γ d@ x) : (.const (f x)) := by
  intro j
  induction j
  all_goals (try (case _ ih => apply ih))
  all_goals (try (case _ ih _ => apply ih))
  case wf_ax f h _ => exists f

  theorem var_wf : Jud jk Γ (.bound K x) A -> Γ ⊢ (Γ d@ x) : .const K := by
  intro j
  generalize tdef : Term.bound K x = t at j
  induction j <;> cases tdef
  all_goals (try simp at *)
  case wf_var h => apply h
  case var ih => apply ih
  case iconv ih => apply ih

  -- theorem wf_is_proof : (.bound K x) ⊢ Γ -> Γ ⊢ t : A := by
  -- intro j
  -- generalize tydef : JudKind.wf = ty at j
  -- generalize Tdef : Term.none = T at j
  -- induction j <;> cases tydef
  -- all_goals (try subst Tdef; simp at *)
  -- case wf_ax => exists □; constructor
  -- case wf_var Γ x K h _ =>
  --   exists (Γ d@ x); constructor
  --   constructor; apply h; apply Term.none
  -- case wf_pi ih1 ih2 =>
  -- case wf_lam => sorry
  -- case wf_app => sorry
  -- case wf_conv => sorry


  inductive IsPreProof : Term -> Prop where
  | ax : IsPreProof (.const K)
  | bound : IsPreProof (.bound K x)
  | all : IsPreProof A -> IsPreProof B -> IsPreProof (.all mf A B)
  | lam : IsPreProof A -> IsPreProof t -> IsPreProof (.lam mf A t)
  | app : IsPreProof f -> IsPreProof a -> IsPreProof (.app mf f a)
  | conv : IsPreProof B -> IsPreProof t -> IsPreProof (.conv B t 0)

  namespace IsPreProof
    theorem from_subst : IsPreProof ([σ]t) -> IsPreProof t := by
    intro j
    induction t generalizing σ <;> (try (simp at j; cases j))
    case bound K x => constructor
    case _ => constructor
    case _ ih1 ih2 j1 j2 =>
      constructor; apply ih1 j1; apply ih2 j2
    case _ ih1 ih2 j1 j2 =>
      constructor; apply ih1 j1; apply ih2 j2
    case _ ih1 ih2 j1 j2 =>
      constructor; apply ih1 j1; apply ih2 j2
    case _ ih1 ih2 j1 j2 =>
      constructor; apply ih1 j1; apply ih2 j2

    theorem ren : IsPreProof t -> IsPreProof ([r#r]t) := by
    intro j
    induction j generalizing r <;> simp
    case ax => constructor
    case bound => constructor
    case all _j1 _j2 ih1 ih2 =>
      constructor; apply ih1
      replace ih2 := @ih2 (Term.Ren.lift r)
      simp at ih2; exact ih2
    case lam _j1 _j2 ih1 ih2 =>
      constructor; apply ih1
      replace ih2 := @ih2 (Term.Ren.lift r)
      simp at ih2; exact ih2
    case app _j1 _j2 ih1 ih2 =>
      constructor; apply ih1; apply ih2
    case conv _j1 _j2 ih1 ih2 =>
      constructor; apply ih1; apply ih2

    theorem lift : (∀ n s, σ n = .replace s -> IsPreProof s) -> ∀ n s, ^σ n = .replace s -> IsPreProof s := by
    intro h n s eq; simp at *
    cases n <;> simp at eq
    case _ n =>
      unfold Term.Subst.compose at eq; simp at eq
      generalize xdef : σ n = x at *
      cases x <;> simp at *
      case _ t =>
        subst eq
        replace h := h n t xdef
        apply ren h

    theorem subst : (∀ n s, σ n = .replace s -> IsPreProof s) -> IsPreProof t -> IsPreProof ([σ]t) := by
    intro h j
    induction j generalizing σ <;> simp
    case ax => constructor
    case bound K n =>
      generalize xdef : σ n = x at *
      cases x <;> simp
      case _ => constructor
      case _ t => apply h n t xdef
    case all _j1 _j2 ih1 ih2 =>
      constructor; apply ih1 h
      replace ih2 := @ih2 (^σ) (lift h)
      simp at ih2; exact ih2
    case lam _j1 _j2 ih1 ih2 =>
      constructor; apply ih1 h
      replace ih2 := @ih2 (^σ) (lift h)
      simp at ih2; exact ih2
    case app _j1 _j2 ih1 ih2 =>
      constructor; apply ih1 h; apply ih2 h
    case conv _j1 _j2 ih1 ih2 =>
      constructor; apply ih1 h; apply ih2 h

    theorem beta : IsPreProof b -> IsPreProof t -> IsPreProof (b β[t]) := by
    simp; intro j1 j2
    apply subst
    case _ =>
      intro n s eq
      cases n <;> simp at *
      subst eq; exact j2
    case _ => exact j1

    theorem from_proof : Γ ⊢ t : A -> IsPreProof t := by
    intro j;
    generalize tydef : JudKind.prf = ty at j
    induction j <;> cases tydef
    all_goals (try simp at *)
    case ax => constructor
    case var => constructor
    case pi _j1 _j2 ih1 ih2 => constructor <;> simp [*]
    case tpi => constructor <;> simp [*]
    case lam _j1 _j2 ih1 ih2 => constructor; cases ih1; all_goals simp [*]
    case app => constructor <;> simp [*]
    case econv => constructor <;> simp [*]
    case iconv => simp [*]

    theorem from_proof_type : Γ ⊢ t : A -> IsPreProof A := by
    intro j
    generalize tydef : JudKind.prf = ty at j
    induction j <;> cases tydef
    all_goals (try simp at *)
    case ax => constructor
    case var h _ =>
      cases h
      case _ h2 => apply from_proof h2
    case pi => constructor
    case tpi => constructor
    case lam j _ _ _ => apply from_proof j
    case app _j1 j2 j3 ih1 _ih2 =>
      cases ih1
      case _ cj1 cj2 =>
        subst j3; apply beta; apply cj2
        apply from_proof j2
    case econv j _ _ _ => apply from_proof j
    case iconv j _ _ _ => apply from_proof j

  end IsPreProof

end FomegaMut
