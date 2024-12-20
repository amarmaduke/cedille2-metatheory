
import Common
import Fomega.Proof

namespace Fomega

  theorem ctx_wf : Γ ⊢ t : A -> ∃ (f:Nat -> Const), ∀ x, Γ ⊢ (Γ d@ x) : (.const (f x)) := by
  intro j
  induction j
  all_goals (try (case _ ih => apply ih))
  all_goals (try (case _ ih _ => apply ih))
  case ax f h _ => exists f

  inductive IsPreProof : Term -> Prop where
  | ax : IsPreProof (.const K)
  | bound : IsPreProof (.bound K x)
  | all : IsPreProof A -> IsPreProof B -> IsPreProof (.all mf A B)
  | lam : IsPreProof A -> IsPreProof t -> IsPreProof (.lam mf A t)
  | app : IsPreProof f -> IsPreProof a -> IsPreProof (.app mf f a)
  | conv : IsPreProof B -> IsPreProof t -> IsPreProof (.conv 0 B t)

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
    intro j; induction j
    case ax => constructor
    case var => constructor
    case pi _j1 _j2 ih1 ih2 => constructor <;> simp [*]
    case tpi => constructor <;> simp [*]
    case lam j1 _j2 ih1 ih2 => constructor; cases ih1; all_goals simp [*]
    case app => constructor <;> simp [*]
    case econv => constructor <;> simp [*]
    case iconv => simp [*]

    theorem from_proof_type : t ⊢ Γ -> Γ ⊢ t : A -> IsPreProof A := by
    intro h j; induction j
    case ax => constructor
    case var =>
      cases h
      case _ h => apply (from_proof h)
    case pi => constructor
    case tpi => constructor
    case lam j _ _ _ => apply from_proof j
    case app _j1 j2 j3 ih1 _ih2 =>
      cases h
      case _ h1 h2 =>
        cases (ih1 h1)
        case _ p1 p2 =>
        subst j3; apply beta p2 (from_proof j2)
    case econv j _ _ _ => apply from_proof j
    case iconv j _ _ _ => apply from_proof j

  end IsPreProof

end Fomega
