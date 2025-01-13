
import Common
import Fomega.Proof

namespace Fomega

  theorem judgment_ctx_wf : Judgment v Γ idx -> ⊢ Γ := by
  intro j
  induction j
  case nil => constructor
  case cons j1 j2 _ _ => constructor; apply j1; apply j2
  all_goals try simp [*]

  inductive IsPreProof : Term -> Prop where
  | ax : IsPreProof (.const K)
  | bound : IsPreProof (.bound K x)
  | all : IsPreProof A -> IsPreProof B -> IsPreProof (.all mf A B)
  | lam : IsPreProof A -> IsPreProof t -> IsPreProof (.lam mf A t)
  | app : IsPreProof f -> IsPreProof a -> IsPreProof (.app mf f a)
  | times : IsPreProof A -> IsPreProof B -> IsPreProof (.times A B)
  | pair : IsPreProof a -> IsPreProof b -> IsPreProof (.pair a b)
  | fst : IsPreProof t -> IsPreProof (.fst t)
  | snd : IsPreProof t -> IsPreProof (.snd t)
  | unit_ty : IsPreProof .unit_ty
  | unit : IsPreProof .unit
  | unit_rec : IsPreProof t1 -> IsPreProof t2 -> IsPreProof (.unit_rec t1 t2)

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
    case _ ih j => constructor; apply ih j
    case _ ih j => constructor; apply ih j
    case _ ih1 ih2 j1 j2 =>
      constructor; apply ih1 j1; apply ih2 j2
    case _ => constructor
    case _ => constructor
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
    case times ih1 ih2 =>
      constructor; apply ih1; apply ih2
    case pair ih1 ih2 =>
      constructor; apply ih1; apply ih2
    case fst ih => constructor; apply ih
    case snd ih => constructor; apply ih
    case unit => constructor
    case unit_ty => constructor
    case unit_rec ih1 ih2 =>
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
    case times ih1 ih2 =>
      constructor; apply ih1 h; apply ih2 h
    case pair ih1 ih2 =>
      constructor; apply ih1 h; apply ih2 h
    case fst ih => constructor; apply ih h
    case snd ih => constructor; apply ih h
    case unit => constructor
    case unit_ty => constructor
    case unit_rec ih1 ih2 =>
      constructor; apply ih1 h; apply ih2 h

    theorem beta : IsPreProof b -> IsPreProof t -> IsPreProof (b β[t]) := by
    simp; intro j1 j2
    apply subst
    case _ =>
      intro n s eq
      cases n <;> simp at *
      subst eq; exact j2
    case _ => exact j1

    @[simp]
    abbrev FromProofType : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
    | .prf => λ (t, _) => IsPreProof t
    | .wf => λ () => True

    theorem from_proof : Judgment v Γ ix -> FromProofType v ix := by
    intro j; induction j <;> simp at *
    all_goals (try (constructor <;> simp [*]))
    case conv => simp [*]

    -- theorem from_proof_type : t ⊢ Γ -> Γ ⊢ t : A -> IsPreProof A := by
    -- intro h j; induction j
    -- case ax => constructor
    -- case var =>
    --   cases h
    --   case _ h => apply (from_proof h)
    -- case pi => constructor
    -- case tpi => constructor
    -- case lam j _ _ _ => apply from_proof j
    -- case app _j1 j2 j3 ih1 _ih2 =>
    --   cases h
    --   case _ h1 h2 =>
    --     cases (ih1 h1)
    --     case _ p1 p2 =>
    --     subst j3; apply beta p2 (from_proof j2)
    -- case econv j _ _ _ => apply from_proof j
    -- case iconv j _ _ _ => apply from_proof j

  end IsPreProof

end Fomega
