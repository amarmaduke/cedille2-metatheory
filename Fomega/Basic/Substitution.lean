
import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken

namespace Fomega.Proof

  theorem lift_subst_rename :
    (∀ n y, σ n = .rename y -> [σ](Γ d@ n) = Δ d@ y) ->
    (∀ n y, ^σ n = .rename y -> [^σ]((A :: Γ) d@ n) = ([σ]A :: Δ) d@ y)
  := by
  intro h1 n y h2
  cases n
  case _ => simp at *; subst h2; simp
  case _ n =>
    simp at *; unfold Term.Subst.compose at h2; simp at h2
    generalize ydef : σ n = y at *
    cases y <;> simp at h2
    case _ z =>
      subst h2; simp
      replace h1 := h1 n z ydef
      rw [<-Term.subst_apply_compose_commute, h1]

  theorem lift_subst_replace :
    (∀ n t, σ n = .replace t -> Δ ⊢ t : ([σ]Γ d@ n)) ->
    (∀ n t, ^σ n = .replace t -> ([σ]A :: Δ) ⊢ t : ([^σ](A :: Γ) d@ n))
  := by
  intro h1 n t h2
  cases n <;> simp at *
  case _ n =>
    unfold Term.Subst.compose at h2; simp at h2
    generalize ydef : σ n = y at *
    cases y <;> simp at h2
    case _ t' =>
      replace h1 := h1 n t' ydef
      subst h2
      rw [<-Term.subst_apply_compose_commute]
      apply weaken; exact h1

  theorem lift_subst_replace_wf :
    (∀ n t, σ n = .replace t -> t ⊢ Δ) ->
    (∀ n t, ^σ n = .replace t -> t ⊢ ([σ]A :: Δ))
  := by
  intro h1 n t h2
  cases n <;> simp at *
  case _ n =>
    unfold Term.Subst.compose at h2; simp at h2
    generalize ydef : σ n = y at *
    cases y <;> simp at h2
    case _ t' =>
      rw [<-h2]; apply weaken_wf; apply h1 n t' ydef

  theorem subst :
    (∀ n t, σ n = .replace t -> IsPreProof t) ->
    (∀ n y, σ n = .rename y -> [σ](Γ d@ n) = Δ d@ y) ->
    (∀ n t, σ n = .replace t -> Δ ⊢ t : ([σ]Γ d@ n)) ->
    Γ ⊢ t : A -> Δ ⊢ ([σ]t) : ([σ]A)
  := by
  intro h1 h2 h3 j
  induction j generalizing Δ σ
  case ax ih =>
    replace ih := ih 0 h1 h2 h3
    have lem := ctx_wf ih
    cases lem
    case _ f lem =>
      constructor; apply lem
  case var Γ x K _ ih =>
    simp; generalize ydef : σ x = y at *
    cases y <;> simp
    case _ y =>
      rw [h2 x y ydef]; constructor
      replace ih := ih h1 h2 h3; simp at ih; rw [h2 _ _ ydef] at ih
      apply ih
    case _ t' => apply h3 x t' ydef
  case pi Γ' A' K B _j1 _j2 ih1 ih2 =>
    simp; constructor; apply ih1 h1 h2 h3
    replace ih2 := @ih2 (^σ) ([σ]A' :: Δ) (IsPreProof.lift h1) (lift_subst_rename h2) (lift_subst_replace h3)
    simp at ih2; exact ih2
  case tpi Γ' A' B _j1 _j2 ih1 ih2 =>
    simp; constructor; apply ih1 h1 h2 h3
    replace ih2 := @ih2 (^σ) ([σ]A' :: Δ) (IsPreProof.lift h1) (lift_subst_rename h2)  (lift_subst_replace h3)
    simp at ih2; exact ih2
  case lam Γ' A' B K t' _j1 _j2 ih1 ih2 =>
    simp; constructor; simp at *; apply ih1 h1 h2 h3
    replace ih2 := @ih2 (^σ) ([σ]A' :: Δ) (IsPreProof.lift h1) (lift_subst_rename h2)  (lift_subst_replace h3)
    simp at ih2; exact ih2
  case app _j1 _j2 j3 ih1 ih2 =>
    simp; constructor; apply ih1 h1 h2 h3; apply ih2 h1 h2 h3
    subst j3; simp
  case econv Γ' t' A' B K _j1 _j2 j3 ih1 ih2 =>
    constructor; apply ih1 h1 h2 h3; apply ih2 h1 h2 h3
    apply Term.RedConv.subst _ j3
  case iconv Γ' t' A' B K _j1 _j2 j3 ih1 ih2 =>
    constructor; apply ih1 h1 h2 h3; apply ih2 h1 h2 h3
    apply Term.RedConv.subst _ j3

  theorem subst_wf :
    (∀ n t, σ n = .replace t -> IsPreProof t) ->
    (∀ n y, σ n = .rename y -> [σ](Γ d@ n) = Δ d@ y) ->
    (∀ n t, σ n = .replace t -> Δ ⊢ t : ([σ]Γ d@ n)) ->
    (∀ n t, σ n = .replace t -> t ⊢ Δ) ->
    t ⊢ Γ -> ([σ]t) ⊢ Δ
  := by
  intro h1 h2 h3 h4 j
  induction j generalizing Δ σ
  case _ => constructor
  case var Γ x K j1 _j2 ih =>
    simp; generalize ydef : σ x = y at *
    cases y <;> simp
    case _ y =>
      constructor
      replace j := subst h1 h2 h3 j1
      rw [h2 _ _ ydef] at j; simp at j; exact j
      replace ih := ih h1 h2 h3 h4; rw [h2 _ _ ydef] at ih; exact ih
    case _ t' => apply h4 _ _ ydef
  case pi A Γ B _ _ ih1 ih2 =>
    simp; constructor; apply ih1 h1 h2 h3 h4
    replace ih2 := @ih2 (^σ) ([σ]A::Δ) (IsPreProof.lift h1) (lift_subst_rename h2)
      (lift_subst_replace h3) (lift_subst_replace_wf h4)
    simp at ih2; exact ih2
  case lam A Γ B _ _ ih1 ih2 =>
    simp; constructor; apply ih1 h1 h2 h3 h4
    replace ih2 := @ih2 (^σ) ([σ]A::Δ) (IsPreProof.lift h1) (lift_subst_rename h2)
      (lift_subst_replace h3) (lift_subst_replace_wf h4)
    simp at ih2; exact ih2
  case app ih1 ih2 =>
    simp; constructor; apply ih1 h1 h2 h3 h4; apply ih2 h1 h2 h3 h4
  case conv ih1 ih2 =>
    simp; constructor; apply ih1 h1 h2 h3 h4; apply ih2 h1 h2 h3 h4

  theorem beta : (A::Γ) ⊢ b : B -> Γ ⊢ t : A -> Γ ⊢ (b β[t]) : (B β[t]) := by
  simp; intro j1 j2
  apply @subst _ (A::Γ)
  case _ =>
    intro n s eq
    cases n <;> simp at *
    subst eq; apply IsPreProof.from_proof j2
  case _ =>
    intro n y h
    cases n <;> simp at h
    case _ n => subst h; simp
  case _ =>
    intro n t' h
    cases n <;> simp at h
    case _ => subst h; simp; exact j2
  case _ => exact j1

  theorem beta_wf : b ⊢ (A::Γ) -> Γ ⊢ t : A -> t ⊢ Γ -> (b β[t]) ⊢ Γ := by
  simp; intro j1 j2 j3
  apply @subst_wf _ (A::Γ)
  case _ =>
    intro n s eq
    cases n <;> simp at *
    subst eq; apply IsPreProof.from_proof j2
  case _ =>
    intro n y h
    cases n <;> simp at h
    case _ n => subst h; simp
  case _ =>
    intro n t' h
    cases n <;> simp at h
    case _ => subst h; simp; exact j2
  case _ =>
    intro n t' h
    cases n <;> simp at h
    case _ => subst h; exact j3
  case _ => exact j1

end Fomega.Proof
