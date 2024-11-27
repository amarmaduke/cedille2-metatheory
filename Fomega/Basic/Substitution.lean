
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

  theorem subst :
    (∀ n t, σ n = .replace t -> IsPreProof t) ->
    (∀ n y, σ n = .rename y -> [σ](Γ d@ n) = Δ d@ y) ->
    (∀ n t, σ n = .replace t -> Δ ⊢ t : ([σ]Γ d@ n)) ->
    Γ ⊢ t : A -> Δ ⊢ ([σ]t) : ([σ]A)
  := by
  intro h1 h2 h3 j
  induction j generalizing Δ σ
  case _ => constructor
  case var Γ K x =>
    simp; generalize ydef : σ x = y at *
    cases y <;> simp
    case _ y => rw [h2 x y ydef]; constructor
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
  case app Γ' f A' B a B' _j1 _j2 j3 ih1 ih2 =>
    simp; constructor; apply ih1 h1 h2 h3; apply ih2 h1 h2 h3
    simp at *; subst j3; simp
  case conv Γ' t' A' B K _j1 _j2 j3 ih1 ih2 =>
    constructor; apply ih1 h1 h2 h3; apply ih2 h1 h2 h3
    apply Term.RedConv.subst _ j3

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
    case _ n =>
      subst h; simp
  case _ =>
    intro n t' h
    cases n <;> simp at h
    case _ => subst h; simp; exact j2
  case _ => exact j1

end Fomega.Proof
