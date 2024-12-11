import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof

namespace Fomega.Proof

  abbrev Iℓ (ℓ : Nat) : Subst Term
  | 0 => .rename ℓ
  | n + 1 => .rename (n + 1)

  abbrev repIℓ n ℓ := ^{n}(Iℓ ℓ)

  abbrev Pℓ (ℓ : Nat) : Subst Term
  | 0 => .rename ℓ
  | n + 1 => .rename n

  abbrev repPℓ n ℓ := ^{n}(Pℓ ℓ)

  @[simp]
  theorem Iℓ_after_S : (Iℓ ℓ) ⊙ S = S := by
  funext
  case _ x =>
    cases x <;> simp at *
    <;> unfold Term.Subst.compose at *
    <;> simp at *

  theorem repIℓ_eq ℓ : n = x -> (repIℓ n ℓ) x = .rename (ℓ + x) := by
  intro h
  induction n generalizing x <;> simp
  case _ => subst h; simp
  case _ n ih =>
    simp at ih; unfold repIℓ at ih
    subst h; simp; unfold Term.Subst.compose; simp
    rw [ih]; simp; omega

  theorem repIℓ_neq ℓ : n ≠ x -> (repIℓ n ℓ) x = .rename x := by
  intro h
  induction n generalizing x <;> simp
  case _ => unfold Iℓ; cases x <;> simp at *
  case _ n ih =>
    cases x <;> simp
    case _ x =>
      have nh : n ≠ x := by omega
      unfold Term.Subst.compose
      have ih' := ih nh
      simp; unfold repIℓ at ih'; rw [ih']

  @[simp]
  theorem Pℓ_after_S : (Pℓ ℓ) ⊙ S = I := by
  funext
  case _ x =>
    cases x <;> simp at *
    <;> unfold Term.Subst.compose at *
    <;> simp at *

  theorem repPℓ_lt ℓ : n < x -> (repPℓ n ℓ) x = .rename (x - 1) := by
  intro h
  induction n generalizing x <;> simp
  case _ =>
    cases x <;> simp at *
  case _ n ih =>
    cases x <;> simp
    case _ x =>
      unfold Term.Subst.compose; simp
      have nh : n < x := by omega
      have ih' := ih nh; simp at ih'
      unfold repPℓ at ih'; rw [ih']; simp
      cases x <;> simp at *

  theorem repPℓ_eq ℓ : n = x -> (repPℓ n ℓ) x = .rename (ℓ + x) := by
  intro h
  induction n generalizing x <;> simp
  case _ => subst h; simp
  case _ n ih =>
    simp at ih; unfold repPℓ at ih
    subst h; simp; unfold Term.Subst.compose; simp
    rw [ih]; simp; omega

  theorem repPℓ_ge ℓ : n > x -> (repPℓ n ℓ) x = .rename x  := by
  intro h
  induction n generalizing x <;> simp
  case _ => omega
  case _ n ih =>
    cases x <;> simp
    case _ x =>
      have nh : n > x := by omega
      unfold Term.Subst.compose
      have ih' := ih nh
      simp; unfold repPℓ at ih'; rw [ih']


  -- theorem strengthen_nth_lift_ge n :
  --   (∀ x, x ≥ n → Γ d@ (x + 1) = [^{n}S]Δ d@ x) ->
  --   ∀ x, x ≥ n + 1 → (U :: Γ)d@(x + 1) = [^{n + 1}S](V :: Δ)d@x
  -- := by
  -- intro h1 x h2
  -- cases x <;> simp
  -- case _ => omega
  -- case _ x =>
  --   replace h2 : x ≥ n := by omega
  --   replace h1 := h1 x h2
  --   rw [h1]; simp

  -- theorem strengthen_nth_lift_ge2 A n :
  --   (∀ x, x ≥ n -> [^{n}P]Γ d@ (x + 1) = Δ d@ x) ->
  --   ∀ x, x ≥ n + 1 → [^{n + 1}P](A :: Γ) d@ (x + 1) = ([^{n}P]A :: Δ)d@x
  -- := by sorry

  -- theorem strengthen_nth_lift_lt n :
  --   [^{n}S]V = U ->
  --   (∀ x, x < n -> Γ d@ x = [^{n}S]Δ d@ x) ->
  --   ∀ x, x < n + 1 → (U :: Γ)d@x = [^{n + 1}S](V :: Δ)d@x
  -- := by
  -- intro h0 h1 x h2
  -- cases x <;> simp
  -- case _ => rw [<-Term.subst_apply_compose_commute, h0]
  -- case _ x =>
  --   replace h2 : x < n := by omega
  --   rw [h1 x h2]; simp

  -- theorem strengthen_nth_lift_lt2 A n :
  --   (∀ x, x < n -> [^{n}P]Γ d@ x = Δ d@ x) ->
  --   ∀ x, x < n + 1 → [^{n + 1}P](A :: Γ)d@x = ([^{n}P]A :: Δ)d@x
  -- := by sorry

  -- theorem strengthen_nth2 n  :
  --   Γ ⊢ t : T ->
  --   [repIℓ n Γ.length]t = t ->
  --   IsPreKind T ->
  --   (∀ x, x < n -> [repPℓ n Γ.length]Γ d@ x = Δ d@ x) ->
  --   (∀ x, x + 1 ≥ n -> [repPℓ n Γ.length]Γ d@ (x + 1) = Δ d@ x) ->
  --   Δ ⊢ ([repPℓ n Γ.length]t) : T
  -- := by

  -- theorem strengthen : (A :: Δ) ⊢ ([S]t) : .const K -> Δ ⊢ t : .const K := by
  -- intro j
  -- have lem := @strengthen_nth2 (A::Δ) _ _ Δ 0 j
  -- simp at lem; apply lem

  -- theorem strengthen : (A :: Δ) ⊢ ([S]t) : ([S]T) -> Δ ⊢ t : T := by
  -- intro j
  -- apply strengthen_nth 0 j
  -- case _ => intro x nh; omega
  -- case _ => intro x _; simp
end Fomega.Proof
