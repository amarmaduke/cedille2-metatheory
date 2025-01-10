
import Common
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
    Δ ⊢ ([σ]A) : .const K ->
    (∀ n t, σ n = .replace t -> Δ ⊢ t : ([σ]Γ d@ n)) ->
    (∀ n t, ^σ n = .replace t -> ([σ]A :: Δ) ⊢ t : ([^σ](A :: Γ) d@ n))
  := by
  intro j h1 n t h2
  cases n <;> simp at *
  case _ n =>
    unfold Term.Subst.compose at h2; simp at h2
    generalize ydef : σ n = y at *
    cases y <;> simp at h2
    case _ t' =>
      replace h1 := h1 n t' ydef
      subst h2
      rw [<-Term.subst_apply_compose_commute]
      apply weaken; apply j; apply h1

  @[simp]
  abbrev idx_subst (σ : Subst Term) : JudgmentIndex v -> JudgmentIndex v :=
    match v with
    | .prf => λ (t, A) => ([σ]t, [σ]A)
    | .wf => λ () => ()

  theorem subst :
    (∀ n y, σ n = .rename y -> [σ](Γ d@ n) = Δ d@ y) ->
    (∀ n t, σ n = .replace t -> Δ ⊢ t : ([σ]Γ d@ n)) ->
    Judgment v Γ idx ->
    ⊢ Δ ->
    Judgment v Δ (idx_subst σ idx)
  := by
  intro h2 h3 j1 j2
  induction j1 generalizing Δ σ
  case nil => apply j2
  case cons => apply j2
  case ax Γ _j _ih => simp; constructor; apply j2
  case var Γ x K T _q1 q2 ih =>
    simp; generalize zdef : σ x = z
    cases z
    case _ y =>
      replace ih := ih h2 h3 j2; simp at ih; rw [h2 x y zdef] at ih
      simp; rw [q2, h2 x y zdef]
      constructor; apply ih; rfl
    case _ t => simp; rw [q2]; apply h3 x t zdef
  case pi Γ A K1 K2 B _j1 _j2 ih1 ih2 =>
    have lem1 := ih1 h2 h3 j2
    have lem2 : ⊢ ([σ]A :: Δ) := by constructor; apply j2; apply lem1
    simp; constructor; apply ih1 h2 h3 j2
    replace ih2 := @ih2 (^σ) ([σ]A :: Δ) (lift_subst_rename h2) (lift_subst_replace lem1 h3) lem2
    simp at ih2; exact ih2
  case lam Γ A K1 K2 B t _j1 _j2 _j3 ih1 ih2 ih3 =>
    have lem1 := ih1 h2 h3 j2
    have lem2 : ⊢ ([σ]A :: Δ) := by constructor; apply j2; apply lem1
    simp; constructor; simp at *; apply ih1 h2 h3 j2
    replace ih2 := @ih2 (^σ) ([σ]A :: Δ) (lift_subst_rename h2)  (lift_subst_replace lem1 h3) lem2
    simp at ih2; exact ih2
    replace ih3 := @ih3 (^σ) ([σ]A :: Δ) (lift_subst_rename h2)  (lift_subst_replace lem1 h3) lem2
    simp at ih3; exact ih3
  case app _j1 _j2 j3 ih1 ih2 =>
    simp; constructor; apply ih1 h2 h3 j2; apply ih2 h2 h3 j2
    subst j3; simp
  case prod ih1 ih2 =>
    simp; constructor; apply ih1 h2 h3 j2; apply ih2 h2 h3 j2
  case pair ih1 ih2 ih3 ih4 =>
    simp; constructor; apply ih1 h2 h3 j2; apply ih2 h2 h3 j2
    apply ih3 h2 h3 j2; apply ih4 h2 h3 j2
  case fst ih =>
    simp; constructor; apply ih h2 h3 j2
  case snd ih =>
    simp; constructor; apply ih h2 h3 j2
  case id ih =>
    simp; apply Judgment.id; apply ih h2 h3 j2
  case conv Γ' t' A' B K _j1 _j2 j3 ih1 ih2 =>
    constructor; apply ih1 h2 h3 j2; apply ih2 h2 h3 j2
    apply RedConv.subst _ j3

  theorem beta : (A::Γ) ⊢ b : B -> Γ ⊢ t : A -> Γ ⊢ (b β[t]) : (B β[t]) := by
  simp; intro j1 j2
  have lem := @subst (.replace t :: I) (A::Γ) Γ .prf (b, B); simp at lem
  apply lem
  case _ =>
    intro n y h
    cases n <;> simp at h
    case _ n => subst h; simp
  case _ =>
    intro n t' h
    cases n <;> simp at h
    case _ => subst h; simp; exact j2
  case _ => exact j1
  case _ => apply judgment_ctx_wf j2

end Fomega.Proof
