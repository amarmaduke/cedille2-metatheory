
import Common
import Fomega.Proof
import Fomega.Basic.Weaken

namespace Fomega.Proof

  theorem lift_subst_rename (A : Term) :
    (∀ n y, σ n = .re y -> [σ](Γ d@ n) = Δ d@ y) ->
    (∀ n y, ^σ n = .re y -> [^σ]((A :: Γ) d@ n) = ([σ]A :: Δ) d@ y)
  := by
  intro h1 n y h2
  cases n
  case _ => simp at *; subst h2; simp
  case _ n =>
    simp at *; unfold Subst.compose at h2; simp at h2
    generalize ydef : σ n = y at *
    cases y <;> simp at h2
    case _ z =>
      subst h2; simp
      replace h1 := h1 n z ydef
      rw [<-Term.apply_compose, h1]

  theorem lift_subst_replace :
    Δ ⊢ ([σ]A) : .const K ->
    (∀ n t, σ n = .su t -> Δ ⊢ t : ([σ]Γ d@ n)) ->
    (∀ n t, ^σ n = .su t -> ([σ]A :: Δ) ⊢ t : ([^σ](A :: Γ) d@ n))
  := by
  intro j h1 n t h2
  cases n <;> simp at *
  case _ n =>
    unfold Subst.compose at h2; simp at h2
    generalize ydef : σ n = y at *
    cases y <;> simp at h2
    case _ t' =>
      replace h1 := h1 n t' ydef
      subst h2
      rw [<-Term.apply_compose]
      apply weaken; apply j; apply h1

  @[simp]
  abbrev idx_subst (σ : Subst Term) : JudgmentIndex v -> JudgmentIndex v :=
    match v with
    | .prf => λ (t, A) => ([σ]t, [σ]A)
    | .wf => λ () => ()

  theorem subst :
    (∀ n y, σ n = .re y -> [σ](Γ d@ n) = Δ d@ y) ->
    (∀ n t, σ n = .su t -> Δ ⊢ t : ([σ]Γ d@ n)) ->
    Judgment v Γ idx ->
    ⊢ Δ ->
    Judgment v Δ (idx_subst σ idx)
  := by
  intro h2 h3 j1 j2
  induction j1 generalizing Δ σ
  case nil => apply j2
  case cons => apply j2
  case ax Γ _j _ih => simp; constructor; apply j2
  case var x _ h ih =>
    simp; generalize zdef : σ x = z
    cases z
    case _ y =>
      simp at *; subst h; rw [h2 _ _ zdef]
      constructor; apply j2; rfl
    case _ t =>
      simp at *; subst h; apply h3 _ _ zdef
  case pi Γ A K1 K2 B _j1 _j2 ih1 ih2 =>
    have lem1 := ih1 h2 h3 j2
    have lem2 : ⊢ ([σ]A :: Δ) := by constructor; apply j2; apply lem1
    simp; constructor; apply ih1 h2 h3 j2
    replace ih2 := @ih2 (^σ) ([σ]A :: Δ) (lift_subst_rename _ h2) (lift_subst_replace lem1 h3) lem2
    simp at ih2; exact ih2
  case lam Γ A K1 K2 B t _j1 _j2 _j3 ih1 ih2 ih3 =>
    have lem1 := ih1 h2 h3 j2
    have lem2 : ⊢ ([σ]A :: Δ) := by constructor; apply j2; apply lem1
    simp; constructor; simp at *; apply ih1 h2 h3 j2
    replace ih2 := @ih2 (^σ) ([σ]A :: Δ) (lift_subst_rename _ h2)  (lift_subst_replace lem1 h3) lem2
    simp at ih2; exact ih2
    replace ih3 := @ih3 (^σ) ([σ]A :: Δ) (lift_subst_rename _ h2)  (lift_subst_replace lem1 h3) lem2
    simp at ih3; exact ih3
  case app _j1 _j2 j3 ih1 ih2 =>
    simp; constructor; simp at ih1; apply ih1 h2 h3 j2; apply ih2 h2 h3 j2
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
  case unit ih =>
    simp; constructor; apply ih h2 h3 j2
  case unit_ty ih =>
    simp; constructor; apply ih h2 h3 j2
  case unit_rec ih1 ih2 ih3 =>
    simp; constructor; apply ih1 h2 h3 j2
    apply ih2 h2 h3 j2; apply ih3 h2 h3 j2
  case conv Γ' t' A' B K _j1 _j2 j3 ih1 ih2 =>
    constructor; apply ih1 h2 h3 j2; apply ih2 h2 h3 j2
    apply Red.subst_same j3

  theorem beta : (A::Γ) ⊢ b : B -> Γ ⊢ t : A -> Γ ⊢ (b β[t]) : (B β[t]) := by
  simp; intro j1 j2
  have lem := @subst (.su t :: I) (A::Γ) Γ .prf (b, B); simp at lem
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
