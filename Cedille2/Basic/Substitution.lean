
import Common
import Cedille2.Proof
import Cedille2.Basic.Weaken

namespace Cedille2.Proof

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
  case var Γ x K T j1 j3 ih =>
    simp; generalize zdef : σ x = z
    cases z
    case _ y =>
      simp at *; subst j3; rw [h2 _ _ zdef]
      replace ih := ih h2 h3 j2; rw [h2 _ _ zdef] at ih
      constructor; apply ih; rfl
    case _ t =>
      simp at *; subst j3; apply h3 _ _ zdef
  case pi Γ A K1 K2 B _j1 _j2 ih1 ih2 =>
    have lem1 := ih1 h2 h3 j2
    have lem2 : ⊢ ([σ]A :: Δ) := by constructor; apply j2; apply lem1
    simp; constructor; apply ih1 h2 h3 j2
    replace ih2 := @ih2 (^σ) ([σ]A :: Δ) (lift_subst_rename _ h2) (lift_subst_replace lem1 h3) lem2
    simp at ih2; exact ih2
  case lam A m K B t q1 q2 q3 q4 ih1 ih2 ih3 =>
    have lem1 := ih1 h2 h3 j2
    have lem2 : ⊢ ([σ]A :: Δ) := by constructor; apply j2; apply lem1
    replace ih2 := @ih2 (^σ) ([σ]A :: Δ) (lift_subst_rename _ h2) (lift_subst_replace lem1 h3) lem2
    replace ih3 := @ih3 (^σ) ([σ]A :: Δ) (lift_subst_rename _ h2) (lift_subst_replace lem1 h3) lem2
    simp at ih2; simp at ih3
    simp; constructor; apply lem1
    apply ih2; apply ih3
    intro h v1 v2 τ
    have lem := q4 h
    rw [erase_subst]; simp
    rw [Subst.map_S_compose_left erase_rename_commute]; simp
    apply lem
  case app _j1 _j2 j3 ih1 ih2 =>
    simp; constructor; simp at ih1
    apply ih1 h2 h3 j2; apply ih2 h2 h3 j2
    subst j3; simp
  case inter_ty A B _ _ ih1 ih2 =>
    have lem1 := ih1 h2 h3 j2
    have lem2 : ⊢ ([σ]A :: Δ) := by constructor; apply j2; apply lem1
    replace ih2 := @ih2 (^σ) ([σ]A :: Δ) (lift_subst_rename _ h2) (lift_subst_replace lem1 h3) lem2
    simp at *; constructor; apply lem1; apply ih2
  case inter t A B s g1 g2 q1 q2 q3 q4 q5 ih1 ih2 ih3 ih4 =>
    have lem1 := ih2 h2 h3 j2
    have lem2 : ⊢ ([σ]A :: Δ) := by constructor; apply j2; apply lem1
    replace ih3 := @ih3 (^σ) ([σ]A :: Δ) (lift_subst_rename _ h2) (lift_subst_replace lem1 h3) lem2
    simp at ih3; replace ih4 := ih4 h2 h3 j2
    simp at ih4
    simp; constructor; apply ih1 h2 h3 j2
    apply lem1; apply ih3; simp; apply ih4
    rw [erase_subst, erase_subst]
    apply Erased.convb_subst; apply q5
  case fst ih =>
    simp; constructor; apply ih h2 h3 j2
  case snd A B B' j1 j2 ih =>
    simp; apply @Judgment.snd _ _ _ ([^σ]B)
    apply ih h2 h3 j2; simp [*]
  case eq ih1 ih2 ih3 =>
    simp; constructor; apply ih1 h2 h3 j2
    apply ih2 h2 h3 j2; apply ih3 h2 h3 j2
  case refl j1 j2 j3 j4 ih1 ih2 ih3 =>
    simp; constructor; apply ih1 h2 h3 j2
    apply ih2 h2 h3 j2; apply ih3 h2 h3 j2
    rw [erase_subst, erase_subst]
    apply Erased.convb_subst; apply j4
  case subst ih1 ih2 ih3 ih4 =>
    replace ih3 := ih3 h2 h3 j2; simp at ih3
    simp; constructor; apply ih1 h2 h3 j2
    apply ih2 h2 h3 j2; simp; apply ih3
    apply ih4 h2 h3 j2
  case phi ih1 ih2 ih3 =>
    replace ih2 := ih2 h2 h3 j2; simp at ih2
    simp; constructor; apply ih1 h2 h3 j2
    apply ih2; apply ih3 h2 h3 j2
  case iconv Γ' t' A' B K _j1 _j2 j3 ih1 ih2 =>
    constructor; apply ih1 h2 h3 j2; apply ih2 h2 h3 j2
    apply Red.Conv.subst_same j3
  case econv j ih1 ih2 =>
    simp; apply Judgment.econv; apply ih1 h2 h3 j2
    apply ih2 h2 h3 j2
    rw [erase_subst, erase_subst]
    apply Erased.convb_subst; apply j

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

end Cedille2.Proof
