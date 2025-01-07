
import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof

namespace Fomega.Proof

  theorem rename_lift r A :
    (∀ x, [r#r](Γ d@ x) = Δ d@ (r x)) ->
    ∀ x, [r#(Term.Ren.lift r)]((A::Γ) d@ x) = ([r#r]A::Δ) d@ (Term.Ren.lift r x)
  := by
  intro h x; simp
  cases x <;> simp at *
  case _ x => rw [<-h x]; simp

  -- theorem rename (r : Ren) : Γ ⊢ t : A ->
  --   (∀ x, [r#r](Γ d@ x) = Δ d@ (r x)) ->
  --   Δ ⊢ ([r#r]t) : ([r#r]A)

  @[simp]
  abbrev idx_ren (r : Ren) : JudgmentIndex v -> JudgmentIndex v :=
    match v with
    | .prf => λ (t, A) => ([r#r]t, [r#r]A)
    | .wf => λ () => ()

  theorem rename (r : Ren) :
    Judgment v Γ idx ->
    ⊢ Δ ->
    (∀ x, [r#r](Γ d@ x) = Δ d@ (r x)) ->
    Judgment v Δ (idx_ren r idx)
  := by
  intro j h1 h2
  induction j generalizing Δ r
  case nil => simp; apply h1
  case cons => simp; apply h1
  case ax ih =>
    replace ih := ih r h1 h2
    simp at *; constructor; apply ih
  case var x K T j1 j2 ih =>
    simp at *; rw [j2, h2 x]; constructor
    rw [<-(h2 x)]; apply ih r h1 h2; rfl
  case pi Γ' A' K B _j1 _j2 ih1 ih2 =>
    simp; constructor
    case _ => apply ih1 r h1 h2
    case _ =>
      have lem : ⊢ ([r#r]A' :: Δ) := by constructor; apply h1; apply ih1 r h1 h2
      replace ih2 := @ih2 ([r#r]A' :: Δ) (Term.Ren.lift r) lem (rename_lift r A' h2)
      simp at ih2; exact ih2
  case tpi Γ' A' B _j1 _j2 ih1 ih2 =>
    simp; constructor
    case _ => apply ih1 r h1 h2
    case _ =>
      have lem : ⊢ ([r#r]A' :: Δ) := by constructor; apply h1; apply ih1 r h1 h2
      replace ih2 := @ih2 ([r#r]A' :: Δ) (Term.Ren.lift r) lem (rename_lift r A' h2)
      simp at ih2; exact ih2
  case lam Γ A B K t j1 j2 ih1 ih2  =>
    simp; constructor
    case _ =>
      have lem : ⊢ ([r#r]A :: Δ) := by
        constructor; apply h1; replace ih1 := ih1 r h1 h2; simp at ih1
      replace ih1 := @ih1 ([r#r]A :: Δ) (Term.Ren.lift r) lem (rename_lift r A h2)
      simp at ih1; exact ih1
    case _ =>
      have lem : ⊢ ([r#r]A :: Δ) := by constructor; apply h1; apply ih1 r h1 h2
      replace ih2 := @ih2 ([r#r]A :: Δ) (Term.Ren.lift r) lem (rename_lift r A h2)
      simp at ih2; exact ih2
  case app Γ' f A' B a B' _j1 _j2 j3 ih1 ih2 =>
    simp; constructor
    case _ => apply ih1 r h1 h2
    case _ => apply ih2 r h1 h2
    case _ => subst j3; simp
  case conv Γ' t A' B K _j1 _j2 j3 ih1 ih2 =>
    constructor
    case _ => apply ih1 r h1 h2
    case _ => apply ih2 r h1 h2
    case _ => apply RedConv.subst; apply j3

  -- theorem rename_wf (r : Ren) : t ⊢ Γ ->
  --   (∀ x, [r#r](Γ d@ x) = Δ d@ (r x)) ->
  --   ([r#r]t) ⊢ Δ
  -- := by
  -- intro j h
  -- induction j generalizing Δ r
  -- case ax => simp; constructor
  -- case var j1 _j2 ih =>
  --   have j2 := rename r j1 h
  --   simp at *; constructor; rw [h] at j2; exact j2
  --   replace ih := ih r h; rw [h _] at ih; exact ih
  -- case pi A Γ B _ _ ih1 ih2 =>
  --   simp; constructor; apply ih1 r h
  --   replace ih2 := @ih2 ([r#r]A :: Δ) (Term.Ren.lift r) (rename_lift r A h); simp at ih2
  --   exact ih2
  -- case lam A Γ B _ _ ih1 ih2 =>
  --   simp; constructor; apply ih1 r h
  --   replace ih2 := @ih2 ([r#r]A :: Δ) (Term.Ren.lift r) (rename_lift r A h); simp at ih2
  --   exact ih2
  -- case app _ _ ih1 ih2 =>
  --   simp; constructor; apply ih1 r h; apply ih2 r h
  -- case conv _ _ ih1 ih2 =>
  --   simp; constructor; apply ih1 r h; apply ih2 r h

  -- theorem weaken B : Γ ⊢ t : A -> (B::Γ) ⊢ ([S]t) : ([S]A) := by
  -- intro j; apply rename; exact j
  -- case _ => intro x; simp; rw [Term.S_to_rS]; unfold rS; simp

  -- theorem weaken_wf A : t ⊢ Γ -> ([S]t) ⊢ (A::Γ) := by
  -- intro j; apply rename_wf; exact j
  -- case _ => intro x; simp; rw [Term.S_to_rS]; unfold rS; simp


namespace Fomega.Proof
