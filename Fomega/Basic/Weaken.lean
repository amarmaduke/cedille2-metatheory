
import Common
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
  case var x K T _j1 j2 ih =>
    simp at *; rw [j2, h2 x]; constructor
    rw [<-(h2 x)]; apply ih r h1 h2; rfl
  case pi Γ A K1 K2 B _j1 _j2 ih1 ih2 =>
    simp; constructor
    case _ => apply ih1 r h1 h2
    case _ =>
      have lem : ⊢ ([r#r]A :: Δ) := by constructor; apply h1; apply ih1 r h1 h2
      replace ih2 := @ih2 ([r#r]A :: Δ) (Term.Ren.lift r) lem (rename_lift r A h2)
      simp at ih2; exact ih2
  case lam Γ A K1 K2 B t _j1 _j2 _j3 ih1 ih2 ih3 =>
    have lem : ⊢ ([r#r]A :: Δ) := by
      constructor; apply h1; apply ih1 r h1 h2
    simp; constructor
    case _ => apply ih1 r h1 h2
    case _ =>
      replace ih2 := @ih2 ([r#r]A :: Δ) (Term.Ren.lift r) lem (rename_lift r A h2)
      simp at ih2; exact ih2
    case _ =>
      replace ih3 := @ih3 ([r#r]A :: Δ) (Term.Ren.lift r) lem (rename_lift r A h2)
      simp at ih3; exact ih3
  case app Γ' f A' B a B' _j1 _j2 j3 ih1 ih2 =>
    simp; constructor
    case _ => apply ih1 r h1 h2
    case _ => apply ih2 r h1 h2
    case _ => subst j3; simp
  case prod ih1 ih2 =>
    simp; constructor
    case _ => apply ih1 r h1 h2
    case _ => apply ih2 r h1 h2
  case pair ih1 ih2 ih3 ih4 =>
    simp; constructor
    case _ => apply ih1 r h1 h2
    case _ => apply ih2 r h1 h2
    case _ => apply ih3 r h1 h2
    case _ => apply ih4 r h1 h2
  case fst ih =>
    simp; constructor; case _ => apply ih r h1 h2
  case snd ih =>
    simp; constructor; case _ => apply ih r h1 h2
  case id ih =>
    simp; apply Judgment.id; case _ => apply ih r h1 h2
  case conv Γ' t A' B K _j1 _j2 j3 ih1 ih2 =>
    constructor
    case _ => apply ih1 r h1 h2
    case _ => apply ih2 r h1 h2
    case _ => apply RedConv.subst; apply j3

  theorem weaken :
    Γ ⊢ B : .const K ->
    Γ ⊢ t : A ->
    (B::Γ) ⊢ ([S]t) : ([S]A)
  := by
  intro j1 j2; apply rename _ j2;
  case _ => constructor; apply judgment_ctx_wf j1; apply j1
  case _ => intro x; simp; rw [Term.S_to_rS]; unfold rS; simp

namespace Fomega.Proof
