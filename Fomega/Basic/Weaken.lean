
import Common
import Fomega.Proof
import Fomega.Reduction

namespace Fomega.Proof

  theorem rename_lift r (A : Term) :
    (∀ x, [r.to](Γ d@ x) = Δ d@ (r x)) ->
    ∀ x, [r.lift.to]((A::Γ) d@ x) = ([r.to]A::Δ) d@ (Ren.lift r x)
  := by
  intro h x; simp
  cases x <;> simp at *
  case _ => rw [Subst.lift_lemma]; simp
  case _ x => rw [Subst.lift_lemma, <-h x]; simp

  @[simp]
  abbrev idx_ren (r : Ren) : JudgmentIndex v -> JudgmentIndex v :=
    match v with
    | .prf => λ (t, A) => ([r.to]t, [r.to]A)
    | .wf => λ () => ()

  theorem rename (r : Ren) :
    Judgment v Γ idx ->
    ⊢ Δ ->
    (∀ x, [r.to](Γ d@ x) = Δ d@ (r x)) ->
    Judgment v Δ (idx_ren r idx)
  := by
  intro j h1 h2
  induction j generalizing Δ r
  case nil => simp; apply h1
  case cons => simp; apply h1
  case ax ih =>
    replace ih := ih r h1 h2
    simp at *; constructor; apply ih
  case var _ h _ =>
    simp at *; constructor; apply h1; subst h
    apply h2
  case pi Γ A K1 K2 B _j1 _j2 ih1 ih2 =>
    simp; constructor
    case _ => apply ih1 r h1 h2
    case _ =>
      have lem : ⊢ ([r.to]A :: Δ) := by constructor; apply h1; apply ih1 r h1 h2
      replace ih2 := @ih2 ([r.to]A :: Δ) (Ren.lift r) lem (rename_lift r A h2)
      simp at ih2; rw [Subst.lift_lemma] at ih2; simp at ih2; exact ih2
  case lam Γ A K1 K2 B t _j1 _j2 _j3 ih1 ih2 ih3 =>
    have lem : ⊢ ([r.to]A :: Δ) := by
      constructor; apply h1; apply ih1 r h1 h2
    simp; constructor
    case _ => apply ih1 r h1 h2
    case _ =>
      replace ih2 := @ih2 ([r.to]A :: Δ) (Ren.lift r) lem (rename_lift r A h2)
      simp at ih2; rw [Subst.lift_lemma] at ih2; simp at ih2; exact ih2
    case _ =>
      replace ih3 := @ih3 ([r.to]A :: Δ) (Ren.lift r) lem (rename_lift r A h2)
      simp at ih3; rw [Subst.lift_lemma] at ih3; simp at ih3; exact ih3
  case app Γ' f A' B a B' _j1 _j2 j3 ih1 ih2 =>
    simp; constructor
    case _ => simp at ih1; apply ih1 r h1 h2
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
    simp; constructor; apply ih r h1 h2
  case snd ih =>
    simp; constructor; apply ih r h1 h2
  case unit ih =>
    simp; constructor; apply ih r h1 h2
  case unit_ty ih =>
    simp; constructor; apply ih r h1 h2
  case unit_rec ih1 ih2 ih3 ih4 =>
    simp; constructor; apply ih1 r h1 h2
    apply ih2 r h1 h2; apply ih3 r h1 h2
    apply ih4 r h1 h2
  case conv Γ' t A' B K _j1 _j2 j3 ih1 ih2 =>
    constructor
    case _ => apply ih1 r h1 h2
    case _ => apply ih2 r h1 h2
    case _ => apply Red.Conv.subst_same; apply j3

  theorem weaken :
    Γ ⊢ B : .const K ->
    Γ ⊢ t : A ->
    (B::Γ) ⊢ ([S]t) : ([S]A)
  := by
  intro j1 j2; apply rename _ j2;
  case _ => constructor; apply judgment_ctx_wf j1; apply j1
  case _ => intro x; simp; rw [Subst.to_S]

namespace Fomega.Proof
