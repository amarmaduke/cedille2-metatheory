
import Fomega.Proof
import Fomega.Basic

namespace Fomega

  @[simp]
  abbrev CheckArgs : JudgmentVariant -> Type
  | .prf => Term
  | .wf => Unit

  @[simp]
  abbrev CheckRets : JudgmentVariant -> Type
  | .prf => Option Term
  | .wf => Option Unit

  partial def normalize : Term -> Term := by sorry

  def is_kind : Term -> Option Const := by sorry

  def is_type : Term -> Option Unit := by sorry

  def is_dom : Const -> Const -> Option Unit := by sorry

  def is_pi : Term -> Option (Term × Term) := by sorry

  def is_times : Term -> Option (Term × Term) := by sorry

  def is_unit : Term -> Option Unit := by sorry

  def conv : Term -> Term -> Option Unit := by sorry

  def check_witness : (k : JudgmentVariant) -> Ctx Term -> CheckArgs k -> CheckRets k
  | .wf, _, () => .some .unit
  | .prf, _, t => .some t

  instance inst_Inhabited_check_def : Inhabited ((k : JudgmentVariant) -> Ctx Term -> CheckArgs k -> CheckRets k) where
    default := check_witness

  @[simp]
  def check : (k : JudgmentVariant) -> Ctx Term -> CheckArgs k -> CheckRets k
  | .wf, [], () => .some .unit
  | .wf, .cons A Γ, () => do
    let Ak <- check .prf Γ A
    let _ <- check .wf Γ ()
    let _ <- is_kind Ak
    .some ()
  | .prf, _, □ => .none
  | .prf, Γ, ★ => do
    let _ <- check .wf Γ ()
    .some □
  | .prf, Γ, #x => do
    let _ <- check .wf Γ ()
    .some (Γ d@ x)
  | .prf, Γ, Π[A] B => do
    let Ak <- check .prf Γ A
    let Ak <- is_kind Ak
    let Bk <- check .prf (A::Γ) B
    let Bk <- is_kind Bk
    let _ <- is_dom Ak Bk
    .some (.const Bk)
  | .prf, Γ, `λ[A] t => do
    let Ak <- check .prf Γ A
    let Ak <- is_kind Ak
    let B <- check .prf (A::Γ) t
    let Bk <- check .prf (A::Γ) B
    let Bk <- is_kind Bk
    let _ <- is_dom Ak Bk
    .some (Π[A] B)
  | .prf, Γ, f `@ a => do
    let T <- check .prf Γ f
    let (A, B) <- is_pi T
    let A' <- check .prf Γ a
    let _ <- conv A A'
    .some (B β[a])
  | .prf, Γ , A ⊗ B => do
    let Ak <- check .prf Γ A
    let _ <- is_type Ak
    let Bk <- check .prf Γ B
    let _ <- is_type Bk
    .some ★
  | .prf, Γ, (.pair t s) => do
    let A <- check .prf Γ t
    let Ak <- check .prf Γ A
    let _ <- is_type Ak
    let B <- check .prf Γ s
    let Bk <- check .prf Γ B
    let _ <- is_type Bk
    .some (A ⊗ B)
  | .prf, Γ, (.fst t) => do
    let T <- check .prf Γ t
    let (A, _) <- is_times T
    .some A
  | .prf, Γ, (.snd t) => do
    let T <- check .prf Γ t
    let (_, B) <- is_times T
    .some B
  | .prf, Γ, .unit_ty => do
    let _ <- check .wf Γ ()
    .some ★
  | .prf, Γ, .unit => do
    let _ <- check .wf Γ ()
    .some (U)
  | .prf, Γ, (.unit_rec d u t) => do
    let _ <- check .prf Γ d
    let T <- check .prf Γ u
    let _ <- is_unit T
    let A <- check .prf Γ t
    let Ak <- check .prf Γ A
    let _ <- is_type Ak
    .some A
  decreasing_by
    repeat sorry

  @[simp]
  abbrev CheckSoundType (Γ : Ctx Term) : (v : JudgmentVariant) -> CheckArgs v -> CheckRets v -> Prop
  | .prf => λ t r => ∀ A, r = .some A -> Γ ⊢ t : A
  | .wf => λ _ r => r = .some () -> ⊢ Γ

  theorem check_sound : check v Γ t = r -> CheckSoundType Γ v t r := by
  intro h
  induction v, Γ, t, r using check.induct <;> simp at *
  case _ => intro h2; constructor
  case _ ih1 ih2 =>
    intro h1; subst h1
    rw [Option.bind_eq_some] at h
    cases h; case _ v1 h =>
    cases h; case _ h1 h2 =>
    rw [Option.bind_eq_some] at h2
    cases h2; case _ v2 h2 =>
    cases h2; case _ h2 h3 =>
    rw [Option.bind_eq_some] at h3
    cases h3; case _ v3 h3 =>
    replace ih1 := ih1 _ h1
    replace ih2 := ih2 h2
    sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry

end Fomega
