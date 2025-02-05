
import Fomega.Proof
import Fomega.Basic

namespace Fomega
  partial def normalize (t : Term) : Term :=
    let t' := t.compl
    if t' == t then t else normalize t'

  @[simp]
  def is_kind : Term -> Option Const
  | .const K => .some K
  | _ => .none

  @[simp]
  def is_type : Term -> Option Unit
  | .const .type => .some ()
  | _ => .none

  def is_dom : Const -> Const -> Option Unit := by sorry

  def is_pi (t : Term) : Option (Term × Term) :=
    match normalize t with
    | .all A B => .some (A, B)
    | _ => .none

  def is_times (t : Term) : Option (Term × Term) :=
    match normalize t with
    | .times A B => .some (A, B)
    | _ => .none

  def is_unit (t : Term) : Option Unit :=
    match normalize t with
    | .unit_ty => .some ()
    | _ => .none

  def conv (a b : Term) : Option Unit :=
    if normalize a == normalize b then .some () else .none

  inductive Depth where
  | term | type | kind

  def infer : Depth -> Ctx Term -> Term -> Option Term
  | .kind, Γ, ★ => .some □
  | .term, Γ, #x => .some (Γ d@ x)
  | .type, Γ, #x => .some (Γ d@ x)
  | Γ, Π[A] B => do
    let Ak <- infer Γ A
    let Ak <- is_kind Ak
    let Bk <- infer (A::Γ) B
    let Bk <- is_kind Bk
    let _ <- is_dom Ak Bk
    .some (.const Bk)
  | Γ, `λ[A] t => do
    let Ak <- infer Γ A
    let Ak <- is_kind Ak
    let B <- infer (A::Γ) t
    let Bk <- infer (A::Γ) B
    let Bk <- is_kind Bk
    let _ <- is_dom Ak Bk
    .some (Π[A] B)
  | Γ, f `@ a => do
    let T <- infer Γ f
    let (A, B) <- is_pi T
    let A' <- infer Γ a
    let _ <- conv A A'
    .some (B β[a])
  | Γ , A ⊗ B => do
    let Ak <- infer Γ A
    let _ <- is_type Ak
    let Bk <- infer Γ B
    let _ <- is_type Bk
    .some ★
  | Γ, (.pair t s) => do
    let A <- infer Γ t
    let Ak <- infer Γ A
    let _ <- is_type Ak
    let B <- infer Γ s
    let Bk <- infer Γ B
    let _ <- is_type Bk
    .some (A ⊗ B)
  | Γ, (.fst t) => do
    let T <- infer Γ t
    let (A, _) <- is_times T
    .some A
  | Γ, (.snd t) => do
    let T <- infer Γ t
    let (_, B) <- is_times T
    .some B
  | Γ, .unit_ty => .some ★
  | Γ, .unit => .some (U)
  | Γ, (.unit_rec d u t) => do
    let _ <- infer Γ d
    let T <- infer Γ u
    let _ <- is_unit T
    let A <- infer Γ t
    let Ak <- infer Γ A
    let _ <- is_type Ak
    .some A
  | _, _, _ => .none

  -- @[simp]
  -- abbrev CheckSoundType (Γ : Ctx Term) : (v : JudgmentVariant) -> CheckArgs v -> CheckRets v -> Prop
  -- | .prf => λ t r => ∀ A, r = .some A -> Γ ⊢ t : A
  -- | .wf => λ _ r => r = .some () -> ⊢ Γ

  -- theorem check_sound : check v Γ t = r -> CheckSoundType Γ v t r := by
  -- intro h
  -- induction v, Γ, t, r using check.induct <;> simp at *
  -- case _ => intro h2; constructor
  -- case _ ih1 ih2 =>
  --   intro h1; subst h1
  --   rw [Option.bind_eq_some] at h
  --   cases h; case _ v1 h =>
  --   cases h; case _ h1 h2 =>
  --   rw [Option.bind_eq_some] at h2
  --   cases h2; case _ v2 h2 =>
  --   cases h2; case _ h2 h3 =>
  --   rw [Option.bind_eq_some] at h3
  --   cases h3; case _ v3 h3 =>
  --   replace ih1 := ih1 _ h1
  --   replace ih2 := ih2 h2
  --   sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry

end Fomega
