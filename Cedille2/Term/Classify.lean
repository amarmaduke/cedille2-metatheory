import Common
import Cedille2.Term
import Cedille2.Reduction

namespace Cedille2.Term
  def action_size : Subst.Action Term -> Nat
  | .su t => t.size
  | .re _ => 0

  inductive Class : Type where
  | term : Class
  | type : Class
  | kind : Class
  | none : Class

  @[simp]
  def class_eq : Class -> Class -> Bool
  | .term, .term => true
  | .type, .type => true
  | .kind, .kind => true
  | .none, .none => true
  | _, _ => false

  @[simp]
  instance instClassBEq : BEq Class where
    beq := class_eq

  @[simp]
  instance instClassLawfulBEq : LawfulBEq Class where
    eq_of_beq := by {
      intro a b e
      cases a <;> cases b <;> simp [*] at * <;> injection e
    }
    rfl := by intro a <;> cases a <;> simp

  instance instDecidableEq : DecidableEq Class
  | a, b => by {
    cases a
    all_goals {
      cases b <;> simp
      any_goals (apply isFalse; intro h; apply h)
      apply isTrue; simp
    }
  }

  def witness : Class -> Term
  | .term => .var .type 0
  | .type => .var .kind 0
  | .kind => .const .type
  | .none => .const .kind

  @[simp]
  def size_of_subst_rename_renamer : Ren -> Ren
  | _, 0 => 0
  | r, n + 1 => (r n) + 1

  @[simp]
  theorem size_of_subst_rename {t : Term} (r : Ren)
    : Term.size ([r.to]t) = Term.size t
  := by
  have lem (r : Ren) :
    .re 0::(@S Term) ⊙ r.to = (size_of_subst_rename_renamer r).to
  := by
    unfold Ren.to; simp
    funext; case _ x =>
      cases x <;> simp
      case _ n => unfold Subst.compose; simp
  induction t generalizing r <;> simp [*]
  case _ => unfold Ren.to; simp

  theorem size_of_subst_lift (σ : Subst Term)
    : (∀ n, action_size (σ n) = 0) -> ∀ n, action_size ((^σ) n) = 0
  := by
  intro h n; simp
  cases n
  case _ => simp [action_size]
  case _ n =>
    simp [Subst.compose]
    generalize ψdef : σ n = ψ
    cases ψ
    case _ m => simp [action_size]
    case _ t =>
      have lem := h n
      simp [action_size]
      rw [ψdef] at lem
      simp [action_size] at lem
      have lem2 : @S Term = Ren.to (λ x => x + 1) := by
        unfold S; unfold Ren.to; simp
      rw [lem2, size_of_subst_rename]
      apply lem

  theorem size_of_subst {σ : Subst Term} {t : Term}
    : (∀ n, action_size (σ n) = 0) -> ([σ]t).size = t.size
  := by
  intro h
  induction t generalizing σ <;> simp [*]
  case var w k =>
    generalize ψdef : σ k = ψ
    cases ψ <;> simp at *
    case _ t =>
      have lem := h k
      rw [ψdef] at lem; simp [action_size] at lem
      apply lem
  case lam m t A iht ihA =>
    have lem : ∀ n, action_size ((^σ) n) = 0 := size_of_subst_lift σ h
    simp at lem; apply ihA lem
  case all m A B ihA ihB =>
    have lem : ∀ n, action_size ((^σ) n) = 0 := size_of_subst_lift σ h
    simp at lem; apply ihB lem
  case inter _ _ B t s ihB iht ihs =>
    have lem : ∀ n, action_size ((^σ) n) = 0 := size_of_subst_lift σ h
    simp at lem; apply ihB lem
  case inter_ty A B ihA ihB =>
    have lem : ∀ n, action_size ((^σ) n) = 0 := size_of_subst_lift σ h
    simp at lem; apply ihB lem

  @[simp]
  theorem size_of_witness
    : Term.size (t β[witness c]) = Term.size t
  := by
  have lem : ∀ n : Nat, action_size ((.su (witness c) :: I) n) = 0 := by
    intro n; cases n
    case _ => cases c <;> simp [action_size, witness]
    case _ => simp [action_size]
  simp at lem
  rw [size_of_subst lem]

  @[simp]
  def classify : Term -> Class
  | .var .type _ => .term
  | .var .kind _ => .type
  | .const .type => .kind
  | .const .kind => .none
  | .lam _ _ t => classify t
  | .app _ (.lam _ _ t) a =>
    let ct := classify t
    let ca := classify a
    let cw := classify (t β[witness ca])
    if ct != .none && ca != .none && ct == cw
    then ct
    else .none
  | .app _ f _ => classify f
  | .all _ _ B => classify B
  | .inter _ _ _ t s =>
    if t.classify == .term && s.classify == .term
    then .term
    else .none
  | .fst t =>
    if t.classify == .term then .term
    else .none
  | .snd t =>
    if t.classify == .term then .term
    else .none
  | .inter_ty _ _ => .type
  | .refl t =>
    if t.classify == .term then .term
    else .none
  | .subst _ e t =>
    if e.classify == .term && t.classify == .term
    then .term
    else .none
  | .phi a b e =>
    if a.classify == .term && b.classify == .term && e.classify == .term
    then .term
    else .none
  | .eq _ _ => .type
  | .conv _ _ _ t => t.classify

  theorem classify_red {t t' : Term} : t -β> t' -> t.classify = t'.classify := by
  intro r; induction r <;> simp at *
  all_goals try simp [*]
  case _ =>
    split <;> simp at *
    case _ e1 e2 =>
      split
      case _ h =>
        rw [<-e2] at e1; rw [e1]
        sorry
      case _ h => sorry
    case _ e1 e2 => sorry
    case _ e1 e2 => sorry
    case _ e1 e2 => sorry
    case _ e1 e2 => sorry
  case _ =>
    split <;> simp at *
    case _ e1 e2 =>
      split at e1 <;> simp at *
      simp [*]
    case _ e _ _ _ =>
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


  -- def classify2 : Term -> Class
  -- | .var .type _ => .term
  -- | .var .kind _ => .type
  -- | .const .type => .kind
  -- | .const .kind => .none
  -- | .lam mt A t =>
  --   let cA := classify A
  --   if (cA == .kind || cA == .type) && classify t == .type
  --   then .type
  --   else .none
  -- | .lam m0 A t =>
  --   let cA := classify A
  --   if (cA == .kind || cA == .type) && classify t == .term
  --   then .term
  --   else .none
  -- | .lam mf A t =>
  --   if classify A == .type && classify t == .term
  --   then .term
  --   else .none
  -- | .app mt (.lam mt A t) a =>
  --   let cA := classify A
  --   let ca := classify a
  --   let clam := (cA == .kind && ca == .type) || (cA == .type && ca == .term)
  --   if clam && classify t == .type && classify (t β[ witness ca ]) == .type
  --   then .type
  --   else .none
  -- | .app mt f a =>
  --   let ca := classify a
  --   if (ca == .type || ca == .term) && classify f = .type
  --   then .type
  --   else .none
  -- | .app m0 (.lam m0 A t) a =>
  --   let cA := classify A
  --   let ca := classify a
  --   let clam := (cA == .kind && ca == .type) || (cA == .type && ca == .term)
  --   if clam && classify t == .term && classify (t β[ witness ca ]) == .term
  --   then .term
  --   else .none
  -- | .app m0 f a =>
  --   let ca := classify a
  --   if (ca == .type || ca == .term) && classify f = .term
  --   then .term
  --   else .none
  -- | .app mf (.lam mf A t) a =>
  --   let ca := classify a
  --   if classify A == .type
  --     && classify t == .term
  --     && ca == .term
  --     && classify (t β[ witness ca ]) == .term
  --   then .term
  --   else .none
  -- | .app mf f a =>
  --   if classify f == .term && classify a == .term
  --   then .term
  --   else .none
  -- | .all mt A B =>
  --   let cA := classify A
  --   if (cA == .kind || cA == .type) && classify B == .kind
  --   then .kind
  --   else .none
  -- | .all m0 A B =>
  --   let cA := classify A
  --   if (cA == .kind || cA == .type) && classify B == .type
  --   then .type
  --   else .none
  -- | .all mf A B =>
  --   if classify A == .type && classify B == .type
  --   then .type
  --   else .none
  -- | .inter _ _ T a b =>
  --   if classify T == .type && classify a == .term && classify b == .term
  --   then .term
  --   else .none
  -- | .fst t => if classify t == .term then .term else .none
  -- | .snd t => if classify t == .term then .term else .none
  -- | .inter_ty A B =>
  --   if classify A == .type && classify B == .type
  --   then .type
  --   else .none
  -- | .refl t =>
  --   if classify t == .term
  --   then .term
  --   else .none
  -- | .subst P e t =>
  --   if classify P == .type && classify e == .term && classify t == .term
  --   then .term
  --   else .none
  -- | .phi a b e =>
  --   if classify a == .term && classify b == .term && classify e == .term
  --   then .term
  --   else .none
  -- | .eq a b =>
  --   if classify a == .term && classify b == .term
  --   then .type
  --   else .none
  -- | .conv _ _ A t =>
  --   if classify A == .type && classify t == .term
  --   then .term
  --   else .none
  -- termination_by t => Term.size t

end Cedille2.Term
