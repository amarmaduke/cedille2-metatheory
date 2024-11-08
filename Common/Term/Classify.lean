
import Common.Term
import Common.Term.Substitution

namespace Term

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
  | .term => bound .type 0
  | .type => bound .kind 0
  | .kind => const .type
  | .none => .none

  def size_of_subst_rename_renamer : Ren -> Ren
  | _, 0 => 0
  | r, n + 1 => rS (r n)

  @[simp]
  theorem size_of_subst_rename
    : Term.size ([r#r]t) = Term.size t
  := by {
    have lem r : .rename 0::S ⊙ r#r = r#(size_of_subst_rename_renamer r) := by {
      funext
      case _ x =>
        cases x <;> simp [size_of_subst_rename_renamer]
        unfold Subst.compose; simp
    }
    induction t generalizing r
    all_goals simp [*]
  }

  theorem size_of_subst_lift (σ : Subst Term)
    : (∀ n, (σ n).size = 0) -> ∀ n, ((^σ) n).size = 0
  := by {
    intro h n; simp
    cases n
    case _ => simp [SubstAction.size]
    case _ n =>
      simp [Subst.compose]
      generalize ψdef : σ n = ψ
      cases ψ
      case _ m => simp [SubstAction.size]
      case _ t =>
        have lem := h n
        simp [SubstAction.size]
        rw [ψdef] at lem
        simp [SubstAction.size] at lem
        rw [Term.S_to_rS, size_of_subst_rename]
        apply lem
  }

  theorem size_of_subst {σ : Subst Term} {t : Term}
    : (∀ n, (σ n).size = 0) -> ([σ]t).size = t.size
  := by {
    intro h
    induction t generalizing σ <;> simp [*]
    case bound w k =>
      generalize ψdef : σ k = ψ
      cases ψ <;> simp at *
      case _ t =>
        have lem := h k
        rw [ψdef] at lem; simp [SubstAction.size] at lem
        apply lem
    case lam m t A iht ihA =>
      have lem : ∀ n, ((^σ) n).size = 0 := size_of_subst_lift σ h
      simp at lem; apply ihA lem
    case all m A B ihA ihB =>
      have lem : ∀ n, ((^σ) n).size = 0 := size_of_subst_lift σ h
      simp at lem; apply ihB lem
    case prod A B ihA ihB =>
      have lem : ∀ n, ((^σ) n).size = 0 := size_of_subst_lift σ h
      simp at lem; apply ihB lem
  }

  @[simp]
  theorem size_of_witness
    : Term.size ([.replace (witness c) :: I ]t) = Term.size t
  := by {
    have lem : ∀ n : Nat, ((.replace (witness c) :: I) n).size = 0 := by {
      intro n; cases n
      case _ => cases c <;> simp [SubstAction.size, witness]
      case _ => simp [SubstAction.size]
    }
    simp at lem
    rw [size_of_subst lem]
  }

  def classify : Term -> Class
  | bound .type _ => .term
  | bound .kind _ => .type
  | none => .none
  | const .type => .kind
  | const .kind => .none
  | lam mt A t =>
    let cA := classify A
    if (cA == .kind || cA == .type) && classify t == .type
    then .type
    else .none
  | lam m0 A t =>
    let cA := classify A
    if (cA == .kind || cA == .type) && classify t == .term
    then .term
    else .none
  | lam mf A t =>
    if classify A == .type && classify t == .term
    then .term
    else .none
  | app mt (lam mt A t) a =>
    let cA := classify A
    let ca := classify a
    let clam := (cA == .kind && ca == .type) || (cA == .type && ca == .term)
    if clam && classify t == .type && classify (t β[ witness ca ]) == .type
    then .type
    else .none
  | app mt f a =>
    let ca := classify a
    if (ca == .type || ca == .term) && classify f = .type
    then .type
    else .none
  | app m0 (lam m0 A t) a =>
    let cA := classify A
    let ca := classify a
    let clam := (cA == .kind && ca == .type) || (cA == .type && ca == .term)
    if clam && classify t == .term && classify (t β[ witness ca ]) == .term
    then .term
    else .none
  | app m0 f a =>
    let ca := classify a
    if (ca == .type || ca == .term) && classify f = .term
    then .term
    else .none
  | app mf (lam mf A t) a =>
    let ca := classify a
    if classify A == .type
      && classify t == .term
      && ca == .term
      && classify (t β[ witness ca ]) == .term
    then .term
    else .none
  | app mf f a =>
    if classify f == .term && classify a == .term
    then .term
    else .none
  | all mt A B =>
    let cA := classify A
    if (cA == .kind || cA == .type) && classify B == .kind
    then .kind
    else .none
  | all m0 A B =>
    let cA := classify A
    if (cA == .kind || cA == .type) && classify B == .type
    then .type
    else .none
  | all mf A B =>
    if classify A == .type && classify B == .type
    then .type
    else .none
  | pair T a b =>
    if classify T == .type && classify a == .term && classify b == .term
    then .term
    else .none
  | fst t => if classify t == .term then .term else .none
  | snd t => if classify t == .term then .term else .none
  | prod A B =>
    if classify A == .type && classify B == .type
    then .type
    else .none
  | refl t =>
    if classify t == .term
    then .term
    else .none
  | subst P e =>
    if classify P == .type && classify e == .term
    then .term
    else .none
  | phi a b e =>
    if classify a == .term && classify b == .term && classify e == .term
    then .term
    else .none
  | eq A a b =>
    if classify A == .type && classify a == .term && classify b == .term
    then .term
    else .none
  | conv _ t _ => classify t
  termination_by t => size t

end Term
