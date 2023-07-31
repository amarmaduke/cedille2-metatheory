
import «Mathlib»
import Common.Util
import Common.Syntax
import Common.Notation

notation:300 "Map!" α:300 => List (Name × α)

namespace Map
  def single (x : Name) (t : α) : Map! α := List.cons (x, t) List.nil

  notation "[" x ":" t "]" => single x t

  def mem (m : Map! α) (x : Name) : Bool :=
    match m with
    | List.nil => false
    | List.cons (n, _t) tail => if n == x then true else mem tail x

  @[simp] def mem_nil : @mem α [] x = false := by {
    unfold mem; simp
  }

  @[simp] def mem_cons : y = x -> mem (List.cons (y, v) t) x = true := by {
    intro h; unfold mem; rw [h]; simp
  }

  @[simp] def mem_cons_not : y ≠ x -> mem (List.cons (y, v) t) x = mem t x := by {
    intro h
    have lem1 : (y == x) = false := Name.beq_of_not_eq h
    generalize h1 : mem ((y, v) :: t) x = m'
    unfold mem at h1
    rewrite [lem1] at h1
    simp at h1
    rw [h1]
  }

  def lookup (m : Map! α) (x : Name) (h : mem m x = true) : α :=
    match m with
    | List.nil => by {
      simp at h
    }
    | List.cons (n, t) tail => if h' : n == x then t else by {
      have lem1 := Name.not_eq_of_beq (Name.beq_of_not_beq h')
      rewrite [mem_cons_not lem1] at h
      exact (Map.lookup tail x h)
    }

  def lookup? (m : Map! α) (x : Name) : Option α := List.lookup x m

  def remove (m : Map! α) (x : Name) : Map! α :=
    match m with
    | List.nil => List.nil
    | List.cons (n, t) tail =>
      if n == x then tail else
        List.cons (n, t) (remove tail x)

  def fv (m : Map! α) : FvSet! :=
    match m with
    | List.nil => List.nil
    | List.cons (n, _) tail => List.cons n (fv tail)

  @[simp] lemma fv_append : fv (Γ ++ Δ) = fv Γ ++ fv Δ := sorry

  @[simp] lemma fv_single : fv (single x A) = [x] := sorry

  def subst [HasSubst α α] (v : Name) (w : α) (Γ : Map! α) : Map! α :=
    match Γ with
    | List.nil => List.nil
    | List.cons (n, t) tail => List.cons (n, [v := w]t) (subst v w tail)

  instance [HasSubst α α] : HasSubst α (Map! α) where
    subst := subst

  @[simp] lemma subst_nil [HasSubst α α] {t : α} : [x := t](@List.nil (Name × α)) = [] := sorry

  @[simp] lemma subst_append [HasSubst α α] {t : α} {Γ Δ : Map! α}
    : [x := t](Γ ++ Δ) = [x := t]Γ ++ [x := t]Δ
    := sorry

  def rename [HasHOpen α] [HasHClose α] (x y : Name) (Γ : Map! (α n)) : Map! (α n) :=
    match Γ with
    | List.nil => List.nil
    | List.cons (n, t) tail => if x == n
      then List.cons (y, {_|-> y}{_<-| y}t) (rename x y tail)
      else List.cons (n, {_|-> y}{_<-| y}t) (rename x y tail)

  notation:200 "[" x:200 "|->" y:200 "]" t:200 => rename x y t

  @[simp] lemma rename_append [HasHOpen α] [HasHClose α] {Γ Δ : Map! (α n)}
    : [x |-> y](Γ ++ Δ) = [x |-> y]Γ ++ [x |-> y]Δ
  := sorry

  @[simp] lemma rename_single [HasHOpen α] [HasHClose α] {A : (α n)}
    : [x |-> y][x : A] = [y : {_|-> y}{_<-| x}A]
  := sorry

  def size (m : Map! α) : Nat :=
    match m with
    | List.nil => 0
    | List.cons _h t => size t + 1

  @[simp] def size_nil : @size α List.nil = 0 := by congr

  @[simp] def size_cons : size (h :: t) = size t + 1 := by congr

  def size_remove : mem m x = true -> size (remove m x) < size m := by {
    induction m <;> intro h
    case nil => {
      simp at h
    }
    case cons y t t_ih => {
      let (y1, y2) := y
      cases (Name.decEq y1 x)
      case isFalse h' => {
        rewrite [mem_cons_not h'] at h
        unfold remove
        have lem1 : (y1 == x) = false := sorry
        rewrite [lem1]; simp
        have lem2 := t_ih h
        linarith
      }
      case isTrue h' => {
        unfold remove; rewrite [h']; simp
      }
    }
  }

  @[simp] lemma subst_single [HasSubst α α] {t A : α}
    : [x := t][y : A] = [y : [x := t]A]
    := sorry

  lemma append_cases (Γ : Map! α)
    : (Γ = []) ∨ (∃ x : Name, ∃ A : α, ∃ Δ : Map! α, Γ = Δ ++ [x:A])
    := sorry

  def Disjoint (Γ1 Γ2 : Map! α) : Prop := FvSet.Disjoint (fv Γ1) (fv Γ2)

  -- def lookup_implies_Mem : lookup Γ x = some A -> x ∈ (fv Γ) := sorry

  -- def lookup_weaken : Disjoint (Γ₁ ++ Γ₂) Δ
  --   -> lookup (Γ₁ ++ Γ₂) x = some A
  --   -> lookup (Γ₁ ++ Δ ++ Γ₂) x = some A
  --   :=
  --   sorry

  def mem_disjoint {Γ : Map! α} {a : α} : ¬ x ∈ fv Δ -> Disjoint Γ Δ -> Disjoint ([x : a] ++ Γ) Δ := sorry
end Map