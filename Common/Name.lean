
import «Mathlib»
import Common.Util

def Name := String × Nat

instance : BEq Name where
  beq := λ (x1, i1) (x2, i2) => x1 == x2 && i1 == i2

instance : LawfulBEq Name where
  eq_of_beq := @λ a b h => @eq_of_beq (String × Nat) _ _ a b h
  rfl := @λ a => @LawfulBEq.rfl (String × Nat) _ _ a

instance : Ord Name where
  compare := λ (x1, i1) (x2, i2) =>
    match (compare x1 x2) with
    | Ordering.lt => Ordering.lt
    | Ordering.eq => compare i1 i2
    | Ordering.gt => Ordering.gt

namespace Name
  def beq_of_not_eq {a b : Name} : a ≠ b -> (a == b) = false := sorry
  def not_eq_of_beq {a b : Name} : (a == b) = false -> a ≠ b := sorry
  def beq_of_not_beq {a b : Name} : (a == b) ≠ true -> (a == b) = false := sorry 

  def decEq (a : Name) (b : Name) : Decidable (a = b) :=
    match String.decEq a.1 b.1 with
    | isTrue h1 =>
      match Nat.decEq a.2 b.2 with
      | isTrue h2 =>
        have lem1 : a = b := by {
          cases a
          cases b
          congr
        }
        isTrue lem1
      | isFalse h2 =>
        have lem1 : a ≠ b := by {
          intros h3
          have lem2 : a.2 = b.2 := by congr
          contradiction
        }
        isFalse lem1
    | isFalse h1 =>
      have lem1 : a ≠ b := by {
        intros h2
        have lem2 : a.1 = b.1 := by congr
        contradiction
      }
      isFalse lem1

  def inc (x : Name) : Name :=
    match x with
    | (n, i) => (n, i + 1)
end Name

def FvSet := List Name

instance : Membership Name FvSet where
  mem := λ n s => List.Mem n s

instance : HAppend FvSet FvSet FvSet where
  hAppend := λ x y => List.append x y

instance : HasSubset FvSet where
  Subset := List.Subset

namespace FvSet
  def Disjoint (l1 l2 : FvSet) : Prop := List.Disjoint l1 l2

  def not_mem_nil : x ∉ [] := sorry

  def not_mem_left {A B : FvSet} : x ∉ A ++ B -> x ∉ A := sorry

  def not_mem_right {A B : FvSet} : x ∉ A ++ B -> x ∉ B := sorry

  def not_mem_head {A : FvSet} : x ∉ y :: A -> x ≠ y := sorry

  def not_mem_cons {A : FvSet} : x ∉ y :: A -> x ∉ A := sorry 

end FvSet

namespace Name

  def fresh_with_seed (set : FvSet) (x : Name) : Name :=
    match set with
    | List.nil => x
    | List.cons n tail => if n == x
      then fresh_with_seed tail (inc x)
      else fresh_with_seed tail x
  
  def fresh (set : FvSet) : Name :=
    match set with
    | List.nil => ("x", 0)
    | List.cons n tail => fresh_with_seed tail n 

  lemma fresh_is_fresh : (fresh Γ) ∉ Γ := sorry

end Name