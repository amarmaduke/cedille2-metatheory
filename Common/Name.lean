-- 
import Common.Mathlib
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
  def beq_of_not_eq {a b : Name} : a ≠ b -> (a == b) = false := by {
    intro h
    have lem : ¬ (a == b) = true := contra (@LawfulBEq.eq_of_beq Name _ _ a b) h
    simp [*]
  }

  def not_eq_of_beq {a b : Name} : (a == b) = false -> a ≠ b := by {
    intro h1 h2; subst h2
    rw [LawfulBEq.rfl] at h1
    contradiction
  }

  def beq_of_not_beq {a b : Name} : (a == b) ≠ true -> (a == b) = false := by simp [*] 

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

notation:300 "FvSet!" => List Name

namespace FvSet
  def Disjoint (l1 l2 : FvSet!) : Prop := List.Disjoint l1 l2

  def not_mem_nil : x ∉ [] := by simp

  lemma not_mem_append {A B : FvSet!} : x ∉ A ++ B -> x ∉ A ∧ x ∉ B := by {
    intro h
    rewrite [List.mem_append_eq] at h
    apply And.intro _ _
    intro h2; apply h (Or.inl h2)
    intro h2; apply h (Or.inr h2)
  }

  def not_mem_left {A B : FvSet!} : x ∉ A ++ B -> x ∉ A := λ h => (not_mem_append h).1
  def not_mem_right {A B : FvSet!} : x ∉ A ++ B -> x ∉ B := λ h => (not_mem_append h).2

  def not_mem_head {A : FvSet!} : x ∉ y :: A -> x ≠ y := List.ne_of_not_mem_cons
  def not_mem_cons {A : FvSet!} : x ∉ y :: A -> x ∉ A := List.not_mem_of_not_mem_cons

  lemma subset_mem {x : Name} {A B : FvSet!} : A ⊆ B -> x ∈ A -> x ∈ B := by {
    intro h1 h2
    apply h1 h2
  }

  lemma subset_left {A B C : FvSet!} : A ⊆ B -> A ⊆ B ++ C := by {
    intro h
    induction A <;> simp at *
    case cons hd tl ih => {
      apply And.intro _ (ih h.2)
      apply Or.inl h.1
    }
  }

  lemma subset_right {A B C : FvSet!} : A ⊆ C -> A ⊆ B ++ C := by {
    intro h
    induction A <;> simp at *
    case cons hd tl ih => {
      apply And.intro _ (ih h.2)
      apply Or.inr h.1
    }
  }

  lemma subset_cons {A B : FvSet!} : x ∉ A -> A ⊆ x :: B -> A ⊆ B := by {
    intro h1 h2
    induction A <;> simp at *
    case cons hd tl ih => {
      replace h1 := demorgan h1
      casesm* _ ∧ _; case _ e1 e2 e3 e4 =>
      apply And.intro _ (ih e4 e2)
      cases e1
      case _ h => exfalso; subst h; contradiction
      case _ h => exact h
    }
  }

  lemma subset_trans {A B C : FvSet!} : A ⊆ B -> B ⊆ C -> A ⊆ C := by {
    intro h1 h2
    induction A generalizing B <;> simp at *
    case cons hd tl ih => {
      cases h1; case _ e1 e2 =>
      apply And.intro (h2 e1) (ih e2 h2)
    }
  }

  lemma subset_comm {A B C : FvSet!} : A ⊆ B ++ C -> A ⊆ C ++ B := by {
    intro h
    induction A generalizing B C <;> simp at *
    case cons hd tl ih => {
      apply And.intro _ (ih h.2)
      cases h.1
      case _ h => apply Or.inr h
      case _ h => apply Or.inl h
    }
  }

  lemma subset_append {A B C : FvSet!} : A ⊆ x :: (B ++ C) <-> A ⊆ (x :: B) ++ (x :: C) := by {
    apply Iff.intro _ _
    intro h
    induction A generalizing B C <;> simp at *
    case cons hd tl ih => {
      apply And.intro _ (ih h.2)
      cases h.1
      case _ h => apply Or.inl h
      case _ h => {
        cases h
        case _ h =>  apply Or.inr _; apply Or.inl h
        case _ h => {
          apply Or.inr _; apply Or.inr _; apply Or.inr h
        }
      }
    }
    intro h
    induction A generalizing B C <;> simp at *
    case cons hd tl ih => {
      apply And.intro _ (ih h.2)
      cases h.1
      case _ h => apply Or.inl h
      case _ h => {
        cases h
        case _ h => apply Or.inr _; apply Or.inl h
        case _ h => {
          cases h
          case _ h => apply Or.inl h
          case _ h => apply Or.inr _; apply Or.inr h
        }
      }
    }
  } 

  lemma not_mem_subset_not_mem {A B : FvSet!} : x ∉ A -> B ⊆ A -> x ∉ B := by {
    intro h1 h2
    induction B generalizing A <;> simp at *
    case cons hd tl ih => {
      intro h
      cases h
      case _ h => subst h; apply h1 h2.1
      case _ h => apply (ih h1 h2.2) h
    }
  }


end FvSet

namespace Name

  def fresh_with_seed (set : FvSet!) (x : Name) : Name :=
    match set with
    | List.nil => x
    | List.cons n tail => if n == x
      then fresh_with_seed tail (inc x)
      else fresh_with_seed tail x
  
  def fresh (set : FvSet!) : Name :=
    match set with
    | List.nil => ("x", 0)
    | List.cons n tail => fresh_with_seed tail n 

  lemma fresh_is_fresh : (fresh Γ) ∉ Γ := sorry

end Name