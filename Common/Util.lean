
import Common.Mathlib

def contra {A B} : (A -> B) -> Not B -> Not A := by
  intros h1 h2 h3
  exact (h2 (h1 h3))

lemma demorgan : ¬ (A ∨ B) -> ¬ A ∧ ¬ B := by {
  intro h; apply And.intro _ _
  intro h2; apply h (Or.inl h2)
  intro h2; apply h (Or.inr h2)
}

def ne_sym : x ≠ y -> y ≠ x := sorry 

def append_eq {a c : List α} {b d : α} : a ++ [b] = c ++ [d] -> a = c ∧ b = d := sorry

def pair_eq : (a, b) = (c, d) -> a = c ∧ b = d := sorry

def nat_add_le {a b c : Nat} : a + b ≤ c -> a ≤ c ∧ b ≤ c := sorry  

def fin_cast {i u : Nat} : (h : i < i + 1) -> Fin.mk i h = ↑i := sorry

def fin_cast2 {n : Nat} {i : Fin (n + 1)} : i = ↑i.val := sorry
