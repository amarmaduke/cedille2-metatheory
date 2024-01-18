
import Common.Mathlib

def contra {A B} : (A -> B) -> Not B -> Not A := by
  intros h1 h2 h3
  exact (h2 (h1 h3))

lemma demorgan : ¬ (A ∨ B) -> ¬ A ∧ ¬ B := by {
  intro h; apply And.intro _ _
  intro h2; apply h (Or.inl h2)
  intro h2; apply h (Or.inr h2)
}

lemma demorgan3 : ¬ (A ∨ B ∨ C) -> ¬ A ∧ ¬ B ∧ ¬ C := by {
  intro h
  have lem := demorgan h
  cases lem; case _ h1 h2 =>
  have lem2 := demorgan h2
  cases lem2; case _ h3 h4 =>
  apply And.intro h1 _
  apply And.intro h3 h4
}

lemma demorgan4 : ¬ (A ∨ B ∨ C ∨ D) -> ¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D := by {
  intro h
  have lem := demorgan3 h
  casesm* _ ∧ _; case _ h1 h2 h3 =>
  have lem2 := demorgan h3
  cases lem2; case _ h4 h5 =>
  apply And.intro h1 (And.intro h2 (And.intro h4 h5))
}

def ne_sym : x ≠ y -> y ≠ x := by intro h1 h2; subst h2; contradiction

def append_eq {a c : List α} {b d : α} : a ++ [b] = c ++ [d] -> a = c ∧ b = d := by {
  intro h
  induction a generalizing c
  case nil => {
    rw [List.nil_append] at h
    cases c
    case nil => {
      rw [List.nil_append] at h
      injection h with e1 e2; simp [*]
    }
    case cons hd tl => injection h with e1 e2; simp at *
  }
  case cons hd tl ih => {
    cases c
    case nil => injection h with e1 e2; simp at *
    case cons hd' tl' => {
      injection h with e1 e2; simp at *
      have lem := ih e2
      simp [*]
    }
  }
}

def pair_eq : (a, b) = (c, d) -> a = c ∧ b = d := by {
  intro h; injection h with e1 e2
  subst e1; subst e2; simp
}
