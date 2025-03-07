
def contra {A B} : (A -> B) -> Not B -> Not A := by
  intros h1 h2 h3
  exact (h2 (h1 h3))

theorem demorgan : ¬ (A ∨ B) -> ¬ A ∧ ¬ B := by {
  intro h; apply And.intro _ _
  intro h2; apply h (Or.inl h2)
  intro h2; apply h (Or.inr h2)
}

theorem demorgan3 : ¬ (A ∨ B ∨ C) -> ¬ A ∧ ¬ B ∧ ¬ C := by {
  intro h
  have lem := demorgan h
  cases lem; case _ h1 h2 =>
  have lem2 := demorgan h2
  cases lem2; case _ h3 h4 =>
  apply And.intro h1 _
  apply And.intro h3 h4
}

-- theorem demorgan4 : ¬ (A ∨ B ∨ C ∨ D) -> ¬ A ∧ ¬ B ∧ ¬ C ∧ ¬ D := by {
--   intro h
--   have lem := demorgan3 h
--   casesm* _ ∧ _; case _ h1 h2 h3 =>
--   have lem2 := demorgan h3
--   cases lem2; case _ h4 h5 =>
--   apply And.intro h1 (And.intro h2 (And.intro h4 h5))
-- }

def ne_sym : x ≠ y -> y ≠ x := by intro h1 h2; subst h2; contradiction

def append_eq {a c : List α} {b d : α} : a ++ [b] = c ++ [d] -> a = c ∧ b = d := by {
  intro h
  induction a generalizing c
  case nil =>
    rw [List.nil_append] at h
    cases c
    case nil =>
      rw [List.nil_append] at h
      injection h with e1 e2; simp [*]
    case cons hd tl => injection h with e1 e2; simp at *
  case cons hd tl ih =>
    cases c
    case nil => injection h with e1 e2; simp at *
    case cons hd' tl' =>
      injection h with e1 e2; simp at *
      have lem := ih e2
      simp [*]
}

def pair_eq : (a, b) = (c, d) -> a = c ∧ b = d := by {
  intro h; injection h with e1 e2
  subst e1; subst e2; simp
}

@[simp]
def rep : Nat -> (A -> A) -> A -> A
| 0, _, a => a
| n + 1, f, a => f (rep n f a)

namespace Nat
  inductive DecOrd (n m : Nat) : Prop where
  | eq : n = m -> DecOrd n m
  | lt : n < m -> DecOrd n m
  | gt : n > m -> DecOrd n m

  def decOrd n m : DecOrd n m := by
    cases Nat.decLt n m
    case _ h =>
      cases Nat.decEq n m
      case _ h2 =>
        cases Nat.decLt m n
        case _ h3 => exfalso; omega
        case _ h => exact DecOrd.gt h
      case _ h => exact DecOrd.eq h
    case _ h => exact DecOrd.lt h
end Nat
