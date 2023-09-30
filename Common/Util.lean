
import Common.Mathlib

def contra {A B} : (A -> B) -> Not B -> Not A := by
  intros h1 h2 h3
  exact (h2 (h1 h3))

lemma demorgan : ¬ (A ∨ B) -> ¬ A ∧ ¬ B := by {
  intro h; apply And.intro _ _
  intro h2; apply h (Or.inl h2)
  intro h2; apply h (Or.inr h2)
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

def fin_cast {i : Nat} : (h : i < i + 1) -> Fin.mk i h = ↑i := by {
  intro h
  induction i
  case zero => simp [*]
  case succ x ih => {
    simp; rw [<-Fin.succ_mk _ x, ih (by linarith), Fin.add_def, Fin.succ]; simp
    have lem1 : (x + 1) ≠ 0 := by linarith
    have lem2 := (@Nat.mod_eq_iff_lt x _ lem1).2 (by linarith)
    have lem3 : (Nat.succ x + 1) ≠ 0 := by linarith
    have lem4 := (@Nat.mod_eq_iff_lt (x + 1) _ lem3).2 (by linarith)
    rw [lem2, lem4]  
  }
}

def fin_cast2 {n : Nat} {i : Fin (n + 1)} : i = ↑i.val := by {
  induction i; simp
  case mk iv il =>
  induction iv <;> simp
  case succ x _ih => {
    have lem : x < n := by linarith
    rw [<- Fin.succ_mk n x lem, Fin.add_def, Fin.succ]; simp
    have lem1 : (n + 1) ≠ 0 := by linarith
    have lem2 := (@Nat.mod_eq_iff_lt (x + 1) _ lem1).2 (by linarith)
    rw [lem2]
  }
}
