

def contra {A B} : (A -> B) -> Not B -> Not A := by
  intros h1 h2 h3
  exact (h2 (h1 h3))

def ne_sym : x ≠ y -> y ≠ x := sorry 

def append_eq {a c : List α} {b d : α} : a ++ [b] = c ++ [d] -> a = c ∧ b = d := sorry

def pair_eq : (a, b) = (c, d) -> a = c ∧ b = d := sorry

def nat_add_le {a b c : Nat} : a + b ≤ c -> a ≤ c ∧ b ≤ c := sorry  
