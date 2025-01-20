
import Common.Substitution

variable {T : Type} [Inhabited T] [SubstitutionType T] [SubstitutionTypeLaws T]

def Ctx (T : Type) := List T

@[simp]
def nth : List T -> Nat -> T
| [], _ => default
| .cons h _, 0 => h
| .cons _ t, n + 1 => nth t n

@[simp]
def dnth : List T -> Nat -> T
| [], _ => default
| .cons h _, 0 => [S]h
| .cons _ t, n + 1 => [S](dnth t n)

infix:1000 "@" => nth
infix:1000 "d@" => dnth

-- theorem dnth_as_nth : Γ d@ n = [Sn (n + 1)](Γ @ n) := by
-- induction n generalizing Γ
-- case zero =>
--   cases Γ <;> simp
-- case succ n ih =>
--   simp; cases Γ <;> simp
--   case _ A Γ =>
--     rw [ih]; simp
