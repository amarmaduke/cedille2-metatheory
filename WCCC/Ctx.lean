
import Common

namespace WCCC

  abbrev Ctx := List Term

  @[simp]
  def nth : List Term -> Nat -> Term
  | [], _ => .none
  | .cons h _, 0 => h
  | .cons _ t, n + 1 => nth t n

  @[simp]
  def dnth : List Term -> Nat -> Term
  | [], _ => .none
  | .cons h _, 0 => [S]h
  | .cons _ t, n + 1 => [S](dnth t n)

end WCCC

infix:1000 "@" => WCCC.nth
infix:1000 "d@" => WCCC.dnth

namespace WCCC

  theorem dnth_as_nth : Γ d@ n = [Sn (n + 1)](Γ @ n) := by
  induction n generalizing Γ
  case zero =>
    cases Γ <;> simp
  case succ n ih =>
    simp; cases Γ <;> simp
    case _ A Γ =>
      rw [ih]; simp

end WCCC
