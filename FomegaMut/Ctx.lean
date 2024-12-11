
import Common

namespace FomegaMut

  abbrev Ctx := List Term

  @[simp]
  def nth : List Term -> Nat -> Term
  | [], _ => ★
  | .cons h _, 0 => h
  | .cons _ t, n + 1 => nth t n

  @[simp]
  def dnth : List Term -> Nat -> Term
  | [], _ => ★
  | .cons h _, 0 => [S]h
  | .cons _ t, n + 1 => [S](dnth t n)

end FomegaMut

infix:1000 "@" => FomegaMut.nth
infix:1000 "d@" => FomegaMut.dnth

namespace FomegaMut

  theorem dnth_as_nth : Γ d@ n = [Sn (n + 1)](Γ @ n) := by
  induction n generalizing Γ
  case zero =>
    cases Γ <;> simp
  case succ n ih =>
    simp; cases Γ <;> simp
    case _ A Γ =>
      rw [ih]; simp

end FomegaMut
