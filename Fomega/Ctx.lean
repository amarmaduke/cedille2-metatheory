
import Common

namespace Fomega

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

end Fomega

infix:1000 "@" => Fomega.nth
infix:1000 "d@" => Fomega.dnth

namespace Fomega

  theorem dnth_as_nth : Γ d@ n = [Sn (n + 1)](Γ @ n) := by
  induction n generalizing Γ
  case zero =>
    cases Γ <;> simp
  case succ n ih =>
    simp; cases Γ <;> simp
    case _ A Γ =>
      rw [ih]; simp

end Fomega
