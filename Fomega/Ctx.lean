
import Common

namespace Fomega

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

end Fomega

infix:1000 "@" => Fomega.nth
infix:1000 "d@" => Fomega.dnth
