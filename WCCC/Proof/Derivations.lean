import Common
import WCCC.Proof

namespace WCCC

  @[simp]
  def cBool : Term := ∀f[★] ∀f[0!!] ∀f[1!!] 2!!

  @[simp]
  def ctt : Term := λf[★] λf[0!!] λf[1!!] 1!

  @[simp]
  def cff : Term := λf[★] λf[0!!] λf[1!!] 0!

  @[simp]
  def cFalse : Term := ∀f[★] 0!!

end WCCC
