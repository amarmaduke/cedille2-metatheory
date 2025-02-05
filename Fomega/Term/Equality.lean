import Fomega.Term.Definition

namespace Fomega.Const
  @[simp]
  def beq : Const -> Const -> Bool
  | .kind, .kind => true
  | .type, .type => true
  | _, _ => false

  @[simp]
  instance instBEq_Const : BEq Const where
    beq := Const.beq

  instance instLawfulBEq_Const : LawfulBEq Const where
    eq_of_beq := by intro a b h; cases a <;> cases b <;> simp at * <;> simp [*]
    rfl := by intro a; cases a <;> simp
end Fomega.Const

namespace Fomega.Term
  def beq : Term -> Term -> Bool
  | var x, var y => x == y
  | const k1, const k2 => k1 == k2
  | app x1 x2, app y1 y2 => beq x1 y1 && beq x2 y2
  | lam x1 x2, lam y1 y2 => beq x1 y1 && beq x2 y2
  | all x1 x2, all y1 y2 => beq x1 y1 && beq x2 y2
  | pair x1 x2, pair y1 y2 => beq x1 y1 && beq x2 y2
  | fst x, fst y => beq x y
  | snd x, snd y => beq x y
  | times x1 x2, times y1 y2 => beq x1 y1 && beq x2 y2
  | unit, unit => true
  | unit_ty, unit_ty => true
  | unit_rec x1 x2 x3, unit_rec y1 y2 y3 =>
    beq x1 y1 && beq x2 y2 && beq x3 y3
  | _, _ => false

  @[simp]
  instance instBEq_Term : BEq Term where
    beq := Term.beq

  instance instLawfulBEq_Term : LawfulBEq Term where
    eq_of_beq := by sorry
    rfl := by sorry

end Fomega.Term
