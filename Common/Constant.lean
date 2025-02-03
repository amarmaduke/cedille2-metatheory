inductive Const : Type where
| kind | type
deriving Repr

namespace Const
  @[simp]
  def beq : Const -> Const -> Bool
  | .kind, .kind => true
  | .type, .type => true
  | _, _ => false
end Const

@[simp]
instance instBEq_Const : BEq Const where
  beq := Const.beq

instance instLawfulBEq_Const : LawfulBEq Const where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> simp at * <;> simp [*]
  rfl := by intro a; cases a <;> simp
