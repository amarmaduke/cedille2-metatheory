inductive Mode where
| free
| erased
| type
deriving Repr

notation "m0" => Mode.erased
notation "mt" => Mode.type
notation "mf" => Mode.free

@[reducible, simp]
instance Mode_inst_BEq : BEq Mode where
  beq m1 m2 := match m1, m2 with
  | .free, .free => true
  | .erased, .erased => true
  | .type, .type => true
  | _, _ => false

instance Mode_inst_LawfulBEq : LawfulBEq Mode where
  eq_of_beq := by intro m1 m2 h; cases m1 <;> cases m2 <;> simp at *
  rfl := by intro m; cases m <;> simp
