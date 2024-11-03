
import Common

namespace WCCC.Mode

  @[simp]
  def dom (m : Mode) (K : Const) : Term :=
    match m with
    | mf => .const .type
    | mt => .const K
    | m0 => .const K

  @[simp]
  def codom (m : Mode) : Term :=
    match m with
    | mf => .const .type
    | mt => .const .kind
    | m0 => .const .type

  @[simp]
  def mul : Mode -> Mode -> Mode
  | mt, _ => mt
  | m0, mt => mt
  | m0, _ => m0
  | mf, m2 => m2

  inductive Mem : Mode -> Mode -> Prop where
  | mt : Mem m mt
  | m0_m0 : Mem m0 m0
  | m0_mf : Mem mf m0
  | mf : Mem mf mf

  infixl:190 " ∈ " => Mem
  infixl:200 "*" => mul

  @[simp]
  theorem mem_refl : m ∈ m := by {
    cases m <;> constructor <;> simp
  }

  @[simp]
  theorem mem_trans : m1 ∈ m2 -> m2 ∈ m3 -> m1 ∈ m3 := by {
    intro j1 j2
    cases m2
    case free =>
      cases j1; simp [*]
    case erased =>
      cases j1; exact j2
      cases j2 <;> constructor
    case type =>
      cases j2; exact j1
  }

  theorem mem_mul m : m1 ∈ m2 -> (m1*m) ∈ m2*m := by {
    intro h
    induction h generalizing m
    case _ m1 => simp; constructor
    case _ => cases m <;> simp
    case _ => cases m <;> simp; constructor
    case _ => simp
  }

  @[simp]
  theorem mul_assoc : m1*(m2*m3) = (m1*m2)*m3 := by {
    cases m1 <;> simp
    cases m2 <;> simp
    cases m3 <;> simp
  }

  theorem mul_comm : m1*m2 = m2*m1 := by {
    cases m1 <;> simp
    <;> cases m2 <;> simp
  }

  @[simp]
  instance : HMul Mode (List (Mode × A)) (List (Mode × A)) where
    hMul m Γ := List.map (λ (m2, a) => (m * m2, a)) Γ

  prefix:max "#" => λ m => Term.bound (Term.mode_to_sort m) 0

end WCCC.Mode
