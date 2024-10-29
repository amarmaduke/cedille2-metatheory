
import Common

namespace WCCC

  namespace Mode
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
  end Mode

  infixl:190 " ∈ " => Mode.Mem
  infixl:200 "*" => Mode.mul

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

  @[simp]
  instance : HMul Mode (List (Mode × A)) (List (Mode × A)) where
    hMul m Γ := List.map (λ (m2, a) => (Mode.mul m m2, a)) Γ

  prefix:max "#" => λ m => Term.bound (Term.mode_to_sort m) 0

end WCCC
