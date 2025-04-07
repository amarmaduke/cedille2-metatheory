import Mathlib.SetTheory.ZFC.Basic
import SetTheory.Classical
import SetTheory.Relation
import SetTheory.Function

namespace ZFSet.Nat
  def zero : ZFSet := ∅
  def succ (n : ZFSet) := n ∪ {n}
  def pred := ZFSet.sUnion
end ZFSet.Nat

namespace Nat
  def to_zfset : Nat -> ZFSet
  | 0 => ZFSet.Nat.zero
  | n + 1 => ZFSet.Nat.succ n.to_zfset
end Nat

@[simp]
instance instOfNat_ZFSet : (n : Nat) -> OfNat ZFSet n := λ n => OfNat.mk (n.to_zfset)

namespace ZFSet.Nat

  theorem discriminate : ¬ succ k = zero := by sorry

  def lt : ZFSet -> ZFSet -> Prop := (·∈·)
  def le m n := lt m (succ n)

  instance instLT_ZFSet : LT ZFSet where
    lt := lt

  instance instLE_ZFSet : LE ZFSet where
    le := le

  theorem le_case {m n : ZFSet} : m ≤ n -> m = n ∨ m < n := by sorry

  theorem succ_intro1 : x = n -> x < succ n := by sorry

  theorem succ_intro2 : x < n -> x < succ n := by sorry

  theorem lt_is_le {x y : ZFSet} : x < y -> x ≤ y := by sorry

  theorem le_refl {n : ZFSet} : n ≤ n := by sorry

  def is_nat (n : ZFSet) : Prop := ∀ X : ZFSet, zero ∈ X -> (∀ k, k ∈ X -> succ k ∈ X) -> n ∈ X

  theorem is_nat_zero : is_nat zero := by sorry

  theorem is_nat_succ : is_nat n -> is_nat (succ n) := by sorry

  def NatSet := ZFSet.sep is_nat omega

  theorem zero_mem_nat : zero ∈ NatSet := by sorry

  theorem succ_mem_nat : n ∈ NatSet -> succ n ∈ NatSet := by sorry

  theorem induction : ∀ (P : ZFSet -> Prop), P zero -> (∀ n, n ∈ NatSet -> P n -> P (succ n)) -> ∀ n, n ∈ NatSet -> P n := by sorry

  theorem lt_trans : p ∈ NatSet -> m < n -> n < p -> m < p := by sorry

  theorem pred_succ_eq : n ∈ NatSet -> pred (succ n) = n := by sorry

  theorem pred_mem_nat : n ∈ NatSet -> pred n ∈ NatSet := by sorry

  theorem succ_injective : m ∈ NatSet -> n ∈ NatSet -> succ m = succ n -> m = n := by sorry

  def max := ZFSet.union

  theorem lt_zero_succ : n ∈ NatSet -> zero < succ n := by sorry

  theorem lt_mono : m ∈ NatSet -> n ∈ NatSet -> m < n -> succ m < succ n := by sorry

  theorem le_total : m ∈ NatSet -> n ∈ NatSet -> m < n ∨ m = n ∨ n < m := by sorry

  theorem max_sym : max m n = max n m := by sorry

  @[simp]
  theorem max_refl : max m m = m := by sorry

  theorem max_lt : n ∈ NatSet -> m < n -> max m n = n := by sorry

  theorem max_mem_nat : m ∈ NatSet -> n ∈ NatSet -> max m n ∈ NatSet := by sorry

  theorem to_zfset_mem_nat {n : Nat} : n.to_zfset ∈ NatSet := by sorry

  theorem to_zfset_equiv {m n: Nat }: m.to_zfset = n.to_zfset <-> m = n := by sorry

  theorem to_zfset_reflect : x ∈ NatSet -> ∃ n : Nat, x = n.to_zfset := by sorry

  def REC f (g : ZFSet -> ZFSet -> ZFSet) n y :=
    ∀ P : ZFSet -> ZFSet -> Prop, P zero f -> (∀ m x, m ∈ NatSet -> P m x -> P (succ m) (g m x)) -> P n y

  noncomputable def recurse f g n := Classical.epsilon (REC f g n)

  theorem rec_def f g : n ∈ NatSet -> REC f g n (recurse f g n) := by sorry

  theorem recurse_zero : recurse f g zero = f := by sorry

  theorem recurse_succ : n ∈ NatSet -> recurse f g (succ n) = g n (recurse f g n) := by sorry

  theorem recurse_mem_nat (P : ZFSet -> ZFSet) :
    n ∈ NatSet ->
    f ∈ P zero ->
    (∀ {k h}, k ∈ NatSet -> h ∈ P k -> g k h ∈ P (succ k)) ->
    recurse f g n ∈ P n
  := by sorry

end ZFSet.Nat
