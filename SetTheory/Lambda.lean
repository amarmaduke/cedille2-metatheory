import Mathlib.SetTheory.ZFC.Basic
import SetTheory.Classical
import SetTheory.Relation
import SetTheory.Function
import SetTheory.Naturals
import SetTheory.Transfinite
import SetTheory.Ordinals

namespace ZFSet.Lambda

  def lambda_functor (A X : ZFSet) :=
    prod {0} Nat.NatSet
    ∪ prod {1} A
    ∪ (prod {2} (prod X X)
    ∪ prod {3} X)

  theorem lambda_functor_mono : X ⊆ Y -> lambda_functor A X ⊆ lambda_functor A Y := by sorry

  def var n := pair 0 n
  def const x := pair 1 x
  def app a b := pair 2 (pair a b)
  def abs a := pair 3 a

  theorem lambda_functor_induction : ∀ X (P : ZFSet -> Prop),
    (∀ n, n ∈ Nat.NatSet -> P (var n)) ->
    (∀ x, x ∈ A -> P (const x)) ->
    (∀ a b, a ∈ X -> b ∈ X -> P (app a b)) ->
    (∀ a, a ∈ X -> P (abs a)) ->
    ∀ a, a ∈ lambda_functor A X -> P a
  := by sorry

  theorem var_compatible : n ∈ Nat.NatSet -> var n ∈ lambda_functor A X := by sorry

  theorem const_compatible : x ∈ A -> const x ∈ lambda_functor A X := by sorry

  theorem app_compatible : a ∈ X -> b ∈ X -> app a b ∈ lambda_functor A X := by sorry

  theorem abs_compatible : a ∈ X -> abs a ∈ lambda_functor A X := by sorry

  noncomputable def lambda_n A (n : Nat) := Ord.transfinite_iteration (lambda_functor A) (n.to_zfset_ordinal)

  theorem lambda_n_incl_succ : lambda_n A k ⊆ lambda_n A (k + 1) := by sorry

  theorem lambda_n_eq : lambda_n A (k + 1) = lambda_functor A (lambda_n A k) := by sorry

  theorem lambda_incl : k ≤ k' -> lambda_n A k ⊆ lambda_n A k' := by sorry

  noncomputable def lambda_set A := Ord.transfinite_iteration (lambda_functor A) omega

  theorem lambda_intro k : lambda_n A k ⊆ lambda_set A := by sorry

  theorem lambda_elim : x ∈ lambda_set A -> ∃ k, x ∈ lambda_n A k := by sorry

  theorem lambda_n_case : ∀ k (P : ZFSet -> Prop),
    (∀ n, n ∈ Nat.NatSet -> P (var n)) ->
    (∀ x, x ∈ A -> P (const x)) ->
    (∀ a b k', k' < k -> a ∈ lambda_n A k' -> b ∈ lambda_n A k' -> P (app a b)) ->
    (∀ a k', (k' < k) -> a ∈ lambda_n A k' -> P (abs a)) ->
    ∀ a, a ∈ lambda_n A k -> P a
  := by sorry

  theorem lambda_fix : ∀ (P : ZFSet -> Prop),
    (∀ k, (∀ k' x, k' < k -> x ∈ lambda_n A k' -> P x) -> ∀ x, x ∈ lambda_n A k -> P x) ->
    ∀ x, x ∈ lambda_set A -> P x
  := by sorry

  theorem lambda_ind : ∀ (P : ZFSet -> Prop),
    (∀ n, n ∈ Nat.NatSet -> P (var n)) ->
    (∀ x, x ∈ A -> P (const x)) ->
    (∀ a b, a ∈ lambda_set A -> b ∈ lambda_set A -> P (app a b)) ->
    (∀ a, a ∈ lambda_set A -> P (abs a)) ->
    ∀ a, a ∈ lambda_set A -> P a
  := by sorry

  theorem lambda_eqn : lambda_set A = lambda_functor A (lambda_set A) := by sorry

  theorem var_compatible0 : n ∈ Nat.NatSet -> var n ∈ lambda_set A := by sorry

  theorem const_compatible0 : x ∈ A -> const x ∈ lambda_set A := by sorry

  theorem app_compatible0 : a ∈ lambda_set A -> b ∈ lambda_set A -> app a b ∈ lambda_set A := by sorry

  theorem abs_compatible0 : a ∈ lambda_set A -> abs a ∈ lambda_set A := by sorry

  noncomputable def pure_lambda_set := lambda_set Nat.zero




end ZFSet.Lambda
