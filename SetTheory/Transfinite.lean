import Mathlib.SetTheory.ZFC.Basic
import SetTheory.Classical
import SetTheory.Relation
import SetTheory.Naturals

namespace ZFSet

  -- def is_wf x := ∀ (P: ZFSet -> Prop), (∀ a, (∀ b, b ∈ a -> P b) -> P a) -> P x

  -- def all_wellfounded (x : ZFSet) : is_wf x := by
  -- unfold is_wf; intro P ih
  -- apply ZFSet.inductionOn
  -- intro y h; apply ih y h

  def transitive (x p : ZFSet) := x ∈ p ∧ (∀ a b, a ∈ b -> b ∈ p -> a ∈ p)

  def is_transitive_closure (x y : ZFSet) := transitive x y ∧ (∀ p, transitive x p -> y ⊆ p)

  theorem is_transitive_closure_functional :
    is_transitive_closure x y ->
    is_transitive_closure x y' ->
    y = y'
  := by sorry

  theorem is_transitive_closure_intro f :
    (∀ b, b ∈ a -> is_transitive_closure b (f b)) ->
    is_transitive_closure a ({a} ∪ supremum a f)
  := by sorry

  noncomputable def transitive_closure x := Classical.epsilon (is_transitive_closure x)

  notation "[∈" x "]*" => transitive_closure x

  theorem transitive_closure_intro1 x : x ∈ [∈ x]* := by sorry

  theorem transitive_closure_intro2 : y ∈ [∈ x]* -> z ∈ y -> z ∈ [∈ x]* := by sorry

  theorem transitive_closure_transitive : y ∈ [∈ x]* -> z ∈ [∈ y]* -> z ∈ [∈ x]* := by sorry

  theorem induction_transitive_closure x (P : ZFSet -> Prop) :
    (∀ a, a ∈ [∈ x]* -> (∀ b, b ∈ a -> P b) -> P a) -> P x
  := by sorry

  variable (F : (ZFSet -> ZFSet) -> ZFSet -> ZFSet)

  def fun_app (x y : ZFSet) := ZFSet.Rel.image (ZFSet.sep (λ p => ZFSet.fst p = y) x)

  def is_transfinite_recursion_relation (P : ZFSet) := ∀ o y,
    pair o y ∈ P ->
    ∃ f, (∀ n, n ∈ o -> pair n (fun_app f n) ∈ P) ∧ (y = F (fun_app f) o)

  theorem is_transfinite_recursion_relation_functional :
    is_transfinite_recursion_relation G P ->
    is_transfinite_recursion_relation G P' ->
    pair o y ∈ P ->
    pair o y' ∈ P' ->
    y = y'
  := by sorry

  def transfinite_recursion_prop F o P := is_transfinite_recursion_relation F P
    ∧ (∃ y, pair o y ∈ P) ∧ (∀ P' y, is_transfinite_recursion_relation F P' -> pair o y ∈ P' -> P ⊆ P')

  noncomputable def transfinite_recursive_set F x := Classical.epsilon (transfinite_recursion_prop F x)

  noncomputable def wellfounded_recursive_set F x :=
    Classical.epsilon (fun y => pair x y ∈ transfinite_recursive_set F x)

  theorem wellfounded_recursive_set_unfold F x :
    wellfounded_recursive_set F x = F (wellfounded_recursive_set F) x
  := by sorry

  theorem wellfounded_recursive_set_induction : ∀ x (P : ZFSet -> ZFSet -> Prop),
    (∀ y, (∀ x, x ∈ y -> P x (wellfounded_recursive_set F x)) -> P y (F (wellfounded_recursive_set F) y)) ->
    P x (wellfounded_recursive_set F x)
  := by sorry

end ZFSet
