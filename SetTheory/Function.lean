import Mathlib.SetTheory.ZFC.Basic
import SetTheory.Classical
import SetTheory.Relation

namespace ZFSet
  def is_function f := IsRel f ∧ ∀ x y y', Rel.app f x y -> Rel.app f x y' -> y = y'

  def app (f x : ZFSet) : ZFSet := ⋃₀ (ZFSet.sep (λ y => Rel.app f x y) (Rel.image f))

  theorem app_defined : is_function f -> Rel.app f x y -> app f x = y := by
  intro h1 h2; unfold app
  unfold is_function at h1; apply ext
  intro z; apply Iff.intro
  case _ =>
    intro h; simp at h
    casesm* ∃ _, _, _ ∧ _; case _ h6 h7 u h3 h4 h5 =>
      have lem := h7 _ _ _ h5 h2; rw [<-lem]; apply h3
  case _ =>
    intro h3; simp
    apply Exists.intro y; apply And.intro _ h3
    apply And.intro _ h2
    apply Rel.image_intro h2

  theorem app_elim : is_function f -> x ∈ Rel.domain f -> Rel.app f x (app f x) := by
  intro h1 h2
  unfold Rel.app; unfold is_function at h1; unfold IsRel at h1
  unfold Rel.domain at h2; simp at h2
  casesm* ∃ _, _, _ ∧ _; case _ h5 h6 u v h3 h4 w h1 h2 =>
    have lem1 : is_function f := by
      unfold is_function; apply And.intro _ h6
      unfold IsRel; apply h5
    have lem2 : Rel.app f x v := by
      unfold Rel.app; apply h3
    have lem3 := app_defined lem1 lem2
    rw [lem3]; apply h3

  def func (A B : ZFSet) := ZFSet.sep
    (λ r => is_function r ∧ ∀ {x : ZFSet}, x ∈ A -> ∃ y : ZFSet, y ∈ B ∧ Rel.app r x y)
    (relations A B)

  theorem func_rel_incl : func A B ⊆ relations A B := by
  intro z h; unfold relations; simp; intro w h2
  unfold func at h; simp at h
  have lem := h.1; unfold relations at lem; simp at lem
  apply lem h2

  theorem func_is_function : f ∈ func A B -> is_function f := by
  intro h; unfold is_function; unfold func at h
  unfold is_function at h; simp at h
  casesm* _ ∧ _; case _ h1 h2 h3 h4 =>
    apply And.intro h3 h4

  theorem fun_domain_func : f ∈ func A B -> Rel.domain f = A := by
  intro h; unfold func at h; simp at h
  unfold is_function at h
  apply ext; intro z; apply Iff.intro
  case _ =>
    intro h2
    sorry
  case _ =>
    intro h2
    sorry

  theorem app_typ : f ∈ func A B -> x ∈ A -> app f x ∈ B := by sorry

  theorem func_narrow {f A B B' : ZFSet} : f ∈ func A B -> (∀ x, x ∈ A -> app f x ∈ B') -> f ∈ func A B' := by sorry

  def lam_rel (F : ZFSet -> ZFSet) A B := Rel.inject (fun x y => F x = y) A B

  theorem lam_rel_mem_func {A B : ZFSet} : (∀ x, x ∈ A -> f x ∈ B) -> lam_rel f A B ∈ func A B := by sorry

  theorem beta_rel_eq {x A B : ZFSet} : x ∈ A -> (∀ x, x ∈ A -> f x ∈ B) -> app (lam_rel f A B) x = f x := by sorry

  noncomputable def lam A (F : ZFSet -> ZFSet) := Classical.image (λ x => pair x (F x)) A

  theorem lam_is_function {A f} : is_function (lam A f) := by sorry

  theorem lam_mem_func {A B : ZFSet} : (∀ x, x ∈ A -> f x ∈ B) -> lam A f ∈ func A B := by sorry

  theorem beta_eq {x A : ZFSet} : x ∈ A -> app (lam A f) x = f x := by sorry

  noncomputable def dep_func (A : ZFSet) (B : ZFSet -> ZFSet) :=
    ZFSet.sep (λ f => ∀ x, x ∈ A -> app f x ∈ B x) (func A (⋃₀ (Classical.image B A)))

  theorem dep_func_intro {f F : ZFSet -> ZFSet} {dom : ZFSet} :
    (∀ x, x ∈ dom -> f x ∈ F x) -> lam dom f ∈ dep_func dom F
  := by sorry

  theorem func_eta {f A B : ZFSet} : f ∈ func A B -> f = lam A (λ x => app f x) := by sorry

  theorem dep_func_eta : f ∈ dep_func dom F -> f = lam dom (λ x => app f x) := by sorry

  theorem dep_func_incl_func : dep_func A B ⊆ func A (⋃₀ (Classical.image B A)) := by sorry

  theorem dep_func_elim : f ∈ dep_func A B -> x ∈ A -> app f x ∈ B x := by sorry
end ZFSet
