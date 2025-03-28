import Mathlib.SetTheory.ZFC.Basic
import SetTheory.Classical

namespace ZFSet
  def fst (p : ZFSet.{u}) : ZFSet.{u} := ZFSet.sep (λ i => ∃ x y, pair x y = p ∧ i ∈ x) (⋃₀ ⋃₀ p)

  @[simp]
  theorem fst_of_pair : fst (pair x y) = x := by
  unfold fst; simp; unfold pair; simp
  apply ext; intro z; simp; intro h
  apply Or.inl; apply h

  theorem fst_prod_compatible : p ∈ prod A B -> fst p ∈ A := by
  intro h; simp at h
  casesm* ∃ _, _, _ ∧ _; case _ a h1 b h2 h3 =>
    subst h3; simp; apply h1

  def snd (p : ZFSet.{u}) : ZFSet.{u} := ZFSet.sep (λ i => ∃ x y, pair x y = p ∧ i ∈ y) (⋃₀ ⋃₀ p)

  @[simp]
  theorem snd_of_pair : snd (pair x y) = y := by
  unfold snd; simp; unfold pair; simp
  apply ext; intro z; simp; intro h
  apply Or.inr; apply h

  theorem snd_prod_compatible : p ∈ prod A B -> snd p ∈ B := by
  intro h; simp at h
  casesm* ∃ _, _, _ ∧ _; case _ a h1 b h2 h3 =>
    subst h3; simp; apply h2

  theorem pair_eta : p ∈ prod A B -> p = pair (fst p) (snd p) := by
  intro h; simp at h
  casesm* ∃ _, _, _ ∧ _; case _ a h1 b h2 h3 =>
    subst h3; simp

  def IsRel (R : ZFSet) := ∀ p, p ∈ R -> p = pair (fst p) (snd p)

  def relations A B := powerset (prod A B)

  namespace Rel
    def app (r x y : ZFSet) := pair x y ∈ r
    def domain (p : ZFSet) := ZFSet.sep (λ x => ∃ y, pair x y ∈ p) (⋃₀ ⋃₀ p)
    def image (p : ZFSet) := ZFSet.sep (λ y => ∃ x, pair x y ∈ p) (⋃₀ ⋃₀ p)

    theorem domain_always_relates : x ∈ domain r -> ∃ y, app r x y := by
    intro h; unfold domain at h; simp at h
    casesm* ∃ _, _, _ ∧ _; case _ a b h1 h2 z h3 h4 =>
      unfold app; exists b

    theorem domain_intro : app r x y -> x ∈ domain r := by
    intro h; unfold app at h; unfold domain; simp
    apply And.intro; apply Exists.intro {x}; apply And.intro
    apply Exists.intro (x.pair y); apply And.intro h
    unfold pair; simp; simp; exists y

    theorem image_intro : app r x y -> y ∈ image r := by
    intro h; unfold app at h; unfold image; simp
    apply And.intro; apply Exists.intro {x, y}; apply And.intro
    apply Exists.intro (x.pair y); apply And.intro h
    unfold pair; simp; simp; exists x

    def compose f g := ZFSet.sep
      (λ p => ∃ y, app g (fst p) y ∧ app f y (snd p))
      (prod (domain g) (image f))

    theorem compose_intro : app g x y -> app f y z -> app (compose f g) x z := by
    intro h1 h2; unfold app; unfold compose; simp
    apply And.intro; apply And.intro
    apply domain_intro h1; apply image_intro h2
    apply Exists.intro y; apply And.intro h1 h2

    theorem app_domain_compatible : r ∈ relations A B -> app r x y -> x ∈ A := by
    intro h1 h2; unfold app at h2
    have lem : pair x y ∈ prod A B := by
      unfold relations at h1; simp at h1; apply h1 h2
    have lem2 : fst (pair x y) ∈ A := by apply fst_prod_compatible lem
    simp at lem2; apply lem2

    theorem app_image_compatible : r ∈ relations A B -> app r x y -> y ∈ B := by
    intro h1 h2; unfold app at h2
    have lem : pair x y ∈ prod A B := by
      unfold relations at h1; simp at h1; apply h1 h2
    have lem2 : snd (pair x y) ∈ B := by apply snd_prod_compatible lem
    simp at lem2; apply lem2

    theorem is_relation : f ∈ relations A B -> IsRel f := by
    intro h1; unfold IsRel; intro p h2
    unfold relations at h1; simp at h1
    have lem := h1 h2
    apply pair_eta lem

    theorem domain_incl : r ∈ relations A B -> domain r ⊆ A := by
    intro h; unfold relations at h; simp at h
    intro z h2; unfold domain at h2; simp at h2
    casesm* ∃ _, _, _ ∧ _; case _ u v h3 h4 w h1 h2 =>
      have lem := h h3
      simp at lem; apply lem.1

    theorem image_incl : r ∈ relations A B -> image r ⊆ B := by
    intro h; unfold relations at h; simp at h
    intro z h2; unfold image at h2; simp at h2
    casesm* ∃ _, _, _ ∧ _; case _ u v h3 h4 w h1 h2 =>
      have lem := h h3
      simp at lem; apply lem.2

    theorem rel_mem_relations : IsRel r -> domain r ⊆ A -> image r ⊆ B -> r ∈ relations A B := by
    intro h1 h2 h3
    unfold IsRel at h1
    unfold relations; simp; intro z h4
    rw [h1 _ h4] at *; simp; apply And.intro
    apply h2; apply domain_intro; unfold app; apply h4
    apply h3; apply image_intro; unfold app; apply h4

    def inject (R : ZFSet -> ZFSet -> Prop) A B := ZFSet.sep (λ p => R (fst p) (snd p)) (prod A B)

    theorem inject_mem_relations : inject R A B ∈ relations A B := by
    unfold relations; unfold inject; simp
    intro z h1; simp at h1
    casesm* ∃ _, _, _ ∧ _; case _ h4 u h3 v h1 h2 =>
      subst h2; simp [*]

    theorem inject_intro {R : ZFSet -> ZFSet -> Prop} {x y A B : ZFSet}:
      x ∈ A -> y ∈ B -> R x y -> app (inject R A B) x y
    := by
    intro h1 h2 h3; unfold inject; unfold app; simp [*]

    theorem inject_elim : app (inject R A B) x y -> x ∈ A ∧ y ∈ B ∧ R x y := by
    intro h; unfold inject at h; unfold app at h; simp at h; simp [*]

  end Rel

  noncomputable def supremum (x : ZFSet) (F: ZFSet -> ZFSet) : ZFSet := ⋃₀ (Classical.image F x)

  noncomputable def sigma A B := ZFSet.sep (λ p => snd p ∈ B (fst p)) (prod A (supremum A B))

  theorem sigma_nodep : prod A B = sigma A (λ _ => B) := by sorry

  theorem sigma_intro : x ∈ A -> y ∈ B x -> pair x y ∈ sigma A B := by sorry

  theorem fst_sigma_compatible : p ∈ sigma A B -> fst p ∈ A := by sorry

  theorem snd_sigma_compatible : p ∈ sigma A B -> snd p ∈ B (fst p) := by sorry

end ZFSet
