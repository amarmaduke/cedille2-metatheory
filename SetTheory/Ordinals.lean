import Mathlib.SetTheory.ZFC.Basic
import SetTheory.Classical
import SetTheory.Relation
import SetTheory.Function
import SetTheory.Naturals
import SetTheory.Transfinite

namespace ZFSet.Ord

  def is_directed o := ∀ x y, x < o -> y < o -> ∃ (z : ZFSet), z < o ∧ x ⊆ z ∧ y ⊆ z

  def plump_set (f : ZFSet -> ZFSet) ub := ZFSet.sep (λ x =>
    (∀ y, y ∈ ub -> y ∈ x -> y ∈ f y)
    ∧ (∀ y z, y ∈ ub -> z ∈ f y -> z ⊆ y -> y ∈ x -> z ∈ x)
    ∧ is_directed x)
    (powerset ub)

  noncomputable def plumps := wellfounded_recursive_set plump_set

  theorem plumps_def (ub x : ZFSet) :
    x ∈ plumps ub <-> x ⊆ ub ∧ (∀ y, y ∈ ub -> y ∈ x -> y ∈ plumps y)
      ∧ (∀ z y, y ∈ ub -> z ∈ plumps y -> z ⊆ y -> y ∈ x -> z ∈ x)
      ∧ is_directed x
  := by sorry

  theorem plump_bound : x ⊆ ub2 -> x ∈ plumps ub1 -> x ∈ plumps ub2 := by sorry

  def is_ordinal x := x ∈ plumps x

  theorem is_ordinal_inv : is_ordinal x -> y < x -> is_ordinal y := by sorry

  theorem is_ordinal_plump : is_ordinal z -> is_ordinal x -> x ⊆ y -> y ∈ z -> x ∈ z := by sorry

  theorem is_ordinal_directed : is_ordinal z -> is_directed z := by sorry

  theorem is_ordinal_intro x :
    (∀ a b, is_ordinal a -> a ⊆ b -> b ∈ x -> a ∈ x) ->
    is_directed x ->
    (∀ y, y ∈ x -> is_ordinal y) ->
    is_ordinal x
  := by sorry

  theorem is_ordinal_trans : is_ordinal x -> z < y -> y < x -> z < x := by sorry

  theorem is_ordinal_ind x : ∀ (P : ZFSet -> Prop),
    (∀ y, is_ordinal y -> y ⊆ x -> (∀ z, z < y -> P z) -> P y) ->
    is_ordinal x -> P x
  := by sorry

  theorem lt_antirefl : is_ordinal x -> ¬ (x < x) := by sorry

  theorem is_ordinal_zero : is_ordinal ZFSet.Nat.zero := by sorry

  def osucc x := ZFSet.sep is_ordinal (powerset x)

end ZFSet.Ord

namespace Nat
  def to_zfset_ordinal : Nat -> ZFSet
  | 0 => ZFSet.Nat.zero
  | n + 1 => ZFSet.Ord.osucc n.to_zfset_ordinal
end Nat

namespace ZFSet.Ord

  theorem lt_osucc : is_ordinal x -> x < osucc x := by sorry

  theorem lt_succ_le : x < osucc y -> x ⊆ y := by sorry

  theorem le_lt_succ : is_ordinal x -> x ⊆ y -> x < osucc y := by sorry

  theorem le_succ_lt : is_ordinal x -> osucc x ⊆ y -> x < y := by sorry

  theorem le_lt_trans : is_ordinal z -> x < osucc y -> y < z -> x < z := by sorry

  theorem lt_le : is_ordinal o -> o' ∈ o -> o' ⊆ o := by sorry

  theorem is_ordinal_succ : is_ordinal n -> is_ordinal (osucc n) := by sorry

  theorem lt_osucc_compatible : is_ordinal m -> n < m -> osucc n < osucc m := by sorry

  theorem osucc_mono : is_ordinal n -> is_ordinal m -> n ⊆ m -> osucc n ⊆ osucc m := by sorry

  theorem lt_osucc_inv : is_ordinal o -> osucc o < osucc o' -> o < o' := by sorry

  theorem is_ordinal_eq : is_ordinal o -> o = supremum o osucc := by sorry

  def increasing (F : ZFSet -> ZFSet) := ∀ x y, is_ordinal x -> is_ordinal y -> y ⊆ x -> F y ⊆ F x

  def increasing_bounded o (F : ZFSet -> ZFSet) := ∀ x x', x' < o -> x < x' -> F x ⊆ F x'

  def succ_ordinal o := ∃ o', is_ordinal o' ∧ o = osucc o'

  def limit_ordinal o := is_ordinal o ∧ (∀ x, x < o -> osucc x < o)

  theorem limit_is_ordinal : ∀ o, limit_ordinal o -> is_ordinal o := by sorry

  theorem limit_union : limit_ordinal o -> sUnion o = o := by sorry

  theorem limit_union_intro  : is_ordinal o -> sUnion o = o -> limit_ordinal o := by sorry

  theorem discriminate_limit_succ : limit_ordinal o -> succ_ordinal o -> False := by sorry

  theorem is_ordinal_binary_inter : is_ordinal x -> is_ordinal y -> is_ordinal (x ∩ y) := by sorry

  theorem binary_inter_succ : is_ordinal x -> is_ordinal y -> osucc x ∩ osucc y = osucc (x ∩ y) := by sorry

  variable (F : (ZFSet -> ZFSet) -> ZFSet -> ZFSet)

  def is_transfinite_recursion_relation (P : ZFSet) := ∀ o y,
    pair o y ∈ P ->
    ∃ f, (∀ n, n ∈ o -> pair n (fun_app f n) ∈ P) ∧ y = F (fun_app f) o

  theorem is_transfinite_recursion_relation_functional :
    is_transfinite_recursion_relation F P ->
    is_transfinite_recursion_relation F P' ->
    pair o y ∈ P ->
    pair o y' ∈ P' ->
    y = y'
  := by sorry

  def transfinite_recursion_relation o y := ∃ (P : ZFSet), is_transfinite_recursion_relation F P ∧ pair o y ∈ P

  -- Not convinced we need the ordinal formulation of transfinite recursion

  noncomputable def G (F : ZFSet -> ZFSet) (f : ZFSet -> ZFSet) o := supremum o (fun o' => F (f o'))

  noncomputable def transfinite_iteration (F : ZFSet -> ZFSet) := transfinite_recursive_set (G F)

  theorem transfinite_iteration_eq (F : ZFSet -> ZFSet) {o : ZFSet} :
    transfinite_iteration F o = supremum o (λ o' => F (transfinite_iteration F o'))
  := by sorry

  theorem transfinite_iteration_intro (F : ZFSet -> ZFSet) :
    o' < o -> x ∈ F (transfinite_iteration F o') -> x ∈ transfinite_iteration F o
  := by sorry

  theorem transfinite_iteration_elim (F : ZFSet -> ZFSet) :
    x ∈ transfinite_iteration F o -> ∃ o', o' < o ∧ x ∈ F (transfinite_iteration F o')
  := by sorry

  theorem transfinite_iteration_initial (F : ZFSet -> ZFSet) : transfinite_iteration F Nat.zero = ∅ := by sorry

  theorem transfinite_iteration_induction (F : ZFSet -> ZFSet) (n X : ZFSet) :
    (∀ a, a ∈ X -> F a ∈ X) ->
    (∀ m G, m ⊆ n -> (∀ x, x < m -> G x ∈ X) -> supremum m G ∈ X) ->
    transfinite_iteration F n ∈ X
  := by sorry

  def ordinal_binary_supremum_relation (x y z : ZFSet) := ∀ (P : ZFSet -> ZFSet -> ZFSet -> Prop),
    (∀ x y (g : ZFSet -> ZFSet -> ZFSet), (∀ x' y', x' ∈ x -> y' ∈ y -> P x' y' (g x' y'))
      -> P x y (x ∪ y ∪ supremum x (λ x' => Classical.image (λ y' => g x' y') y)))
    -> P x y z

  theorem ordinal_binary_supremum_relation_intro (x y : ZFSet) (g : ZFSet -> ZFSet -> ZFSet) :
    (∀ x' y', x' ∈ x -> y' ∈ y -> ordinal_binary_supremum_relation x' y' (g x' y')) ->
    ordinal_binary_supremum_relation x y (x ∪ y ∪ supremum x (λ x' => Classical.image (λ y' => g x' y') y))
  := by sorry

  theorem ordinal_binary_supremum_relation_elim (x y z : ZFSet) :
    ordinal_binary_supremum_relation x y z ->
    ∃ (g : ZFSet -> ZFSet -> ZFSet),
      (∀ x' y', x' ∈ x -> y' ∈ y -> ordinal_binary_supremum_relation x' y' (g x' y'))
      ∧ z = x ∪ y ∪ supremum x (λ x' => Classical.image (λ y' => g x' y') y)
  := by sorry

  theorem ordinal_binary_supremum_relation_unique :
    ordinal_binary_supremum_relation x y z ->
    ordinal_binary_supremum_relation x y z' ->
    z = z'
  := by sorry

  noncomputable def ordinal_binary_supremum x y := Classical.epsilon (ordinal_binary_supremum_relation x y)

  notation:60 x "⊔" y:59 => ordinal_binary_supremum x y

  theorem ordinal_binary_supremum_def : x ⊔ y = x ∪ y ∪ supremum x (λ x' => Classical.image (λ y' => x' ⊔ y') y) := by sorry

  theorem ordinal_binary_supremum_axiom :
    z ∈ x ⊔ y <-> z ∈ x ∨ z ∈ y ∨ ∃ x', x' ∈ x ∧ ∃ y', y' ∈ y ∧ z = x' ⊔ y'
  := by sorry

  theorem ordinal_binary_supremum_incl1 : x ⊆ x ⊔ y := by sorry

  theorem ordinal_binary_supremum_incl2 : y ⊆ x ⊔ y := by sorry

  theorem ordinal_binary_supremum_mono : x ⊆ x' -> y ⊆ y' -> x ⊔ y ⊆ x' ⊔ y' := by sorry

  theorem is_directed_ordinal_binary_supremum : is_directed x -> is_directed y -> is_directed (x ⊔ y) := by sorry

  theorem ordinal_binary_supremum_proof :
    is_ordinal x ->
    is_ordinal y ->
    is_ordinal (x ⊔ y) ∧ (∀ z, is_ordinal z -> z ∩ (x ⊔ y) = z ∩ x ⊔ z ∩ y)
  := by sorry

  theorem is_ordinal_ordinal_binary_supremum : is_ordinal x -> is_ordinal y -> is_ordinal (x ⊔ y) := by sorry

  theorem ordinal_binary_supremum_least_upper_bound :
    is_ordinal x -> is_ordinal y -> is_ordinal y ->
    x ⊆ z -> y ⊆ z -> x ⊔ y ⊆ z
  := by sorry

  theorem ordinal_binary_supremum_refl : is_ordinal x -> x ⊔ x = x := by sorry

  theorem ordinal_binary_supremum_lt : is_ordinal z -> x ∈ z -> y ∈ z -> x ⊔ y ∈ z := by sorry

  theorem is_directed_succ : is_ordinal o -> is_directed (osucc o) := by sorry

  theorem ordinal_binary_supremum_sym : x ⊔ y = y ⊔ x := by sorry

  theorem ordinal_binary_supremum_assoc :
    is_ordinal x -> is_ordinal y -> is_ordinal z -> x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z
  := by sorry

  section
    variable (I : ZFSet) (f : ZFSet -> ZFSet) (f_ord : ∀ x, x ∈ I -> is_ordinal (f x))

    theorem is_ordinal_supf_intro : n ∈ I -> f n ⊆ supremum I f := by sorry

    theorem is_ordinal_supf_elim : x < supremum I f -> ∃ n, n ∈ I ∧ x < f n := by sorry

    theorem is_directed_ordinal_supremum : is_directed (supremum I f) := by sorry

    theorem is_ordinal_supf : is_ordinal (supremum I f) := by sorry
  end

  section
    variable (f : Nat -> ZFSet) (f_ord : ∀ n, is_ordinal (f n)) (f_mono : ∀ m n, m ≤ n -> f m ⊆ f n)

    noncomputable def lift_f x := Classical.epsilon (λ y => ∃ n, x = n.to_zfset ∧ f n = y)

    noncomputable def ordinal_supremum := supremum Nat.NatSet (lift_f f)

    theorem is_ordinal_sup_intro : ∀ n, f n ⊆ ordinal_supremum f := by sorry

    theorem is_ordinal_sup_elim : x < ordinal_supremum f -> ∃ n, x < f n := by sorry

    theorem is_ordinal_ordinal_supremum : is_ordinal (ordinal_supremum f) := by sorry

    theorem ordinal_supremum_induction (X : ZFSet) :
      (∀ n, f n ∈ X) ->
      (∀ g, (∀ n, n ∈ Nat.NatSet -> g n ∈ X) -> supremum Nat.NatSet g ∈ X) ->
      ordinal_supremum f ∈ X
    := by sorry

    theorem is_ordinal_union :
      (∀ y, y ∈ x -> is_ordinal y) ->
      (∀ a a', a ∈ x -> a' ∈ x -> ∃ b, b ∈ x ∧ a ⊆ b ∧ a' ⊆ b) ->
      is_ordinal (⋃₀ x)
    := by sorry

    theorem is_ordinal_inter : (∀ y, y ∈ x -> is_ordinal y) -> is_ordinal (⋂₀ x) := by sorry
  end

  theorem nat_to_zfset_ordinal_is_ordinal (n : Nat) : is_ordinal (n.to_zfset_ordinal) := by sorry

  noncomputable def omega := ordinal_supremum Nat.to_zfset_ordinal

  theorem is_ordinal_omega : is_ordinal omega := by sorry

  theorem zero_lt_omega : Nat.zero < omega := by sorry

  theorem osucc_lt_omega : n < omega -> osucc n < omega := by sorry

  theorem omega_limit_ordinal : limit_ordinal omega := by sorry

  section
    variable (I : ZFSet) (f : ZFSet -> ZFSet) (f_ord : ∀ x, x ∈ I -> is_ordinal (f x))

    noncomputable def ordinal_supf X := supremum X (λ x => Classical.image (λ y => x ⊔ y) X)

    noncomputable def ordinal_supfn : Nat -> ZFSet
    | 0 => supremum I f
    | n + 1 => ordinal_supf (ordinal_supfn n)

    noncomputable def osup := ordinal_supremum (ordinal_supfn I f)

    theorem osupf_def : z ∈ ordinal_supf X <-> ∃ x, x ∈ X ∧ ∃ y, y ∈ X ∧ z = x ⊔ y := by sorry

    theorem osupf_mono : X ⊆ Y -> ordinal_supf X ⊆ ordinal_supf Y := by sorry

    theorem osupfn_mono : m ≤ n -> ordinal_supfn I f m ⊆ ordinal_supfn I f n := by sorry

    theorem osup_intro : x ∈ I -> f x ⊆ osup I f := by sorry

    theorem is_ordinal_osupfn : x ∈ ordinal_supfn I f n -> is_ordinal x := by sorry

    theorem is_ordinal_osup : is_ordinal (osup I f) := by sorry

    theorem osup_lub z : is_ordinal z -> (∀ x, x ∈ I -> f x ⊆ z) -> osup I f ⊆ z := by sorry
  end

  theorem is_ordinal_eq_osup : is_ordinal o -> o = osup o osucc := by sorry

  noncomputable def to_ordinal (X : ZFSet) := osup (ZFSet.sep is_ordinal X) osucc

  theorem to_ordinal_is_ordinal : ∀ x, is_ordinal (to_ordinal x) := by sorry

  theorem to_ordinal_ordinal : is_ordinal o -> to_ordinal o = o := by sorry

end ZFSet.Ord
