import Common
import Mathlib.Data.Set.Defs
import Realizer.Term
import Realizer.Reduction

namespace Realizer

  structure weak_candidate (X : Set Term) : Prop where
    sn : ∀ t, t ∈ X -> SN Red t
    red : ∀ t u, t ∈ X -> t -β>* u -> u ∈ X
    wit : ∃ w, w ∈ X

  def weak_chain (t : Term) : Set Term := λ u => t -β>* u

  theorem weakest_candidates : ∀ t, SN Red t -> weak_candidate (weak_chain t) := by sorry

  structure is_candidate (X : Set Term) : Prop where
    sn : ∀ t, t ∈ X -> SN Red t
    red : ∀ t u, t ∈ X -> t -β>* u -> u ∈ X
    exp : ∀ t, t.neutral -> (∀ u, t -β> u -> u ∈ X) -> t ∈ X

  theorem sn_is_candidate : is_candidate (SN Red) := by sorry

  theorem var_in_cand : is_candidate X -> .var n ∈ X := by sorry

  theorem weaker_cand : is_candidate X -> weak_candidate X := by sorry

  theorem sat1_in_cand : is_candidate X -> SN Red u -> (.var n `@ u) ∈ X := by sorry

  theorem cand_sat :
    is_candidate X ->
    Term.occurs 0 m ∨ SN Red u ->
    u β[m] ∈ X ->
    ((`λ m) `@ u) ∈ X
  := by sorry

  def inter (X : Type) (F : X -> Set Term) t := SN Red t ∧ ∀ x, F x t

  theorem is_can_inter : (∀ x : X, is_candidate (F x)) -> is_candidate (inter X F) := by sorry

  theorem is_can_weak : is_candidate X -> is_candidate (λ t => SN Red t ∧ X t) := by sorry

  def Neutral : Set Term := λ t => SN Red t ∧ ∃ u, t -β>* u ∧ Term.normal u ∧ Term.neutral u

  theorem neutral_is_cand : is_candidate Neutral := by sorry

  section
    variable (P : Set Term)

    def compl : Set Term := λ t => ∀ C, is_candidate C -> (∀ u, SN Red u -> u ∈ P -> u ∈ C) -> t ∈ C

    theorem is_can_compl : is_candidate (compl P) := by sorry

    theorem compl_intro : SN Red t -> t ∈ P -> t ∈ compl P := by sorry

    theorem compl_elim : t ∈ compl P -> (∃ u, t =β= u ∧ u ∈ compl P ∧ u ∈ P) ∨ Neutral t := by sorry
  end

  def arrow (X Y : Set Term) : Set Term := λ t => ∀ u, u ∈ X -> (t `@ u) ∈ Y

  theorem weak_cand_arrow : weak_candidate X -> is_candidate Y -> is_candidate (arrow X Y) := by sorry

  theorem weak_lam_sound_arrow :
    (∀ t, t ∈ X -> SN Red t) ->
    is_candidate Y ->
    (∀ n, n ∈ X -> (n β[m]) ∈ Y) ->
    (`λ m) ∈ arrow X Y
  := by sorry

  theorem is_candidate_arrow : is_candidate X -> is_candidate Y -> is_candidate (arrow X Y) := by sorry

  theorem lam_sound_arrow :
    is_candidate X ->
    is_candidate Y ->
    (∀ n, n ∈ X -> (n β[m]) ∈ Y) ->
    (`λ m) ∈ arrow X Y
  := by sorry

  def pi (X : Set Term) (Y : Term -> Set Term) : Set Term :=
    λ t => ∀ u u', u =β= u' -> u ∈ X -> u' ∈ X -> (t `@ u) ∈ Y u'

  theorem is_cand_pi (Y : Term -> Set Term) :
    is_candidate X ->
    (∀ u, is_candidate (Y u)) ->
    is_candidate (pi x y)
  := by sorry

  theorem lam_sound_pi :
    is_candidate X ->
    (∀ u, is_candidate (Y u)) ->
    (∀ n n', n ∈ X -> n' ∈ X -> n' =β= n -> (n β[m]) ∈ Y n') ->
    (`λ m) ∈ pi X Y
  := by sorry

  def union (X Y : Set Term) : Set Term := compl (λ t => t ∈ X ∨ t ∈ Y)

  theorem is_cand_union : is_candidate (union X Y) := by sorry

  theorem is_cand_union1 : is_candidate X -> t ∈ X -> t ∈ union X Y := by sorry

  theorem is_cand_union2 : is_candidate Y -> t ∈ Y -> t ∈ union X Y := by sorry

  theorem cand_context :
    (∀ X, is_candidate X -> u ∈ X -> u' ∈ X) ->
    ∀ X, is_candidate X -> (u `@ v) ∈ X -> (u' `@ v) ∈ X
  := by sorry

  theorem cand_sat1 :
    is_candidate X ->
    Term.occurs 0 m ∨ SN Red u ->
    ((u β[m]) `@ v) ∈ X ->
    ((`λ m) `@ u `@ v) ∈ X
  := by sorry

  theorem cand_sat2 :
    is_candidate X ->
    Term.occurs 0 m ∨ SN Red u ->
    ((u β[m]) `@ v `@ w) ∈ X ->
    ((`λ m) `@ u `@ v `@ w) ∈ X
  := by sorry

  theorem cand_sat3 :
    is_candidate X ->
    Term.occurs 0 m ∨ SN Red u ->
    ((u β[m]) `@ v `@ w `@ x) ∈ X ->
    ((`λ m) `@ u `@ v `@ w `@ x) ∈ X
  := by sorry

end Realizer
