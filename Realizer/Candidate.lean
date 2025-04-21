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

  theorem weakest_candidates : ∀ t, SN Red t -> weak_candidate (weak_chain t) := by
  intro t h1; constructor
  case _ =>
    intro t' h
    apply SN.preservation h1 h
  case _ =>
    intro t' u h r; unfold weak_chain at *
    apply Star.trans h r
  case _ =>
    apply Exists.intro t
    apply Star.refl

  structure is_candidate (X : Set Term) : Prop where
    sn : ∀ t, t ∈ X -> SN Red t
    red : ∀ t u, t ∈ X -> t -β>* u -> u ∈ X
    exp : ∀ t, t.neutral -> (∀ u, t -β> u -> u ∈ X) -> t ∈ X

  theorem sn_is_candidate : is_candidate (SN Red) := by
  constructor
  case _ => intro t h; apply h
  case _ => intro t u h r; apply SN.preservation h r
  case _ => intro t h1 h2; constructor; apply h2

  theorem var_in_cand : is_candidate X -> .var n ∈ X := by
  intro h; cases h; case _ h1 h2 h3 =>
    apply h3; unfold Term.neutral; simp
    intro u r; cases r

  theorem weaker_cand : is_candidate X -> weak_candidate X := by
  intro h; have lem := h
  cases h; case _ h1 h2 h3 =>
    constructor; apply h1; apply h2
    apply Exists.intro (.var 0); apply var_in_cand lem

  theorem sat1_in_cand : is_candidate X -> SN Red u -> (.var n `@ u) ∈ X := by
  intro h1 h2
  induction h2; case _ t' h ih =>
    cases h1; case _ h1 h2 h3 =>
      apply h3; unfold Term.neutral; simp
      intro u' h4; cases h4
      case _ v r => cases r
      case _ t'' r => apply ih _ r

  theorem cand_sat :
    is_candidate X ->
    Term.occurs 0 m ∨ SN Red u ->
    m β[u] ∈ X ->
    ((`λ m) `@ u) ∈ X
  := by
  intro h1 h2 h3
  cases h1; case _ q1 q2 q3 =>
    have lem1 : SN Red u := by
      cases h2
      case _ h =>
        -- Sketch:
        --   occurs 0 m = true => u ∈ m β[u]
        --   but, SN (m β[u]), hence u ∈ SN (m β[u])
        --   therefore, SN u
        sorry
      case _ h => apply h
    clear h2; induction lem1; case _ z hz ihz =>
      have lem2 : SN Red m := by
        have lem := q1 _ h3
        apply SN.subst_preimage lem
      induction lem2; case _ w hw ihw =>
        apply q3; unfold Term.neutral; simp
        intro u' r; cases r
        case _ => apply h3
        case _ w' r =>
          cases r; case _ w' r =>
            have lem3 : w β[z] -β>* w' β[z] := by sorry
            apply @ihw _ r _ (q2 _ _ h3 lem3)
            intro y r2 h4
            have lem4 : w β[z] -β>* w β[y] := by sorry
            replace ihz := ihz y r2 (q2 _ _ h3 lem4)
            have lem5 : (`λ w `@ y) -β>* (`λ w' `@ y) := by sorry
            apply q2 _ _ ihz lem5
        case _ z' r =>
          have lem3 : w β[z] -β>* w β[z'] := by
            sorry
          apply ihz _ r (q2 _ _ h3 lem3)

  def inter (X : Type u) (F : X -> Set Term) t := SN Red t ∧ ∀ x, F x t

  theorem is_can_inter : (∀ x : X, is_candidate (F x)) -> is_candidate (inter X F) := by
  intro h; constructor
  case _ =>
    intro t h2; unfold inter at h2
    cases h2; case _ h2 h3 =>
      apply h2
  case _ =>
    intro t u h2 r; unfold inter at *
    cases h2; case _ h2 h3 =>
      replace h2 := SN.preservation h2 r
      apply And.intro h2; intro x
      replace h := h x; cases h; case _ q1 q2 q3 =>
        apply q2 _ _ (h3 x) r
  case _ =>
    intro t h2 h3; unfold inter at *
    apply And.intro
    case _ =>
      constructor; intro y r
      replace h3 := h3 _ r
      apply h3.1
    case _ =>
      intro x; cases (h x); case _ q1 q2 q3 =>
        apply q3 _ h2; intro u r
        replace h3 := h3 _ r
        apply h3.2

  theorem is_can_weak : is_candidate X -> is_candidate (λ t => SN Red t ∧ X t) := by
  intro h; cases h; case _ q1 q2 q3 =>
    constructor
    case _ => intro t h; apply h.1
    case _ =>
      intro t u h r; apply And.intro
      apply SN.preservation h.1 r
      apply q2 _ _ h.2 r
    case _ =>
      intro t h1 h2
      have lem := q3 _ h1 (λ u r => (h2 u r).2)
      apply And.intro (q1 _ lem) lem

  def Neutral : Set Term := λ t => SN Red t ∧ ∃ u, t -β>* u ∧ Term.normal u ∧ Term.neutral u

  theorem neutral_is_cand : is_candidate Neutral := by
  unfold Neutral; constructor
  case _ => intro t h; apply h.1
  case _ =>
    intro t u h r
    cases h; case _ h1 h2 =>
    cases h2; case _ t' h2 =>
      apply And.intro; apply SN.preservation h1 r
      have lem := Red.confluence r h2.1
      cases lem; case _ w wr =>
        apply Exists.intro w; apply And.intro wr.1
        sorry
  case _ =>
    intro t h1 h2; apply And.intro
    case _ =>
      constructor; intro y r
      replace h2 := h2 _ r
      apply h2.1
    case _ =>

      sorry

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
