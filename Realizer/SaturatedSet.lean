import Common
import Mathlib.Data.Set.Defs
import Realizer.Term
import Realizer.Reduction
import Realizer.Candidate

namespace Realizer

  structure SaturatedSetTheory where
    Sat : Type
    eq : Sat -> Sat -> Prop
    mem : Term -> Sat -> Prop
    eq_def : eq X Y <-> (∀ t, mem t X <-> mem t Y)
    incl A B := ∀ t, mem t A -> mem t B
    sat_sn {S : Sat} : mem t S -> SN Red t
    mem_exp {S : Sat} :
      Term.occurs 0 m ∨ SN Red u ->
      mem (u β[m]) S ->
      mem ((`λ m) `@ u) S
    daimon : Term
    var_sat : ∀ (S : Sat), mem daimon S
    mem_context : (∀ S, mem u S -> mem u' S) -> ∀ S, mem (u `@ v) S -> mem (u' `@ v) S
    sn_sat : Sat
    sn_sat_intro : SN Red t -> mem t sn_sat
    prod_sat : Sat -> Sat -> Sat
    prod_sat_intro : (∀ v, mem v A -> mem (v β[m]) B) -> mem (`λ m) (prod_sat A B)
    prod_sat_elim : mem u (prod_sat A B) -> mem v A -> mem (u `@ v) B
    inter_sat : ∀ (A : Type), (A -> Sat) -> Sat
    inter_sat_intro : A -> (∀ x:A, mem u (F x)) -> mem u (inter_sat A F)
    inter_sat_elim : mem u (inter_sat A F) -> ∀ x:A, mem u (F x)

  namespace Sat
    @[simp]
    abbrev SatSet := (P : Set Term) ×' (is_candidate P)

    def mem t (S : SatSet) := S.1 t
    def eq X Y := ∀ t, mem t X <-> mem t Y

    theorem eq_def : eq X Y <-> (∀ t, mem t X <-> mem t Y) := by sorry

    def incl_sat A B := ∀ t, mem t A -> mem t B

    theorem sat_sn {S : SatSet} : mem t S -> SN Red t := by sorry

    def daimon := Term.var 0

    theorem var_sat : ∀ (S : SatSet), mem daimon S := by sorry

    theorem mem_exp (S : SatSet) :
      Term.occurs 0 m ∨ SN Red u ->
      mem (u β[m]) S ->
      mem ((`λ m) `@ u) S
    := by sorry

    theorem sat_context : (∀ S, mem u S -> mem u' S) -> ∀ S, mem (u `@ v) S -> mem (u' `@ v) S := by sorry

    def SNSat : SatSet := by unfold SatSet; constructor; apply sn_is_candidate

    theorem sn_sat_intro : SN Red t -> mem t SNSat := by sorry

    def prod_sat (X Y : SatSet) : SatSet := by
      unfold SatSet; constructor
      case fst => apply arrow X.1 Y.1
      case snd => apply is_candidate_arrow X.2 Y.2

    theorem prod_sat_intro : (∀ v, mem v A -> mem (v β[m]) B) -> mem (`λ m) (prod_sat A B) := by sorry

    theorem prod_sat_elim : mem u (prod_sat A B) -> mem v A -> mem (u `@ v) B := by sorry

    def inter_sat (A : Type) (F : A -> SatSet) : SatSet := by
      unfold SatSet; constructor
      case fst => apply inter A (λ a => (F a).1)
      case snd => apply is_can_inter (λ a => (F a).2)

    theorem inter_sat_intro : A -> (∀ x:A, mem u (F x)) -> mem u (inter_sat A F) := by sorry

    theorem inter_sat_elim : mem u (inter_sat A F) -> ∀ x:A, mem u (F x) := by sorry

  end Sat

end Realizer
