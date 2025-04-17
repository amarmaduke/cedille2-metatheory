
import Common
import Realizer
import SetTheory
import CC.Term
import CC.Proof
import CC.Model
import CC.MakeObject
import CC.GenModelSN

namespace CC.Model

  noncomputable def mk_ty (x : ZFSet) (S : Realizer.Sat.SatSet) : ZFSet := .pair x (.Lambda.isat S)

  noncomputable def El (T : ZFSet) : ZFSet := .fst T

  noncomputable def Real (T : ZFSet) := ZFSet.Lambda.ssat (.snd T)

  noncomputable def pi_sat A (F : ZFSet -> Realizer.Sat.SatSet) :=
    Realizer.Sat.prod_sat (Real A) (Realizer.Sat.inter_sat (PSigma (λ y => y ∈ El A)) (λ p => F p.1))

  noncomputable def sn_prod A (F : ZFSet -> ZFSet) :=
    mk_ty (ZFSet.cc_prod (El A) (λ x => El (F x))) (pi_sat A (λ x => Real (F x)))

  noncomputable def sn_lam A F := ZFSet.cc_lam (El A) F

  noncomputable def sn_app := ZFSet.app

  theorem sn_prod_intro :
    (∀ x, x ∈ El dom -> f x ∈ El (F x)) ->
    sn_lam dom f ∈ El (sn_prod dom F)
  := by
  intro h; unfold sn_lam; unfold sn_prod; unfold El; unfold mk_ty
  rw [ZFSet.fst_of_pair]; apply ZFSet.cc_prod_intro
  apply h

  theorem sn_prod_elim :
    f ∈ El (sn_prod dom F) ->
    x ∈ El dom ->
    ZFSet.cc_app f x ∈ El (F x)
  := by sorry

  theorem cc_impredicative_prod_non_empty :
    (∀ x, x ∈ dom -> F x = {∅}) ->
    ZFSet.cc_prod dom F = {∅}
  := by sorry

  noncomputable def sn_props := mk_ty (ZFSet.Lambda.repl_sat (λ A => mk_ty {∅} A)) Realizer.Sat.SNSat

  theorem sn_impredicative_prod :
    (∀ x, x ∈ El dom -> F x ∈ El sn_props) ->
    sn_prod dom F ∈ El sn_props
  := by sorry

  theorem sn_proof_of_false : ∅ ∈ El (sn_prod sn_props (λ P => P)) := by sorry

  def X := ZFSet

  def inX x y := x ∈ El y

  theorem prod_intro :
    (∀ x, inX x dom -> inX (f x) (F x)) ->
    inX (sn_lam dom f) (sn_prod dom F)
  := by
  intro h; unfold inX; apply sn_prod_intro; apply h

  theorem prod_elim :
    inX f (sn_prod dom F) ->
    inX x dom ->
    inX (sn_app f x) (F x)
  := by sorry

  theorem impredicative_prod :
    (∀ x, inX x dom -> inX (F x) sn_props) ->
    inX (sn_prod dom F) sn_props
  := by sorry

  theorem beta_eq :
    inX x dom ->
    sn_app (sn_lam dom F) x = F x
  := by sorry

  theorem real_sort : Real sn_props = Realizer.Sat.SNSat := by sorry

  theorem real_prod :
    Real (sn_prod A B) = Realizer.Sat.prod_sat (Real A)
      (Realizer.Sat.inter_sat (PSigma (λ y => y ∈ El A)) (λ p => Real (B p.1)))
  := by sorry

  def daimon : ZFSet := ∅

  theorem daimon_false : daimon ∈ El (sn_prod sn_props (λ P => P)) := by sorry

  @[simp]
  noncomputable instance inst_CCModel : CCModel where
    X := X
    inX := inX
    props := sn_props
    app := sn_app
    lam := sn_lam
    prod := sn_prod
    prod_intro := @prod_intro
    prod_elim := by {
      intro dom f x F; apply @prod_elim
    }
    impredicative_prod := @impredicative_prod
    beta_eq := by {
      intro dom F x; apply @beta_eq
    }

  @[simp]
  noncomputable instance inst_SNAddon : SNAddon where
    real := Real
    real_sort := real_sort
    real_prod := by {
      intro A B; simp; unfold inX; unfold X
      apply @real_prod
    }
    daimon := daimon
    daimon_false := daimon_false

  @[simp]
  noncomputable def interp_term : CC.Term -> CC.Model.Term
  | .const .type => prop
  | .const .kind => kind
  | .var x => ref x
  | .app _ f a => app (interp_term f) (interp_term a)
  | .lam A t => abs (interp_term A) (interp_term t)
  | .pi A B => prod (interp_term A) (interp_term B)

  noncomputable def interp_env := List.map interp_term

  theorem red_sound : Term.Red x y -> ¬ Term.MemConst .kind x -> red (interp_term x) (interp_term y) := by
  intro h1 h2
  induction h1
  case _ =>
    simp;
    sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry

  theorem sn_sound : SN red (interp_term t) -> ¬ Term.MemConst .kind t -> SN Term.Red t := by sorry

  theorem interp_sound :
    ParProof .prf Γ (t, t', A) ->
      typed (interp_env Γ) (interp_term t) (interp_term A)
      ∧ eq_typed (interp_env Γ) (interp_term t) (interp_term t')
  := by sorry

  theorem interp_wf :
    ParProof .wf Γ () -> wf (interp_env Γ)
  := by sorry

  theorem interp_sound2 :
    ParProof .prf Γ (t, t', A) ->
      wf (interp_env Γ)
      ∧ typed (interp_env Γ) (interp_term t) (interp_term A)
  := by sorry

  theorem strong_normalization : ParProof .prf Γ (t, t', A) -> @SN.{0} CC.Term Term.Red t := by
  intro h
  have lem : ¬ Term.MemConst .kind t := by
    intro h2; sorry
  apply interp_sound2 at h
  have h2 : typed.{1} (interp_env Γ) (interp_term t) (interp_term A) := h.2
  apply model_strong_normalization _ _ _ h.1 at h2
  apply sn_sound h2 lem

end CC.Model
