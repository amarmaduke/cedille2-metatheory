
import Cedille.Def
import Cedille.Lemma.Conv

namespace Cedille

  lemma infer_implies_cinfer : Γ ⊢ t : A -> Γ ⊢ t >: A := by {
    intro j; apply ConInfer.infer j RedStar.refl
  }

  lemma infer_implies_check : Γ ⊢ t : A -> Γ ⊢ t =: A := by {
    intro j; apply Check.check j Conv.refl
  }

  lemma infer_implies_wf : Γ ⊢ t : A -> ⊢ Γ := sorry

  lemma cinfer_implies_check : Γ ⊢ t >: A -> Γ ⊢ t =: A := by {
    intro j; cases j
    case _ A' j step =>
    apply Check.check j _
    apply Conv.red_b Conv.refl step
  }

  lemma check_from_cinfer :
    Γ ⊢ t >: A ->
    A =β= B ->
    Γ ⊢ t =: B
  := by {
    intros j e
    cases j
    case _ C j step =>
    have lem := Conv.red_b e step
    apply Check.check j lem
  }

  lemma cinfer_destruct : Γ ⊢ t >: B -> ∃ A, Γ ⊢ t : A ∧ A -β>* B := by {
    intros j; cases j
    case _ B j step => exists B
  }

  lemma rename_ctx_invariant {Γ : Map! Term} : (y : Name) -> x ∉ Map.fv Γ -> [x |-> y]Γ = Γ
  := sorry

  lemma rename_term_invariant {A : Term} : (y : Name) -> x ∉ fv A -> {_|-> y}{_<-| x}A = A
  := sorry

  lemma rename_infer (x : Name) :
    Γ ⊢ t : A ->
    y ∉ (Map.fv Γ ++ fv t ++ fv A) ->
    [x |-> y]Γ ⊢ {_|-> y}{_<-| x}t : {_|-> y}{_<-| x}A
  := sorry

end Cedille
