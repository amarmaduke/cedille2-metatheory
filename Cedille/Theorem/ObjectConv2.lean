
import Cedille.Def
import Cedille.Lemma

namespace Cedille

  lemma proof_red_to_object_red_step (x : Name) :
    Γ ⊢ t : A ->
    t -β> s ->
    (erase x t) -β>* (erase x s)
  := sorry

  lemma proof_red_to_object_red (x : Name) :
    Γ ⊢ t : A ->
    t -β>* s ->
    (erase x t) -β>* (erase x s)
  := by {
    intros j step
    induction step
    case refl => apply RedStar.refl
    case step t1 t2 t3 t4 step ih => {
      sorry
    }
  }

  theorem proof_to_object_conv (x : Name) :
    Γ ⊢ t : A ->
    Γ ⊢ s : B ->
    t =β= s ->
    (erase x t) =β= (erase x s)
  := by {
    intros j1 j2 e
    cases e
    case _ t1 t2 s1 e s2 =>
    have s1 := proof_red_to_object_red x j1 s1
    have s2 := proof_red_to_object_red x j2 s2
    sorry
  }

end Cedille
