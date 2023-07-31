
import Cedille.Def
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure

namespace Cedille

  lemma red_pi : A -β>* A' -> B -β>* B' -> pi m A B -β>* pi m A' B' := sorry

  lemma red_pi1 : A -β>* A' -> pi m A B -β>* pi m A' B := sorry

  lemma red_pi2 : {_|-> x}B -β>* B' -> pi m A B -β>* pi m A ({_<-| x}B') := sorry

  lemma red_lam1 : A -β>* A' -> lam m A B -β>* lam m A' B := sorry

  lemma red_lam2 : {_|-> x}B -β>* B' -> lam m A B -β>* lam m A ({_<-| x}B') := sorry

  lemma red_app1 : f -β>* f' -> app m f a -β>* app m f' a := sorry

  lemma red_app2 : a -β>* a' -> app m f a -β>* app m f a' := sorry

  lemma red_inter1 : A -β>* A' -> inter A B -β>* inter A' B := sorry

  lemma red_inter2 : {_|-> x}B -β>* B' -> inter A B -β>* inter A ({_<-| x}B') := sorry

  lemma red_pair1 : t -β>* t' -> pair t s a -β>* pair t' s a := sorry

  lemma red_fst : t -β>* t' -> fst t -β>* fst t' := sorry

  lemma red_snd : t -β>* t' -> snd t -β>* snd t' := sorry

  lemma red_eq1 : a -β>* a' -> eq A a b -β>* eq A a' b := sorry

  lemma red_eq2 : b -β>* b' -> eq A a b -β>* eq A a b' := sorry

  lemma red_promote : t -β>* t' -> promote t -β>* promote t' := sorry

  lemma red_phi : a -β>* a' -> phi a b e -β>* phi a' b e := sorry

  lemma red_deltatop : t -β>* t' -> deltatop t -β>* deltatop t' := sorry

  lemma red_open_erase : {_|-> x}(erase t) -β> s -> erase ({_|-> x}t) -β> s := sorry

  lemma red_strictify_erasure :
    erase ({_|-> Name.fresh S1}t) -β> s ->
    erase ({_|-> Name.fresh (S1 ++ S2)}t) -β> s
  := sorry

  lemma red_open_close : A -β>* {_|-> x}B -> ({_<-| x}A) -β>* B := sorry

  namespace RedStar
    lemma trans : a -β>* b -> b -β>* c -> a -β>* c := by {
      intros h1 h2
      induction h1 generalizing c
      case refl a' => simp [*]
      case step t1 t2 t3 s1 _s2 ih => {
        have lem := ih h2
        apply RedStar.step s1 lem
      }
    }

  end RedStar

  lemma ctt_normal : ¬ (ctt -β> t) := sorry
  lemma cff_normal : ¬ (cff -β> t) := sorry
  lemma cbool_normal : ¬ (cbool -β> t) := sorry

end Cedille
