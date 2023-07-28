
import Cedille.Def

namespace Cedille

  lemma red_pi1 : A -β>* A' -> pi m A B -β>* pi m A' B := sorry

  lemma red_pi2 : {_|-> x}B -β>* B' -> pi m A B -β>* pi m A ({_<-| x}B') := sorry

  lemma red_lam1 : A -β>* A' -> lam m A B -β>* lam m A' B := sorry

  lemma red_lam2 : {_|-> x}B -β>* B' -> lam m A B -β>* lam m A ({_<-| x}B') := sorry

  lemma red_app1 : f -β>* f' -> app m f a -β>* app m f' a := sorry

  lemma red_app2 : a -β>* a' -> app m f a -β>* app m f a' := sorry

  lemma red_inter1 : A -β>* A' -> inter A B -β>* inter A' B := sorry

  lemma red_inter2 : {_|-> x}B -β>* B' -> inter A B -β>* inter A ({_<-| x}B') := sorry

  lemma red_pair1 : t -β>* t' -> pair t s -β>* pair t' s := sorry

  lemma red_fst : t -β>* t' -> fst t -β>* fst t' := sorry

  lemma red_snd : t -β>* t' -> snd t -β>* snd t' := sorry

  lemma red_eq1 : a -β>* a' -> eq a b -β>* eq a' b := sorry

  lemma red_eq2 : b -β>* b' -> eq a b -β>* eq a b' := sorry

  lemma red_promote : t -β>* t' -> promote t -β>* promote t' := sorry

  lemma red_phi : a -β>* a' -> phi a b e -β>* phi a' b e := sorry

  lemma red_delta : t -β>* t' -> delta t -β>* delta t' := sorry

  lemma red_open_erase : {_|-> x}(erase t) -β> s -> erase ({_|-> x}t) -β> s := sorry

  namespace RedStar

    lemma transitive : a -β>* b -> b -β>* c -> a -β>* c := sorry

  end RedStar


end Cedille
