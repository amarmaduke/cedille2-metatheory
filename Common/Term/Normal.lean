
import Common.Term

namespace Term

  mutual
    inductive Neutral : Term -> Prop where
    | bound : Neutral (.bound c k)
    | app : Neutral f ->  Normal a -> Neutral (.app m f a)
    | fst : Neutral t -> Neutral (.fst t)
    | snd : Neutral t -> Neutral (.snd t)
    | subst : Normal P -> Neutral e -> Neutral (.subst P e)
    | phi :  Normal a ->  Normal b -> Neutral e -> Neutral (.phi a b e)
    | conv :  Normal B ->  Neutral t -> Neutral (.conv B t c)

    inductive Normal : Term -> Prop where
    | bound : Normal (.bound c k)
    | const : Normal (.const K)
    | lam : Normal A -> Normal t -> Normal (.lam m A t)
    | app : Neutral f -> Normal a -> Normal (.app m f a)
    | all : Normal A -> Normal B -> Normal (.all m A B)
    | pair : Normal T -> Normal t -> Normal s -> Normal (.pair T t s)
    | fst : Neutral t -> Normal (.fst t)
    | snd : Neutral t -> Normal (.snd t)
    | prod : Normal A -> Normal B -> Normal (.prod A B)
    | refl : Normal t -> Normal (.refl t)
    | subst : Normal P -> Neutral e -> Normal (.subst P e)
    | phi : Normal a -> Normal b -> Neutral e -> Normal (.phi a b e)
    | eq : Normal A -> Normal a -> Normal b -> Normal (.eq A a b)
    | conv : Normal B -> Normal t -> Normal (.conv B t c)
  end

end Term
