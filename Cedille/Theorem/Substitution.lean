
import Cedille.Def
import Cedille.Lemma

namespace Cedille

  theorem substitution {C : Term} :
    Γ1 ⊢ a : A ->
    (Γ1 ++ [x:A] ++ Γ2) ⊢ t : B ->
    (Γ1 ++ [x := a]Γ2) ⊢ [x := a]t : [x := a]A
  := sorry 

end Cedille
