
import Common
import Fomega.Ctx

namespace Fomega

  inductive Conv : Term -> Term -> Prop
  | ax : Conv ★ ★
  | bound x : Conv (.bound K x) (.bound K x)
  | all_congr : Conv A1 A2 -> Conv B1 B2 -> Conv (.all mf A1 B1) (.all mf A2 B2)
  | lam_congr : Conv A1 A2 -> Conv t1 t2 -> Conv (.lam mf A1 t1) (.lam mf A2 t2)
  | lam_eta : Conv (.lam mf A t1) (Term.eta mf A t2) -> Conv (.lam mf A t1) t2
  | app_congr : Conv f1 f2 -> Conv a1 a2 -> Conv (.app m f1 a1) (.app m f2 a2)
  | app_beta : Conv (b β[t]) t2 -> Conv (.app mf (.lam mf A b) t) t2

end Fomega

notation:100 A:32 " === " B:31 => Fomega.Conv A B

namespace Fomega

  inductive Proof : Ctx -> Term -> Term -> Prop
  | ax : Proof Γ ★ □
  | var :
    Γ = Γ1 ++ [A] ++ Γ2 ->
    Proof Γ1 A (.const K) ->
    Proof Γ (.bound K Γ1.length) A
  | pi :
    Proof Γ A K ->
    Proof (Γ ++ [A]) B ★ ->
    Proof Γ (.all mf A B) ★
  | tpi :
    Proof Γ A □ ->
    Proof (Γ ++ [A]) B □ ->
    Proof Γ (.all mf A B) □
  | lam :
    Proof Γ (.all mf A B) K ->
    Proof (Γ ++ [A]) t B ->
    Proof Γ (.lam mf A t) (.all mf A B)
  | app :
    Proof Γ f (.all mf A B) ->
    Proof Γ a A ->
    Proof Γ (.app mf f a) (B β[a])
  | conv :
    Proof Γ t A ->
    Proof Γ B K ->
    A === B ->
    Proof Γ t B
end Fomega

notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Fomega.Proof Γ t A
