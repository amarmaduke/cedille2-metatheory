
import Common
import Fomega.Ctx

namespace Fomega

  inductive Conv : Term -> Term -> Prop
  | ax : Conv (.const K) (.const K)
  | bound x : Conv (.bound K x) (.bound K x)
  | all_congr : Conv A1 A2 -> Conv B1 B2 -> Conv (.all mf A1 B1) (.all mf A2 B2)
  | lam_congr : Conv A1 A2 -> Conv t1 t2 -> Conv (.lam mf A1 t1) (.lam mf A2 t2)
  -- | lam_eta1 :
  --   Conv (.lam mf A t1) (Term.eta mf A t2) ->
  --   Conv (.lam mf A t1) t2
  -- | lam_eta2 :
  --   Conv (Term.eta mf A t1) (.lam mf A t2) ->
  --   Conv t1 (.lam mf A t2)
  | app_congr : Conv f1 f2 -> Conv a1 a2 -> Conv (.app m f1 a1) (.app m f2 a2)
  | app_beta1 :
    Conv (b β[t]) t2 ->
    Conv (.app mf (.lam mf A b) t) t2
  | app_beta2 :
      Conv t1 (b β[t]) ->
      Conv t1 (.app mf (.lam mf A b) t)

end Fomega

notation:100 A:32 " === " B:31 => Fomega.Conv A B

namespace Fomega

  inductive Proof : Ctx -> Term -> Term -> Prop
  | ax : Proof Γ ★ □
  | var :
    -- Proof Γ A (.const K) ->
    Proof Γ (.bound K x) (Γ d@ x)
  | pi :
    Proof Γ A (.const K) ->
    Proof (A::Γ) B ★ ->
    Proof Γ (.all mf A B) ★
  | tpi :
    Proof Γ A □ ->
    Proof (A::Γ) B □ ->
    Proof Γ (.all mf A B) □
  | lam :
    Proof Γ (.all mf A B) (.const K) ->
    Proof (A::Γ) t B ->
    Proof Γ (.lam mf A t) (.all mf A B)
  | app :
    Proof Γ f (.all mf A B) ->
    Proof Γ a A ->
    B' = (B β[a]) ->
    Proof Γ (.app mf f a) B'
  | conv :
    Proof Γ t A ->
    Proof Γ B (.const K) ->
    A === B ->
    Proof Γ t B

  inductive Wf : Term -> Ctx -> Prop
  | ax : Wf ★ Γ
  | var :
    Proof Γ (Γ d@ x) (.const K) ->
    Wf (.bound K x) Γ
  | pi : Wf A Γ -> Wf B (A::Γ) -> Wf (.all mf A B) Γ
  | lam : Wf A Γ -> Wf B (A::Γ) -> Wf (.lam mf A B) Γ
  | app : Wf f Γ -> Wf a Γ -> Wf (.app mf f a) Γ

end Fomega

notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Fomega.Proof Γ t A
notation:170 t:170 " ⊢ " Γ:170 => Fomega.Wf t Γ
