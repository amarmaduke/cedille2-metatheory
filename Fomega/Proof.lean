
import Common
import Fomega.Ctx

namespace Fomega

  inductive Proof : Ctx -> Term -> Term -> Prop
  | ax :
    ∀ (f : Nat -> Const), (∀ x, Proof Γ (Γ d@ x) (.const (f x))) ->
    Proof Γ ★ □
  | var :
    Proof Γ (Γ d@ x) (.const K) ->
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
  | econv :
    Proof Γ t A ->
    Proof Γ B (.const K) ->
    A =β= B ->
    Proof Γ (.conv 0 B t) B
  | iconv :
    Proof Γ t A ->
    Proof Γ B (.const K) ->
    A =β= B ->
    Proof Γ t B

  inductive Wf : Term -> Ctx -> Prop
  | ax : Wf (.const K) Γ
  | var :
    Proof Γ (Γ d@ x) (.const K) ->
    Wf (Γ d@ x) Γ ->
    Wf (.bound K x) Γ
  | pi : Wf A Γ -> Wf B (A::Γ) -> Wf (.all mf A B) Γ
  | lam : Wf A Γ -> Wf B (A::Γ) -> Wf (.lam mf A B) Γ
  | app : Wf f Γ -> Wf a Γ -> Wf (.app mf f a) Γ
  | conv : Wf B Γ -> Wf t Γ -> Wf (.conv 0 B t) Γ

end Fomega

notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Fomega.Proof Γ t A
notation:170 t:170 " ⊢ " Γ:170 => Fomega.Wf t Γ
