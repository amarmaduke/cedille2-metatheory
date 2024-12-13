
import Common
import FomegaMut.Ctx

namespace FomegaMut

  inductive JudKind : Type where
  | prf
  | wf

  inductive Jud : JudKind -> Ctx -> Term -> Term -> Prop
  -- Well-formed context Judgement
  -- | wf_ax ξ :
  --   ∀ (f : Nat -> Const), (∀ x, Jud .prf Γ (Γ d@ x) (.const (f x))) ->
  --   Jud .wf Γ ★ ξ
  -- | wf_var ξ :
  --   Jud .prf Γ (Γ d@ x) (.const K) ->
  --   Jud .wf Γ (.bound K x) ξ
  -- | wf_pi ξ : Jud .wf Γ A ξ -> Jud .wf (A::Γ) B ξ -> Jud .wf Γ (.all mf A B) ξ
  -- | wf_lam ξ : Jud .wf Γ A ξ -> Jud .wf (A::Γ) B ξ -> Jud .wf Γ (.lam mf A B) ξ
  -- | wf_app ξ : Jud .wf Γ f ξ -> Jud .wf Γ a ξ -> Jud .wf Γ (.app mf f a) ξ
  -- | wf_conv ξ : Jud .wf Γ B ξ -> Jud .wf Γ t ξ -> Jud .wf Γ (.conv B t 0) ξ
  -- Proof Judgement
  | ax :
    ∀ (f : Nat -> Const), (∀ x, Jud .prf Γ (Γ d@ x) (.const (f x))) ->
    -- Jud .wf Γ ★ ξ ->
    Jud .prf Γ ★ □
  | var :
    Jud .prf Γ (Γ d@ x) (.const K) ->
    -- Jud .wf Γ (.bound K x) ξ ->
    Jud .prf Γ (.bound K x) (Γ d@ x)
  | pi :
    Jud .prf Γ A (.const K) ->
    Jud .prf (A::Γ) B ★ ->
    Jud .prf Γ (.all mf A B) ★
  | tpi :
    Jud .prf Γ A □ ->
    Jud .prf (A::Γ) B □ ->
    Jud .prf Γ (.all mf A B) □
  | lam :
    Jud .prf Γ (.all mf A B) (.const K) ->
    Jud .prf (A::Γ) t B ->
    Jud .prf Γ (.lam mf A t) (.all mf A B)
  | app :
    Jud .prf Γ f (.all mf A B) ->
    Jud .prf Γ a A ->
    B' = (B β[a]) ->
    Jud .prf Γ (.app mf f a) B'
  | econv :
    Jud .prf Γ t A ->
    Jud .prf Γ B (.const K) ->
    A =β= B ->
    Jud .prf Γ (.conv B t 0) B
  | iconv :
    Jud .prf Γ t A ->
    Jud .prf Γ B (.const K) ->
    A =β= B ->
    Jud .prf Γ t B

  -- inductive Wf : Term -> Ctx -> Prop
  -- | ax : Wf (.const K) Γ
  -- | var :
  --   Proof Γ (Γ d@ x) (.const K) ->
  --   Wf (Γ d@ x) Γ ->
  --   Wf (.bound K x) Γ
  -- | pi : Wf A Γ -> Wf B (A::Γ) -> Wf (.all mf A B) Γ
  -- | lam : Wf A Γ -> Wf B (A::Γ) -> Wf (.lam mf A B) Γ
  -- | app : Wf f Γ -> Wf a Γ -> Wf (.app mf f a) Γ
  -- | conv : Wf B Γ -> Wf t Γ -> Wf (.conv B t 0) Γ

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Jud JudKind.prf Γ t A
  notation:170 t:170 " ⊢ " Γ:170 => Jud JudKind.wf Γ t Term.none

end FomegaMut

-- notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => FomegaMut.Jud FomegaMut.JudKind..prf Γ t A
-- notation:170 t:170 " ⊢ " Γ:170 => FomegaMut.Jud FomegaMut.JudKind.wf Γ t Term.none
