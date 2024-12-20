
import Common
import WCCC.Mode
import WCCC.Ctx

namespace WCCC

  inductive Proof : Ctx -> Term -> Term -> Prop
  | ax :
    ∀ (f : Nat -> Const), (∀ x, Proof Γ (Γ d@ x) (.const (f x))) ->
    Proof Γ ★ □
  | var :
    Proof Γ (Γ d@ x) (.const K) ->
    Proof Γ (.bound K x) (Γ d@ x)
  | pi :
    Proof Γ A (Mode.dom m K) ->
    Proof (A::Γ) B (Mode.codom m) ->
    Proof Γ (.all m A B) (Mode.codom m)
  | lam :
    Proof Γ (.all m A B) (Mode.codom m) ->
    Proof (A::Γ) t B ->
    Proof Γ (.lam m A t) (.all m A B)
  | app :
    Proof Γ f (.all m A B) ->
    Proof Γ a A ->
    Proof Γ (.app m f a) (B β[a])
  | prod :
    Proof Γ A ★ ->
    Proof (A::Γ) B ★ ->
    Proof Γ (.prod A B) ★
  | pair :
    Proof (A::Γ) B ★ ->
    Proof Γ t A ->
    Proof Γ s (B β[t]) ->
    t.erase =β{n}= s.erase ->
    Proof Γ (.pair B t s) (.prod A B)
  | fst :
    Proof Γ t (.prod A B) ->
    Proof Γ (.fst t) A
  | snd :
    Proof Γ t (.prod A B) ->
    Proof Γ (.snd t) (B β[.fst t])
  | eq :
    Proof Γ A ★ ->
    Proof Γ a A ->
    Proof Γ b A ->
    Proof Γ (.eq A a b) ★
  | refl :
    Proof Γ t A ->
    Proof Γ (.refl t) (.eq A t t)
  | subst :
    Proof Γ e (.eq A a b) ->
    Proof Γ Pr (.all mt A ★) ->
    Proof Γ (.subst Pr e) (.all mf (.app mt Pr a) (.app mt Pr b))
  | phi :
    Proof Γ a A ->
    Proof Γ b (.prod A B) ->
    Proof Γ e (.eq A a (.fst b)) ->
    Proof Γ (.phi a b e) (.prod A B)
  | iconv :
    Proof Γ t A ->
    Proof Γ B K ->
    A =β= B ->
    Proof Γ t B
  | econv :
    Proof Γ t A ->
    Proof Γ B K ->
    A.erase =β{n}= B.erase ->
    Proof Γ (.conv B t n) B

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Proof Γ t A

end WCCC
