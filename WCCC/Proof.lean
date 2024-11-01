
import Common
import WCCC.Mode

namespace WCCC

  abbrev Ctx := List (Mode × Term)

  inductive Conv : CvTerm -> Term -> Term -> Prop
  | sym : Conv c t2 t1 -> Conv (.sym c) t1 t2
  | trans : Conv c1 t1 t2 -> Conv c2 t2 t3 -> Conv (.trans c1 c2) t1 t3
  | none : Conv .none .none .none
  | const : Conv .const (.const K) (.const K)
  | bound x : Conv (.bound x) (.bound K x) (.bound K x)
  | all_congr : Conv c1 A1 A2 -> Conv c2 B1 B2 ->
    Conv (.all_congr c1 c2) (.all m A1 B1) (.all m A2 B2)
  | lam_congr : Conv c1 A1 A2 -> Conv c2 t1 t2 ->
    Conv (.lam_congr c1 c2) (.lam m A1 t1) (.lam m A2 t2)
  | lam_eta : Conv c (.lam m A t1) (.lam m A (.app m t2 #m)) ->
    Conv (.lam_eta c) (.lam m A t1) t2
  | lam_mf_erased : Conv c t1 t2 ->
    Conv (.lam_mf_erased c) (.lam mf A1 t1) (.lam mf A2 t2)
  | lam_m0_erased : Conv c t1 t2 ->
    Conv (.lam_m0_erased c) (.lam m0 A t1) t2
  | app_congr : Conv c1 f1 f2 -> Conv c2 a1 a2 ->
    Conv (.app_congr c1 c2) (.app m f1 a1) (.app m f2 a2)
  | app_beta :
    Conv c (b β[t]) t2 ->
    Conv (.app_beta c) (.app m (.lam m A b) t) t2
  | app_m0_erased : Conv c t1 t2 ->
    Conv (.app_m0_erased c) (.app m0 t1 a) t2
  | prod_congr : Conv c1 A1 A2 -> Conv c2 B1 B2 ->
    Conv (.prod_congr c1 c2) (.prod A1 B1) (.prod A2 B2)
  | pair_congr : Conv c1 T1 T2 -> Conv c2 t1 t2 -> Conv c3 s1 s2 ->
    Conv (.pair_congr c1 c2 c3) (.pair T1 t1 s1) (.pair T2 t2 s2)
  | pair_erased : Conv c t1 t2 ->
    Conv (.pair_erased c) (.pair T1 t1 s1) t2
  | fst_congr : Conv c t1 t2 -> Conv (.fst_congr c) (.fst t1) (.fst t2)
  | fst_erased : Conv c t1 t2 -> Conv (.fst_erased c) (.fst t1) t2
  | snd_congr : Conv c t1 t2 -> Conv (.snd_congr c) (.snd t1) (.snd t2)
  | snd_erased : Conv c t1 t2 -> Conv (.snd_erased c) (.snd t1) t2
  | phi_erased : Conv c a1 t2 -> Conv (.phi_erased c) (.phi a1 b1 e1) t2
  | phi_congr : Conv c1 a1 a2 -> Conv c2 b1 b2 -> Conv c3 e1 e2 ->
    Conv (.phi_congr c1 c2 c3) (.phi a1 b1 e1) (.phi a2 b2 e2)
  | eq_congr : Conv c1 A1 A2 -> Conv c2 a1 a2 -> Conv c3 b1 b2 ->
    Conv (.eq_congr c1 c2 c3) (.eq A1 a1 b1) (.eq A2 a2 b2)
  | refl_congr : Conv c t1 t2 -> Conv (.refl_congr c) (.refl t1) (.refl t2)
  | refl_erased : Conv c (.lam mf .none (.bound .type 0)) t2 ->
    Conv (.refl_erased c) (.refl t1) t2
  | subst_congr : Conv c1 P1 P2 -> Conv c2 e1 e2 ->
    Conv (.subst_congr c1 c2) (.subst P1 e1) (.subst P2 e2)
  | subst_erased : Conv c e1 t2 -> Conv (.subst_erased c) (.subst P1 e1) t2
  | conv_congr : Conv c1 x1 x2 -> Conv c2 y1 y2 ->
    Conv (.conv_congr c1 c2) (.conv x1 y1 z1) (.conv x2 y2 z2)
  | conv_erased : Conv c t1 t2 -> Conv (.conv_erased c) (.conv A1 t1 c1) t2

  notation:100 c:33 " : " A:32 " === " B:31 => Conv c A B

  inductive Proof : Ctx -> Mode -> Term -> Term -> Prop
  | ax : Proof Γ mt ★ □
  | var :
    List.getD Γ x (mf, .none) = (m1, [r#(Term.Pn (x + 1))]A) ->
    Proof (List.drop (x + 1) Γ) mt ([r#(Term.Pn (x + 1))]A) (.const K) ->
    m1 ∈ m2 ->
    Proof Γ m2 (.bound K x) A
  | pi :
    Proof Γ mt A (Mode.dom m K) ->
    Proof ((mt, A)::Γ) mt B (Mode.codom m) ->
    Proof Γ mt (.all m A B) (Mode.codom m)
  | lam :
    Proof Γ mt A (Mode.dom m2 K) ->
    Proof ((m2, A)::Γ) m1 t B ->
    Proof ((mt, A)::Γ) mt B (Mode.codom m2) ->
    Proof Γ m1 (.lam m2 A t) (.all m2 A B)
  | app :
    Proof Γ m1 f (.all m2 A B) ->
    Proof Γ (m1*m2) a A ->
    Proof Γ m1 (.app m2 f a) (B β[a])
  | prod :
    Proof Γ mt A ★ ->
    Proof ((mt, A)::Γ) mt B ★ ->
    Proof Γ mt (.prod A B) ★
  | pair :
    Proof Γ mt B (.all mf A ★) ->
    Proof Γ m t A ->
    Proof Γ m0 s (B β[t]) ->
    Proof Γ m (.pair B t s) (.prod A B)
  | fst :
    Proof Γ m t (.prod A B) ->
    Proof Γ m (.fst t) A
  | snd :
    Proof Γ m0 t (.prod A B) ->
    m0 ∈ m ->
    Proof Γ m (.snd t) (B β[.fst t])
  | eq :
    Proof Γ mt A ★ ->
    Proof Γ mt a A ->
    Proof Γ mt b A ->
    Proof Γ mt (.eq A a b) ★
  | refl :
    Proof Γ m0 t A ->
    Proof Γ m (.refl t) (.eq A t t)
  | subst :
    Proof Γ m e (.eq A a b) ->
    Proof Γ mt P (.all mt A ★) ->
    Proof Γ m (.subst P e) (.all mf (.app mt P a) (.app mt P b))
  | conv :
    Proof Γ m t A ->
    Proof Γ mt B K ->
    c : A === B ->
    Proof Γ m (.conv B t c) B

  notation:170 Γ:170 " ⊢[" m:170 "] " t:170 " : " A:170 => Proof Γ m t A

end WCCC
