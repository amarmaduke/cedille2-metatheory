import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification
import Fomega.Basic.Preservation

namespace Fomega.Proof

  abbrev Cand := Term -> Prop

  @[simp]
  def PossibleRedex : Term -> Bool
  | .app _ _ _ => true
  | _ => false

  structure Reducible (P : Cand) : Prop where
    normal : ∀ t, P t -> Term.SN t
    preserve : ∀ t t', P t -> t -β> t' -> P t'
    expand : ∀ t, PossibleRedex t -> (∀ t', t -β> t' -> P t') -> P t

  @[simp]
  def L (ty : Term) (rho : Nat -> Cand) : Cand :=
    match ty with
    | .const _ => λ t => Term.SN t
    | .bound _ x => rho x
    | .all mf A B => λ f => ∀ a, L A rho a -> L B rho (.app mf f a)
    | .app mf f a => λ t => False
    | _ => λ _ => False

  def EL (Γ : Ctx) (f : Nat -> Const) (rho : Nat -> Cand) (σ : Subst Term) : Prop :=
    ∀ x, L (Γ d@ x) rho ([σ].bound (f x) x)

  def Admissible (rho : Nat -> Cand) := ∀ x, Reducible (rho x)

  -- Facts about Reducible Sets

  theorem reducible_sn : Reducible Term.SN := by
  constructor; simp
  case _ =>
    intro t t' h r
    cases h; case _ h => apply h _ r
  case _ =>
    intro t _ h
    constructor; intro y r; apply h _ r

  theorem L_reducible2 ty rho :
    Γ ⊢ ty : .const K ->
    Admissible rho ->
    Reducible (L ty rho)
  := by
  intro j ah
  have ph := IsPreProof.from_proof j
  induction ph generalizing Γ K
  case ax => sorry
  case bound => sorry
  case all A B p1 p2 ih1 ih2 =>
    have lem1 : Reducible (L A rho) := by sorry
    have lem2 : Reducible (L B rho) := by sorry
    cases lem1; case _ A1 A2 A3 =>
    cases lem2; case _ B1 B2 B3 =>
      constructor
      case _ =>
        intro t Lh
        simp at Lh
        sorry
      case _ =>
        intro t t' Lh r
        simp at Lh; simp
        intro a La
        have lem1 := Lh _ La
        replace r := @Term.Red.app_congr1 _ _ mf a r
        apply B2 _ _ lem1 r
      case _ =>
        intro t pr h; simp at h; simp
        intro a La
        sorry
  case lam => sorry
  case app => sorry
  case conv => sorry

  theorem L_reducible ty rho :
    (∃ Γ K, Γ ⊢ ty : .const K) ->
    IsPreProof ty ->
    Admissible rho ->
    Reducible (L ty rho)
  := by
  intro h ph ah
  induction ph
  case ax K =>
    constructor
    case _ =>
      intro t Lh
      unfold L at *
      apply Lh
    case _ =>
      intro t t' Lh r
      unfold L at *
      sorry
    case _ =>
      intro t pr h
      unfold L
      sorry
  case bound K x =>
    replace ah := ah x
    cases ah
    case _ h1 h2 h3 =>
      constructor
      case _ =>
        intro t Lh; simp at Lh
        apply h1 _ Lh
      case _ =>
        intro t t' Lh r; simp at Lh; simp
        apply h2 _ _ Lh r
      case _ =>
        intro t pr h; simp at h; simp
        apply h3 _ pr h
  case all A B p1 p2 ih1 ih2 =>
    constructor
    case _ =>
      intro t Lh; simp at Lh
      sorry
    case _ => sorry
    case _ => sorry
  case lam => sorry
  case app => sorry
  case conv => sorry

  theorem L_sn : Admissible rho -> L A rho t -> Term.SN t := by sorry

  theorem L_var A K x : Admissible rho -> L A rho (.bound K x) := by sorry


-- Lemma beta_expansion A B rho s t :
--   admissible rho -> sn t -> L A rho s.[t/] ->
--   L A rho (App (Abs B s) t).
  theorem beta_expansion :
    Admissible rho ->
    Term.SN t ->
    L A rho (b β[t]) ->
    L A rho (.app mf (.lam mf A b) t)
  := by sorry

-- Lemma L_ext T rho tau :
--   (forall i s, rho i s <-> tau i s) -> (forall s, L T rho s <-> L T tau s).

  theorem L_ext : (∀ i t, rho i t <-> tau i t) -> (∀ t, L A rho t <-> L A tau t) := by sorry

  theorem L_ren : L ([r#r]A) rho t <-> L A (λ i => rho (r i)) t := by sorry

  @[simp]
  def Lsubstcomp (rho : Nat -> Cand) (σ : Subst Term) (i : Nat) : Cand :=
    match σ i with
    | .rename j => rho j
    | .replace t => L t rho

  theorem L_subst : L ([σ]A) rho t <-> L A (Lsubstcomp rho σ) t := by sorry

  theorem soundness : Γ ⊢ t : A -> ∀ f rho σ, Admissible rho -> EL Γ f rho σ -> L A rho ([σ]t) := by
  intro j
  induction j
  case ax => sorry
  case var => sorry
  case pi ih1 ih2 =>
    intro f rho σ ah eh
    simp; sorry
  case tpi => sorry
  case lam j1 j2 ih1 ih2 =>
    intro f rho σ ah eh
    simp; unfold L
    intro a lh
    sorry
  case app j1 j2 j3 ih1 ih2 =>
    intro f rho σ ah eh
    simp; sorry
  case econv => sorry
  case iconv => sorry

  theorem rho_id : Admissible (λ _ => Term.SN) := by
  intro x; simp; apply reducible_sn

  theorem type_L : Γ ⊢ t : A -> Admissible rho -> L A rho t := by
  intro j h
  have lem1 := ctx_wf j
  cases lem1
  case _ f lem1 =>
    have lem := soundness j f rho I h
    simp at lem; apply lem
    intro x; simp
    apply L_var _ _ _ h

  theorem strong_normalization : Γ ⊢ t : A -> Term.SN t := by
  intro j
  apply L_sn; apply rho_id; apply type_L
  apply j; apply rho_id

end Fomega.Proof
