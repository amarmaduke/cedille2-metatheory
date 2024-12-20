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

  def PossibleRedex : Term -> Bool
  | .app _ _ _ => true
  | _ => false

  structure Reducible (P : Cand) : Prop where
    normal : ∀ t, P t -> Term.SN t
    preserve : ∀ t t', P t -> t -β> t' -> P t'
    expand : ∀ t, PossibleRedex t -> (∀ t', t -β> t' -> P t') -> P t

  def L (ty : Term) (rho : Nat -> Cand) : Cand :=
    match ty with
    | .bound .kind x => rho x
    | .all mf A B => λ f => ∀ a, L A rho a -> L B rho (.app mf f a)
    | _ => λ _ => False

  def EL (Γ : Ctx) (f : Nat -> Const) (rho : Nat -> Cand) (σ : Subst Term) : Prop :=
    ∀ x, L (Γ d@ x) rho ([σ].bound (f x) x)

  def Admissible (rho : Nat -> Cand) := ∀ x, Reducible (rho x)

  def stream_to_subst : (Nat -> Term) -> Subst Term
  | s, n => .replace (s n)

  prefix:15 ":s2s:" => stream_to_subst

  -- Facts about Reducible Sets

  theorem reducible_sn : Reducible Term.SN := by
  constructor; simp
  case _ =>
    intro t t' h r
    cases h; case _ h => apply h _ r
  case _ =>
    intro t _ h
    constructor; intro y r; apply h _ r

  theorem L_reducible ty rho : Admissible rho -> Reducible (L ty rho) := by
  sorry

  theorem L_sn : Admissible rho -> L A rho t -> Term.SN t := by sorry

  theorem L_var A K x : Admissible rho -> L A rho (.bound K x) := by sorry

  theorem soundness : Γ ⊢ t : A -> ∀ f rho σ, Admissible rho -> EL Γ f rho σ -> L A rho ([σ]t) := by
  intro j
  induction j
  case ax => sorry
  case var => sorry
  case pi => sorry
  case tpi => sorry
  case lam => sorry
  case app => sorry
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
