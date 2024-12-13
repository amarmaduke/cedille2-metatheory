import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification

namespace Fomega.Proof

  abbrev ctx_red x Γ Γ' := ∀ n, Γ d@ x -β> Γ' d@ x ∧ (n ≠ x -> Γ d@ n = Γ' d@ n)

  theorem ctx_red_lift : ctx_red x Γ Γ' -> ctx_red (x + 1) (A::Γ) (A::Γ') := by sorry

  theorem preservation_jud : Γ ⊢ t : A ->
    (∀ t', t -β> t' -> Γ ⊢ t' : A)
    ∧ (∀ x Γ', ctx_red x Γ Γ' -> Γ' ⊢ t : A)
    ∧ (∀ x Γ', ctx_red x Γ Γ' -> t = Γ d@ x -> Γ' ⊢ Γ' d@ x : A)
  := by
  intro j
  induction j
  case ax Γ f h ih =>
    apply And.intro
    intro t' r; cases r
    sorry
  case var Γ i K h ih =>
    have ih1 := ih.1; have ih2 := ih.2.1; have ih3 := ih.2.2; clear ih
    apply And.intro
    case _ => intro t' r; cases r
    apply And.intro
    case _ =>
      intro x Γ' r
      cases Nat.decEq i x
      case _ hv =>
        rw [(r i).2 hv] at *; constructor
        apply ih2 _ _ r
      case _ hv =>
        subst hv
        constructor; constructor
        apply ih3 i _ r; rfl
        apply ih2 _ _ r
        exists (Γ' d@ i); apply And.intro; apply Term.RedStar.refl
        apply Term.RedStar.step; apply (r i).1; apply Term.RedStar.refl
    case _ =>
      intro x Γ' r ht
      replace r := (r x).1; rw [<-ht] at r
      cases r
  case pi => sorry
  case tpi => sorry
  case lam => sorry
  case app => sorry
  case econv => sorry
  case iconv => sorry

  -- theorem preservation : Γ ⊢ t : A -> t -β>* t' -> Γ ⊢ t' : A := by
  -- intro j r
  -- induction r generalizing Γ A
  -- case _ => exact j
  -- case _ r1 _r2 ih => apply ih (preservation1 j r1)

  theorem preservation_type : Γ ⊢ t : A -> A -β>* A' -> Γ ⊢ t : A' := by sorry

end Fomega.Proof
