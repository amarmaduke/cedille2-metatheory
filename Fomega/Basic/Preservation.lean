import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution
import Fomega.Basic.Inversion
import Fomega.Basic.Classification

namespace Fomega.Proof


  inductive CtxRed : Ctx -> Ctx -> Prop where
  | nil : CtxRed [] []
  | head : A -β> A' -> CtxRed (A::Γ) (A'::Γ)
  | tail : CtxRed Γ Γ' -> CtxRed (A::Γ) (A::Γ')

  namespace CtxRed

    theorem refl : CtxRed Γ Γ := by
    induction Γ
    case _ => constructor
    case _ hd tl ih => apply tail; apply ih

    theorem nth x : CtxRed Γ Γ' -> Γ d@ x = Γ' d@ x ∨ Γ d@ x -β> Γ' d@ x := by
    intro j; induction j generalizing x; simp
    case _ A A' Δ r =>
      cases x <;> simp
      apply Or.inr; apply Red.subst1_same; apply r
    case _ Γ Γ' A _ ih =>
      cases x <;> simp
      case _ x =>
        cases (ih x)
        case _ h => apply Or.inl; rw [h]
        case _ h => apply Or.inr; apply Red.subst1_same; apply h

  end CtxRed

  @[simp]
  abbrev PreservationType (Γ : Ctx) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, A) => ∀ {t' Γ'}, t = t' ∨ t -β> t' -> CtxRed Γ Γ' -> Γ' ⊢ t' : A
  | .wf => λ () => ∀ {Γ'}, CtxRed Γ Γ' -> ⊢ Γ'

  theorem preservation1 : Judgment v Γ ix -> PreservationType Γ v ix := by
  intro j; induction j <;> simp at *
  case nil =>
    intro Γ' r
    cases r; constructor
  case cons Γ A K j1 j2 ih1 ih2 =>
    intro Γ' r
    cases r
    case _ A' r => constructor; apply j1; apply ih2 (Or.inr r) CtxRed.refl
    case _ Γ' r => constructor; apply ih1 r; apply ih2 (Or.inl rfl) r
  case ax Γ j ih =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 => rw [<-r1]; constructor; apply ih r2
    case _ r1 => cases r1
  case var Γ x K T j1 j2 ih =>
    intro t' Γ' r1 r2
    cases r1
    case _ r1 =>
      rw [<-r1]; apply @Judgment.conv _ _ (Γ' d@ x) _ K

    case _ r1 => cases r1
  case pi => sorry
  case lam Γ A K1 K2 B t j1 j2 j3 ih1 ih2 ih3 => sorry
  case app => sorry
  case conv => sorry

  -- abbrev ctx_red x Γ Γ' := ∀ n, Γ d@ x -β> Γ' d@ x ∧ (n ≠ x -> Γ d@ n = Γ' d@ n)

  -- theorem ctx_red_lift : ctx_red x Γ Γ' -> ctx_red (x + 1) (A::Γ) (A::Γ') := by sorry

  -- theorem preservation_ctx_lift : (∀ n, Γ d@ n -β> Δ d@ n ∨ Γ d@n = Δ d@ n) ->
  --   A -β> A' ∨ A = A' ->
  --   ∀ n, (A::Γ) d@ n -β> (A'::Δ) d@ n ∨ (A::Γ) d@n = (A'::Δ) d@ n
  -- := by sorry

  -- theorem preservation1_term : Γ ⊢ t : A ->
  --   (∀ n, Γ d@ n -β> Δ d@ n ∨ Γ d@n = Δ d@ n) ->
  --   Δ ⊢ t : A ∧ (∀ t', t -β> t' -> Δ ⊢ t' : A)
  -- := by
  -- intro j h
  -- induction j generalizing Δ
  -- case ax Γ f j ih =>
  --   apply And.intro
  --   case _ =>
  --     apply Proof.ax f
  --     intro x
  --     cases (h x)
  --     case _ hx => apply (ih x h).2 _ hx
  --     case _ hx => rw [<-hx]; apply (ih x h).1
  --   case _ => intro t' r; cases r
  -- case var Γ x K j ih =>
  --   apply And.intro
  --   case _ =>
  --     constructor; constructor
  --     cases (h x)
  --     case _ hx => apply (ih h).2 _ hx
  --     case _ hx => rw [<-hx]; apply (ih h).1
  --     apply (ih h).1
  --     cases (h x)
  --     case _ hx =>
  --       exists (Δ d@ x); apply And.intro
  --       apply Term.Red.refl; apply Term.RedStar.step; apply hx; apply Term.Red.refl
  --     case _ hx => rw [hx]; apply Term.RedConv.refl
  --   case _ => intro t' r; cases r
  -- case pi Γ A K B j1 j2 ih1 ih2 =>
  --   apply And.intro
  --   case _ =>
  --     constructor
  --     apply (ih1 h).1
  --     apply (@ih2 (A::Δ) (preservation_ctx_lift h (Or.inr rfl))).1
  --   case _ => sorry
  -- case tpi => sorry
  -- case lam Γ A B K t j1 j2 ih1 ih2 =>
  --   apply And.intro
  --   case _ =>
  --     constructor
  --     apply (ih1 h).1
  --     apply (@ih2 (A::Δ) (preservation_ctx_lift h (Or.inr rfl))).1
  --   case _ =>
  --     intro t' r
  --     cases r
  --     case lam_congr1 A' r =>
  --       constructor; constructor
  --       apply (ih1 h).2 _ (Term.Red.all_congr1 r)
  --       apply (@ih2 (A'::Δ) (preservation_ctx_lift h (Or.inl r))).1
  --       apply (ih1 h).1
  --       exists (.all mf A' B); apply And.intro
  --       apply Term.Red.refl
  --       apply Term.Red.congr1 (λ A => .all mf A B) Term.Red.all_congr1
  --       apply Term.RedStar.step r; apply Term.Red.refl
  --     case lam_congr2 t' r =>
  --       constructor; apply (ih1 h).1
  --       apply (@ih2 (A::Δ) (preservation_ctx_lift h (Or.inr rfl))).2 _ r
  -- case app Γ f A B a B' j1 j2 j3 ih1 ih2 =>
  --   apply And.intro
  --   case _ =>
  --     constructor
  --     apply (ih1 h).1; apply (ih2 h).1; apply j3
  --   case _ =>
  --     intro t' r
  --     sorry
  -- case econv Γ t A B K j1 j2 j3 ih1 ih2 =>
  --   apply And.intro
  --   case _ =>
  --     constructor
  --     apply (ih1 h).1; apply (ih2 h).1; apply j3
  --   case _ =>
  --     intro t' r
  --     sorry
  -- case iconv Γ t A B K j1 j2 j3 ih1 ih2 =>
  --   apply And.intro
  --   case _ =>
  --     constructor
  --     apply (ih1 h).1; apply (ih2 h).1; apply j3
  --   case _ => sorry

  -- theorem preservation_jud : Γ ⊢ t : A ->
  --   (∀ t', t -β> t' -> Γ ⊢ t' : A)
  --   ∧ (∀ x Γ', ctx_red x Γ Γ' -> Γ' ⊢ t : A)
  --   ∧ (∀ x Γ', ctx_red x Γ Γ' -> t = Γ d@ x -> Γ' ⊢ Γ' d@ x : A)
  -- := by
  -- intro j
  -- induction j
  -- case ax Γ f h ih =>
  --   apply And.intro
  --   intro t' r; cases r
  --   sorry
  -- case var Γ i K h ih =>
  --   have ih1 := ih.1; have ih2 := ih.2.1; have ih3 := ih.2.2; clear ih
  --   apply And.intro
  --   case _ => intro t' r; cases r
  --   apply And.intro
  --   case _ =>
  --     intro x Γ' r
  --     cases Nat.decEq i x
  --     case _ hv =>
  --       rw [(r i).2 hv] at *; constructor
  --       apply ih2 _ _ r
  --     case _ hv =>
  --       subst hv
  --       constructor; constructor
  --       apply ih3 i _ r; rfl
  --       apply ih2 _ _ r
  --       exists (Γ' d@ i); apply And.intro; apply Term.RedStar.refl
  --       apply Term.RedStar.step; apply (r i).1; apply Term.RedStar.refl
  --   case _ =>
  --     intro x Γ' r ht
  --     replace r := (r x).1; rw [<-ht] at r
  --     cases r
  -- case pi => sorry
  -- case tpi => sorry
  -- case lam => sorry
  -- case app => sorry
  -- case econv => sorry
  -- case iconv => sorry

  -- theorem preservation : Γ ⊢ t : A -> t -β>* t' -> Γ ⊢ t' : A := by
  -- intro j r
  -- induction r generalizing Γ A
  -- case _ => exact j
  -- case _ r1 _r2 ih => apply ih (preservation1 j r1)

  theorem preservation_type : Γ ⊢ t : A -> A -β>* A' -> Γ ⊢ t : A' := by sorry

end Fomega.Proof
