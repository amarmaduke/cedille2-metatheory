
import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof
import Fomega.Conv
import Fomega.FreeVars

namespace Fomega

  namespace Proof

    theorem rename_strong (r : Ren) : (p : Γ ⊢ t : A) ->
      (∀ x, IsFreeVar x Γ t A p -> [r#r](Γ d@ x) = Δ d@ (r x)) ->
      Δ ⊢ ([r#r]t) : ([r#r]A)
    := by
    intro j h
    induction j generalizing Δ r
    case ax => constructor
    case var A' Γ' x K j1 j2 ih =>
      simp; constructor
      case _ =>
        subst j1; rw [h x (by {
          apply IsFreeVar.var2; simp; apply j2
        })]
      case _ => apply ih r (by {
        intro x fv
        apply h x; apply IsFreeVar.var1; apply j1; apply fv
      })
    case pi Γ' A' K B j1 j2 ih1 ih2 =>
      simp; constructor
      case _ => apply ih1 r (by {
        intro x fv
        apply h x; apply IsFreeVar.pi1; apply fv; apply j2
      })
      case _ =>
        replace ih2 := @ih2 ([r#r]A' :: Δ) (Term.Ren.lift r) (by {
          intro x fv
          cases x <;> simp
          case _ x =>
            replace h := h x (by {
              apply IsFreeVar.pi2; apply j1; apply fv
            })
            rw [<-Term.subst_apply_compose_commute, h]
        })
        simp at ih2; exact ih2
    case tpi Γ' A' B j1 j2 ih1 ih2 =>
      simp; constructor
      case _ => apply ih1 r (by {
        intro x fv
        apply h x; apply IsFreeVar.tpi1; apply fv; apply j2
      })
      case _ =>
        replace ih2 := @ih2 ([r#r]A' :: Δ) (Term.Ren.lift r) (by {
          intro x fv
          cases x <;> simp
          case _ x =>
            replace h := h x (by {
              apply IsFreeVar.tpi2; apply j1; apply fv
            })
            rw [<-Term.subst_apply_compose_commute, h]
        })
        simp at ih2; exact ih2
    case lam Γ' A' B K t j1 j2 ih1 ih2 =>
      simp; constructor
      case _ => simp at ih1; apply ih1 r (by {
        intro x fv
        apply h x; apply IsFreeVar.lam1; apply fv; apply j2
      })
      case _ =>
        replace ih2 := @ih2 ([r#r]A' :: Δ) (Term.Ren.lift r) (by {
          intro x fv
          cases x <;> simp
          case _ x =>
            replace h := h x (by {
              apply IsFreeVar.lam2; apply j1; apply fv
            })
            rw [<-Term.subst_apply_compose_commute, h]
        })
        simp at ih2; exact ih2
    case app Γ' f A' B a B' j1 j2 j3 ih1 ih2 =>
      simp; constructor
      case _ => apply ih1 r (by {
        intro x fv
        apply h x; apply IsFreeVar.app1; apply fv; apply j2; apply j3
      })
      case _ => apply ih2 r (by {
        intro x fv
        apply h x; apply IsFreeVar.app2; apply j1; apply fv; apply j3
      })
      case _ => subst j3; simp
    case conv Γ' t A' B K j1 j2 j3 ih1 ih2 =>
      constructor
      case _ => apply ih1 r (by {
        intro x fv
        apply h x; apply IsFreeVar.conv1; apply fv; apply j2; apply j3
      })
      case _ => apply ih2 r (by {
        intro x fv
        apply h x; apply IsFreeVar.conv2; apply j1; apply fv; apply j3
      })
      case _ => apply Conv.rename; apply j3

    theorem rename (r : Ren) : Γ ⊢ t : A ->
      (∀ x, [r#r](Γ d@ x) = Δ d@ (r x)) ->
      Δ ⊢ ([r#r]t) : ([r#r]A)
    := by
    intro j h
    apply rename_strong r j
    intro x _fv; apply h x

    theorem weaken B : Γ ⊢ t : A -> (B::Γ) ⊢ ([S]t) : ([S]A) := by
    intro j; apply rename; exact j
    case _ => intro x; simp; rw [Term.S_to_rS]; unfold rS; simp

    theorem contract_strong_lift n :
      --[^{n}S]V = U ->
      (∀ x y A, (^{n}S) x = .rename y -> [^{n}S]A = Γ d@ y -> A = Δ d@ x) ->
      ∀ x y A, (^{n + 1}S) x = .rename y -> [^{n + 1}S]A = (U::Γ) d@ y -> A = (V::Δ) d@ x
    := by
    intro h1 x y A h2 h3
    cases x
    case _ => sorry
    case _ x =>
      simp at *; cases y
      case _ => sorry
      case _ y =>
        simp at *
        have h4 : (^{n}S) x = .rename y := by sorry
        replace h1 := h1 x y A h4
        sorry

    theorem contract_strong n :
      Γ ⊢ ([^{n}S]t) : ([^{n}S]T) ->
      (∀ x y A, (^{n}S) x = .rename y -> [^{n}S]A = Γ d@ y -> A = Δ d@ x) ->
      Δ ⊢ t : T
    := by
    intro j h
    generalize sdef : [^{n}S]t = s at j
    generalize Udef : [^{n}S]T = U at j
    induction j generalizing t T n Δ
    case ax =>
      cases t <;> simp at sdef
      case _ _ x =>
        have lem := @Term.rep_n_S_exists n x
        cases lem; case _ z h => rw [h] at sdef; simp at sdef
      case _ K =>
        subst sdef; cases T <;> simp at Udef
        case _ _ x =>
          have lem := @Term.rep_n_S_exists n x
          cases lem; case _ z h => rw [h] at Udef; simp at Udef
        case _ K => subst Udef; constructor
    case var A Γ x K j1 j2 ih =>
      cases t <;> simp at sdef
      case _ K' y =>
        generalize σdef : (^{n}S) y = σ at sdef
        cases σ
        case _ z =>
          simp at sdef
          cases sdef
          case _ e1 e2 =>
            subst e1; subst e2
            constructor
            case _ =>
              subst j1
              apply h y z T σdef Udef
            case _ => apply ih n h Udef (by simp)
        case _ => sorry
    case pi Γ A K B j1 j2 ih1 ih2 =>
      sorry
    case tpi => sorry
    case lam Γ A B K t' j1 j2 ih1 ih2 =>
      cases t <;> simp at sdef
      case _ _ x =>
        have lem := @Term.rep_n_S_exists n x
        cases lem; case _ z h => rw [h] at sdef; simp at sdef
      case _ m r1 r2 =>
        cases T <;> simp at Udef
        case _ _ x =>
          have lem := @Term.rep_n_S_exists n x
          cases lem; case _ z h => rw [h] at Udef; simp at Udef
        case _ m' R1 R2 =>
          rw [sdef.1, Udef.1]
          have lem : R1 = r1 := by sorry
          subst lem; constructor
          case _ =>
            apply @ih1 (.all mf R1 R2) (.const K) Δ n h
            simp [*]; simp
          case _ =>
            apply @ih2 r2 R2 (R1::Δ) (n + 1) _
            simp [*]; simp [*]
            apply contract_strong_lift
            exact h
    case app => sorry
    case conv => sorry

    theorem contract2 :
      (A :: Δ) ⊢ ([S]t) : ([S]T) -> Δ ⊢ t : T
    := by
    intro j
    apply contract_strong 0 j
    case _ =>
      intro x y T h1 h2
      simp at *
      cases y <;> simp at *
      case _ y =>
        subst h1
        exact Term.rename_injective rS Term.rS_injective h2

    theorem contract :
      (A :: Δ) ⊢ ([S]t) : ([S]T) -> Δ ⊢ t : T
    := by
      intro j
      have lem := @rename_strong (A :: Δ) _ _ Δ rP j
        (by {
          intro x h
          cases x
          /-
          A : Term
          Δ : List Term
          t T : Term
          j : (A :: Δ) ⊢ ([S]t) : ([S]T)
          h : IsFreeVar 0 (A :: Δ) ([S]t) ([S]T) j
          ⊢ [Term.Subst.from_ren rP](A :: Δ)d@0 = Δ d@rP 0
          -/
          case _ => sorry
          case _ x => simp; rw [<-Term.P_to_rP]; simp
        })
      rw [<-Term.P_to_rP] at lem; simp at lem; exact lem

    theorem lift_subst :
      (∀ n K, Δ ⊢ ([σ](Γ d@ n)) : .const K -> Δ ⊢ ([σ](.bound K n)) : ([σ](Γ d@ n))) ->
      ∀ n K, ([σ]A :: Δ) ⊢ ([^σ]((A :: Γ) d@ n)) : .const K -> ([σ]A :: Δ) ⊢ ([^σ](.bound K n)) : ([^σ]((A :: Γ) d@ n))
    := by
    intro h n K j
    cases n <;> simp
    case _ => constructor; simp; simp at j; exact j
    case _ n =>
      generalize ydef : (S ⊙ σ) n = y
      cases y
      case _ x =>
        simp at *
        replace h := h n K
        unfold Term.Subst.compose at ydef; simp at ydef
        generalize zdef : σ n = z at *
        cases z; simp at *
        case _ t' =>
          have lem : ([σ]A :: Δ) ⊢ ([S][σ]Γ d@ n) : ([S].const K) := by simp; exact j
          replace j := contract lem
          replace h := weaken ([σ]A) (h j)
          simp at h; subst ydef; exact h
        case _ t' => simp at *
      case _ t =>
        simp at *
        replace h := h n K
        unfold Term.Subst.compose at ydef; simp at ydef
        generalize zdef : σ n = z at *
        cases z; simp at *
        case _ t' =>
          simp at ydef; subst ydef; simp at h
          have lem : ([σ]A :: Δ) ⊢ ([S][σ]Γ d@ n) : ([S].const K) := by simp; exact j
          replace j := contract lem
          have h' := weaken ([σ]A) (h j)
          simp at h'; exact h'

    theorem subst :
      (∀ n s, σ n = .replace s -> IsPreProof s) ->
      (∀ n K, Δ ⊢ ([σ](Γ d@ n)) : .const K -> Δ ⊢ ([σ](.bound K n)) : ([σ](Γ d@ n))) ->
      Γ ⊢ t : A -> Δ ⊢ ([σ]t) : ([σ]A)
    := by
    intro h1 h2 j
    induction j generalizing Δ σ
    case _ => constructor
    case var A' Γ' x K j1 j2 ih =>
      simp; generalize ydef : σ x = y at *
      cases y
      case _ y =>
        simp at *;
        replace ih := ih h1 h2
        replace h := h2 x K
        rw [ydef, <-j1] at h;
        replace h := h ih
        subst j1; exact h
      case _ t' =>
        simp at *;
        replace ih := ih h1 h2
        replace h := h2 x K
        rw [ydef, <-j1] at h;
        replace h := h ih
        subst j1; exact h
    case pi Γ' A' K B _j1 _j2 ih1 ih2 =>
      simp; constructor; apply ih1 h1 h2
      replace ih2 := @ih2 (^σ) ([σ]A' :: Δ) (IsPreProof.lift h1) (lift_subst h2)
      simp at ih2; exact ih2
    case tpi Γ' A' B _j1 _j2 ih1 ih2 =>
      simp; constructor; apply ih1 h1 h2
      replace ih2 := @ih2 (^σ) ([σ]A' :: Δ) (IsPreProof.lift h1) (lift_subst h2)
      simp at ih2; exact ih2
    case lam Γ' A' B K t' _j1 _j2 ih1 ih2 =>
      simp; constructor; simp at *; apply ih1 h1 h2
      replace ih2 := @ih2 (^σ) ([σ]A' :: Δ) (IsPreProof.lift h1) (lift_subst h2)
      simp at ih2; exact ih2
    case app Γ' f A' B a B' _j1 _j2 j3 ih1 ih2 =>
      simp; constructor; apply ih1 h1 h2; apply ih2 h1 h2
      simp at *; subst j3; simp
    case conv Γ' t' A' B K _j1 _j2 j3 ih1 ih2 =>
      constructor; apply ih1 h1 h2; apply ih2 h1 h2
      apply Conv.subst
      case _ =>
        intro n s eq
        apply h1 n s eq
      case _ => exact j3

    theorem beta : (A::Γ) ⊢ b : B -> Γ ⊢ t : A -> Γ ⊢ (b β[t]) : (B β[t]) := by
    simp; intro j1 j2
    apply @subst _ _ (A::Γ)
    case _ =>
      intro n s eq
      cases n <;> simp at *
      subst eq; apply IsPreProof.from_proof j2
    case _ =>
      intro n K j; simp
      cases n
      case _ => simp; exact j2
      case _ x => simp at *; constructor; simp; exact j
    case _ => exact j1

  end Proof

end Fomega
