
import Common
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Inversion
import Cedille.Lemma.Red

namespace Cedille

  lemma project_ctx_proof : ⊢ Γ -> (x, A) ∈ Γ -> ∃ K, Γ ⊢ A >: const K := sorry

  lemma classification_of_check : Γ ⊢ t =: A -> ∃ K, Γ ⊢ A >: const K := by {
    intro j
    cases j; case _ A' K j conv j2 =>
    exists K
  }

  lemma classification_of_infer : Γ ⊢ t : A ->
    A = kindu ∨ ∃ K, Γ ⊢ A >: const K
  := λ j => @Infer.rec
    (λ Γ t A j => A = kindu ∨ ∃ K, Γ ⊢ A >: const K)
    (λ Γ t A j => A = kindu ∨ ∃ K, Γ ⊢ A >: const K)
    (λ Γ t A j => A = kindu ∨ ∃ K, Γ ⊢ A >: const K)
    (λ Γ wf => True)
  (by {
    intro Γ wf _
    apply Or.inl rfl
  })
  (by {
    intro Γ x A wf xn _
    apply Or.inr _
    have lem := project_ctx_proof wf xn
    cases lem; case _ K j =>
    sorry
  })
  (by {
    intro Γ A m K B S j1 j2 ih1 ih2; simp at *
    cases m <;> simp at *
    case free => {
      apply Or.inr _
      exists Constant.kindU
      sorry
    }
    case erased => {
      apply Or.inr _
      exists Constant.kindU
      sorry
    }
  })
  (by {
    intro Γ A m K t B S j1 j2 j3 ih1 ih2; simp at *
    sorry
  })
  (by {
    intro Γ f m A B a S j1 j2 ih1 ih2
    cases ih1 <;> simp at *
    case inr h => {
      casesm* ∃ _, _, _ ∧ _; case _ K A' j step =>
      sorry
    }
  })
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  (by {
    intro Γ t A B j step ih
    sorry
  })
  (by {
    intro Γ t A B K j1 j2 conv ih1 ih2
    apply Or.inr _
    exists K
  })
  (by simp)
  (by simp)
  Γ
  t
  A
  j

  lemma classification_of_infer2 : Γ ⊢ t : A ->
    A = kindu ∨ ∃ K, Γ ⊢ A >: const K
  := λ j => @Nat.rec
    (λ s => ∀ Γ t A,
      size t ≤ s ->
      Γ ⊢ t >: A ->
      A = kindu ∨ ∃ K, Γ ⊢ A >: const K)
    (by {
      intro Γ t A sh j
      sorry
    })
    (by {
      intro s ih Γ t A sh j
      cases t
      case bound => apply ih Γ (bound _) A (by simp) j
      case free => apply ih Γ (free _) A (by simp) j
      case const => apply ih Γ (const _) A (by simp) j
      case bind b u1 u2 => {
        simp at *
        have s1 : size u1 ≤ s := by linarith
        have s2 : size u2 ≤ s := by linarith
        cases b <;> simp at *
        case lam m => {
          sorry
        }
        case pi m => {
          sorry
          -- cases j; case _ K S j1 j2 =>
          -- cases m <;> simp at *
          -- case free => {
          --   apply Or.inr; exists Constant.kindU; unfold const; simp
          --   apply ConInfer.infer _ _; exact kindu
          --   apply Infer.ax
          --   apply cinfer_implies_wf j1
          --   apply RedStar.refl
          -- }
          -- case erased => {
          --   apply Or.inr; exists Constant.kindU; unfold const; simp
          --   apply ConInfer.infer _ _; exact kindu
          --   apply Infer.ax
          --   apply cinfer_implies_wf j1
          --   apply RedStar.refl
          -- }
        }
        case inter => {
          cases j; case _ A' j step =>
          cases j; case _ S j1 j2 =>
          -- easy
          sorry
        }
      }
      case ctor c u1 u2 u3 => {
        simp at *
        have s1 : size u1 ≤ s := by linarith
        have s2 : size u2 ≤ s := by linarith
        have s3 : size u3 ≤ s := by linarith
        cases c <;> simp at *
        case app m => {
          sorry
        }
        case pair => sorry
        case fst => sorry
        case snd => sorry
        case eq => {
          cases j; case _ T j step =>
          cases j; case _ j1 j2 j3 =>
          -- easy
          sorry
        }
        case refl => {
          sorry
        }
        case eqind => sorry
        case j0 => sorry
        case jω => sorry
        case promote => sorry
        case delta => sorry
        case phi => sorry
      }
    })
    (size t)
    Γ
    t
    A
    (by simp)
    (ConInfer.infer j RedStar.refl)

end Cedille
