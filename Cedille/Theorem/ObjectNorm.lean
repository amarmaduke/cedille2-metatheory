import Cedille.Def
import Cedille.Lemma
import Cedille.Theorem.Conv

namespace Cedille

  theorem object_red_norm1 (S: FvSet!) (s : Term 0) : 
    Γ ⊢ t =: A ->
    Γ ⊢ s =: A ->
    (∀ x, x ∉ S -> erase x t -β> erase x s) ->
    t -β>+ s
  := λ h1 h2 h3 => @Nat.rec
    (λ si => ∀ S Γ t s A,
      size t ≤ si ->
      Γ ⊢ t =: A ->
      Γ ⊢ s =: A ->
      (∀ x, x ∉ S -> erase x t -β> erase x s) ->
      t -β>+ s)
    sorry
    (by {
      intro si ih S Γ t s A sh j1 j2 er
      cases t
      case bound => apply ih S Γ (bound _) s A (by simp) j1 j2 er
      case free => apply ih S Γ (free _) s A (by simp) j1 j2 er
      case const => apply ih S Γ (const _) s A (by simp) j1 j2 er
      case bind b u1 u2 => {
        simp at *
        have shu1 : size u1 ≤ si := by linarith
        have shu2 : size u2 ≤ si := by linarith
        cases b <;> simp at *
        case lam m => {
          cases m
          case free => sorry
          case type => sorry
          case erased => {
            simp at er
            cases j1; case _ A' K j1 c j3 =>
            cases j1; case _ K2 B S2 j4 j5 j6 =>
            sorry
          }
        }
        case pi m => {
          cases m
          case free => sorry
          case type => sorry
          case erased => {
            sorry
          }
        }
        case inter => {
          -- have to do induction on size of s here
          sorry
        }
      }
      case ctor => {
        sorry
      }
    })
    (size t + size s)
    S
    Γ
    t
    s
    A
    (by simp)
    h1
    h2
    h3

  theorem object_red_norm2 (S: FvSet!) (s : Term 0) : 
    Γ ⊢ t =: A ->
    Γ ⊢ s =: A ->
    (∀ x, x ∉ S -> erase x t -β> erase x s) ->
    t -β>+ s
  := λ j1 j2 er => @Check.rec
    (λ Γ t A j => ∀ (S: FvSet!) (s: Term 0),
      Γ ⊢ s =: A ->
      (∀ x, x ∉ S -> erase x t -β> erase x s) ->
      t -β>+ s)
    (λ Γ t A j => ∀ (S: FvSet!) (s: Term 0),
      Γ ⊢ s =: A ->
      (∀ x, x ∉ S -> erase x t -β> erase x s) ->
      t -β>+ s)
    (λ Γ t A j => ∀ (S: FvSet!) (s: Term 0),
      Γ ⊢ s =: A ->
      (∀ x, x ∉ S -> erase x t -β> erase x s) ->
      t -β>+ s)
    (λ Γ wf => ⊢ Γ)
    sorry
    sorry
    sorry
    (by {
      intro Γ A m K t B S j1 j2 j3 ih1 ih2 S2 s j4 er; simp at *
      cases m
      case free => sorry
      case type => sorry
      case erased => {
        sorry
      }
    })
    sorry
    sorry
    sorry
    (by {
      intro Γ t A B j ih S s j2 er
      cases j2; case _ A2 K2 j2 c1 j3 =>
      cases j2
      case ax => sorry
      case var => sorry
      case pi => sorry
      case lam => sorry
      case app => sorry
      case inter => sorry
      case pair => sorry
      case fst => sorry
      case snd => sorry
      case eq => sorry
      case refl => sorry
      case eqind => sorry
      case promote => sorry
      case phi => sorry
      case delta => sorry
    })
    sorry
    sorry
    (by {
      intro Γ t A j ih S s j1 er
      have xfresh := @Name.fresh_is_fresh S
      generalize xdef : Name.fresh S = x at *
      replace er := er x xfresh
      simp at *
    })
    (by {
      intro Γ A P x y r w j1 j2 j3 j4 j5 j6 ih1 ih2 ih3 ih4 ih5 ih6 S s j7 er
      sorry
    })
    (by {
      intro Γ e T a b A B j1 j2 j3 c1 ih1 ih2 ih3 S s j4 er
      sorry
    })
    (by {
      sorry
    })
    (by {
      intro Γ e a ih S s j2 er
      sorry
    })
    (by {
      intro Γ t A B j step ih S s j1 er
      have lem : A =β= B := sorry
      have j1 : Γ ⊢ s =: A := sorry
      apply ih S s j1 er
    })
    (by {
      intro Γ t A B K j1 j2 conv ih1 ih2 S s j3 er
      replace j1 : Γ ⊢ s =: A := sorry
      apply ih1 S s j1 er
    })
    (by simp; constructor)
    (by {
      intro x Γ A K xin wf j wf2 ih
      apply Wf.append xin wf j
    })
    Γ
    t
    A
    j1
    S
    s
    j2
    er



end Cedille
