import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Inversion
import Cedille.Lemma.Syntax

namespace Cedille

  lemma subst_check {A : Term} :
    Jud v (Γ ++ [x : A]) t A ->
    Γ ⊢ a =: A -> Jud v Γ ([a =: x]t) ([a =: x]A)
  := by {
    intro j
    generalize Δdef : (Γ ++ [x : A]) = Δ at *
    induction j
    case app md Γ' f m A' B a' j1 j2 => {
      intro j3
    }
  }

  -- lemma subst_erase {n} (t1 : Term n) (t2 : Term (n + 1))
  --   : erase x ([_:= t1]t2) = [_:= erase x t1]erase x t2
  -- := @Nat.rec
  --   (λ s => ∀ {n} {t1:Term n} {t2: Term (n + 1)},
  --     size t2 ≤ s ->
  --     erase x ([_:= t1]t2) = [_:= erase x t1]erase x t2)
  --   sorry
  --   (by {
  --     intro s ih n t1 t2 sh
  --     sorry
  --   })
  --   (size t2)
  --   n
  --   t1
  --   t2
  --   (by simp)

  -- lemma subst_erase (S : FvSet!) {t1 : Term 0} {t2 : Term 1}
  --   : (∀ x ∉ S, PseObj ({_|-> x}t2)) ->
  --     erase x ([_:= t1]t2) = [_:= erase x t1]erase x t2
  -- := @Nat.rec
  --   (λ s => ∀ {n:Nat} {t1:Term n} {t2:Term (n + 1)},
  --     size t2 ≤ s ->
  --     (∀ x ∉ S, x ∉ (fv ∘ erase x) ({_|-> x}t)) ->
  --     erase x ([_:= t1]t2) = [_:= erase x t1]erase x t2)
  --   sorry
  --   (by {
  --     intro s ih n' t1 t2 sh h
  --     cases t2 <;> simp at sh
  --     case bound j => apply @ih _ t1 (bound j) (by simp) h
  --     case free x => apply @ih _ t1 (free x) (by simp) h
  --     case const k => apply @ih _ t1 (const k) (by simp) h
  --     case bind k u1 u2 => {
  --       have sh1 : size u1 ≤ s := by linarith
  --       have sh2 : size u2 ≤ s := by linarith
  --       cases k <;> simp at *
  --       case lam md => {
  --         cases md
  --         case free => sorry
  --         case type => sorry
  --         case erased => {

  --           sorry
  --         }
  --       }
  --       case pi md => sorry
  --       case inter => sorry
  --     }
  --     case ctor k u1 u2 u3 => {
  --       have sh1 : size u1 ≤ s := by linarith
  --       have sh2 : size u2 ≤ s := by linarith
  --       have sh3 : size u3 ≤ s := by linarith
  --       cases k <;> simp at *
  --       case app md => {
  --         cases md <;> simp at *
  --         case free => rw [ih sh1, ih sh2]
  --         case type => rw [ih sh1, ih sh2]
  --         case erased => apply ih sh1
  --       }
  --       case pair => apply ih sh1
  --       case fst => apply ih sh1
  --       case snd => apply ih sh1
  --       case eq => rw [ih sh1, ih sh2, ih sh3]
  --       case refl => {
  --         unfold HasHSubst.hsubst; unfold Syntax.instHasHSubstSyntax; simp
  --         unfold Syntax.hsubst; unfold bound; simp
  --         split
  --         case _ h => exfalso; linarith
  --         case _ => simp
  --       }
  --       case eqind => rw [ih sh3]
  --       case jω => rw [ih sh1, ih sh2]
  --       case promote => rw [ih sh1]
  --       case delta => rw [ih sh1]
  --       case phi => rw [ih sh1]
  --     }
  --   })
  --   (size t2)
  --   t1
  --   t2
  --   (by simp)

  -- lemma subst_pseobj {S : FvSet!} :
  --   PseObj a ->
  --   (∀ x, x ∉ S -> PseObj ({_|-> x}f)) ->
  --   PseObj ([_:= a]f)
  -- := by sorry

end Cedille
