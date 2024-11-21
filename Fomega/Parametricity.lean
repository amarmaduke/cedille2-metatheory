
import Common
import Fomega.Proof

namespace Fomega.Proof

  def Tuple (n : Nat) (T : (i : Nat) -> i < n -> Type) : Type := (i : Nat) -> (b : i < n) -> T i b

  abbrev RelCtx n := Tuple n (λ _ _ => Ctx)
  abbrev RelKind n (Γ : RelCtx n) := Tuple n (λ i b => Σ' (t : Term), (t ⊢ Γ i b ∧ Γ i b ⊢ t : □))

  -- abbrev rel_kinds n Γ : RelKind n Γ := λ _ _ => PSigma.mk □ (by sorry)
  -- abbrev rel_types n Γ : RelKind n Γ := λ _ _ => PSigma.mk ★ (by sorry)

  abbrev RelType n Γ (k : RelKind n Γ) := Tuple n (λ i b => Σ' (t : Term), (t ⊢ Γ i b ∧ Γ i b ⊢ t : (k i b).1))

  abbrev RelTerm n Γ (k : RelKind n Γ) (φ : RelType n Γ k) := Tuple n (λ i b => Σ' (t : Term), (t ⊢ (Γ i b) ∧ (Γ i b) ⊢ t : (φ i b).1))

  def Rel (n : Nat) Γ (k : RelKind n Γ) (φ : RelType n Γ k) : Type := RelTerm n Γ k φ -> Prop

  -- abbrev fnTpiType {n : Nat} {Γ : RelCtx n} {k : RelKind n}
  --   (α : RelType n Γ k) (ty : RelType n (λ i b => (α i b).1 :: (Γ i b)) (rel_types n))
  --   : RelType n Γ (rel_types n)
  -- := λ i b => PSigma.mk (.all mf (α i b).1 (ty i b).1) (by {
  --   apply And.intro; constructor; exact (α i b).2.1; exact (ty i b).2.1
  --   constructor; exact (α i b).2.2; exact (ty i b).2.2
  -- })

  -- def fnTpi {n : Nat} {Γ : RelCtx n} {k : RelKind n}
  --   (α : RelType n Γ k) (ty : RelType n (λ i b => (α i b).1 :: (Γ i b)) (rel_types n))
  --   (F : (φ:RelType n Γ k) -> Rel n Γ k φ -> Prop)
  --   : Rel n Γ (rel_types n) (fnTpiType α ty)
  -- := λ t => ∀ (s:RelType n Γ k) R,
  --   F (λ i b => (ty i b).1 β[(s i b).1]) R ->
  --   R (λ i b => PSigma.mk (.app mf (t i b).1 (s i b))
  --     (by {
  --     apply And.intro; constructor; exact (t i b).2.1; exact (h i b).1
  --     constructor; exact (t i b).2.2; exact (h i b).2; simp
  --   }))

  def KindMap (n:Nat) (Γ : RelCtx n) : Type := Nat -> RelKind n Γ
  def TypeMap (n:Nat) Γ (k : KindMap n Γ) : Type := Nat -> RelType n Γ (k n)
  def TermMap (n:Nat) Γ (k : KindMap n Γ) (φ : TypeMap n Γ k) : Type := Nat -> RelTerm n Γ (k n) (φ n)

  theorem parametricity : ∀ (n : Nat) (Γ : RelCtx n), (Fam : ∀ {n Γ k φ}, Rel n Γ k φ) (ζ : KindMap n Γ) (ξ : TypeMap n Γ ζ) (φ : TermMap n Γ ζ ξ)
    (∀ i, Fam (φ i)) -> True
  := by sorry


end Fomega.Proof
