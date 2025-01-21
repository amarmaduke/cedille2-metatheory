import Fomega.Term
import Common.Reduction

inductive Red : Term -> Term -> Prop where
-- Steps
| beta : Red ((`λ b) `@ t) (b β[t])
| proj1 : Red ((Term.pair t s).fst) t
| proj2 : Red ((Term.pair t s).snd) s
| unit_rec : Red (.unit_rec (u) t) t
-- Congruences
| lam_congr : Red t t' -> Red (.lam t) (.lam t')
| app_congr1 : Red f f' -> Red (.app f t) (.app f' t)
| app_congr2 : Red t t' -> Red (.app f t) (.app f t')
| all_congr1 : Red A A' -> Red (.all A B) (.all A' B)
| all_congr2 : Red B B' -> Red (.all A B) (.all A B')
| pair_congr1 : Red t t' -> Red (.pair t s) (.pair t' s)
| pair_congr2 : Red s s' -> Red (.pair t s) (.pair t s')
| fst_congr : Red t t' -> Red (.fst t) (.fst t')
| snd_congr : Red t t' -> Red (.snd t) (.snd t')
| times_congr1 : Red A A' -> Red (.times A B) (.times A' B)
| times_congr2 : Red B B' -> Red (.times A B) (.times A B')
| unit_rec_congr1 : Red t1 t1' -> Red (.unit_rec t1 t2) (.unit_rec t1' t2)
| unit_rec_congr2 : Red t2 t2' -> Red (.unit_rec t1 t2) (.unit_rec t1 t2')

inductive ParRed : Term -> Term -> Prop where
-- Steps
| beta : ParRed b b' -> ParRed t t' -> ParRed ((`λ b) `@ t) (b' β[t'])
| proj1 : ParRed t t' -> ParRed s s' -> ParRed ((Term.pair t s).fst) t'
| proj2 : ParRed t t' -> ParRed s s' -> ParRed ((Term.pair t s).snd) s'
| unit_rec : ParRed t t' -> ParRed (.unit_rec (u) t) t'
-- Congruences
| lam_congr : ParRed t t' -> ParRed (.lam t) (.lam t')
| app_congr : ParRed f f' -> ParRed t t' -> ParRed (.app f t) (.app f' t')
| all_congr : ParRed A A' -> ParRed B B' -> ParRed (.all A B) (.all A' B')
| pair_congr : ParRed t t' -> ParRed s s' -> ParRed (.pair t s) (.pair t' s')
| fst_congr : ParRed t t' -> ParRed (.fst t) (.fst t')
| snd_congr : ParRed t t' -> ParRed (.snd t) (.snd t')
| times_congr : ParRed A A' -> ParRed B B' -> ParRed (.times A B) (.times A' B')
| unit_rec_congr : ParRed t1 t1' -> ParRed t2 t2' -> ParRed (.unit_rec t1 t2) (.unit_rec t1' t2')
| var : ParRed (.var x) (.var x)
| const : ParRed (.const k) (.const k)
| unit : ParRed .unit .unit
| unit_ty : ParRed .unit_ty .unit_ty

namespace Term
  @[simp]
  def compl : Term -> Term
  | app (lam b) t => (compl b) β[compl t]
  | fst (pair t _) => compl t
  | snd (pair _ s) => compl s
  | unit_rec (u) t => compl t
  | lam t => lam (compl t)
  | app f a => app (compl f) (compl a)
  | all A B => all (compl A) (compl B)
  | pair t s => pair (compl t) (compl s)
  | times t1 t2 => times (compl t1) (compl t2)
  | fst t => fst (compl t)
  | snd t => snd (compl t)
  | unit => unit
  | unit_ty => unit_ty
  | unit_rec t1 t2 => unit_rec (compl t1) (compl t2)
  | var n => var n
  | const K => const K
end Term

@[simp]
instance instReductionCompletion_Term : ReductionCompletion Term ParRed where
  compl := Term.compl

infix:40 " -β> " => Red
infix:39 " -β>* " => @Star Term Red
infix:38 " =β= " => @Conv Term Red
infix:40 " =β> " => ParRed
infix:39 " =β>* " => @Star Term ParRed
infix:38 " ≡β≡ " => @Conv Term ParRed

namespace ParRed
  theorem red_refl : t =β> t := by
  induction t <;> constructor <;> simp [*]

  theorem red_subst_same σ : s =β> t -> [σ]s =β> [σ]t := by
  intro h; induction h generalizing σ <;> simp
  any_goals try apply red_refl
  any_goals try constructor <;> simp [*]
  case _ b b' t t' _ _ ih1 ih2 =>
    have lem : (`λ([^σ]b) `@ ([σ]t)) =β> ([^σ]b') β[[σ]t'] := by
      apply ParRed.beta (ih1 ^σ) (ih2 _)
    simp at lem; apply lem
  case _ => sorry
  case _ => sorry

  theorem red_subst (σ τ : Subst Term) :
    (∀ n t, σ n = .su t -> ∃ t', τ n = .su t' ∧ t =β> t') ->
    (∀ n k, σ n = .re k -> τ n = .re k) ->
    s =β> t -> [σ]s =β> [τ]t
  := by
  intro h1 h2 r
  induction r generalizing σ τ <;> simp
  case _ b b' t t' _ _ ih1 ih2 =>
    have lem : (`λ([^σ]b) `@ ([σ]t)) =β> ([^τ]b') β[[τ]t'] := by
      apply ParRed.beta
      replace ih1 := ih1 (^σ) (^τ) (Subst.lift_replace red_subst_same h1) (Subst.lift_rename h2)
      apply ih1; apply ih2 _ _ h1 h2
    simp at lem; apply lem
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  -- case _ ih1 ih2 =>
  --   apply ParRed.app; apply ih1 _ _ h1 h2; apply ih2 _ _ h1 h2
  -- case _ _ ih =>
  --   constructor
  --   replace ih := ih (^σ) (^τ) (Subst.lift_replace red_subst_same h1) (Subst.lift_rename h2)
  --   simp at ih; apply ih
  -- case _ x =>
  --   generalize udef : σ x = u
  --   cases u <;> simp at *
  --   case _ y => rw [h2 x y udef]; simp; constructor
  --   case _ t =>
  --     cases (h1 x t udef); case _ v lem =>
  --       rw [lem.1]; simp; apply lem.2

  theorem red_beta : b =β> b' -> t =β> t' -> b β[t] =β> b' β[t'] := by
  intro r1 r2; apply red_subst
  case _ =>
    intro n s h; cases n <;> simp at *
    case _ => subst h; apply r2
  case _ =>
    intro n k h; cases n <;> simp at *; simp [*]
  case _ => apply r1

  theorem triangle : t =β> s -> s =β> Term.compl t := by
  intro h; induction h <;> simp at * <;> try (constructor <;> simp [*])
  case _ b b' t t' r1 r2 ih1 ih2 => apply red_beta ih1 ih2
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ a a' f f' _ r2 ih1 ih2 => sorry
    -- cases f <;> simp at * <;> try (constructor <;> simp [*])
    -- case _ t =>
    --   cases f'
    --   case _ => cases ih2
    --   case _ => cases r2
    --   case _ b =>
    --     cases ih2; case _ ih2 =>
    --       apply ParRed.beta ih2 ih1
  case _ => sorry
  case _ => sorry
  case _ => sorry

end ParRed

instance instReductionTriangle_Term : ReductionTriangle Term ParRed where
  triangle := ParRed.triangle

namespace Red
  theorem red1_subst_same : t -β> s -> [σ]t -β> [σ]s := by sorry

  theorem to_par1 : t -β> s -> t =β> s := by sorry

  theorem from_par1 : t =β> s -> t -β>* s := by sorry

  theorem to_par : t -β>* s -> t =β>* s := by sorry

  theorem from_par : t =β>* s -> t -β>* s := by sorry

  theorem to_conv : t =β= s -> t ≡β≡ s := by sorry

  theorem from_conv : t ≡β≡ s -> t =β= s := by sorry

  theorem subst_same : t =β= s -> ([σ]t) =β= ([σ]s) := by sorry

  theorem red_subst (σ τ : Subst Term) :
    (∀ n t, σ n = .su t -> ∃ t', τ n = .su t' ∧ t -β> t') ->
    (∀ n k, σ n = .re k -> τ n = .re k) ->
    s -β> t -> [σ]s -β> [τ]t
  := by sorry

  theorem red_const_forces_const : .const K -β>* t -> t = .const K := by sorry

  namespace Conv
    theorem subst (σ τ : Subst Term) :
      (∀ n t, σ n = .su t -> ∃ t', τ n = .su t' ∧ t =β= t') ->
      (∀ n k, σ n = .re k -> τ n = .re k) ->
      s =β= t -> [σ]s =β= [τ]t
    := by sorry

    theorem beta : b =β= b' -> t =β= t' -> b β[t] =β= b' β[t'] := by sorry

    theorem const_conv_implies_eq K1 K2 : (.const K1) =β= (.const K2) -> K1 = K2 := by sorry

    theorem refl : t =β= t := by sorry

    theorem sym : t =β= s -> s =β= t := by sorry

    theorem trans : x =β= y -> y =β= z -> x =β= z := by sorry

    theorem all_congr : Π[A] B =β= Π[A'] B' -> A =β= A' ∧ B =β= B' := by sorry

    theorem times_congr : (A ⊗ B) =β= (A' ⊗ B') -> A =β= A' ∧ B =β= B' := by sorry

  end Conv
end Red
