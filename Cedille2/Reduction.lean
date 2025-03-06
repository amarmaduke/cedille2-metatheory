import Cedille2.Term
import Common

namespace Cedille2

inductive Red : Term -> Term -> Prop where
-- Steps
| beta : Red ((`λ(m)[A] b) `@(m2) t) (b β[t])
| fst : Red ((Term.inter g1 g2 B t s).!1) t
| snd : Red ((Term.inter g1 g2 B t s).!2) s
| subst : Red (.subst Pr (.refl v) t) t
| phi : Red (.phi a b (.refl t)) b
-- Conv steps
| conv_beta : Red
  ((.conv g1 g2 (`∀(m1)[A1] B) (`λ(m2)[A2] b)) `@(m3) t)
  (.conv g1 g2 (B β[t]) (b β[.conv g1 g2 A2 t]))
| conv_fst : Red
  ((.conv g1 g2 ([A]∩ B1) (.inter g3 g4 B2 t s)).!1)
  (.conv g1 g2 A t)
| conv_snd : Red
  ((.conv g1 g2 ([A]∩ B1) (.inter g3 g4 B2 t s)).!2)
  (.conv g1 g2 (B1 β[.conv g1 g2 A t]) s)
| conv_subst : Red
  ((.subst Pr (.conv g1 g2 (.eq a b) (.refl u)) t))
  (.conv g1 g2 (Pr `@τ b `@τ (.conv g1 g2 (.eq a b) (.refl u))) t)
| conv_phi : Red
  (.phi a b (.conv g1 g2 (.eq x y) (.refl t)))
  b
| conv_conv : Red
  (.conv g1 g2 A (.conv g3 g4 B t))
  (.conv (g1 + g3) (g2 + g4) A t)
-- Congruences
| lam_congr1 : Red A A' -> Red (.lam m A t) (.lam m A' t)
| lam_congr2 : Red t t' -> Red (.lam m A t) (.lam m A t')
| app_congr1 : Red f f' -> Red (.app m f t) (.app m f' t)
| app_congr2 : Red t t' -> Red (.app m f t) (.app m f t')
| all_congr1 : Red A A' -> Red (.all m A B) (.all m A' B)
| all_congr2 : Red B B' -> Red (.all m A B) (.all m A B')
| inter_congr1 : Red B B' -> Red (.inter g1 g2 B t s) (.inter g1 g2 B' t s)
| inter_congr2 : Red t t' -> Red (.inter g1 g2 B t s) (.inter g1 g2 B t' s)
| inter_congr3 : Red s s' -> Red (.inter g1 g2 B t s) (.inter g1 g2 B t s')
| fst_congr : Red t t' -> Red (.fst t) (.fst t')
| snd_congr : Red t t' -> Red (.snd t) (.snd t')
| inter_ty_congr1 : Red A A' -> Red (.inter_ty A B) (.inter_ty A' B)
| inter_ty_congr2 : Red B B' -> Red (.inter_ty A B) (.inter_ty A B')
| refl_congr : Red t t' -> Red (.refl t) (.refl t')
| eq_congr1 : Red A A' -> Red (.eq A B) (.eq A' B)
| eq_congr2 : Red B B' -> Red (.eq A B) (.eq A B')
| subst_congr1 : Red t1 t1' -> Red (.subst t1 t2 t3) (.subst t1' t2 t3)
| subst_congr2 : Red t2 t2' -> Red (.subst t1 t2 t3) (.subst t1 t2' t3)
| subst_congr3 : Red t3 t3' -> Red (.subst t1 t2 t3) (.subst t1 t2 t3')
| phi_congr1 : Red t1 t1' -> Red (.phi t1 t2 t3) (.phi t1' t2 t3)
| phi_congr2 : Red t2 t2' -> Red (.phi t1 t2 t3) (.phi t1 t2' t3)
| phi_congr3 : Red t3 t3' -> Red (.phi t1 t2 t3) (.phi t1 t2 t3')
| conv_congr1 : Red t1 t1' -> Red (.conv g1 g2 t1 t2) (.conv g1 g2 t1' t2)
| conv_congr2 : Red t2 t2' -> Red (.conv g1 g2 t1 t2) (.conv g1 g2 t1 t2')

inductive ParRed : Term -> Term -> Prop where
-- Steps
| beta : ParRed b b' -> ParRed t t' ->
  ParRed ((`λ(m)[A] b) `@(m2) t) (b' β[t'])
| fst : ParRed t t' ->
  ParRed ((Term.inter g1 g2 B t s).!1) t'
| snd : ParRed s s' ->
  ParRed ((Term.inter g1 g2 B t s).!2) s'
| subst : ParRed t t' ->
  ParRed (.subst Pr (.refl v) t) t'
| phi : ParRed b b' ->
  ParRed (.phi a b (.refl t)) b
-- Conv steps
| conv_beta : ParRed B B' -> ParRed A2 A2' -> ParRed b b' -> ParRed t t' ->
  ParRed
  ((.conv g1 g2 (`∀(m1)[A1] B) (`λ(m2)[A2] b)) `@(m3) t)
  (.conv g1 g2 (B' β[t']) (b' β[.conv g1 g2 A2' t']))
| conv_fst : ParRed A A' -> ParRed t t' ->
  ParRed
  ((.conv g1 g2 ([A]∩ B1) (.inter g3 g4 B2 t s)).!1)
  (.conv g1 g2 A' t')
| conv_snd : ParRed A A' -> ParRed B1 B1'-> ParRed t t' -> ParRed s s' ->
  ParRed
  ((.conv g1 g2 ([A]∩ B1) (.inter g3 g4 B2 t s)).!2)
  (.conv g1 g2 (B1' β[.conv g1 g2 A' t']) s')
| conv_subst :
  ParRed Pr Pr' -> ParRed a a' -> ParRed b b' ->
  ParRed u u' -> ParRed t t' ->
  ParRed
  ((.subst Pr (.conv g1 g2 (.eq a b) (.refl u)) t))
  (.conv g1 g2 (Pr' `@τ b' `@τ (.conv g1 g2 (.eq a' b') (.refl u'))) t')
| conv_phi : ParRed b b' ->
  ParRed
  (.phi a b (.conv g1 g2 (.eq x y) (.refl t)))
  b'
| conv_conv : ParRed A A' -> ParRed t t' ->
  ParRed
  (.conv g1 g2 A (.conv g3 g4 B t))
  (.conv (g1 + g3) (g2 + g4) A' t')
-- Congruences
| lam_congr : ParRed A A' -> ParRed t t' ->
  ParRed (.lam m A t) (.lam m A' t')
| app_congr : ParRed f f' -> ParRed t t' ->
  ParRed (.app m f t) (.app m f' t')
| all_congr : ParRed A A' -> ParRed B B' ->
  ParRed (.all m A B) (.all m A' B')
| inter_congr : ParRed B B' -> ParRed t t' -> ParRed s s' ->
  ParRed (.inter g1 g2 B t s) (.inter g1 g2 B' t' s')
| fst_congr : ParRed t t' -> ParRed (.fst t) (.fst t')
| snd_congr : ParRed t t' -> ParRed (.snd t) (.snd t')
| inter_ty_congr : ParRed A A' -> ParRed B B' ->
  ParRed (.inter_ty A B) (.inter_ty A' B')
| refl_congr : ParRed t t' -> ParRed (.refl t) (.refl t')
| eq_congr : ParRed A A' -> ParRed B B' ->
  ParRed (.eq A B) (.eq A' B')
| subst_congr : ParRed t1 t1' -> ParRed t2 t2' -> ParRed t3 t3' ->
  ParRed (.subst t1 t2 t3) (.subst t1' t2' t3')
| phi_congr : ParRed t1 t1' -> ParRed t2 t2' -> ParRed t3 t3' ->
  ParRed (.phi t1 t2 t3) (.phi t1' t2' t3')
| conv_congr : ParRed t1 t1' -> ParRed t2 t2' ->
  ParRed (.conv g1 g2 t1 t2) (.conv g1 g2 t1' t2')
| var : ParRed (.var K x) (.var K x)
| const : ParRed (.const k) (.const k)

namespace Term
  @[simp]
  def compl : Term -> Term
  | app _ (lam _ _ b) t => (compl b) β[compl t]
  | app _ (conv g1 g2 (all _ _ B) (lam _ A2 b)) t =>
    let B' := compl B
    let t' := compl t
    let b' := compl b
    let A2' := compl A2
    conv g1 g2 (B' β[t']) (b' β[conv g1 g2 A2' t'])
  | fst (inter _ _ _ t _) => compl t
  | fst (conv g1 g2 (inter_ty A _) (inter _ _ _ t _)) =>
    conv g1 g2 (compl A) (compl t)
  | snd (inter _ _ _ _ s) => compl s
  | snd (conv g1 g2 (inter_ty A B) (inter _ _ _ t s)) =>
    let B' := compl B
    let A' := compl A
    let t' := compl t
    let s' := compl s
    conv g1 g2 (B' β[conv g1 g2 A' t']) s'
  | subst _ (refl _) t => compl t
  | subst Pr (conv g1 g2 (eq a b) (refl u)) t =>
    let Pr' := compl Pr
    let a' := compl a
    let b' := compl b
    let u' := compl u
    let t' := compl t
    conv g1 g2 (Pr' `@τ b' `@τ (conv g1 g2 (eq a' b') (refl u'))) t'
  | phi _ b (refl _) => compl b
  | phi _ b (conv _ _ (eq _ _) (refl _)) => compl b
  | conv g1 g2 A (conv g3 g4 _ t) =>
    conv (g1 + g3) (g2 + g4) (compl A) (compl t)
  | lam m A t => lam m (compl A) (compl t)
  | app m f a => app m (compl f) (compl a)
  | all m A B => all m (compl A) (compl B)
  | inter g1 g2 B t s =>
    inter g1 g2 (compl B) (compl t) (compl s)
  | inter_ty A B => inter_ty (compl A) (compl B)
  | fst t => fst (compl t)
  | snd t => snd (compl t)
  | refl t => refl (compl t)
  | eq a b => eq (compl a) (compl b)
  | subst t1 t2 t3 =>
    subst (compl t1) (compl t2) (compl t3)
  | phi t1 t2 t3 =>
    phi (compl t1) (compl t2) (compl t3)
  | conv g1 g2 t1 t2 =>
    conv g1 g2 (compl t1) (compl t2)
  | var K n => var K n
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
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  -- case _ b b' t t' A _ _ ih1 ih2 =>
  --   have lem : (`λ[[σ]A] ([^σ]b) `@ ([σ]t)) =β> ([^σ]b') β[[σ]t'] := by
  --     apply ParRed.beta (ih1 ^σ) (ih2 _)
  --   simp at lem; apply lem
  -- case _ ih1 ih2 => apply ParRed.fst; apply ih1; apply ih2
  -- case _ ih1 ih2 => apply ParRed.snd; apply ih1; apply ih2

  theorem red_subst (σ τ : Subst Term) :
    (∀ n t, σ n = .su t -> ∃ t', τ n = .su t' ∧ t =β> t') ->
    (∀ n k, σ n = .re k -> τ n = .re k) ->
    s =β> t -> [σ]s =β> [τ]t
  := by
  intro h1 h2 r
  induction r generalizing σ τ <;> simp
  any_goals (solve | constructor)
  any_goals (solve | try case _ ih => constructor; apply ih _ _ h1 h2)
  any_goals (solve | try case _ ih1 ih2 => constructor; apply ih1 _ _ h1 h2; apply ih2 _ _ h1 h2)
  any_goals (solve | try case _ ih1 ih2 ih3 =>
    constructor; apply ih1 _ _ h1 h2; apply ih2 _ _ h1 h2; apply ih3 _ _ h1 h2)
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
  -- case _ b b' t t' A  _ _ ih1 ih2 =>
  --   have lem : (`λ[[σ]A]([^σ]b) `@ ([σ]t)) =β> ([^τ]b') β[[τ]t'] := by
  --     apply ParRed.beta
  --     replace ih1 := ih1 (^σ) (^τ) (Subst.lift_replace red_subst_same h1) (Subst.lift_rename h2)
  --     apply ih1; apply ih2 _ _ h1 h2
  --   simp at lem; apply lem
  -- case _ A A' t t' _ _ ih1 ih2 =>
  --   have lem : `λ[[σ]A][^σ]t =β> `λ[[τ]A'][^τ]t' := by
  --     constructor
  --     apply ih1 _ _ h1 h2
  --     apply ih2 (^σ) (^τ) (Subst.lift_replace red_subst_same h1) (Subst.lift_rename h2)
  --   simp at lem; apply lem
  -- case _ A A' B B' _ _ ih1 ih2 =>
  --   have lem : Π[[σ]A][^σ]B =β> Π[[τ]A'][^τ]B' := by
  --     constructor; apply ih1 _ _ h1 h2
  --     apply ih2 (^σ) (^τ) (Subst.lift_replace red_subst_same h1) (Subst.lift_rename h2)
  --   simp at lem; apply lem
  -- case _ ih1 ih2 ih3 =>
  --   constructor; apply ih1 _ _ h1 h2
  --   apply ih2 _ _ h1 h2; apply ih3 _ _ h1 h2
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
  -- case _ ih1 ih2 => apply red_beta ih1 ih2
  -- case _ ih _ => apply ih
  -- case _ ih => apply ih
  -- case _ ih => apply ih
  -- case _ f f' a a' r1 _ ih1 ih2 =>
  --   cases f <;> simp at * <;> try (constructor <;> simp [*])
  --   case _ t =>
  --     cases f'
  --     any_goals (try cases r1)
  --     case _ b =>
  --       cases ih1; case _ ih1 =>
  --         apply ParRed.beta ih1 ih2
  -- case _ t t' r ih =>
  --   cases t <;> simp at * <;> try (constructor <;> simp [*])
  --   case _ s1 s2 =>
  --     cases t'
  --     any_goals (try cases r)
  --     case _ r1 r2 =>
  --       cases ih; case _ ih1 ih2 =>
  --         apply ParRed.fst; apply ih1; apply ih2
  -- case _ t t' r ih =>
  --   cases t <;> simp at * <;> try (constructor <;> simp [*])
  --   case _ s1 s2 =>
  --     cases t'
  --     any_goals (try cases r)
  --     case _ r1 r2 =>
  --       cases ih; case _ ih1 ih2 =>
  --         apply ParRed.snd; apply ih1; apply ih2
  -- case _ t1 t1' t2 t2' t3 t3' _r1 r2 _r3 ih1 ih2 ih3 =>
  --   cases t2 <;> simp at * <;> try (constructor <;> simp [*])
  --   case _ =>
  --     cases t2'
  --     any_goals (try cases r2)
  --     case _ =>
  --       apply ParRed.unit_rec; apply ih3

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


  theorem red_subst (σ τ : Subst Term) :
    (∀ n t, σ n = .su t -> ∃ t', τ n = .su t' ∧ t -β> t') ->
    (∀ n k, σ n = .re k -> τ n = .re k) ->
    s -β> t -> [σ]s -β> [τ]t
  := by sorry

  theorem red_const_forces_const : .const K -β>* t -> t = .const K := by sorry

  namespace Conv
    theorem subst_same : t =β= s -> ([σ]t) =β= ([σ]s) := by sorry

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

    theorem all_congr : `∀(m)[A] B =β= `∀(m')[A'] B' -> m = m' ∧ A =β= A' ∧ B =β= B' := by sorry

    theorem times_congr : ([A]∩ B) =β= ([A']∩ B') -> A =β= A' ∧ B =β= B' := by sorry

  end Conv
end Red

end Cedille2
