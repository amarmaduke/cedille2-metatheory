import Common
import Erased.Term

namespace Erased
  inductive Red : Term -> Term -> Prop where
  | beta : Red ((`λ b) `@ t) (b β[t])
  | app_congr1 : Red a a' -> Red (f `@ a) (f `@ a')
  | app_congr2 : Red f f' -> Red (f `@ a) (f' `@ a)
  | appt_congr1 : Red a a' -> Red (f `@τ a) (f `@τ a')
  | appt_congr2 : Red f f' -> Red (f `@τ a) (f' `@τ a)
  | all_congr1 : Red A A' -> Red (`∀(m)[A] B) (`∀(m)[A'] B)
  | all_congr2 : Red B B' -> Red (`∀(m)[A] B) (`∀(m)[A] B')
  | lamt_congr1 : Red A A' -> Red (`λ[A]t) (`λ[A']t)
  | lamt_congr2 : Red t t' -> Red (`λ[A]t) (`λ[A]t')
  | lam_congr : Red t t' -> Red (`λ t) (`λ t')
  | inter_ty_congr1 : Red A A' -> Red ([A]∩ B) ([A']∩ B)
  | inter_ty_congr2 : Red B B' -> Red ([A]∩ B) ([A]∩ B')
  | eq_congr1 : Red A A' -> Red (.eq A B) (.eq A' B)
  | eq_congr2 : Red B B' -> Red (.eq A B) (.eq A B')

  inductive ParRed : Term -> Term -> Prop where
  | beta : ParRed b b' -> ParRed t t' -> ParRed ((`λ b) `@ t) (b' β[t'])
  | app : ParRed a a' -> ParRed f f' -> ParRed (f `@ a) (f' `@ a')
  | appt : ParRed a a' -> ParRed f f' -> ParRed (f `@τ a) (f' `@τ a')
  | lam : ParRed t t' -> ParRed (`λ t) (`λ t')
  | all : ParRed A A' -> ParRed B B' -> ParRed (`∀(m)[A] B) (`∀(m)[A'] B')
  | lamt : ParRed A A' -> ParRed t t' -> ParRed (`λ[A]t) (`λ[A']t')
  | inter_ty : ParRed A A' -> ParRed B B' -> ParRed ([A]∩ B) ([A']∩ B')
  | eq_congr : ParRed A A' -> ParRed B B' -> ParRed (.eq A B) (.eq A' B')
  | var : ParRed (.var K x) (.var K x)
  | const : ParRed (.const K) (.const K)

  infix:40 " -β> " => Red
  infix:40 " =β> " => ParRed
  notation:39 x:39 " -β[" n:39 "]>* " y:39 => @StarB _ Red n x y
  notation:39 x:39 " =β[" n:39 "]>* " y:39 => @StarB _ ParRed n x y
  notation:38 x:38 " =β[" g1:38 ";" g2:38 "]= " y:38 => @ConvB _ Red g1 g2 x y
  notation:38 x:38 " ≡β[" g1:38 ";" g2:38 "]≡ " y:38 => @ConvB _ ParRed g1 g2 x y

  namespace ParRed
    @[simp]
    def compl : Term -> Term
    | `λt `@  a => (compl t) β[compl a]
    | f `@ a => (compl f) `@ (compl a)
    | f `@τ a => (compl f) `@τ (compl a)
    | `λ[A]t => `λ[compl A]compl t
    | `λt => `λ(compl t)
    | `∀(m)[A]B => `∀(m)[compl A]compl B
    | [A]∩ B => [compl A]∩ compl B
    | .eq A B => .eq (compl A) (compl B)
    | .var K x => .var K x
    | .const k => .const k

    theorem red_refl : t =β> t := by
    induction t <;> constructor <;> simp [*]

    theorem red_subst_same σ : s =β> t -> [σ]s =β> [σ]t := by
    intro h; induction h generalizing σ <;> simp
    case _ b b' t t' _ _ ih1 ih2 =>
      have lem : (`λ([^σ]b) `@ ([σ]t)) =β> ([^σ]b') β[[σ]t'] := by
        apply ParRed.beta (ih1 ^σ) (ih2 _)
      simp at lem; apply lem
    any_goals try (
      case _ ih1 ih2 =>
        constructor; apply ih1; apply ih2
    )
    case _ ih => constructor; apply ih
    all_goals apply red_refl

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
    all_goals try (
      case _ ih1 ih2 =>
        constructor; apply ih1 _ _ h1 h2; apply ih2 _ _ h1 h2
    )
    case _ _ ih =>
      constructor
      replace ih := ih (^σ) (^τ) (Subst.lift_replace red_subst_same h1) (Subst.lift_rename h2)
      simp at ih; apply ih
    all_goals try (
      case _ _ ih1 ih2 =>
        constructor; apply ih1 _ _ h1 h2
        replace ih2 := ih2 (^σ) (^τ) (Subst.lift_replace red_subst_same h1) (Subst.lift_rename h2)
        simp at ih2; apply ih2
    )
    case _ x =>
      generalize udef : σ x = u
      cases u <;> simp at *
      case _ y => rw [h2 x y udef]; simp; constructor
      case _ t =>
        cases (h1 x t udef); case _ v lem =>
          rw [lem.1]; simp; apply lem.2
    case _ => apply red_refl

    theorem starb_subst (σ : Subst Term) : s =β[g]>* t -> [σ]s =β[g]>* [σ]t := by
    intro r
    induction r
    case _ n t' => apply StarB.refl
    case _ j1 j2 ih =>
      constructor; apply ih
      apply red_subst σ σ _ _ j2
      case _ =>
        intro n t h; exists t
        apply And.intro h ParRed.red_refl
      case _ =>
        intro n k h; apply h

    theorem red_beta : b =β> b' -> t =β> t' -> b β[t] =β> b' β[t'] := by
    intro r1 r2; apply red_subst
    case _ =>
      intro n s h; cases n <;> simp at *
      case _ => subst h; apply r2
    case _ =>
      intro n k h; cases n <;> simp at *; simp [*]
    case _ => apply r1

    theorem triangle : t =β> s -> s =β> compl t := by
    intro h; induction h <;> simp at * <;> try (constructor <;> simp [*])
    case _ b b' t t' r1 r2 ih1 ih2 => apply red_beta ih1 ih2
    case _ a a' f f' _ r2 ih1 ih2 =>
      cases f <;> simp at * <;> try (constructor <;> simp [*])
      case _ t =>
        cases f'; all_goals (try cases r2)
        case _ b =>
          cases ih2; case _ ih2 =>
            apply ParRed.beta ih2 ih1

    theorem strip : s =β> t1 -> s =β[n]>* t2 -> ∃ t, t1 =β[n]>* t ∧ t2 =β> t := by
    intro h1 h2
    induction h2 generalizing t1
    case _ t' => exists t1; apply And.intro; apply StarB.refl; apply h1
    case _ n' x y z _r1 r2 ih =>
      replace ih := ih h1
      cases ih
      case _ w ih =>
        replace r2 := triangle r2
        have lem := triangle ih.2
        replace lem := StarB.step ih.1 lem
        exists (compl y)

    theorem confluence : s =β[g1]>* t1 -> s =β[g2]>* t2 -> t1 ≡β[g2;g1]≡ t2 := by
    intro h1 h2
    induction h1 generalizing t2
    case _ z =>
      exists t2; apply And.intro
      apply h2; apply StarB.refl
    case _ g3 s y t1 _r1 r2 ih =>
      replace ih := ih h2
      cases ih; case _ w ih =>
        have lem := strip r2 ih.1
        cases lem; case _ q lem =>
          exists q; apply And.intro
          apply lem.1; apply StarB.step ih.2 lem.2

    theorem refl : t ≡β[g1;g2]≡ t := by
    exists t; apply And.intro; apply StarB.refl; apply StarB.refl

    theorem sym : x ≡β[g1;g2]≡ y -> y ≡β[g2;g1]≡ x := by
    intro h; cases h; case _ w h =>
      exists w; apply And.intro; apply h.2; apply h.1

    theorem trans : x ≡β[gx;gy1]≡ y -> y ≡β[gy2;gz]≡ z -> x ≡β[gx + gy2;gz + gy1]≡ z := by
    intro h1 h2
    cases h1; case _ w1 h1 =>
    cases h2; case _ w2 h2 =>
      have lem := confluence h1.2 h2.1
      cases lem; case _ q lem =>
        exists q; apply And.intro
        apply StarB.trans h1.1 lem.1
        apply StarB.trans h2.2 lem.2

    theorem compl_sound : t =β> (compl t) := by apply triangle; apply red_refl

    -- theorem conv_sound : ConvB.convb compl g1 g2 a b -> a ≡β[g1;g2]≡ b := by
    -- intro h; apply ConvB.conv_sound _ h; apply compl_sound
  end ParRed

  namespace Red
    theorem to_par_red : x -β> y -> x =β> y := by
    intro h; induction h
    all_goals (try case _ ih => constructor; apply ih; apply ParRed.red_refl)
    all_goals (try case _ ih => constructor; apply ParRed.red_refl; apply ih)
    case _ => constructor; apply ParRed.red_refl; apply ParRed.red_refl
    case _ ih => constructor; apply ih

    theorem par_sound : x =β[g1;g2]= y -> x ≡β[g1;g2]≡ y := by
    apply ConvB.promote to_par_red
  end Red

  theorem convb_subst (σ : Subst Term) : s ≡β[g1;g2]≡ t -> [σ]s ≡β[g1;g2]≡ [σ]t := by
  intro j
  cases j; case _ w r =>
    have lem1 := ParRed.starb_subst σ r.1
    have lem2 := ParRed.starb_subst σ r.2
    apply Exists.intro ([σ]w)
    apply And.intro lem1 lem2

end Erased
