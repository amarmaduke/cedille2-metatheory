import Untyped.Subst
import Untyped.Term

inductive Red : Term -> Term -> Prop where
| beta : Red ((`λ b) `@ t) (b β[t])
| app_congr1 : Red a a' -> Red (f `@ a) (f `@ a')
| app_congr2 : Red f f' -> Red (f `@ a) (f' `@ a)
| lam_congr : Red t t' -> Red (`λ t) (`λ t')

inductive SpineRed : Term -> Term -> Prop where
| beta : SpineRed ((`λ b) `@ t) (b β[t])
| app : SpineRed f f' -> SpineRed a a' -> SpineRed (f `@ a) (f' `@ a')
| lam : SpineRed t t' -> SpineRed (`λ t) (`λ t')

inductive ParRed : Term -> Term -> Prop where
| beta : ParRed b b' -> ParRed t t' -> ParRed ((`λ b) `@ t) (b' β[t'])
| app : ParRed a a' -> ParRed f f' -> ParRed (f `@ a) (f' `@ a')
| lam : ParRed t t' -> ParRed (`λ t) (`λ t')
| var : ParRed #x #x

inductive Star (R : Term -> Term -> Prop) : Nat -> Term -> Term -> Prop where
| refl : Star R n t t
| step : Star R n x y -> R y z -> Star R (n + 1) x z

def Conv (R : Term -> Term -> Prop) (g1 g2 : Nat) (x y : Term) : Prop :=
  ∃ z, Star R g1 x z ∧ Star R g2 y z

infix:40 " -β> " => Red
infix:40 " =β> " => ParRed
infix:40 " -s> " => SpineRed
notation:39 x:39 " -β[" n:39 "]>* " y:39 => Star Red n x y
notation:39 x:39 " =β[" n:39 "]>* " y:39 => Star ParRed n x y
notation:39 x:39 " -s[" n:39 "]>* " y:39 => Star SpineRed n x y
notation:38 x:38 " =β[" g1:38 ";" g2:38 "]= " y:38 => Conv Red g1 g2 x y
notation:38 x:38 " ≡β[" g1:38 ";" g2:38 "]≡ " y:38 => Conv ParRed g1 g2 x y
notation:38 x:38 " =s[" g1:38 ";" g2:38 "]= " y:38 => Conv SpineRed g1 g2 x y

namespace Star
  @[simp]
  def star (f : Term -> Term) : Nat -> Term -> Term
  | 0, t => t
  | n + 1, t => star f n (f t)

  theorem weaken k : Star R g x y -> Star R (g + k) x y := by
  intro r; induction r generalizing k
  case _ => constructor
  case _ n _ _ _ _ r2 ih =>
    have lem : n + 1 + k = n + k + 1 := by omega
    rw [lem]; apply Star.step (ih k) r2

  theorem trans : Star R g1 x y -> Star R g2 y z -> Star R (g1 + g2) x z := by
  intro r1 r2; induction r2 generalizing g1 x
  case _ n t => apply weaken n r1
  case _ n a b c _ r2 ih => apply Star.step (ih r1) r2

  theorem promote (Rprm : ∀ {x y}, R1 x y -> R2 x y) :
    Star R1 n x y -> Star R2 n x y
  := by
  intro r; induction r
  case _ => constructor
  case _ _ r ih => constructor; apply ih; apply Rprm r

  theorem star_sound n t : (∀ t, R t (f t)) -> Star R n t (star f n t) := by
  intro h
  have lem : ∀ {t n}, R (star f n t) (star f n (f t)) := by
    intro t n; induction n generalizing t; simp; apply h _
    case _ n ih => simp; apply ih
  induction n
  case _ => simp; constructor
  case _ n ih =>
    constructor; apply ih; simp; apply lem
end Star

namespace Conv
  @[simp]
  def conv (f : Term -> Term) (g1 g2 : Nat) (a b : Term) : Bool :=
    Star.star f g1 a == Star.star f g2 b

  theorem weaken k1 k2 : Conv R g1 g2 x y -> Conv R (g1 + k1) (g2 + k2) x y := by
  intro h; cases h; case _ w h =>
    exists w; apply And.intro
    apply Star.weaken k1 h.1; apply Star.weaken k2 h.2

  theorem promote (Rprm : ∀ {x y}, R1 x y -> R2 x y) :
    Conv R1 g1 g2 x y -> Conv R2 g1 g2 x y
  := by
  intro h; cases h; case _ w h =>
    exists w; apply And.intro
    apply Star.promote Rprm h.1; apply Star.promote Rprm h.2

  theorem conv_sound : (∀ t, R t (f t)) -> conv f g1 g2 a b -> Conv R g1 g2 a b := by
  intro h1 h2; simp at h2
  replace h2 := @LawfulBEq.eq_of_beq Term _ _ _ _ h2
  have lem1 := Star.star_sound g1 a h1
  have lem2 := Star.star_sound g2 b h1
  exists (Star.star f g1 a); apply And.intro
  apply lem1; rw [h2]; apply lem2

end Conv

namespace ParRed
  @[simp]
  def pcompl : Term -> Term
  | `λt `@  a => (pcompl t) β[pcompl a]
  | f `@ a => (pcompl f) `@ (pcompl a)
  | `λt => `λ(pcompl t)
  | #x => #x

  @[simp]
  def gcompl : Term -> Nat × Term
  | `λt `@  a =>
    let (n1, t') := gcompl t
    let (n2, a') := gcompl a
    (n1 + n2 + 1, t' β[a'])
  | f `@ a =>
    let (n1, f') := gcompl f
    let (n2, a') := gcompl a
    (n1 + n2, f' `@ a')
  | `λt =>
    let (n, t') := gcompl t
    (n, `λt')
  | #x => (0, #x)

  theorem gcompl_pcompl : gcompl t = (n, t') -> pcompl t = t' := by
  intro h; induction t using gcompl.induct generalizing n t'
  case _ e1 _ _ e2 ih1 ih2 =>
    simp at *; replace ih1 := ih1 e1
    replace ih2 := ih2 e2
    rw [e1, e2] at h; simp at h
    rw [ih1, ih2]; apply h.2
  case _ f _ fh _ _ e1 _ _ e2 ih1 ih2 =>
    cases f
    case lam => exfalso; apply fh _ rfl
    all_goals (
      replace ih1 := ih1 e1
      replace ih2 := ih2 e2
      simp; simp at h
      rw [e2] at h; try rw [e1] at h
      simp at h
      rw [ih2]; try rw [ih1]
      apply h.2
    )
  case _ e ih =>
    simp at *; replace ih := ih e
    rw [e] at h; simp at h
    rw [ih]; apply h.2
  case _ => simp at *; apply h.2

  theorem red_refl : t =β> t := by
  induction t <;> constructor <;> simp [*]

  theorem red_subst_same σ : s =β> t -> [σ]s =β> [σ]t := by
  intro h; induction h generalizing σ <;> simp
  case _ b b' t t' _ _ ih1 ih2 =>
    have lem : (`λ([^σ]b) `@ ([σ]t)) =β> ([^σ]b') β[[σ]t'] := by
      apply ParRed.beta (ih1 ^σ) (ih2 _)
    simp at lem; apply lem
  case _ ih1 ih2 =>
    constructor; apply ih1; apply ih2
  case _ _ ih =>
    replace ih := ih ^(σ); simp at ih
    constructor; apply ih
  case _ => apply red_refl

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
  case _ ih1 ih2 =>
    apply ParRed.app; apply ih1 _ _ h1 h2; apply ih2 _ _ h1 h2
  case _ _ ih =>
    constructor
    replace ih := ih (^σ) (^τ) (Subst.lift_replace red_subst_same h1) (Subst.lift_rename h2)
    simp at ih; apply ih
  case _ x =>
    generalize udef : σ x = u
    cases u <;> simp at *
    case _ y => rw [h2 x y udef]; simp; constructor
    case _ t =>
      cases (h1 x t udef); case _ v lem =>
        rw [lem.1]; simp; apply lem.2

  theorem red_beta : b =β> b' -> t =β> t' -> b β[t] =β> b' β[t'] := by
  intro r1 r2; apply red_subst
  case _ =>
    intro n s h; cases n <;> simp at *
    case _ => subst h; apply r2
  case _ =>
    intro n k h; cases n <;> simp at *; simp [*]
  case _ => apply r1

  theorem triangle : t =β> s -> s =β> pcompl t := by
  intro h; induction h <;> simp at * <;> try (constructor <;> simp [*])
  case _ b b' t t' r1 r2 ih1 ih2 => apply red_beta ih1 ih2
  case _ a a' f f' _ r2 ih1 ih2 =>
    cases f <;> simp at * <;> try (constructor <;> simp [*])
    case _ t =>
      cases f'
      case _ => cases ih2
      case _ => cases r2
      case _ b =>
        cases ih2; case _ ih2 =>
          apply ParRed.beta ih2 ih1

  theorem strip : s =β> t1 -> s =β[n]>* t2 -> ∃ t, t1 =β[n]>* t ∧ t2 =β> t := by
  intro h1 h2
  induction h2 generalizing t1
  case _ t' => exists t1; apply And.intro; apply Star.refl; apply h1
  case _ n' x y z _r1 r2 ih =>
    replace ih := ih h1
    cases ih
    case _ w ih =>
      replace r2 := triangle r2
      have lem := triangle ih.2
      replace lem := Star.step ih.1 lem
      exists (pcompl y)

  theorem confluence : s =β[g1]>* t1 -> s =β[g2]>* t2 -> t1 ≡β[g2;g1]≡ t2 := by
  intro h1 h2
  induction h1 generalizing t2
  case _ z =>
    exists t2; apply And.intro
    apply h2; apply Star.refl
  case _ g3 s y t1 _r1 r2 ih =>
    replace ih := ih h2
    cases ih; case _ w ih =>
      have lem := strip r2 ih.1
      cases lem; case _ q lem =>
        exists q; apply And.intro
        apply lem.1; apply Star.step ih.2 lem.2

  theorem refl : t ≡β[g1;g2]≡ t := by
  exists t; apply And.intro; apply Star.refl; apply Star.refl

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
      apply Star.trans h1.1 lem.1
      apply Star.trans h2.2 lem.2

  theorem pcompl_sound : t =β> (pcompl t) := by apply triangle; apply red_refl

  theorem conv_sound : Conv.conv pcompl g1 g2 a b -> a ≡β[g1;g2]≡ b := by
  intro h; apply Conv.conv_sound _ h; apply pcompl_sound

end ParRed

namespace Red

  theorem to_par_red : x -β> y -> x =β> y := by
  intro h; induction h
  case _ => constructor; apply ParRed.red_refl; apply ParRed.red_refl
  case _ ih => constructor; apply ih; apply ParRed.red_refl
  case _ ih => constructor; apply ParRed.red_refl; apply ih
  case _ ih => constructor; apply ih

  theorem par_sound : x =β[g1;g2]= y -> x ≡β[g1;g2]≡ y := by
  apply Conv.promote to_par_red

  -- theorem from_gcompl : ParRed.gcompl t = (n, t') -> x -β[n]>* y := by sorry

end Red

namespace SpineRed

  theorem to_par_red : x -s> y -> x =β> y := by
  intro h; induction h
  case _ => constructor; apply ParRed.red_refl; apply ParRed.red_refl
  case _ ih1 ih2 => constructor; apply ih2; apply ih1
  case _ ih => constructor; apply ih

  theorem par_sound : x =s[g1;g2]= y -> x ≡β[g1;g2]≡ y := by
  apply Conv.promote to_par_red

end SpineRed
