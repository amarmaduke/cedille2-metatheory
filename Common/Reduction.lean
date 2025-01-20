import Common.Substitution

class ReductionCompletion (T : Type) (R : T -> T -> Prop) where
  compl : T -> T

class ReductionTriangle (T : Type) (R : T -> T -> Prop) [ReductionCompletion T R] where
  triangle : R t s -> R s (ReductionCompletion.compl R t)

variable {T : Type} {R : T -> T -> Prop}

inductive Star : T -> T -> Prop where
| refl : Star t t
| step : Star x y -> R y z -> Star x z

inductive StarB : Nat -> T -> T -> Prop where
| refl : StarB n t t
| step : StarB n x y -> R y z -> StarB (n + 1) x z

def ConvB (g1 g2 : Nat) (x y : T) : Prop :=
  ∃ z, @StarB T R g1 x z ∧ @StarB T R g2 y z

def Conv (x y : T) : Prop :=
  ∃ z, @Star T R x z ∧ @Star T R y z

namespace Star
  theorem trans : @Star T R x y -> @Star T R y z -> @Star T R x z := by
  intro r1 r2; induction r2 generalizing x
  case _ => apply r1
  case _ a b _ r2 ih => apply Star.step (ih r1) r2

  theorem promote (Rprm : ∀ {x y}, R1 x y -> R2 x y) :
    @Star T R1 x y -> @Star T R2 x y
  := by
  intro r; induction r
  case _ => constructor
  case _ _ r ih => constructor; apply ih; apply Rprm r
end Star

namespace StarB
  @[simp]
  def star (f : T -> T) : Nat -> T -> T
  | 0, t => t
  | n + 1, t => star f n (f t)

  theorem weaken k : @StarB T R g x y -> @StarB T R (g + k) x y := by
  intro r; induction r generalizing k
  case _ => constructor
  case _ n _ _ _ _ r2 ih =>
    have lem : n + 1 + k = n + k + 1 := by omega
    rw [lem]; apply StarB.step (ih k) r2

  theorem trans : @StarB T R g1 x y -> @StarB T R g2 y z -> @StarB T R (g1 + g2) x z := by
  intro r1 r2; induction r2 generalizing g1 x
  case _ n t => apply weaken n r1
  case _ n a b c _ r2 ih => apply StarB.step (ih r1) r2

  theorem promote (Rprm : ∀ {x y}, R1 x y -> R2 x y) :
    @StarB T R1 n x y -> @StarB T R2 n x y
  := by
  intro r; induction r
  case _ => constructor
  case _ _ r ih => constructor; apply ih; apply Rprm r

  theorem star_sound n t : (∀ t, R t (f t)) -> @StarB T R n t (star f n t) := by
  intro h
  have lem : ∀ {t n}, R (star f n t) (star f n (f t)) := by
    intro t n; induction n generalizing t; simp; apply h _
    case _ n ih => simp; apply ih
  induction n
  case _ => simp; constructor
  case _ n ih =>
    constructor; apply ih; simp; apply lem
end StarB

namespace ConvB
  @[simp]
  def convb [BEq T] (f : T -> T) (g1 g2 : Nat) (a b : T) : Bool :=
    StarB.star f g1 a == StarB.star f g2 b

  theorem weaken k1 k2 : @ConvB T R g1 g2 x y -> @ConvB T R (g1 + k1) (g2 + k2) x y := by
  intro h; cases h; case _ w h =>
    exists w; apply And.intro
    apply StarB.weaken k1 h.1; apply StarB.weaken k2 h.2

  theorem promote (Rprm : ∀ {x y}, R1 x y -> R2 x y) :
    @ConvB T R1 g1 g2 x y -> @ConvB T R2 g1 g2 x y
  := by
  intro h; cases h; case _ w h =>
    exists w; apply And.intro
    apply StarB.promote Rprm h.1; apply StarB.promote Rprm h.2

  theorem conv_sound [BEq T] [LawfulBEq T] : (∀ t, R t (f t)) -> convb f g1 g2 a b -> @ConvB T R g1 g2 a b := by
  intro h1 h2; simp at h2
  have lem1 := StarB.star_sound g1 a h1
  have lem2 := StarB.star_sound g2 b h1
  exists (StarB.star f g1 a); apply And.intro
  apply lem1; rw [h2]; apply lem2
end ConvB

namespace Star
  variable [ReductionCompletion T R] [ReductionTriangle T R]

  theorem strip : R s t1 -> @Star T R s t2 -> ∃ t, @Star T R t1 t ∧ R t2 t := by
  intro h1 h2
  induction h2 generalizing t1
  case _ t' => exists t1; apply And.intro; apply Star.refl; apply h1
  case _ n' x y z _r1 r2 ih =>
    replace ih := ih h1
    cases ih
    case _ w ih =>
      replace r2 := ReductionTriangle.triangle r2
      have lem := ReductionTriangle.triangle ih.2
      replace lem := Star.step ih.1 lem
      exists (ReductionCompletion.compl R y)

  theorem confluence : @Star T R s t1 -> @Star T R s t2 -> @Conv T R t1 t2 := by
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
end Star

namespace StarB
  variable [ReductionCompletion T R] [ReductionTriangle T R]

  theorem strip : R s t1 -> @StarB T R n s t2 -> ∃ t, @StarB T R n t1 t ∧ R t2 t := by
  intro h1 h2
  induction h2 generalizing t1
  case _ t' => exists t1; apply And.intro; apply StarB.refl; apply h1
  case _ n' x y z _r1 r2 ih =>
    replace ih := ih h1
    cases ih
    case _ w ih =>
      replace r2 := ReductionTriangle.triangle r2
      have lem := ReductionTriangle.triangle ih.2
      replace lem := StarB.step ih.1 lem
      exists (ReductionCompletion.compl R y)

  theorem confluence : @StarB T R g1 s t1 -> @StarB T R g2 s t2 -> @ConvB T R g2 g1 t1 t2 := by
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
end StarB

namespace Conv
  theorem refl : @Conv T R t t := by
  exists t; apply And.intro; apply Star.refl; apply Star.refl

  theorem sym : @Conv T R x y -> @Conv T R y x := by
  intro h; cases h; case _ w h =>
    exists w; apply And.intro; apply h.2; apply h.1

  theorem trans [ReductionCompletion T R] [ReductionTriangle T R] :
    @Conv T R x y -> @Conv T R y z -> @Conv T R  x z
  := by
  intro h1 h2
  cases h1; case _ w1 h1 =>
  cases h2; case _ w2 h2 =>
    have lem := Star.confluence h1.2 h2.1
    cases lem; case _ q lem =>
      exists q; apply And.intro
      apply Star.trans h1.1 lem.1
      apply Star.trans h2.2 lem.2
end Conv

namespace ConvB
  theorem refl : @ConvB T R g1 g2 t t := by
  exists t; apply And.intro; apply StarB.refl; apply StarB.refl

  theorem sym : @ConvB T R g1 g2 x y -> @ConvB T R g2 g1 y x := by
  intro h; cases h; case _ w h =>
    exists w; apply And.intro; apply h.2; apply h.1

  theorem trans [ReductionCompletion T R] [ReductionTriangle T R] :
    @ConvB T R gx gy1 x y -> @ConvB T R gy2 gz y z -> @ConvB T R (gx + gy2) (gz + gy1) x z
  := by
  intro h1 h2
  cases h1; case _ w1 h1 =>
  cases h2; case _ w2 h2 =>
    have lem := StarB.confluence h1.2 h2.1
    cases lem; case _ q lem =>
      exists q; apply And.intro
      apply StarB.trans h1.1 lem.1
      apply StarB.trans h2.2 lem.2
end ConvB
