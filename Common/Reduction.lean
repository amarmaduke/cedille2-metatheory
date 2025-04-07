import Common.Substitution

class ReductionCompletion (T : Type) (R : T -> T -> Prop) where
  compl : T -> T

class ReductionTriangle (T : Type) (R : T -> T -> Prop) [ReductionCompletion T R] where
  triangle : R t s -> R s (ReductionCompletion.compl R t)

variable {T : Type} {R : T -> T -> Prop}

inductive Star (R : T -> T -> Prop) : T -> T -> Prop where
| refl : Star R t t
| step : Star R x y -> R y z -> Star R x z

inductive Plus (R : T -> T -> Prop) : T -> T -> Prop where
| start : R t t' -> Plus R t t'
| step : Plus R x y -> R y z -> Plus R x z

inductive StarB (R : T -> T -> Prop) : Nat -> T -> T -> Prop where
| refl : StarB R n t t
| step : StarB R n x y -> R y z -> StarB R (n + 1) x z

def ConvB (R : T -> T -> Prop) (g1 g2 : Nat) (x y : T) : Prop :=
  ∃ z, StarB R g1 x z ∧ StarB R g2 y z

def Conv (R : T -> T -> Prop) (x y : T) : Prop :=
  ∃ z, Star R x z ∧ Star R y z

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

namespace Plus
  theorem destruct : @Plus T R x z -> ∃ y, R x y ∧ @Star T R y z := by
  intro r; induction r
  case _ b r =>
    exists b; apply And.intro r Star.refl
  case _ r1 r2 ih =>
    cases ih; case _ u ih =>
      exists u; apply And.intro ih.1
      apply Star.step ih.2 r2

  theorem stepr : R x y -> @Plus T R y z -> @Plus T R x z := by
  intro r1 r2
  induction r2 generalizing x
  case _ r2 => apply Plus.step (Plus.start r1) r2
  case _ r3 r4 ih => apply Plus.step (ih r1) r4

  theorem stepr_from_star : R x y -> @Star T R y z -> @Plus T R x z := by
  intro r1 r2
  induction r2 generalizing x
  case _ => apply Plus.start; apply r1
  case _ r3 r4 ih => apply Plus.step (ih r1) r4
end Plus

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
  theorem congr3_1 t2 t3 (f : T -> T -> T -> T) :
    (∀ {t1 t2 t3 t1'}, R t1 t1' -> R (f t1 t2 t3) (f t1' t2 t3)) ->
    @Star T R t1 t1' ->
    @Star T R (f t1 t2 t3) (f t1' t2 t3)
  := by
  intro fh h2
  induction h2
  case _ => apply refl
  case _ _h3 h4 ih =>
    have h5 := @fh _ t2 t3 _ h4
    apply trans ih (Star.step Star.refl h5)

  -- theorem congr3_2 t1 t3 (f : Term -> Term -> Term -> Term) :
  --   (∀ {t1 t2 t3 t2'}, t2 -β> t2' -> f t1 t2 t3 -β> f t1 t2' t3) ->
  --   t2 -β>* t2' ->
  --   f t1 t2 t3 -β>* f t1 t2' t3
  -- := by
  -- intro fh h2
  -- induction h2
  -- case _ => apply refl
  -- case _ h3 _h4 ih =>
  --   have h5 := @fh t1 _ t3 _ h3
  --   apply trans (RedStar.step h5 refl) ih

  -- theorem congr3_3 t1 t2 (f : Term -> Term -> Term -> Term) :
  --   (∀ {t1 t2 t3 t3'}, t3 -β> t3' -> f t1 t2 t3 -β> f t1 t2 t3') ->
  --   t3 -β>* t3' ->
  --   f t1 t2 t3 -β>* f t1 t2 t3'
  -- := by
  -- intro fh h2
  -- induction h2
  -- case _ => apply refl
  -- case _ h3 _h4 ih =>
  --   have h5 := @fh t1 t2 _ _ h3
  --   apply trans (RedStar.step h5 refl) ih

  -- theorem congr3 (f : Term -> Term -> Term -> Term) :
  --   (∀ {t1 t2 t3 t1'}, t1 -β> t1' -> f t1 t2 t3 -β> f t1' t2 t3) ->
  --   (∀ {t1 t2 t3 t2'}, t2 -β> t2' -> f t1 t2 t3 -β> f t1 t2' t3) ->
  --   (∀ {t1 t2 t3 t3'}, t3 -β> t3' -> f t1 t2 t3 -β> f t1 t2 t3') ->
  --   t1 -β>* t1' -> t2 -β>* t2' -> t3 -β>* t3' ->
  --   f t1 t2 t3 -β>* f t1' t2' t3'
  -- := by
  -- intro f1 f2 f3 h1 h2 h3
  -- have r1 := congr3_1 t2 t3 f f1 h1
  -- have r2 := congr3_2 t1' t3 f f2 h2
  -- have r3 := congr3_3 t1' t2' f f3 h3
  -- apply trans r1; apply trans r2; apply trans r3; apply refl

  -- theorem congr2_1 t2 (f : Term -> Term -> Term) :
  --   (∀ {t1 t2 t1'}, t1 -β> t1' -> f t1 t2 -β> f t1' t2) ->
  --   t1 -β>* t1' ->
  --   f t1 t2 -β>* f t1' t2
  -- := by
  -- intro fh h
  -- apply congr3_1 t2 .none (λ t1 t2 _t3 => f t1 t2)
  -- intro t1 t2 _t3 t1' h; apply fh h
  -- exact h

  -- theorem congr2_2 t1 (f : Term -> Term -> Term) :
  --   (∀ {t1 t2 t2'}, t2 -β> t2' -> f t1 t2 -β> f t1 t2') ->
  --   t2 -β>* t2' ->
  --   f t1 t2 -β>* f t1 t2'
  -- := by
  -- intro fh h
  -- apply congr3_2 t1 .none (λ t1 t2 _t3 => f t1 t2)
  -- intro t1 t2 _t3 t1' h; apply fh h
  -- exact h

  -- theorem congr2 (f : Term -> Term -> Term) :
  --   (∀ {t1 t2 t1'}, t1 -β> t1' -> f t1 t2 -β> f t1' t2) ->
  --   (∀ {t1 t2 t2'}, t2 -β> t2' -> f t1 t2 -β> f t1 t2') ->
  --   t1 -β>* t1' -> t2 -β>* t2' ->
  --   f t1 t2 -β>* f t1' t2'
  -- := by
  -- intro f1 f2 h1 h2
  -- have r1 := congr2_1 t2 f f1 h1
  -- have r2 := congr2_2 t1' f f2 h2
  -- apply trans r1; apply trans r2; apply refl

  -- theorem congr1 (f : Term -> Term) :
  --   (∀ {t1 t1'}, t1 -β> t1' -> f t1 -β> f t1') ->
  --   t1 -β>* t1' ->
  --   f t1 -β>* f t1'
  -- := by
  -- intro fh h
  -- apply congr2_1 .none (λ t1 _t2 => f t1)
  -- intro t1 _t2 t1' h; apply fh h
  -- exact h

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

def Reducible (t : T) := ∃ t', R t t'
def Normal (t : T) := ¬ (@Reducible T R t)
abbrev NormalForm (t : T) (t' : T) := @Star T R t t' ∧ @Normal T R t'
def WN (t : T) := ∃ t', @NormalForm T R t t'

inductive SN (R : T -> T -> Prop) : T -> Prop where
| sn : (∀ y, R x y -> SN R y) -> SN R x

inductive SNPlus (R : T -> T -> Prop) : T -> Prop where
| sn : (∀ y, Plus R x y -> SNPlus R y) -> SNPlus R x

theorem snplus_impies_sn : SNPlus R t -> SN R t := by
intro h; induction h; case _ t' _ ih =>
  constructor; intro t'' r
  apply ih t'' (Plus.start r)

theorem sn_preimage (f : T -> T) x :
  (∀ x y, R x y -> R (f x) (f y)) ->
  SN R (f x) ->
  SN R x
:= by
intro h sh
generalize zdef : f x = z at sh
induction sh generalizing f x
case _ x' h' ih =>
  subst zdef; constructor
  intro y r
  apply ih (f y) (h _ _ r) f y h rfl

theorem sn_preservation_step : SN R t -> R t t' -> SN R t' := by
intro h red
induction h
case _ z h1 _h2 =>
  apply h1 _ red

theorem sn_preservation : SN R t -> @Star T R t t' -> SN R t' := by
intro h red
induction red
case _ => simp [*]
case _ _ r2 ih => apply sn_preservation_step ih r2

theorem sn_star : (∀ y, @Star T R t y -> SN R y) -> SN R t := by
intro h
constructor
intro y r
apply h y (Star.step Star.refl r)

theorem snplus_preservation_step : SNPlus R t -> R t t' -> SNPlus R t' := by
intro h r; induction h; case _ z h _ =>
  apply h _ (Plus.start r)

theorem snplus_preservation : SNPlus R t -> @Star T R t t' -> SNPlus R t' := by
intro h r; induction r
case _ => apply h
case _ _ r2 ih =>
  apply snplus_preservation_step ih r2

theorem sn_implies_snplus : SN R t -> SNPlus R t := by
intro h; induction h; case _ t' _ ih =>
  constructor; intro t'' r
  have lem := Plus.destruct r
  cases lem; case _ z lem =>
    have lem2 := ih z lem.1
    apply snplus_preservation lem2 lem.2

-- theorem sn_expansion_step : SN R t' -> R t t' -> SN R t := by
-- intro h red
-- induction h generalizing t
-- case _ z h ih =>
--   have lem := reducible_decidable z
--   sorry

-- theorem sn_subst : SN ([σ]t) -> SN t := by
-- apply sn_preimage (Subst.apply σ)
-- intro x y r; apply Red.subst1_same σ r

-- theorem sn_implies_wn : SN t -> WN t := by
-- intro h
-- induction h
-- case sn t' _ ih =>
--   have lem : Reducible t' ∨ Normal t' := reducible_decidable t'
--   cases lem
--   case _ h' =>
--     cases h'
--     case _ t'' h' =>
--       have lem := ih _ h'
--       cases lem
--       case _ z lem =>
--         exists z; apply And.intro
--         apply RedStar.step; apply h'; apply lem.1
--         apply lem.2
--   case _ h' =>
--     exists t'; apply And.intro; apply Red.refl
--     apply h'
