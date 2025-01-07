import Common.Term
import Common.Term.Substitution

inductive Red : Term -> Term -> Prop where
-- Basic reduction Steps
| beta : Red (.app m1 (.lam m2 A b) t) (b β[t])
| proj1 : Red (.fst (.pair n B t s)) t
| proj2 : Red (.snd (.pair n B t s)) s
| substelim : Red (.subst Pr (.refl t)) (.lam mf (Pr `@τ t `@τ .refl t) (.bound .type 0))
| phi : Red (.phi a b (.refl t)) b
-- Weak conversion passthrough reduction steps
-- .app m (.conv n (.all m A1 B1) (.all m A2 B2) b) t -β>
--   .conv n (B1 β[t]) (B2 β[.conv n A2 t]) (.app m b (.conv n A2 t))

-- .fst (.conv n (.prod A1 B1) (.prod A2 B2) t) -β>
--   .conv n A1 A2 (.fst t)

-- .snd (.conv n (.prod A1 B1) (.prod A2 B2) t) -β>
--   .conv n (B1 β[.conv n A1 (.fst t)]) (B2 β[.fst t]) (.snd t)

-- .subst Pr (.conv n (.eq A1 a1 b1) (.eq A2 a2 b2) t) -β>
--   .conv n (Pr a1 (.refl a1) -> Pr b1 (.conv n (.eq A1 a1 b1) (.eq A2 a2 b2) t))
--           (Pr a2 (.refl a2) -> Pr b2 t)
--     (.subst Pr t)

-- .phi B a' b' (.conv n (.eq A1 a1 b1) (.eq A2 a2 b2) t) -β>
--   .conv n (.prod A1 B) (.prod A2 B) (.phi a' b' t)
| conv_beta : Red (.app m (.conv n (.all m A1 B) (.lam m A2 b)) t) (.conv n (B β[t]) (b β[.conv n A2 t]))
| conv_fst : Red (.fst (.conv n (.prod A B1) (.pair n2 B2 t s))) (.conv n A t)
| conv_snd : Red (.snd (.conv n (.prod A B1) (.pair n2 B2 t s))) (.conv n (B1 β[.conv n A t]) s)
| conv_subst :
  Red (.subst Pr (.conv n (.eq A a b) (.refl t)))
    (.conv n (.all mf (Pr `@τ a `@τ .refl a) (Pr `@τ b `@τ (.conv n (.eq A a b) (.refl t))))
      (.lam mf (Pr `@τ t `@τ .refl t) (.bound .type 0)))
| conv_phi : Red (.phi a b (.conv n (.eq A x y) (.refl t))) b
| conv_conv : Red (.conv n1 A (.conv n2 B t)) (.conv (n1 + n2) A t)
-- Congruences
| lam_congr1 : Red A A' -> Red (.lam m A t) (.lam m A' t)
| lam_congr2 : Red t t' -> Red (.lam m A t) (.lam m A t')
| app_congr1 : Red f f' -> Red (.app m f t) (.app m f' t)
| app_congr2 : Red t t' -> Red (.app m f t) (.app m f t')
| all_congr1 : Red A A' -> Red (.all m A B) (.all m A' B)
| all_congr2 : Red B B' -> Red (.all m A B) (.all m A B')
| pair_congr1 : Red B B' -> Red (.pair n B t s) (.pair n B' t s)
| pair_congr2 : Red t t' -> Red (.pair n B t s) (.pair n B t' s)
| pair_congr3 : Red s s' -> Red (.pair n B t s) (.pair n B t s')
| fst_congr : Red t t' -> Red (.fst t) (.fst t')
| snd_congr : Red t t' -> Red (.snd t) (.snd t')
| prod_congr1 : Red A A' -> Red (.prod A B) (.prod A' B)
| prod_congr2 : Red B B' -> Red (.prod A B) (.prod A B')
| refl_congr : Red t t' -> Red (.refl t) (.refl t')
| subst_congr1 : Red B B' -> Red (.subst B e) (.subst B' e)
| subst_congr2 : Red e e' -> Red (.subst B e) (.subst B e')
| phi_congr1 : Red a a' -> Red (.phi a b e) (.phi a' b e)
| phi_congr2 : Red b b' -> Red (.phi a b e) (.phi a b' e)
| phi_congr3 : Red e e' -> Red (.phi a b e) (.phi a b e')
| eq_congr1 : Red A A' -> Red (.eq A a b) (.eq A' a b)
| eq_congr2 : Red a a' -> Red (.eq A a b) (.eq A a' b)
| eq_congr3 : Red b b' -> Red (.eq A a b) (.eq A a b')
| conv_congr1 : Red A A' -> Red (.conv n A t) (.conv n A' t)
| conv_congr2 : Red t t' -> Red (.conv n A t) (.conv n A t')

inductive RedStar : Term -> Term -> Prop where
| refl : RedStar t t
| step : Red x y -> RedStar y z -> RedStar x z

inductive RedBounded : Nat -> Term -> Term -> Prop where
| refl : RedBounded n t t
| step : Red x y -> RedBounded n y z -> RedBounded (n + 1) x z

abbrev RedConv (A : Term) (B : Term) : Prop := ∃ C, RedStar A C ∧ RedStar B C

abbrev RedConvBounded (n : Nat) (A : Term) (B : Term) : Prop := ∃ C, RedBounded n A C ∧ RedBounded n B C

inductive ParRed : Term -> Term -> Prop where
-- | bound : ParRed (.bound K n) (.bound K n)
-- | none : ParRed .none .none
-- | const : ParRed (.const K) (.const K)
-- | beta : ParRed A A' -> ParRed b b' -> ParRed t t' -> ParRed (.app m (.lam m A b) t) (b' β[t'])
-- | proj1 : ParRed B B' -> ParRed t t' -> ParRed s s' -> ParRed (.fst (.pair B t s)) t'
-- | proj2 : ParRed B B' -> ParRed t t' -> ParRed s s' -> ParRed (.snd (.pair B t s)) s'
-- | substelim : ParRed B B' -> ParRed t t' -> ParRed (.subst B (.refl t)) (.lam mf (.app mt B' t') (.bound .type 0))
-- | conv_lam : ParRed B B' -> ParRed A2 A2' -> ParRed t t' ->
--   ParRed (.conv (.all m A1 B) (.lam m A2 t) n) (.lam m A2' (.conv B' t' n))
-- | conv_pair : ParRed T T' -> ParRed t t' -> ParRed s s' ->
--   ParRed (.conv T (.pair T t s) n) (.pair T' t' s')
-- | conv_refl : ParRed A A' -> ParRed t t' ->
--   ParRed (.conv (.eq A t t) (.refl t) n) (.refl (conv A' t' n))
-- | conv_all : ParRed A A' -> ParRed B B' ->
--   ParRed (.conv (.const K) (.all m A B) n) (.all m A' B')
-- | conv_prod : ParRed A A' -> ParRed B B' ->
--   ParRed (.conv ★ (.prod A B) n) (.prod A' B')
-- | conv_eq : ParRed A A' -> ParRed a a' -> ParRed b b' ->
--   ParRed (.conv ★ (.eq A a b) n) (.eq A' a' b')
-- | lam_congr : ParRed A A' -> ParRed t t' -> ParRed (.lam m A t) (.lam m A' t')
-- | app_congr : ParRed f f' -> ParRed a a' -> ParRed (.app m f a) (.app m f' a')
-- | all_congr : ParRed A A' -> ParRed B B' -> ParRed (.all m A B) (.all m A' B')
-- | pair_congr : ParRed B B' -> ParRed t t' -> ParRed s s' -> ParRed (.pair B t s) (.pair B' t' s')
-- | fst_congr : ParRed t t' -> ParRed (.fst t) (.fst t')
-- | snd_congr : ParRed t t' -> ParRed (.snd t) (.snd t')
-- | prod_congr : ParRed A A' -> ParRed B B' -> ParRed (.prod A B) (.prod A' B')
-- | refl_congr : ParRed t t' -> ParRed (.refl t) (.refl t')
-- | subst_congr : ParRed B B' -> ParRed e e' -> ParRed (.subst B e) (.subst B' e')
-- | phi_congr : ParRed a a' -> ParRed b b' -> ParRed e e' -> ParRed (.phi a b e) (.phi a' b' e')
-- | eq_congr : ParRed A A' -> ParRed a a' -> ParRed b b' -> ParRed (.eq A a b) (.eq A' a' b')
-- | conv_congr : ParRed A A' -> ParRed t t' -> ParRed (.conv A t c) (.conv A' t' c)

-- @[simp]
-- def pcompl : Term -> Term
-- | .app mf (.lam mf _ b) t
-- | .app m0 (.lam m0 _ b) t
-- | .app mt (.lam mt _ b) t => (pcompl b) β[pcompl t]
-- | .fst (.pair _ t _) => pcompl t
-- | .snd (.pair _ _ s) => pcompl s
-- | .subst B (.refl t) => .lam mf (.app mt (pcompl B) (pcompl t)) (.bound .type 0)
-- | .conv (.all m1 A1 B) (.lam m2 A2 t) n => .lam m2 (pcompl A2) (.conv (pcompl B) (pcompl t) n)
-- | .conv T1 (.pair T2 t s) n =>
--   if T1 == T2 then .pair (pcompl T1) (pcompl t) (pcompl s)
--   else .conv (pcompl T1) (pcompl (.pair T2 t s)) n
-- | .conv (.eq A t1 t2) (.refl t3) n =>
--   if t1 == t2 && t2 == t3 then .refl (conv (pcompl A) (pcompl t1) n)
--   else .conv (pcompl (.eq A t1 t2)) (pcompl (.refl t3)) n
-- | .conv (.const _) (.all m A B) _ => .all m (pcompl A) (pcompl B)
-- | .conv ★ (.prod A B) _ => .prod (pcompl A) (pcompl B)
-- | .conv ★ (.eq A a b) _ => .eq (pcompl A) (pcompl a) (pcompl b)
-- | .lam m A t => .lam m (pcompl A) (pcompl t)
-- | .app m f a => .app m (pcompl f) (pcompl a)
-- | .all m A B => .all m (pcompl A) (pcompl B)
-- | .pair B t s => .pair (pcompl B) (pcompl t) (pcompl s)
-- | .fst t => .fst (pcompl t)
-- | .snd t => .snd (pcompl t)
-- | .prod A B => .prod (pcompl A) (pcompl B)
-- | .refl t => .refl (pcompl t)
-- | .subst B e => .subst (pcompl B) (pcompl e)
-- | .phi a b e => .phi (pcompl a) (pcompl b) (pcompl e)
-- | .eq A a b => .eq (pcompl A) (pcompl a) (pcompl b)
-- | .conv A t c => .conv (pcompl A) (pcompl t) c
-- | .bound K n => .bound K n
-- | .const K => .const K
-- | .none => .none

inductive ParRedStar : Term -> Term -> Prop where
-- | refl : ParRedStar t t
-- | step : ParRed x y -> ParRedStar y z -> ParRedStar x z

abbrev ParRedConv (A : Term) (B : Term) : Prop := ∃ C, ParRedStar A C ∧ ParRedStar B C


infix:40 " -β> " => Red
infix:39 " -β>* " => RedStar
notation:39 t:39 " -β>{" n "} " s:39 => RedBounded n t s
infix:38 " =β= " => RedConv
notation:38 t:38 " =β{" n "}= " s:38 => RedConvBounded n t s
infix:40 " =β> " => ParRed
infix:39 " =β>* " => ParRedStar
infix:38 " ≡β≡ " => ParRedConv
