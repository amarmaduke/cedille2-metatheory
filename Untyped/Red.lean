import Untyped.Subst
import Untyped.Term

@[simp]
def conv : Nat -> Nat -> Term -> Term -> Bool
| _, _, #x, #y => x == y
| g1 + 1, g2, (`λ t) `@ a1, f2 `@ a2 => conv g1 g2 (t β[a1]) (f2 `@ a2)
| g1, g2 + 1, f1 `@ a1, (`λ t) `@ a2 => conv g1 g2 (f1 `@ a1) (t β[a2])
| g1, g2, f1 `@ a1, f2 `@ a2 => conv g1 g2 f1 f2 && conv g1 g2 a1 a2
| g1, g2, `λ t1, `λ t2 => conv g1 g2 t1 t2
| _, _, _, _ => false

inductive Red : Term -> Term -> Prop where
| beta : Red ((`λ b) `@ t) (b β[t])
| app_congr1 : Red a a' -> Red (f `@ a) (f `@ a')
| app_congr2 : Red f f' -> Red (f `@ a) (f' `@ a)
| lam_congr : Red t t' -> Red (`λ t) (`λ t')

inductive RedStar : Nat -> Term -> Term -> Prop where
| refl : RedStar 0 t t
| step : Red x y -> RedStar n y z -> RedStar (n + 1) x z

inductive RedConv : Nat -> Nat -> Term -> Term -> Prop where
| var : RedConv g1 g2 #x #x
| beta_le : RedConv g1 g2 (t β[a1]) (f2 `@ a2) -> RedConv (g1 + 1) g2 ((`λ t) `@ a1) (f2 `@ a2)
| beta_ri : RedConv g1 g2 (f1 `@ a1) (t β[a2])  -> RedConv g1 (g2 + 1) (f1 `@ a1) ((`λ t) `@ a2)
| app : RedConv g1 g2 f1 f2 -> RedConv g1 g2 a1 a2 -> RedConv g1 g2 (f1 `@ a1) (f2 `@ a2)
| lam : RedConv g1 g2 t1 t2 -> RedConv g1 g2 (`λ t1) (`λ t2)

infix:40 " -β> " => Red
notation:39 x:39 " -β[" n:39 "]>* " y:39 => RedStar n x y
notation:38 x:38 " =β[" g1:38 ";" g2:38 "]= " y:38 => RedConv g1 g2 x y

namespace RedConv

  theorem weaken : RedConv g1 g2 x y -> RedConv (g1 + k1) (g2 + k2) x y := by sorry

  theorem conv_sound : conv g1 g2 x y -> x =β[g1;g2]= y := by
  intro h; induction g1, g2, x, y using conv.induct <;> simp at *
  case _ => subst h; constructor
  case _ ih => apply beta_le; apply ih h
  case _ ih _ => apply beta_ri; apply ih h
  case _ ih1 ih2 _ _ => apply app (ih1 h.1) (ih2 h.2)
  case _ ih => apply lam (ih h)

  theorem sym : x =β[g1;g2]= y -> y =β[g2;g1]= x := by sorry

  theorem trans : x =β[gx;gy1]= y -> y =β[gy2;gz]= z -> x =β[gx + gy2;yz + gy1]= z := by sorry


end RedConv
