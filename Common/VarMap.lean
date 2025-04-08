

abbrev VarMap T := Nat -> T

namespace VarMap
  def nil (x : T) : VarMap T := λ _ => x

  @[simp]
  def cons (x : T) (i : VarMap T) : VarMap T
  | 0 => x
  | n + 1 => i n

  @[simp]
  def shift (n : Nat) (i : VarMap T) : VarMap T := λ k => i (n + k)

  def lams (n : Nat) (f : VarMap T -> VarMap T) (i : VarMap T) : VarMap T :=
    λ k => if Nat.ble n k then f (shift n i) (k - n) else i k

  theorem cons_ext : x = i' 0 -> i = shift 1 i' -> cons x i = i' := by
  intro h1 h2; subst h1; subst h2
  funext; case _ x =>
    cases x <;> simp
    case _ n =>
      have lem : 1 + n = n + 1 := by omega
      rw [lem]

  @[simp]
  theorem shift0 : shift 0 i = i := by funext; case _ x => simp

  theorem shift_split : shift (n + 1) i = shift n (shift 1 i) := by
  funext; case _ x =>
    cases x <;> simp
    case _ => rw [Nat.add_comm]
    case _ k =>
      have lem : n + 1 + (k + 1) = 1 + (n + (k + 1)) := by omega
      rw [lem]

  @[simp]
  theorem shift_cons : shift 1 (cons x i) = i := by
  funext; case _ x =>
    cases x <;> simp
    case _ => rw [Nat.add_comm]

  theorem lams_bv : k < m -> lams m f i k = i k := by
  intro h1; unfold lams; simp; intro h2
  omega

  theorem lams_shift : shift m (lams m f i) = f (shift m i) := by
  unfold lams; simp; funext; case _ x =>
    cases x <;> simp
    case _ k =>
      have lem : m + (k + 1) - m = k + 1 := by omega
      rw [lem]

  theorem lams0 : lams 0 f i = f (λ k => i k) := by
  unfold lams; simp;

  theorem shift_lams : shift 1 (lams (k + 1) f i) = lams k f (shift 1 i) := by
  unfold lams; simp; funext; case _ x =>
    cases x <;> simp
    case _ =>
      split
      case _ h => subst h; simp
      case _ h => rfl
    case _ n =>
      cases Nat.decLe k (n + 1)
      case _ h =>
        have h2 : ¬ (k + 1 ≤ 1 + (n + 1)) := by omega
        simp [*]
      case _ h =>
        have h2 : k + 1 ≤ 1 + (n + 1) := by omega
        simp [*]; rw [<-shift_split]
        have lem : 1 + (n + 1) - (k + 1) = (n + 1 - k) := by omega
        rw [lem]

  theorem cons_lams : cons x (lams k f i) = lams (k + 1) f (cons x i) := by
  unfold lams; unfold cons; funext; case _ x =>
    cases x <;> simp
    case _ n =>
      split
      case _ h =>
        unfold shift; simp; congr
        funext; case _ x' =>
          cases x' <;> simp
          case _ n' =>
            have lem : k + (n' + 1) = k + 1 + n' := by omega
            rw [lem]
      case _ => rfl

end VarMap
