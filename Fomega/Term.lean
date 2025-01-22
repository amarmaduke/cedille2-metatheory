import Common.Substitution

inductive Const : Type where
| kind | type
deriving Repr

namespace Const
  @[simp]
  def beq : Const -> Const -> Bool
  | .kind, .kind => true
  | .type, .type => true
  | _, _ => false
end Const

@[simp]
instance instBEq_Const : BEq Const where
  beq := Const.beq

instance instLawfulBEq_Const : LawfulBEq Const where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> simp at * <;> simp [*]
  rfl := by intro a; cases a <;> simp

inductive Term : Type where
| var : Nat -> Term
| const : Const -> Term
| app : Term -> Term -> Term
| lam : Term -> Term -> Term
| all : Term -> Term -> Term
| pair : Term -> Term -> Term
| fst : Term -> Term
| snd : Term -> Term
| times : Term -> Term -> Term
| unit : Term
| unit_ty : Term
| unit_rec : Term -> Term -> Term -> Term
deriving Repr

notation "★" => Term.const Const.type
notation "□" => Term.const Const.kind
infixl:15 " `@ " => Term.app
notation "`λ[" A "]" t:50 => Term.lam A t
notation "Π[" A "]" t:50 => Term.all A t
infixl:15 "⊗" => Term.times
notation "(u)" => Term.unit
notation "(U)" => Term.unit_ty
prefix:max "#" => Term.var

instance instInhabited_Term : Inhabited Term where
  default := ★

namespace Term
  @[simp]
  def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
  | var x =>
    match f x with
    | .re y => var y
    | .su t => t
  | const k => const k
  | app t1 t2 => app (smap lf f t1) (smap lf f t2)
  | lam A t => lam (smap lf f A) (smap lf (lf f) t)
  | all t1 t2 => all (smap lf f t1) (smap lf (lf f) t2)
  | pair t1 t2 => pair (smap lf f t1) (smap lf f t2)
  | fst t => fst (smap lf f t)
  | snd t => snd (smap lf f t)
  | times t1 t2 => times (smap lf f t1) (smap lf f t2)
  | unit => unit
  | unit_ty => unit_ty
  | unit_rec t1 t2 t3 => unit_rec (smap lf f t1) (smap lf f t2) (smap lf f t3)

  def beq : Term -> Term -> Bool
  | .var x, .var y => x == y
  | .const k1, .const k2 => k1 == k2
  | .app x1 x2, .app y1 y2 => sorry
  | _, _ => false
end Term

@[simp↓]
instance substType_Term : SubstitutionType Term where
  smap := Term.smap

namespace Term
  @[simp↓]
  theorem subst_var : [σ]#x = match σ x with | .re y => #y | .su t => t := by
  unfold Subst.apply; simp

  @[simp] -- 0[s.σ ] = s
  theorem subst_var_replace : [.su s :: σ]var 0 = s := by simp

  @[simp] -- 0[s.σ ] = s
  theorem subst_var_rename : [.re k :: σ]var 0 = var k := by simp

  @[simp]
  theorem subst_const  : [σ]const k = const k := by unfold Subst.apply; simp

  @[simp]
  theorem subst_app : [σ](app t1 t2) = app ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_lam : [σ](lam A t) = lam ([σ]A) ([^σ]t) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_all : [σ]all t1 t2 = all ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_pair : [σ]pair t1 t2 = pair ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_fst : [σ]fst t = fst ([σ]t) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_snd : [σ]snd t = snd ([σ]t) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_times : [σ]times t1 t2 = times ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_unit : [σ]unit = unit := by unfold Subst.apply; simp

  @[simp]
  theorem subst_unit_ty : [σ]unit_ty = unit_ty := by unfold Subst.apply; simp

  @[simp]
  theorem subst_unit_rec :
    [σ]unit_rec t1 t2 t3 = unit_rec ([σ]t1) ([σ]t2) ([σ]t3)
  := by unfold Subst.apply; simp

  theorem apply_id {t : Term} : [I]t = t := by
  have lem : ^I = @I Term := by
    funext; case _ x =>
    cases x; all_goals (unfold Subst.lift; unfold I; simp)
  induction t
  all_goals (simp at * <;> try simp [*])

  theorem apply_stable {r : Ren} {σ : Subst Term}
    : r.to = σ -> Ren.apply r = Subst.apply σ
  := by
  intro h; funext; case _ x =>
    unfold Ren.apply; simp at *
    unfold Ren.to; simp
    induction x generalizing r σ <;> simp at *
    any_goals simp [*]
    case _ x => rw [<-h]; unfold Ren.to; simp
    any_goals
      rw [Subst.lift_lemma, <-h]
      unfold Ren.fro; simp

  theorem apply_compose {s : Term} {σ τ : Subst Term} : [τ][σ]s = [τ ⊙ σ]s := by
  solve_compose Term, apply_stable, s, σ, τ

end Term

instance substTypeLaws_Term : SubstitutionTypeLaws Term where
  apply_id := Term.apply_id
  apply_compose := Term.apply_compose
  apply_stable := Term.apply_stable
