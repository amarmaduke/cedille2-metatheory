import Common

namespace Erased
  inductive Term : Type where
  | var : Const -> Nat -> Term
  | const : Const -> Term
  | appt : Term -> Term -> Term
  | app : Term -> Term -> Term
  | lamt : Term -> Term -> Term
  | lam : Term -> Term
  | all : Mode -> Term -> Term -> Term
  | inter_ty : Term -> Term -> Term
  | eq : Term -> Term -> Term
  deriving Repr

  infixl:15 "`@" => Term.app
  infixl:15 "`@τ" => Term.appt
  notation "`λ" t:50 => Term.lam t
  notation "`λ[" A "]" t:50 => Term.lamt A t

  notation "`∀(" m ")[" A "]" B:50 => Term.all m A B
  notation "∀f[" A "]" B:50 => Term.all mf A B
  notation "∀τ[" A "]" B:50 => Term.all mt A B
  notation "∀0[" A "]" B:50 => Term.all m0 A B

  notation "[" A "]∩" B:50 => Term.inter_ty A B

  namespace Term
    @[simp]
    def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
    | var K x =>
      match f x with
      | .re y => var K y
      | .su t => t
    | const K => const K
    | appt t1 t2 => appt (smap lf f t1) (smap lf f t2)
    | app t1 t2 => app (smap lf f t1) (smap lf f t2)
    | lamt t1 t2 => lamt (smap lf f t1) (smap lf (lf f) t2)
    | lam t => lam (smap lf (lf f) t)
    | all m t1 t2 => all m (smap lf f t1) (smap lf (lf f) t2)
    | inter_ty t1 t2 => inter_ty (smap lf f t1) (smap lf (lf f) t2)
    | eq t1 t2 => eq (smap lf f t1) (smap lf f t2)

    -- @[simp]
    -- def beq : Term -> Term -> Bool
    -- | #x, #y => x == y
    -- | f1 `@ a1, f2 `@ a2 => beq f1 f2 && beq a1 a2
    -- | `λt1, `λt2 => beq t1 t2
    -- | _, _ => false
  end Term

  @[simp]
  instance substType_Term : SubstitutionType Term where
    smap := Term.smap

  -- @[simp]
  -- instance instBEq_Term : BEq Term where
  --   beq := Term.beq

  -- instance instlawfulBEq_Term : LawfulBEq Term where
  --   rfl := by intro x; induction x <;> simp at * <;> simp [*]
  --   eq_of_beq := by
  --     intro a b h; simp at h
  --     induction a, b using Term.beq.induct <;> simp at *
  --     case _ => simp [*]
  --     case _ ih1 ih2 => apply And.intro; apply ih1 h.1; apply ih2 h.2
  --     case _ ih => apply ih h

  namespace Term

    @[simp↓]
    theorem subst_var :
      [σ](var K x) = match σ x with | .re y => var K y | .su t => t
    := by
    unfold Subst.apply; simp

    @[simp] -- 0[s.σ ] = s
    theorem subst_var_replace
      : [.su s :: σ]var K 0 = s
    := by simp

    @[simp] -- 0[s.σ ] = s
    theorem subst_var_rename
      : [.re k :: σ]var K 0 = var K k
    := by simp

    @[simp]
    theorem subst_const : [σ](const K) = const K := by
    unfold Subst.apply; simp

    @[simp]
    theorem subst_app : [σ](app t1 t2) = app ([σ]t1) ([σ]t2) := by
    unfold Subst.apply; simp

    @[simp]
    theorem subst_appt : [σ](appt t1 t2) = appt ([σ]t1) ([σ]t2) := by
    unfold Subst.apply; simp

    @[simp]
    theorem subst_lam : [σ](lam t) = lam ([^σ]t) := by
    unfold Subst.apply; simp

    @[simp]
    theorem subst_lamt : [σ](lamt A t) = lamt ([σ]A) ([^σ]t) := by
    unfold Subst.apply; simp

    @[simp]
    theorem subst_all : [σ](all m A B) = all m ([σ]A) ([^σ]B) := by
    unfold Subst.apply; simp

    @[simp]
    theorem subst_inter_ty : [σ](inter_ty A B) = inter_ty ([σ]A) ([^σ]B) := by
    unfold Subst.apply; simp

    @[simp]
    theorem subst_eq : [σ](eq A B) = eq ([σ]A) ([σ]B) := by
    unfold Subst.apply; simp

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
      case _ x => rw [<-h]; unfold Ren.to; simp
      all_goals (simp [*])
      all_goals (
        rw [Subst.lift_lemma, <-h]
        unfold Ren.fro; simp
      )

    theorem apply_compose {s : Term} {σ τ : Subst Term} : [τ][σ]s = [τ ⊙ σ]s := by
    solve_compose Term, apply_stable, s, σ, τ

  end Term

  instance substTypeLaws_Term : SubstitutionTypeLaws Term where
    apply_id := Term.apply_id
    apply_compose := Term.apply_compose
    apply_stable := Term.apply_stable

end Erased
