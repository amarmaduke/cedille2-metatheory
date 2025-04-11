import Common

namespace Realizer
  inductive Term : Type where
  | var : Nat -> Term
  | app : Term -> Term -> Term
  | lam : Term -> Term
  deriving Repr

  infixl:15 "`@" => Term.app
  notation "`λ" t:50 => Term.lam t

  namespace Term
    def neutral t :=
      match t with
      | lam _ => false
      | _ => true

    def occurs (n : Nat) : Term -> Bool
    | var i => i == n
    | app f a => or (occurs n f) (occurs n a)
    | lam t => occurs (n + 1) t

    def K := `λ `λ .var 1

    inductive normal : Term -> Prop where
    | var : normal (.var n)
    | app : neutral u -> normal u -> normal v -> normal (u `@ v)
    | lam : normal t -> normal (`λ t)

    @[simp]
    def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
    | var x =>
      match f x with
      | .re y => var y
      | .su t => t
    | app t1 t2 => app (smap lf f t1) (smap lf f t2)
    | lam t => lam (smap lf (lf f) t)

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
      [σ](var x) = match σ x with | .re y => var y | .su t => t
    := by
    unfold Subst.apply; simp

    @[simp] -- 0[s.σ ] = s
    theorem subst_var_replace
      : [.su s :: σ]var 0 = s
    := by simp

    @[simp] -- 0[s.σ ] = s
    theorem subst_var_rename
      : [.re k :: σ]var 0 = var k
    := by simp

    @[simp]
    theorem subst_app : [σ](app t1 t2) = app ([σ]t1) ([σ]t2) := by
    unfold Subst.apply; simp

    @[simp]
    theorem subst_lam : [σ](lam t) = lam ([^σ]t) := by
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

  def vlift (v : VarMap Term) : VarMap Term
  | 0 => .var 0
  | n + 1 => [S](v n)

end Realizer
