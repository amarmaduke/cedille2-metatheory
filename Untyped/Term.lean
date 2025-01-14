import Untyped.Subst

inductive Term : Type where
| var : Nat -> Term
| app : Term -> Term -> Term
| lam : Term -> Term -> Term
deriving Repr

namespace Term
  @[simp]
  def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
  | var x =>
    match f x with
    | .re y => var y
    | .su t => t
  | app t1 t2 => app (smap lf f t1) (smap lf f t2)
  | lam t1 t2 => lam (smap lf f t1) (smap lf (lf f) t2)
end Term

@[simp]
instance substType_Term : SubstitutionType Term where
  smap := Term.smap

namespace Term

  @[simp] -- 0[s.σ ] = s
  theorem subst_var_replace
    : [.su s :: σ]var 0 = s
  := by
  unfold seq_cons; unfold Subst.apply
  unfold SubstitutionType.smap; simp

  @[simp] -- 0[s.σ ] = s
  theorem subst_var_rename
    : [.re k :: σ]var 0 = var k
  := by
  unfold seq_cons; unfold Subst.apply
  unfold SubstitutionType.smap; simp

  @[simp]
  theorem subst_app : [σ](app t1 t2) = app ([σ]t1) ([σ]t2) := by
  unfold Subst.apply; simp

  @[simp]
  theorem subst_lam : [σ](lam t1 t2) = lam ([σ]t1) ([^σ]t2) := by
  unfold Subst.apply; simp

  theorem apply_id {t : Term} : [I]t = t := by
  have lem : ^I = @I Term := by
    funext; case _ x =>
    cases x; all_goals (unfold Subst.lift; unfold I; simp)
  induction t
  all_goals (simp at * <;> try simp [*])
  unfold Subst.apply; unfold I; simp

  theorem apply_stable {r : Ren} {σ : Subst Term} : r.to = σ -> r.apply = σ.apply := by
  intro h; funext; case _ x =>
    unfold Ren.apply; simp at *
    unfold Ren.to; simp
    induction x generalizing r σ <;> simp at *
    case _ x => unfold Subst.apply; simp; rw [<-h]; unfold Ren.to; simp
    case _ => simp [*]
    case _ =>
      simp [*]; rw [Subst.lift_lemma, <-h]
      unfold Ren.fro; simp

  theorem apply_compose {s : Term} {σ τ : Subst Term} : [τ][σ]s = [τ ⊙ σ]s := by
    solve_compose Term, apply_stable, s, σ, τ

end Term

instance substTypeLaws_Term : SubstitutionTypeLaws Term where
  apply_id := Term.apply_id
  apply_compose := Term.apply_compose
  apply_stable := Term.apply_stable
