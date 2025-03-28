import Common

namespace CC

  inductive Binder where
  | lam | pi

  inductive Term where
  | var : Nat -> Term
  | const : Const -> Term
  | binder : Binder -> Term -> Term -> Term
  | app : Term -> Term -> Term

  notation "★" => Term.const Const.type
  notation "□" => Term.const Const.kind
  notation "#" t:max => Term.var t
  notation:100 "`λ[" A "]" t:100 => Term.binder Binder.lam A t
  notation:100 "Π[" A "]" B:100 => Term.binder Binder.pi A B
  notation:100 f:100 "`@" a:110 => Term.app f a

  -- Parsing check
  -- #check ∀ t s, t `@ s = t `@ s
  -- #check ∀ a b c d, Π[a] Π[b] c `@ #0 `@ c = d
  -- #check ∀ a b c d, `λ[a] `λ[b] b `@ a `@ #4 = d
  -- #check ∀ a b c d, Π[a] `λ[b] Π[c] `λ[d] #2 `@ b = Π[#0] `λ[d] a `@ b

  inductive Ctx where
  | top : Ctx
  | binder1 : Binder -> Ctx -> Term -> Ctx
  | binder2 : Binder -> Term -> Ctx -> Ctx
  | app1 : Ctx -> Term -> Ctx
  | app2 : Term -> Ctx -> Ctx

  notation "lam1" => Ctx.binder1 Binder.lam
  notation "lam2" => Ctx.binder2 Binder.lam
  notation "pi1" => Ctx.binder1 Binder.pi
  notation "pi2" => Ctx.binder2 Binder.pi

  structure Loc where
    ctx : Ctx
    it : Term

  notation:100 Γ " ⊢ " t:100 => Loc.mk Γ t

  -- Parsing Check
  -- #check ∀ a b c d e, e ⊢ `λ[a] b = e ⊢ a `@ b `@ #0

  namespace Term
    @[simp]
    def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
    | var x =>
      match f x with
      | .re y => var y
      | .su t => t
    | const k => const k
    | app t1 t2 => app (smap lf f t1) (smap lf f t2)
    | binder b A t => binder b (smap lf f A) (smap lf (lf f) t)
  end Term

  @[simp low]
  instance substType_Term : SubstitutionType Term where
    smap := Term.smap

  namespace Term
    @[simp↓]
    theorem subst_var : [σ]var x = match σ x with | .re y => var y | .su t => t := by
    unfold Subst.apply
    unfold SubstitutionType.smap
    unfold substType_Term; unfold smap; simp

    @[simp]
    theorem subst_var_replace : [.su s :: σ]var 0 = s := by simp

    @[simp]
    theorem subst_var_rename : [.re y :: σ]var 0 = var y := by simp

    @[simp]
    theorem subst_const  : [σ]const k = const k := by
    unfold Subst.apply
    unfold SubstitutionType.smap
    unfold substType_Term; unfold smap; simp

    @[simp]
    theorem subst_app : [σ](app t1 t2) = app ([σ]t1) ([σ]t2) := by
    unfold Subst.apply
    unfold SubstitutionType.smap
    unfold substType_Term; simp

    @[simp]
    theorem subst_lam : [σ](binder b A t) = binder b ([σ]A) ([^σ]t) := by
    unfold Subst.apply
    unfold SubstitutionType.smap
    unfold substType_Term; simp

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
      unfold Ren.apply
      unfold SubstitutionType.smap
      unfold substType_Term; simp
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

  namespace Loc

    def get_type : Nat -> Ctx -> Option Loc
    | n + 1, .binder2 _ _ Γ => get_type n Γ
    | 0, .binder2 _ A Γ => .some (Γ ⊢ A)
    | n, .binder1 _ Γ _ => get_type n Γ
    | n, .app1 Γ _ => get_type n Γ
    | n, .app2 _ Γ => get_type n Γ
    | _, .top => .none

  end Loc

end CC
