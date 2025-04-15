import Common

namespace CC

  inductive Term where
  | var : Nat -> Term
  | const : Const -> Term
  | lam : Term -> Term -> Term
  | app : Term -> Term -> Term -> Term
  | pi : Term -> Term -> Term

  notation "★" => Term.const Const.type
  notation "□" => Term.const Const.kind
  notation "#" t:max => Term.var t
  notation:100 "`λ[" A "]" t:100 => Term.lam A t
  notation:100 "Π[" A "]" B:100 => Term.pi A B
  notation:100 f:100 "`@[" A "]" a:110 => Term.app A f a

  -- Parsing check
  -- #check ∀ t s, t `@ s = t `@ s
  -- #check ∀ a b c d, Π[a] Π[b] c `@ #0 `@ c = d
  -- #check ∀ a b c d, `λ[a] `λ[b] b `@ a `@ #4 = d
  -- #check ∀ a b c d, Π[a] `λ[b] Π[c] `λ[d] #2 `@ b = Π[#0] `λ[d] a `@ b

  @[simp]
  instance inst_InhabitedTerm : Inhabited Term where
    default := ★

  namespace Term
    @[simp]
    def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
    | var x =>
      match f x with
      | .re y => var y
      | .su t => t
    | const k => const k
    | app t1 t2 t3 => app (smap lf f t1) (smap lf f t2) (smap lf f t3)
    | lam A t => lam (smap lf f A) (smap lf (lf f) t)
    | pi A B => pi (smap lf f A) (smap lf (lf f) B)
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
    theorem subst_app : [σ](app t1 t2 t3) = app ([σ]t1) ([σ]t2) ([σ]t3) := by
    unfold Subst.apply
    unfold SubstitutionType.smap
    unfold substType_Term; simp

    @[simp]
    theorem subst_lam : [σ](lam A t) = lam ([σ]A) ([^σ]t) := by
    unfold Subst.apply
    unfold SubstitutionType.smap
    unfold substType_Term; simp

    @[simp]
    theorem subst_pi : [σ](pi A B) = pi ([σ]A) ([^σ]B) := by
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

    inductive MemConst (c : Const) : Term -> Prop where
    | const : MemConst c (.const c)
    | prod1 : MemConst c A -> MemConst c (Π[A] B)
    | prod2 : MemConst c B -> MemConst c (Π[A] B)
    | lam1 : MemConst c A -> MemConst c (`λ[A] t)
    | lam2 : MemConst c t -> MemConst c (`λ[A] t)
    | app1 : MemConst c f -> MemConst c (f `@[T] a)
    | app2 : MemConst c a -> MemConst c (f `@[T] a)

    inductive Red : Term -> Term -> Prop where
    | beta : Red ((`λ[A] b) `@[T] t) (b β[t])
    | lam1 : Red A A' -> Red (`λ[A] t) (`λ[A'] t)
    | lam2 : Red t t' -> Red (`λ[A] t) (`λ[A] t')
    | app1 : Red f f' -> Red (f `@[T] a) (f' `@[T] a)
    | app2 : Red a a' -> Red (f `@[T] a) (f `@[T] a')
    | pi1 : Red A A' -> Red (Π[A] B) (Π[A'] B)
    | pi2 : Red B B' -> Red (Π[A] B) (Π[A] B')

  end Term

end CC
