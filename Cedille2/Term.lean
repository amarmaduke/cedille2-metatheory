import Common

namespace Cedille2
  inductive Term : Type where
  | var : Const -> Nat -> Term
  | const : Const -> Term
  | app : Mode -> Term -> Term -> Term
  | lam : Mode -> Term -> Term -> Term
  | all : Mode -> Term -> Term -> Term
  | inter : Nat -> Nat -> Term -> Term -> Term -> Term
  | fst : Term -> Term
  | snd : Term -> Term
  | inter_ty : Term -> Term -> Term
  | refl : Term -> Term
  | eq : Term -> Term -> Term
  | subst : Term -> Term -> Term -> Term
  | phi : Term -> Term -> Term -> Term
  | conv : Nat -> Nat -> Term -> Term -> Term
  deriving Repr

  notation "★" => Term.const Const.type
  notation "□" => Term.const Const.kind

  notation f:15 "`@(" m ")" a:14 => Term.app m f a
  infixl:15 "`@f" => Term.app mf
  infixl:15 "`@τ" => Term.app mt
  infixl:15 "`@0" => Term.app m0

  notation "`λ(" m ")[" A "]" t:50 => Term.lam m A t
  notation "λf[" A "]" t:50 => Term.lam mf A t
  notation "λτ[" A "]" t:50 => Term.lam mt A t
  notation "λ0[" A "]" t:50 => Term.lam m0 A t

  notation "`∀(" m ")[" A "]" B:50 => Term.all m A B
  notation "∀f[" A "]" B:50 => Term.all mf A B
  notation "∀τ[" A "]" B:50 => Term.all mt A B
  notation "∀0[" A "]" B:50 => Term.all m0 A B

  notation "[" A "]∩" B:50 => Term.inter_ty A B
  postfix:max ".!1" => Term.fst
  postfix:max ".!2" => Term.snd

  prefix:max "#!" => Term.var Const.kind
  prefix:max "#" => Term.var Const.type

  instance instInhabited_Term : Inhabited Term where
    default := ★

  namespace Term
    @[simp]
    def size : Term -> Nat
    | var _ _ => 0
    | const _ => 0
    | app _ t1 t2 => (size t1) + (size t2) + 1
    | lam _ A t => (size A) + (size t) + 1
    | all _ t1 t2 => (size t1) + (size t2) + 1
    | inter _ _  t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
    | fst t => (size t) + 1
    | snd t => (size t) + 1
    | inter_ty t1 t2 => (size t1) + (size t2) + 1
    | refl t => (size t) + 1
    | eq t1 t2 => (size t1) + (size t2) + 1
    | phi t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
    | subst t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
    | conv _ _ t1 t2 => (size t1) + (size t2) + 1

    @[simp]
    def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
    | var k x =>
      match f x with
      | .re y => var k y
      | .su t => t
    | const k => const k
    | app m t1 t2 => app m (smap lf f t1) (smap lf f t2)
    | lam m A t => lam m (smap lf f A) (smap lf (lf f) t)
    | all m t1 t2 => all m (smap lf f t1) (smap lf (lf f) t2)
    | inter g1 g2 t1 t2 t3 => inter g1 g2 (smap lf (lf f) t1) (smap lf f t2) (smap lf f t3)
    | fst t => fst (smap lf f t)
    | snd t => snd (smap lf f t)
    | inter_ty t1 t2 => inter_ty (smap lf f t1) (smap lf (lf f) t2)
    | refl t => refl (smap lf f t)
    | eq t1 t2 => eq (smap lf f t1) (smap lf f t2)
    | phi t1 t2 t3 => phi (smap lf f t1) (smap lf f t2) (smap lf f t3)
    | subst t1 t2 t3 => subst (smap lf f t1) (smap lf f t2) (smap lf f t3)
    | conv g1 g2 t1 t2 => conv g1 g2 (smap lf f t1) (smap lf f t2)
  end Term

  @[simp]
  instance instSizeOf_Term : SizeOf Term where
    sizeOf := Term.size

  @[simp↓]
  instance substType_Term : SubstitutionType Term where
    smap := Term.smap

  namespace Term
    @[simp↓]
    theorem subst_var : [σ]var k x = match σ x with | .re y => var k y | .su t => t := by
    unfold Subst.apply; simp

    @[simp] -- 0[s.σ ] = s
    theorem subst_var_replace : [.su s :: σ]var k 0 = s := by simp

    @[simp] -- 0[s.σ ] = s
    theorem subst_var_rename : [.re y :: σ]var k 0 = var k y := by simp

    @[simp]
    theorem subst_const  : [σ]const k = const k := by unfold Subst.apply; simp

    @[simp]
    theorem subst_app : [σ](app m t1 t2) = app m ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

    @[simp]
    theorem subst_lam : [σ](lam m A t) = lam m ([σ]A) ([^σ]t) := by unfold Subst.apply; simp

    @[simp]
    theorem subst_all : [σ]all m t1 t2 = all m ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

    @[simp]
    theorem subst_inter : [σ]inter g1 g2 t1 t2 t3 = inter g1 g2 ([^σ]t1) ([σ]t2) ([σ]t3) := by unfold Subst.apply; simp

    @[simp]
    theorem subst_fst : [σ]fst t = fst ([σ]t) := by unfold Subst.apply; simp

    @[simp]
    theorem subst_snd : [σ]snd t = snd ([σ]t) := by unfold Subst.apply; simp

    @[simp]
    theorem subst_inter_ty : [σ]inter_ty t1 t2 = inter_ty ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

    @[simp]
    theorem subst_refl : [σ]refl t = refl ([σ]t) := by unfold Subst.apply; simp

    @[simp]
    theorem subst_eq : [σ]eq t1 t2 = eq ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

    @[simp]
    theorem subst_subst :
      [σ]subst t1 t2 t3 = subst ([σ]t1) ([σ]t2) ([σ]t3)
    := by unfold Subst.apply; simp

    @[simp]
    theorem subst_phi :
      [σ]phi t1 t2 t3 = phi ([σ]t1) ([σ]t2) ([σ]t3)
    := by unfold Subst.apply; simp

    @[simp]
    theorem subst_conv :
      [σ]conv g1 g2 t1 t2 = conv g1 g2 ([σ]t1) ([σ]t2)
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
end Cedille2
