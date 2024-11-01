import Common.Term

namespace Term
  def Ren : Type := Nat -> Nat

  inductive SubstAction (T : Type) : Type where
  | rename : Nat -> SubstAction T
  | replace : T -> SubstAction T

  namespace SubstAction
    def size : SubstAction Term -> Nat
    | .rename _ => 0
    | .replace t => Term.size t
  end SubstAction

  def Subst (T : Type) : Type := Nat -> SubstAction T

  def subst_term_to_subst_cvterm : Subst Term -> Subst CvTerm
  | σ, n => match σ n with
    | .rename k => .rename k
    | .replace t => .replace (.refl t)

  prefix:max "▸" => subst_term_to_subst_cvterm

  @[simp] def I : Ren := λ n => n
  @[simp] def S : Ren := λ n => n + 1
  @[simp] def Sn (x : Nat) : Ren := λ n => n + x
  @[simp] def Pn (x : Nat) : Ren := λ n => n - x

  namespace Ren
    def lift : Ren -> Ren
    | _, 0 => 0
    | σ, n + 1 => σ n + 1

    @[simp]
    def cvapply : Ren -> CvTerm -> CvTerm
    | σ, .sym t => .sym (cvapply σ t)
    | σ, .trans t1 t2 => .trans (cvapply σ t1) (cvapply σ t2)
    | _, .none => .none
    | _, .const => .const
    | σ, .bound k => .bound (σ k)
    | σ, .all_congr t1 t2 => .all_congr (cvapply σ t1) (cvapply (lift σ) t2)
    | σ, .lam_congr t1 t2 => .lam_congr (cvapply σ t1) (cvapply (lift σ) t2)
    | σ, .lam_eta t => .lam_eta (cvapply σ t)
    | σ, .lam_mf_erased t => .lam_mf_erased (cvapply (lift σ) t)
    | σ, .lam_m0_erased t => .lam_m0_erased (cvapply (lift σ) t)
    | σ, .app_congr t1 t2 => .app_congr (cvapply σ t1) (cvapply σ t2)
    | σ, .app_beta t => .app_beta (cvapply σ t)
    | σ, .app_m0_erased t => .app_m0_erased (cvapply σ t)
    | σ, .prod_congr t1 t2 => .prod_congr (cvapply σ t1) (cvapply (lift σ) t2)
    | σ, .pair_congr t1 t2 t3 => .pair_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    | σ, .pair_erased t => .pair_erased (cvapply σ t)
    | σ, .fst_congr t => .fst_congr (cvapply σ t)
    | σ, .fst_erased t => .fst_erased (cvapply σ t)
    | σ, .snd_congr t => .snd_congr (cvapply σ t)
    | σ, .snd_erased t => .snd_erased (cvapply σ t)
    | σ, .phi_congr t1 t2 t3 => .phi_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    | σ, .phi_erased t => .phi_erased (cvapply σ t)
    | σ, .eq_congr t1 t2 t3 => .eq_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    | σ, .refl_congr t => .refl_congr (cvapply σ t)
    | σ, .refl_erased t => .refl_erased (cvapply σ t)
    | σ, .subst_congr t1 t2 => .subst_congr (cvapply σ t1) (cvapply σ t2)
    | σ, .subst_erased t => .subst_erased (cvapply σ t)
    | σ, .conv_congr t1 t2 => .conv_congr (cvapply σ t1) (cvapply σ t2)
    | σ, .conv_erased t => .conv_erased (cvapply σ t)

    @[simp]
    def apply : Ren -> Term -> Term
    | σ, bound c k => bound c (σ k)
    | _, none => none
    | _, const k => const k
    | σ, lam m t1 t2 => lam m (apply σ t1) (apply (lift σ) t2)
    | σ, app m t1 t2 => app m (apply σ t1) (apply σ t2)
    | σ, all m t1 t2 => all m (apply σ t1) (apply (lift σ) t2)
    | σ, pair t1 t2 t3 => pair (apply σ t1) (apply σ t2) (apply σ t3)
    | σ, fst t => fst (apply σ t)
    | σ, snd t => snd (apply σ t)
    | σ, prod t1 t2 => prod (apply σ t1) (apply (lift σ) t2)
    | σ, refl t => refl (apply σ t)
    | σ, subst t1 t2 => subst (apply σ t1) (apply σ t2)
    | σ, phi t1 t2 t3 => phi (apply σ t1) (apply σ t2) (apply σ t3)
    | σ, eq t1 t2 t3 => eq (apply σ t1) (apply σ t2) (apply σ t3)
    | σ, conv t1 t2 c => conv (apply σ t1) (apply σ t2) (cvapply σ c)
  end Ren

  namespace Subst
    def from_ren : Ren -> Subst T
    | σ, n => .rename (σ n)

    def cons : SubstAction T -> Subst T -> Subst T
    | t, _, 0 => t
    | _, σ, n + 1 => σ n

    def cvlift : Subst CvTerm -> Subst CvTerm
    | _, 0 => .rename 0
    | σ, n + 1 => match (σ n) with
      | .replace t => .replace (Ren.cvapply S t)
      | .rename k => .rename (S k)

    def lift : Subst Term -> Subst Term
    | _, 0 => .rename 0
    | σ, n + 1 => match (σ n) with
      | .replace t => .replace (Ren.apply S t)
      | .rename k => .rename (S k)

    @[simp]
    def cvapply : Subst CvTerm -> CvTerm -> CvTerm
    | σ, .sym t => .sym (cvapply σ t)
    | σ, .trans t1 t2 => .trans (cvapply σ t1) (cvapply σ t2)
    | _, .none => .none
    | _, .const => .const
    | σ, .bound k =>
      match σ k with
      | .replace t => t
      | .rename n => .bound n
    | σ, .all_congr t1 t2 => .all_congr (cvapply σ t1) (cvapply (cvlift σ) t2)
    | σ, .lam_congr t1 t2 => .lam_congr (cvapply σ t1) (cvapply (cvlift σ) t2)
    | σ, .lam_eta t => .lam_eta (cvapply σ t)
    | σ, .lam_mf_erased t => .lam_mf_erased (cvapply (cvlift σ) t)
    | σ, .lam_m0_erased t => .lam_m0_erased (cvapply (cvlift σ) t)
    | σ, .app_congr t1 t2 => .app_congr (cvapply σ t1) (cvapply σ t2)
    | σ, .app_beta t => .app_beta (cvapply σ t)
    | σ, .app_m0_erased t => .app_m0_erased (cvapply σ t)
    | σ, .prod_congr t1 t2 => .prod_congr (cvapply σ t1) (cvapply (cvlift σ) t2)
    | σ, .pair_congr t1 t2 t3 => .pair_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    | σ, .pair_erased t => .pair_erased (cvapply σ t)
    | σ, .fst_congr t => .fst_congr (cvapply σ t)
    | σ, .fst_erased t => .fst_erased (cvapply σ t)
    | σ, .snd_congr t => .snd_congr (cvapply σ t)
    | σ, .snd_erased t => .snd_erased (cvapply σ t)
    | σ, .phi_congr t1 t2 t3 => .phi_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    | σ, .phi_erased t => .phi_erased (cvapply σ t)
    | σ, .eq_congr t1 t2 t3 => .eq_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    | σ, .refl_congr t => .refl_congr (cvapply σ t)
    | σ, .refl_erased t => .refl_erased (cvapply σ t)
    | σ, .subst_congr t1 t2 => .subst_congr (cvapply σ t1) (cvapply σ t2)
    | σ, .subst_erased t => .subst_erased (cvapply σ t)
    | σ, .conv_congr t1 t2 => .conv_congr (cvapply σ t1) (cvapply σ t2)
    | σ, .conv_erased t => .conv_erased (cvapply σ t)

    @[simp]
    def apply : Subst Term -> Term -> Term
    | σ, bound c k =>
      match σ k with
      | .replace t => t
      | .rename n => bound c n
    | _, none => none
    | _, const k => const k
    | σ, lam m t1 t2 => lam m (apply σ t1) (apply (lift σ) t2)
    | σ, app m t1 t2 => app m (apply σ t1) (apply σ t2)
    | σ, all m t1 t2 => all m (apply σ t1) (apply (lift σ) t2)
    | σ, pair t1 t2 t3 => pair (apply σ t1) (apply σ t2) (apply σ t3)
    | σ, fst t => fst (apply σ t)
    | σ, snd t => snd (apply σ t)
    | σ, prod t1 t2 => prod (apply σ t1) (apply (lift σ) t2)
    | σ, refl t => refl (apply σ t)
    | σ, subst t1 t2 => subst (apply σ t1) (apply σ t2)
    | σ, phi t1 t2 t3 => phi (apply σ t1) (apply σ t2) (apply σ t3)
    | σ, eq t1 t2 t3 => eq (apply σ t1) (apply σ t2) (apply σ t3)
    | σ, conv t1 t2 c => conv (apply σ t1) (apply σ t2) (cvapply ▸σ c)

    def cvcompose : Subst CvTerm -> Subst CvTerm -> Subst CvTerm
    | σ, τ, n => match (σ n) with
      | .replace t => .replace (cvapply τ t)
      | .rename k => τ k

    def compose : Subst Term -> Subst Term -> Subst Term
    | σ, τ, n => match (σ n) with
      | .replace t => .replace (apply τ t)
      | .rename k => τ k

    def beta : Term -> Term -> Term
    | s, t => apply (cons (.replace t) (from_ren I)) s
  end Subst

  -- notation:100 "r#" σ:110 => Subst.from_ren σ
  prefix:max "r#" => @Subst.from_ren Term
  prefix:max "cr#" => @Subst.from_ren CvTerm
  -- notation:70 t:70 "::" σ:70 => Subst.cons t σ
  infix:70 "::" => Subst.cons
  --notation:100 "^" σ:110 => Subst.lift σ
  prefix:max "^" => Subst.lift
  prefix:max "^" => Subst.cvlift
  notation:90 "[" σ "]" t:89 => Subst.apply σ t
  notation:90 "[" σ "]" t:89 => Subst.cvapply σ t
  notation:90 τ:90 " ⊙ " σ:91 => Subst.compose σ τ
  notation:90 τ:90 " ⊙ " σ:91 => Subst.cvcompose σ τ
  notation:90 s:90 "β[" t "]" => Subst.beta s t

  @[simp] theorem subst_from_ren_x : (r#r) x = .rename (r x) :=
    by unfold Subst.from_ren; rfl

  @[simp] theorem subst_from_cvren_x : (cr#r) x = .rename (r x) :=
    by unfold Subst.from_ren; rfl

  @[simp] theorem subst_cons_zero {σ : Subst T} : (s :: σ) 0 = s :=
    by unfold Subst.cons; rfl
  @[simp] theorem subst_cons_succ {σ : Subst T} : (s :: σ) (n + 1) = σ n :=
    by unfold Subst.cons; rfl

  @[simp]
  theorem subst_lift_is_ren_lift r : r#(Ren.lift r) = ^(r#r) := by {
    funext; case _ x =>
    cases x
    case zero =>
      unfold Subst.from_ren; unfold Ren.lift; simp
      unfold Subst.lift; simp
    case _ n =>
      generalize lhsdef : (r#(Ren.lift r)) (n + 1) = lhs
      generalize rhsdef : (^(r#r)) (n + 1) = rhs
      unfold Subst.from_ren at lhsdef; simp at *
      unfold Ren.lift at lhsdef; simp at *
      unfold Subst.lift at rhsdef; simp at *
      subst lhsdef; subst rhsdef; rfl
  }

  @[simp]
  theorem subst_cvlift_is_ren_cvlift r : cr#(Ren.lift r) = ^(cr#r) := by {
    funext; case _ x =>
    cases x
    case zero =>
      unfold Subst.from_ren; unfold Ren.lift; simp
      unfold Subst.cvlift; simp
    case _ n =>
      generalize lhsdef : (r#(Ren.lift r)) (n + 1) = lhs
      generalize rhsdef : (^(r#r)) (n + 1) = rhs
      unfold Subst.from_ren at lhsdef; simp at *
      unfold Ren.lift at lhsdef; simp at *
      unfold Subst.lift at rhsdef; simp at *
      subst lhsdef; subst rhsdef; rfl
  }

  @[simp]
  theorem subst_cvapply_is_ren_cvapply r t : Ren.cvapply r t = [cr#r]t := by {
    induction t generalizing r
    any_goals (unfold Ren.cvapply; simp [*])
  }

  @[simp]
  theorem subst_from_ren_transport_is_same : ▸(r#r) = cr#r := by {
    funext
    case _ x =>
      cases x
      all_goals (unfold Subst.from_ren; unfold subst_term_to_subst_cvterm; simp [*])
  }

  @[simp]
  theorem subst_apply_is_ren_apply r t : Ren.apply r t = [r#r]t := by {
    induction t generalizing r
    any_goals (unfold Ren.apply; simp [*])
  }

  @[simp]
  theorem subst_cvapply_I_is_id s : [cr#I]s = s := by {
    have lem : ^(cr# I) = cr# I := by {
      funext
      case _ x =>
      cases x
      case _ =>
        unfold Subst.cvlift; simp
      case _ x =>
        unfold Subst.cvlift; simp
    }
    induction s
    all_goals unfold Subst.cvapply
    any_goals simp [*]
  }

  @[simp]
  theorem subst_apply_I_is_id s : [r#I]s = s := by {
    have lem : ^(r# I) = r# I := by {
      funext
      case _ x =>
      cases x
      case _ =>
        unfold Subst.lift; simp
      case _ x =>
        unfold Subst.lift; simp
    }
    induction s
    all_goals unfold Subst.apply
    any_goals simp [*]
  }

  theorem subst_transform_ren_apply_commutes : .refl ([r#r]t) = [cr#r] (.refl t) := by {
    induction t generalizing r
    all_goals simp [*]
    case lam m t1 t2 ih1 ih2 => rw [<-subst_cvlift_is_ren_cvlift, <-subst_lift_is_ren_lift, ih2]
    case all m t1 t2 ih1 ih2 => rw [<-subst_cvlift_is_ren_cvlift, <-subst_lift_is_ren_lift, ih2]
    case prod t1 t2 ih1 ih2 => rw [<-subst_cvlift_is_ren_cvlift, <-subst_lift_is_ren_lift, ih2]
  }

  @[simp]
  theorem subst_transform_lift_commutes : ▸^σ = ^▸σ := by {
    funext
    case _ x =>
    unfold subst_term_to_subst_cvterm; unfold Subst.lift; unfold Subst.cvlift; simp
    cases x
    case _ => simp
    case _ n =>
      simp
      cases σ n
      case _ => simp
      case _ t =>
        simp; rw [subst_transform_ren_apply_commutes]
  }

  theorem subst_transform_apply_commutes : .refl ([σ]t) = [▸σ](.refl t) := by {
    induction t generalizing σ
    all_goals simp [*]
    case bound k i =>
      unfold subst_term_to_subst_cvterm; simp
      cases σ i
      case _ j => simp
      case _ s => simp
  }

  @[simp]
  theorem subst_transform_commutes_with_compose : ▸(σ ⊙ τ) = ▸σ ⊙ ▸τ := by {
    funext
    case _ x =>
    unfold subst_term_to_subst_cvterm; unfold Subst.compose; unfold Subst.cvcompose; simp
    cases (τ x)
    case _ x => simp
    case _ t =>
      simp; rw [subst_transform_apply_commutes]
      unfold subst_term_to_subst_cvterm; simp
  }

  @[simp]
  theorem subst_transform_commutes_with_cons_rename : ▸(.rename k :: σ) = .rename k :: ▸σ := by {
    funext
    case _ x =>
      unfold subst_term_to_subst_cvterm
      cases x <;> simp [*]
  }

  @[simp]
  theorem subst_transform_commutes_with_cons_replace : ▸(.replace t :: σ) = .replace (.refl t) :: ▸σ := by {
    funext
    case _ x =>
      unfold subst_term_to_subst_cvterm
      cases x <;> simp [*]
  }

  @[simp]
  theorem subst_cvapply_twice_is_cvapply_compose {s : CvTerm} {σ τ} : [τ][σ]s = [τ ⊙ σ]s := by {
    have lem1 τ : ^τ ⊙ cr#S = cr#S ⊙ τ := by {
      funext
      unfold Subst.cvcompose; unfold Subst.from_ren; unfold S; simp
      unfold Subst.cvlift; unfold S; simp
      unfold Subst.from_ren; simp
    }
    have lem2 (σ:Subst CvTerm) e : ^(σ ⊙ cr#e) = ^σ ⊙ ^(cr#e) := by {
      funext; case _ n =>
      cases n
      . unfold Subst.from_ren; unfold Subst.cvcompose; unfold Subst.cvlift; simp
      case _ n =>
        generalize lhsdef : (^σ ⊙ ^(cr#e)) (n + 1) = lhs
        unfold Subst.cvlift; simp
        unfold Subst.cvcompose; unfold Subst.from_ren; unfold S; simp
        subst lhs; unfold Subst.cvcompose; unfold Subst.cvlift; simp
        unfold Subst.from_ren; unfold S; simp
    }
    have lem3 σ e s : [σ][cr#e]s = [σ ⊙ cr#e]s := by {
      induction s generalizing σ e
      any_goals simp [*]
      case bound => unfold Subst.cvcompose; simp
      case all_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih]
      case lam_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih]
      case lam_mf_erased _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih]
      case lam_m0_erased _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih]
      case prod_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih]
    }
    have lem4 σ τ : σ ⊙ τ ⊙ cr#S = σ ⊙ (τ ⊙ cr#S) := by {
      funext; case _ x =>
      cases x
      any_goals (unfold Subst.cvcompose; unfold Subst.from_ren; unfold S; simp)
    }
    have lem5 r1 r2 τ : cr#r1 ⊙ (cr#r2 ⊙ τ) = cr#r1 ⊙ cr#r2 ⊙ τ := by {
      funext; case _ x =>
        unfold Subst.cvcompose; simp
        cases τ x <;> simp at *
        case _ t =>
          have lem : [fun x => SubstAction.rename (r1 (r2 x))]t = [cr#r1 ⊙ cr#r2]t := by {
            unfold Subst.cvcompose; simp
          }
          rw [lem, lem3]
    }
    have lem6 e τ : ^(cr#e) ⊙ ^τ = ^(cr#e ⊙ τ) := by {
      funext; case _ n =>
      cases n
      . unfold Subst.cvcompose; unfold Subst.cvlift; simp
      case _ n =>
        have lem : ((^(cr#e) ⊙ ^τ) ⊙ cr#S) n = (^(cr#e ⊙ τ) ⊙ cr#S) n := by {
          rw [lem1, lem4, lem1]
          rw [<-subst_cvlift_is_ren_cvlift, lem5]; simp
          rw [lem1, lem5]
        }
        unfold Subst.cvcompose at lem; unfold S at lem; unfold Subst.from_ren at lem
        unfold Subst.cvcompose; unfold Subst.from_ren
        simp at lem; simp [*]
    }
    have lem7 τ e s : [cr#e][τ]s = [cr#e ⊙ τ]s := by {
      induction s generalizing τ e
      any_goals simp [*]
      case bound k =>
        unfold Subst.cvcompose; simp
        cases τ k <;> simp at *
      case all_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih, <-lem6]; simp
      case lam_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih, <-lem6]; simp
      case lam_mf_erased _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih, <-lem6]; simp
      case lam_m0_erased _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih, <-lem6]; simp
      case prod_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih, <-lem6]; simp
    }
    have lem8 σ τ : σ ⊙ (cr#S ⊙ τ) = σ ⊙ cr#S ⊙ τ := by {
      funext; case _ x =>
        unfold Subst.cvcompose; simp
        cases τ x <;> simp at *
        rw [lem3]; unfold Subst.cvcompose; simp
    }
    have lem9 σ τ : cr#S ⊙ (σ ⊙ τ) = cr#S ⊙ σ ⊙ τ := by {
      funext; case _ x =>
        unfold Subst.cvcompose; simp
        cases τ x <;> simp at *
        rw [lem7]; unfold Subst.cvcompose; simp
    }
    have lem10 (σ τ : Subst CvTerm) : ^σ ⊙ ^τ = ^(σ ⊙ τ) := by {
      funext; case _ x =>
      cases x
      case _ => unfold Subst.cvcompose; unfold Subst.cvlift; simp
      case _ n =>
        have lem : ((^σ ⊙ ^τ) ⊙ cr#S) n = (^(σ ⊙ τ) ⊙ cr#S) n := by {
          rw [lem1, lem4, lem1, lem8, lem1, lem9]
        }
        unfold Subst.cvcompose at lem; unfold S at lem; unfold Subst.from_ren at lem
        unfold Subst.cvcompose
        simp at lem; simp [*]
    }
    induction s generalizing τ σ
    any_goals simp [*]
    case bound k =>
      unfold Subst.cvcompose; simp
      cases σ k <;> simp
  }

  @[simp]
  theorem subst_apply_twice_is_apply_compose {s : Term} {σ τ} : [τ][σ]s = [τ ⊙ σ]s := by {
    have lem1 τ : ^τ ⊙ r#S = r#S ⊙ τ := by {
      funext
      unfold Subst.compose; unfold Subst.from_ren; unfold S; simp
      unfold Subst.lift; unfold S; simp
      unfold Subst.from_ren; simp
    }
    have lem2 (σ:Subst Term) e : ^(σ ⊙ r#e) = ^σ ⊙ ^(r#e) := by {
      funext; case _ n =>
      cases n
      . unfold Subst.from_ren; unfold Subst.compose; unfold Subst.lift; simp
      case _ n =>
        generalize lhsdef : (^σ ⊙ ^(r#e)) (n + 1) = lhs
        unfold Subst.lift; simp
        unfold Subst.compose; unfold Subst.from_ren; unfold S; simp
        subst lhs; unfold Subst.compose; unfold Subst.lift; simp
        unfold Subst.from_ren; unfold S; simp
    }
    have lem3 σ e s : [σ][r#e]s = [σ ⊙ r#e]s := by {
      induction s generalizing σ e
      any_goals simp [*]
      case bound => unfold Subst.compose; simp
      case lam _ _ _ ih => rw [<-subst_lift_is_ren_lift, ih]
      case all _ _ _ ih => rw [<-subst_lift_is_ren_lift, ih]
      case prod _ _ _ ih => rw [<-subst_lift_is_ren_lift, ih]
    }
    have lem4 σ τ : σ ⊙ τ ⊙ r#S = σ ⊙ (τ ⊙ r#S) := by {
      funext; case _ x =>
      cases x
      any_goals (unfold Subst.compose; unfold Subst.from_ren; unfold S; simp)
    }
    have lem5 r1 r2 τ : r#r1 ⊙ (r#r2 ⊙ τ) = r#r1 ⊙ r#r2 ⊙ τ := by {
      funext; case _ x =>
        unfold Subst.compose; simp
        cases τ x <;> simp at *
        case _ t =>
          have lem : [fun x => SubstAction.rename (r1 (r2 x))]t = [r#r1 ⊙ r#r2]t := by {
            unfold Subst.compose; simp
          }
          rw [lem, lem3]
    }
    have lem6 e τ : ^(r#e) ⊙ ^τ = ^(r#e ⊙ τ) := by {
      funext; case _ n =>
      cases n
      . unfold Subst.compose; unfold Subst.lift; simp
      case _ n =>
        have lem : ((^(r#e) ⊙ ^τ) ⊙ r#S) n = (^(r#e ⊙ τ) ⊙ r#S) n := by {
          rw [lem1, lem4, lem1]
          rw [<-subst_lift_is_ren_lift, lem5]; simp
          rw [lem1, lem5]
        }
        unfold Subst.compose at lem; unfold S at lem; unfold Subst.from_ren at lem
        unfold Subst.compose; unfold Subst.from_ren
        simp at lem; simp [*]
    }
    have lem7 τ e s : [r#e][τ]s = [r#e ⊙ τ]s := by {
      induction s generalizing τ e
      any_goals simp [*]
      case bound k =>
        unfold Subst.compose; simp
        cases τ k <;> simp at *
      case lam _ _ _ ih => rw [<-subst_lift_is_ren_lift, ih, <-lem6]; simp
      case all _ _ _ ih => rw [<-subst_lift_is_ren_lift, ih, <-lem6]; simp
      case prod _ _ _ ih => rw [<-subst_lift_is_ren_lift, ih, <-lem6]; simp
    }
    have lem8 σ τ : σ ⊙ (r#S ⊙ τ) = σ ⊙ r#S ⊙ τ := by {
      funext; case _ x =>
        unfold Subst.compose; simp
        cases τ x <;> simp at *
        rw [lem3]; unfold Subst.compose; simp
    }
    have lem9 σ τ : r#S ⊙ (σ ⊙ τ) = r#S ⊙ σ ⊙ τ := by {
      funext; case _ x =>
        unfold Subst.compose; simp
        cases τ x <;> simp at *
        rw [lem7]; unfold Subst.compose; simp
    }
    have lem10 (σ τ : Subst Term) : ^σ ⊙ ^τ = ^(σ ⊙ τ) := by {
      funext; case _ x =>
      cases x
      case _ => unfold Subst.compose; unfold Subst.lift; simp
      case _ n =>
        have lem : ((^σ ⊙ ^τ) ⊙ r#S) n = (^(σ ⊙ τ) ⊙ r#S) n := by {
          rw [lem1, lem4, lem1, lem8, lem1, lem9]
        }
        unfold Subst.compose at lem; unfold S at lem; unfold Subst.from_ren at lem
        unfold Subst.compose
        simp at lem; simp [*]
    }
    induction s generalizing τ σ
    any_goals simp [*]
    case bound k =>
      unfold Subst.compose; simp
      cases σ k <;> simp
  }

  @[simp] -- βst = s[t.I]
  theorem subst_valid1 : s β[t] = [.replace t :: r#I]s := by unfold Subst.beta; simp

  @[simp] -- 0[s.σ ] = s
  theorem subst_valid2_replace
    : [.replace s :: σ]bound c 0 = s
  := by unfold Subst.cons; simp

  @[simp] -- 0[s.σ ] = s
  theorem subst_valid2_rename
    : [.rename k :: σ]bound c 0 = bound c k
  := by unfold Subst.cons; simp

  @[simp]
  theorem cvsubst_valid2_replace
    : [.replace s :: σ]CvTerm.bound 0 = s
  := by unfold Subst.cons; simp

  @[simp]
  theorem cvsubst_valid2_rename
    : [.rename k :: σ]CvTerm.bound 0 = CvTerm.bound k
  := by unfold Subst.cons; simp

  @[simp] -- ⇑σ = 0.(σ ◦ S)
  theorem subst_valid3 {σ : Subst Term} : ^σ = .rename 0 :: (r#S ⊙ σ) := by {
    funext; case _ x =>
      unfold Subst.lift; simp
      unfold Subst.compose; simp
      cases x
      case _ => simp
      case _ n => simp
  }

  @[simp]
  theorem cvsubst_valid3 {σ : Subst CvTerm} : ^σ = .rename 0 :: (cr#S ⊙ σ) := by {
    funext; case _ x =>
      unfold Subst.cvlift; simp
      unfold Subst.cvcompose; simp
      cases x
      case _ => simp
      case _ n => simp
  }

  @[simp] -- 0.S = I
  theorem subst_valid4 : .rename 0 :: r#S = r#I := by {
    funext; case _ x =>
    cases x
    case _ =>
      unfold Subst.cons; unfold Subst.from_ren; simp
    case _ n =>
      unfold Subst.cons; unfold Subst.from_ren; simp
  }

  @[simp]
  theorem cvsubst_valid4 : .rename 0 :: cr#S = cr#I := by {
    funext; case _ x =>
    cases x
    case _ =>
      unfold Subst.cons; unfold Subst.from_ren; simp
    case _ n =>
      unfold Subst.cons; unfold Subst.from_ren; simp
  }

  @[simp] -- σ ◦ I = σ
  theorem subst_valid5 : σ ⊙ r#I = σ := by {
    funext; case _ x =>
    unfold Subst.compose; unfold Subst.from_ren; unfold I; simp
  }

  @[simp]
  theorem cvsubst_valid5 : σ ⊙ cr#I = σ := by {
    funext; case _ x =>
    unfold Subst.cvcompose; unfold Subst.from_ren; unfold I; simp
  }

  @[simp] -- I ◦ σ = σ
  theorem subst_valid6 : r#I ⊙ σ = σ := by {
    funext; case _ x =>
    unfold Subst.compose; simp
    cases x
    all_goals (split; simp [*])
    case _ _ _ e => rw [e]
    case _ _ _ e => rw [e]
  }

  @[simp]
  theorem cvsubst_valid6 : cr#I ⊙ σ = σ := by {
    funext; case _ x =>
    unfold Subst.cvcompose; simp
    cases x
    all_goals (split; simp [*])
    case _ _ _ e => rw [e]
    case _ _ _ e => rw [e]
  }

  @[simp] -- (σ ◦ τ) ◦ μ = σ ◦ (τ ◦ μ)
  theorem subst_valid7 {σ : Subst Term} : σ ⊙ (τ ⊙ μ) = σ ⊙ τ ⊙ μ := by {
    funext; case _ x =>
      unfold Subst.compose; simp
      cases μ x <;> simp
      . unfold Subst.compose; simp
  }

  @[simp]
  theorem cvsubst_valid7 {σ : Subst CvTerm} : σ ⊙ (τ ⊙ μ) = σ ⊙ τ ⊙ μ := by {
    funext; case _ x =>
      unfold Subst.cvcompose; simp
      cases μ x <;> simp
      . unfold Subst.cvcompose; simp
  }

  @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
  theorem subst_valid8_replace {s : Term}
    : τ ⊙ (.replace s :: σ) = .replace ([τ]s) :: (τ ⊙ σ)
  := by {
    funext; case _ x =>
    cases x
    all_goals (unfold Subst.compose; unfold Subst.cons; simp)
  }

  @[simp]
  theorem cvsubst_valid8_replace {s : CvTerm}
    : τ ⊙ (.replace s :: σ) = .replace ([τ]s) :: (τ ⊙ σ)
  := by {
    funext; case _ x =>
    cases x
    all_goals (unfold Subst.cvcompose; unfold Subst.cons; simp)
  }

  @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
  theorem subst_valid8_rename {σ : Subst Term}
    : τ ⊙ (.rename s :: σ) = (τ s) :: (τ ⊙ σ)
  := by {
    funext; case _ x =>
    cases x
    all_goals (unfold Subst.compose; unfold Subst.cons; simp)
  }

  @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
  theorem cvsubst_valid8_rename {σ : Subst CvTerm}
    : τ ⊙ (.rename s :: σ) = (τ s) :: (τ ⊙ σ)
  := by {
    funext; case _ x =>
    cases x
    all_goals (unfold Subst.cvcompose; unfold Subst.cons; simp)
  }

  @[simp] -- S ◦ (s.σ ) = σ
  theorem subst_valid9 : (s :: σ) ⊙ r#S = σ := by {
    funext; case _ x =>
    cases x
    all_goals {
      unfold Subst.compose; unfold Subst.cons; unfold Subst.from_ren
      unfold S; simp
    }
  }

  @[simp]
  theorem cvsubst_valid9 : (s :: σ) ⊙ cr#S = σ := by {
    funext; case _ x =>
    cases x
    all_goals {
      unfold Subst.cvcompose; unfold Subst.cons; unfold Subst.from_ren
      unfold S; simp
    }
  }

  -- @[simp] -- 0[σ ].(S ◦ σ ) = σ
  -- theorem subst_valid10 : .rename 0 :: r#S ⊙ σ = σ := by {
  --   funext; case _ x =>
  --   cases x
  --   case _ => {
  --     unfold Subst.cons; simp;
  --     sorry
  --   }
  --   case _ n => {
  --     unfold Subst.cons; simp; unfold Subst.compose; simp
  --     unfold S; sorry
  --   }
  -- }

  -- (βst)[σ ] = β(s[⇑σ ])(t[σ ])
  theorem subst_beta_distr : [σ](s β[t]) = ([^σ]s) β[ [σ]t ] := by simp

  -- s[σ ][S] = s[S][⇑σ ]
  theorem subst_rw_ex1 : [r#S][σ]s = [^σ][r#S]s := by simp
  -- -- s[⇑σ ][t.I] = s[t.σ ]
  theorem subst_rw_ex2 : [t::r#I][^σ]s = [t::σ]s := by simp
  -- s[⇑σ ][t[σ ].I] = s[t.I][σ ]
  theorem subst_rw_ex3 : [(.replace ([σ]t))::r#I][^σ]s = [σ][.replace t::r#I]s := by simp

  -- s[σ ][S] = s[S][⇑σ ]
  theorem cvsubst_rw_ex1 : [cr#S][σ]s = [^σ][cr#S]s := by simp
  -- -- s[⇑σ ][t.I] = s[t.σ ]
  theorem cvsubst_rw_ex2 : [t::cr#I][^σ]s = [t::σ]s := by simp
  -- s[⇑σ ][t[σ ].I] = s[t.I][σ ]
  theorem cvsubst_rw_ex3 : [(.replace ([σ]t))::cr#I][^σ]s = [σ][.replace t::cr#I]s := by simp

  def mode_to_sort : Mode -> Const
  | mt => .kind
  | mf => .type
  | m0 => .type

  @[simp] theorem mt_to_sort : mode_to_sort mt = .kind := rfl
  @[simp] theorem mf_to_sort : mode_to_sort mf = .type := rfl
  @[simp] theorem m0_to_sort : mode_to_sort m0 = .type := rfl

  def eta : Mode -> Term -> Term -> Term
  | m, A, t => lam m A (app m ([r#S]t) (bound (mode_to_sort m) 0))

  @[simp] theorem S_after_Pn : (r#S ⊙ r#(Pn n)) (n + k) = .rename (k + 1) := by {
    cases n
    case _ => unfold Subst.compose; simp
    case _ n => unfold Subst.compose; simp; omega
  }

  @[simp] theorem S_after_Pn_1 : (r#S ⊙ r#(Pn 1)) 1 = .rename 1 := by {
    unfold Subst.compose; simp
  }

  -- theorem subst_S_classifies_free : [r#S]s = s -> ∀ σ, [σ]s = s := by {
  --   intro h σ
  --   induction s generalizing σ
  --   any_goals (simp at *; simp [*])
  --   any_goals simp
  --   case bound i => {
  --     cases i <;> simp at *
  --     all_goals (exfalso; unfold S at *; simp at h)
  --   }
  --   case lam t1 t2 ih1 ih2 => {
  --     unfold Subst.cons at *; simp at *
  --   }
  --   case all => sorry
  --   case int => sorry
  -- }
end Term
