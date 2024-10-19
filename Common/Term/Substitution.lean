import Common.Term

namespace Term
  def Ren : Type := Nat -> Nat

  inductive SubstAction : Type where
  | rename : Nat -> SubstAction
  | replace : Term -> SubstAction

  namespace SubstAction
    def size : SubstAction -> Nat
    | .rename _ => 0
    | .replace t => Term.size t

  end SubstAction

  def Subst : Type := Nat -> SubstAction

  @[simp] def I : Ren := λ n => n
  @[simp] def S : Ren := λ n => n + 1
  @[simp] def Sn (x : Nat) : Ren := λ n => n + x
  @[simp] def Pn (x : Nat) : Ren := λ n => n - x

  namespace Ren
    def lift : Ren -> Ren
    | _, 0 => 0
    | σ, n + 1 => σ n + 1

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
    | σ, conv t1 t2 c => conv (apply σ t1) (apply σ t2) c
  end Ren

  namespace Subst
    def from_ren : Ren -> Subst
    | σ, n => .rename (σ n)

    def cons : SubstAction -> Subst -> Subst
    | t, _, 0 => t
    | _, σ, n + 1 => σ n

    def lift : Subst -> Subst
    | _, 0 => .rename 0
    | σ, n + 1 => match (σ n) with
      | .replace t => .replace (Ren.apply S t)
      | .rename k => .rename (S k)

    @[simp]
    def apply : Subst -> Term -> Term
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
    | σ, conv t1 t2 c => conv (apply σ t1) (apply σ t2) c

    def compose : Subst -> Subst -> Subst
    | σ, τ, n => match (σ n) with
      | .replace t => .replace (apply τ t)
      | .rename k => τ k

    def beta : Term -> Term -> Term
    | s, t => apply (cons (.replace t) (from_ren I)) s
  end Subst

  notation:100 "r#" σ:110 => Subst.from_ren σ
  notation:70 t:70 "::" σ:70 => Subst.cons t σ
  notation:100 "^" σ:110 => Subst.lift σ
  notation:90 "[" σ "]" t:89 => Subst.apply σ t
  notation:90 τ:90 " ⊙ " σ:91 => Subst.compose σ τ
  notation:90 s:90 "β[" t "]" => Subst.beta s t

  @[simp] theorem subst_from_ren_x : (r#r) x = .rename (r x) :=
    by unfold Subst.from_ren; rfl

  @[simp] theorem subst_cons_zero (σ : Subst) : (s :: σ) 0 = s :=
    by unfold Subst.cons; rfl
  @[simp] theorem subst_cons_succ (σ : Subst) : (s :: σ) (n + 1) = σ n :=
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
  theorem subst_apply_is_ren_apply r t : Ren.apply r t = [r#r]t := by {
    induction t generalizing r
    any_goals (unfold Ren.apply; simp [*])
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

  @[simp]
  theorem subst_apply_twice_is_apply_compose s σ τ : [τ][σ]s = [τ ⊙ σ]s := by {
    have lem1 τ : ^τ ⊙ r#S = r#S ⊙ τ := by {
      funext
      unfold Subst.compose; unfold Subst.from_ren; unfold S; simp
      unfold Subst.lift; unfold S; simp
      unfold Subst.from_ren; simp
    }
    have lem2 (σ:Subst) e : ^(σ ⊙ r#e) = ^σ ⊙ ^(r#e) := by {
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
    have lem10 σ τ : ^σ ⊙ ^τ = ^(σ ⊙ τ) := by {
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

  @[simp] -- ⇑σ = 0.(σ ◦ S)
  theorem subst_valid3 : ^σ = .rename 0 :: (r#S ⊙ σ) := by {
    funext; case _ x =>
      unfold Subst.lift; simp
      unfold Subst.compose; simp
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

  @[simp] -- σ ◦ I = σ
  theorem subst_valid5 : σ ⊙ r#I = σ := by {
    funext; case _ x =>
    unfold Subst.compose; unfold Subst.from_ren; unfold I; simp
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

  @[simp] -- (σ ◦ τ) ◦ μ = σ ◦ (τ ◦ μ)
  theorem subst_valid7 : σ ⊙ (τ ⊙ μ) = σ ⊙ τ ⊙ μ := by {
    funext; case _ x =>
      unfold Subst.compose; simp
      cases μ x <;> simp
      . unfold Subst.compose; simp
  }

  @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
  theorem subst_valid8_replace
    : τ ⊙ (.replace s :: σ) = .replace ([τ]s) :: (τ ⊙ σ)
  := by {
    funext; case _ x =>
    cases x
    all_goals (unfold Subst.compose; unfold Subst.cons; simp)
  }

  @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
  theorem subst_valid8_rename
    : τ ⊙ (.rename s :: σ) = (τ s) :: (τ ⊙ σ)
  := by {
    funext; case _ x =>
    cases x
    all_goals (unfold Subst.compose; unfold Subst.cons; simp)
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
