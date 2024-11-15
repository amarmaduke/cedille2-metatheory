import Common.Util
import Common.Term


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

-- def subst_term_to_subst_cvterm : Subst Term -> Subst CvTerm
-- | σ, n => match σ n with
--   | .rename k => .rename k
--   | .replace t => .replace (.refl t)

-- prefix:max "▸" => subst_term_to_subst_cvterm

@[simp] def rI : Ren := λ n => n
@[simp] def rS : Ren := λ n => n + 1
@[simp] def rP : Ren := λ n => n - 1
@[simp] def rSn (x : Nat) : Ren := λ n => n + x
@[simp] def rPn (x : Nat) : Ren := λ n => n - x

namespace Term

  namespace Ren
    def lift : Ren -> Ren
    | _, 0 => 0
    | σ, n + 1 => σ n + 1

    -- @[simp]
    -- def cvapply : Ren -> CvTerm -> CvTerm
    -- | σ, .sym t => .sym (cvapply σ t)
    -- | σ, .trans t1 t2 => .trans (cvapply σ t1) (cvapply σ t2)
    -- | _, .none => .none
    -- | _, .const => .const
    -- | σ, .bound k => .bound (σ k)
    -- | σ, .all_congr t1 t2 => .all_congr (cvapply σ t1) (cvapply (lift σ) t2)
    -- | σ, .lam_congr t1 t2 => .lam_congr (cvapply σ t1) (cvapply (lift σ) t2)
    -- | σ, .lam_eta t => .lam_eta (cvapply σ t)
    -- | σ, .lam_mf_erased t => .lam_mf_erased (cvapply (lift σ) t)
    -- | σ, .lam_m0_erased t => .lam_m0_erased (cvapply (lift σ) t)
    -- | σ, .app_congr t1 t2 => .app_congr (cvapply σ t1) (cvapply σ t2)
    -- | σ, .app_beta t => .app_beta (cvapply σ t)
    -- | σ, .app_m0_erased t => .app_m0_erased (cvapply σ t)
    -- | σ, .prod_congr t1 t2 => .prod_congr (cvapply σ t1) (cvapply (lift σ) t2)
    -- | σ, .pair_congr t1 t2 t3 => .pair_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    -- | σ, .pair_erased t => .pair_erased (cvapply σ t)
    -- | σ, .fst_congr t => .fst_congr (cvapply σ t)
    -- | σ, .fst_erased t => .fst_erased (cvapply σ t)
    -- | σ, .snd_congr t => .snd_congr (cvapply σ t)
    -- | σ, .snd_erased t => .snd_erased (cvapply σ t)
    -- | σ, .phi_congr t1 t2 t3 => .phi_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    -- | σ, .phi_erased t => .phi_erased (cvapply σ t)
    -- | σ, .eq_congr t1 t2 t3 => .eq_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    -- | σ, .refl_congr t => .refl_congr (cvapply σ t)
    -- | σ, .refl_erased t => .refl_erased (cvapply σ t)
    -- | σ, .subst_congr t1 t2 => .subst_congr (cvapply σ t1) (cvapply σ t2)
    -- | σ, .subst_erased t => .subst_erased (cvapply σ t)
    -- | σ, .conv_congr t1 t2 => .conv_congr (cvapply σ t1) (cvapply σ t2)
    -- | σ, .conv_erased t => .conv_erased (cvapply σ t)

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
    -- | σ, conv t1 t2 c => conv (apply σ t1) (apply σ t2) (cvapply σ c)
  end Ren

  namespace Subst
    def from_ren : Ren -> Subst T
    | σ, n => .rename (σ n)

    def cons : SubstAction T -> Subst T -> Subst T
    | t, _, 0 => t
    | _, σ, n + 1 => σ n

    -- def cvlift : Subst CvTerm -> Subst CvTerm
    -- | _, 0 => .rename 0
    -- | σ, n + 1 => match (σ n) with
    --   | .replace t => .replace (Ren.cvapply rS t)
    --   | .rename k => .rename (rS k)

    def lift : Subst Term -> Subst Term
    | _, 0 => .rename 0
    | σ, n + 1 => match (σ n) with
      | .replace t => .replace (Ren.apply rS t)
      | .rename k => .rename (rS k)

    -- @[simp]
    -- def cvapply : Subst CvTerm -> CvTerm -> CvTerm
    -- | σ, .sym t => .sym (cvapply σ t)
    -- | σ, .trans t1 t2 => .trans (cvapply σ t1) (cvapply σ t2)
    -- | _, .none => .none
    -- | _, .const => .const
    -- | σ, .bound k =>
    --   match σ k with
    --   | .replace t => t
    --   | .rename n => .bound n
    -- | σ, .all_congr t1 t2 => .all_congr (cvapply σ t1) (cvapply (cvlift σ) t2)
    -- | σ, .lam_congr t1 t2 => .lam_congr (cvapply σ t1) (cvapply (cvlift σ) t2)
    -- | σ, .lam_eta t => .lam_eta (cvapply σ t)
    -- | σ, .lam_mf_erased t => .lam_mf_erased (cvapply (cvlift σ) t)
    -- | σ, .lam_m0_erased t => .lam_m0_erased (cvapply (cvlift σ) t)
    -- | σ, .app_congr t1 t2 => .app_congr (cvapply σ t1) (cvapply σ t2)
    -- | σ, .app_beta t => .app_beta (cvapply σ t)
    -- | σ, .app_m0_erased t => .app_m0_erased (cvapply σ t)
    -- | σ, .prod_congr t1 t2 => .prod_congr (cvapply σ t1) (cvapply (cvlift σ) t2)
    -- | σ, .pair_congr t1 t2 t3 => .pair_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    -- | σ, .pair_erased t => .pair_erased (cvapply σ t)
    -- | σ, .fst_congr t => .fst_congr (cvapply σ t)
    -- | σ, .fst_erased t => .fst_erased (cvapply σ t)
    -- | σ, .snd_congr t => .snd_congr (cvapply σ t)
    -- | σ, .snd_erased t => .snd_erased (cvapply σ t)
    -- | σ, .phi_congr t1 t2 t3 => .phi_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    -- | σ, .phi_erased t => .phi_erased (cvapply σ t)
    -- | σ, .eq_congr t1 t2 t3 => .eq_congr (cvapply σ t1) (cvapply σ t2) (cvapply σ t3)
    -- | σ, .refl_congr t => .refl_congr (cvapply σ t)
    -- | σ, .refl_erased t => .refl_erased (cvapply σ t)
    -- | σ, .subst_congr t1 t2 => .subst_congr (cvapply σ t1) (cvapply σ t2)
    -- | σ, .subst_erased t => .subst_erased (cvapply σ t)
    -- | σ, .conv_congr t1 t2 => .conv_congr (cvapply σ t1) (cvapply σ t2)
    -- | σ, .conv_erased t => .conv_erased (cvapply σ t)

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
    | σ, conv t1 t2 c => conv (apply σ t1) (apply σ t2) c
    -- | σ, conv t1 t2 c => conv (apply σ t1) (apply σ t2) (cvapply ▸σ c)

    -- def cvcompose : Subst CvTerm -> Subst CvTerm -> Subst CvTerm
    -- | σ, τ, n => match (σ n) with
    --   | .replace t => .replace (cvapply τ t)
    --   | .rename k => τ k

    def compose : Subst Term -> Subst Term -> Subst Term
    | σ, τ, n => match (σ n) with
      | .replace t => .replace (apply τ t)
      | .rename k => τ k

  end Subst

end Term

@[simp] def I : Subst Term := λ n => .rename n
@[simp] def S : Subst Term := λ n => .rename (n + 1)
@[simp] def P : Subst Term := λ n => .rename (n - 1)
@[simp] def Sn (x : Nat) : Subst Term := λ n => .rename (n + x)
@[simp] def Pn (x : Nat) : Subst Term := λ n => .rename (n - x)

@[simp]
def beta : Term -> Subst Term
| t => Term.Subst.cons (.replace t) I

prefix:max "r#" => @Term.Subst.from_ren Term
-- prefix:max "cr#" => @Term.Subst.from_ren CvTerm
infix:70 "::" => Term.Subst.cons
prefix:max "^" => Term.Subst.lift
notation:1000 "^{" n "}" σ:90 => rep n Term.Subst.lift σ
-- prefix:max "^" => Term.Subst.cvlift
notation:90 "[" σ "]" t:89 => Term.Subst.apply σ t
-- notation:90 "[" σ "]" t:89 => Term.Subst.cvapply σ t
notation:90 τ:90 " ⊙ " σ:91 => Term.Subst.compose σ τ
-- notation:90 τ:90 " ⊙ " σ:91 => Term.Subst.cvcompose σ τ
notation:90 s:90 "β[" t "]" => Term.Subst.apply (beta t) s

namespace Term

  theorem I_to_rI : I = r#rI := by {
    funext
    case _ x =>
      cases x <;> unfold Subst.from_ren <;> simp
  }

  theorem S_to_rS : S = r#rS := by {
    funext
    case _ x =>
      cases x <;> unfold Subst.from_ren <;> simp
  }

  theorem P_to_rP : P = r#rP := by {
    funext
    case _ x =>
      cases x <;> unfold Subst.from_ren <;> simp
  }

  @[simp] theorem subst_from_ren_x : (r#r) x = .rename (r x) :=
    by unfold Subst.from_ren; rfl

  -- @[simp] theorem subst_from_cvren_x : (cr#r) x = .rename (r x) :=
  --   by unfold Subst.from_ren; rfl

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

  -- @[simp]
  -- theorem subst_cvlift_is_ren_cvlift r : cr#(Ren.lift r) = ^(cr#r) := by {
  --   funext; case _ x =>
  --   cases x
  --   case zero =>
  --     unfold Subst.from_ren; unfold Ren.lift; simp
  --     unfold Subst.cvlift; simp
  --   case _ n =>
  --     generalize lhsdef : (r#(Ren.lift r)) (n + 1) = lhs
  --     generalize rhsdef : (^(r#r)) (n + 1) = rhs
  --     unfold Subst.from_ren at lhsdef; simp at *
  --     unfold Ren.lift at lhsdef; simp at *
  --     unfold Subst.lift at rhsdef; simp at *
  --     subst lhsdef; subst rhsdef; rfl
  -- }

  -- @[simp]
  -- theorem subst_cvapply_is_ren_cvapply r t : Ren.cvapply r t = [cr#r]t := by {
  --   induction t generalizing r
  --   any_goals (unfold Ren.cvapply; simp [*])
  -- }

  -- @[simp]
  -- theorem subst_from_ren_transport_is_same : ▸(r#r) = cr#r := by {
  --   funext
  --   case _ x =>
  --     cases x
  --     all_goals (unfold Subst.from_ren; unfold subst_term_to_subst_cvterm; simp [*])
  -- }

  @[simp]
  theorem subst_apply_is_ren_apply r t : Ren.apply r t = [r#r]t := by {
    induction t generalizing r
    any_goals (unfold Ren.apply; simp [*])
  }

  -- @[simp]
  -- theorem subst_cvapply_I_is_id s : [cr#rI]s = s := by {
  --   have lem : ^(cr# rI) = cr# rI := by {
  --     funext
  --     case _ x =>
  --     cases x
  --     case _ =>
  --       unfold Subst.cvlift; simp
  --     case _ x =>
  --       unfold Subst.cvlift; simp
  --   }
  --   induction s
  --   all_goals unfold Subst.cvapply
  --   any_goals simp [*]
  -- }

  -- @[simp]
  -- theorem subst_transform_subst_I_is_crI : ▸I = cr#rI := by sorry

  @[simp]
  theorem subst_apply_I_is_id {s : Term} : [I]s = s := by {
    have lem : ^I = I := by {
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

  -- theorem subst_transform_ren_apply_commutes : .refl ([r#r]t) = [cr#r] (.refl t) := by {
  --   induction t generalizing r
  --   all_goals simp [*]
  --   case lam m t1 t2 ih1 ih2 => rw [<-subst_cvlift_is_ren_cvlift, <-subst_lift_is_ren_lift, ih2]
  --   case all m t1 t2 ih1 ih2 => rw [<-subst_cvlift_is_ren_cvlift, <-subst_lift_is_ren_lift, ih2]
  --   case prod t1 t2 ih1 ih2 => rw [<-subst_cvlift_is_ren_cvlift, <-subst_lift_is_ren_lift, ih2]
  -- }

  -- @[simp]
  -- theorem subst_transform_lift_commutes : ▸^σ = ^▸σ := by {
  --   funext
  --   case _ x =>
  --   unfold subst_term_to_subst_cvterm; unfold Subst.lift; unfold Subst.cvlift; simp
  --   cases x
  --   case _ => simp
  --   case _ n =>
  --     simp
  --     cases σ n
  --     case _ => simp
  --     case _ t =>
  --       simp; rw [subst_transform_ren_apply_commutes]
  -- }

  -- theorem subst_transform_apply_commutes : .refl ([σ]t) = [▸σ](.refl t) := by {
  --   induction t generalizing σ
  --   all_goals simp [*]
  --   case bound k i =>
  --     unfold subst_term_to_subst_cvterm; simp
  --     cases σ i
  --     case _ j => simp
  --     case _ s => simp
  -- }

  -- @[simp]
  -- theorem subst_transform_commutes_with_compose : ▸(σ ⊙ τ) = ▸σ ⊙ ▸τ := by {
  --   funext
  --   case _ x =>
  --   unfold subst_term_to_subst_cvterm; unfold Subst.compose; unfold Subst.cvcompose; simp
  --   cases (τ x)
  --   case _ x => simp
  --   case _ t =>
  --     simp; rw [subst_transform_apply_commutes]
  --     unfold subst_term_to_subst_cvterm; simp
  -- }

  -- @[simp]
  -- theorem subst_transform_commutes_with_cons_rename : ▸(.rename k :: σ) = .rename k :: ▸σ := by {
  --   funext
  --   case _ x =>
  --     unfold subst_term_to_subst_cvterm
  --     cases x <;> simp [*]
  -- }

  -- @[simp]
  -- theorem subst_transform_commutes_with_cons_replace : ▸(.replace t :: σ) = .replace (.refl t) :: ▸σ := by {
  --   funext
  --   case _ x =>
  --     unfold subst_term_to_subst_cvterm
  --     cases x <;> simp [*]
  -- }

  -- @[simp]
  -- theorem subst_cvapply_twice_is_cvapply_compose {s : CvTerm} {σ τ} : [τ][σ]s = [τ ⊙ σ]s := by {
  --   have lem1 τ : ^τ ⊙ cr#rS = cr#rS ⊙ τ := by {
  --     funext
  --     unfold Subst.cvcompose; unfold Subst.from_ren; unfold rS; simp
  --     unfold Subst.cvlift; unfold rS; simp
  --     unfold Subst.from_ren; simp
  --   }
  --   have lem2 (σ:Subst CvTerm) e : ^(σ ⊙ cr#e) = ^σ ⊙ ^(cr#e) := by {
  --     funext; case _ n =>
  --     cases n
  --     . unfold Subst.from_ren; unfold Subst.cvcompose; unfold Subst.cvlift; simp
  --     case _ n =>
  --       generalize lhsdef : (^σ ⊙ ^(cr#e)) (n + 1) = lhs
  --       unfold Subst.cvlift; simp
  --       unfold Subst.cvcompose; unfold Subst.from_ren; unfold rS; simp
  --       subst lhs; unfold Subst.cvcompose; unfold Subst.cvlift; simp
  --       unfold Subst.from_ren; unfold rS; simp
  --   }
  --   have lem3 σ e s : [σ][cr#e]s = [σ ⊙ cr#e]s := by {
  --     induction s generalizing σ e
  --     any_goals simp [*]
  --     case bound => unfold Subst.cvcompose; simp
  --     case all_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih]
  --     case lam_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih]
  --     case lam_mf_erased _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih]
  --     case lam_m0_erased _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih]
  --     case prod_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih]
  --   }
  --   have lem4 σ τ : σ ⊙ τ ⊙ cr#rS = σ ⊙ (τ ⊙ cr#rS) := by {
  --     funext; case _ x =>
  --     cases x
  --     any_goals (unfold Subst.cvcompose; unfold Subst.from_ren; unfold rS; simp)
  --   }
  --   have lem5 r1 r2 τ : cr#r1 ⊙ (cr#r2 ⊙ τ) = cr#r1 ⊙ cr#r2 ⊙ τ := by {
  --     funext; case _ x =>
  --       unfold Subst.cvcompose; simp
  --       cases τ x <;> simp at *
  --       case _ t =>
  --         have lem : [fun x => SubstAction.rename (r1 (r2 x))]t = [cr#r1 ⊙ cr#r2]t := by {
  --           unfold Subst.cvcompose; simp
  --         }
  --         rw [lem, lem3]
  --   }
  --   have lem6 e τ : ^(cr#e) ⊙ ^τ = ^(cr#e ⊙ τ) := by {
  --     funext; case _ n =>
  --     cases n
  --     . unfold Subst.cvcompose; unfold Subst.cvlift; simp
  --     case _ n =>
  --       have lem : ((^(cr#e) ⊙ ^τ) ⊙ cr#rS) n = (^(cr#e ⊙ τ) ⊙ cr#rS) n := by {
  --         rw [lem1, lem4, lem1]
  --         rw [<-subst_cvlift_is_ren_cvlift, lem5]; simp
  --         rw [lem1, lem5]
  --       }
  --       unfold Subst.cvcompose at lem; unfold rS at lem; unfold Subst.from_ren at lem
  --       unfold Subst.cvcompose; unfold Subst.from_ren
  --       simp at lem; simp [*]
  --   }
  --   have lem7 τ e s : [cr#e][τ]s = [cr#e ⊙ τ]s := by {
  --     induction s generalizing τ e
  --     any_goals simp [*]
  --     case bound k =>
  --       unfold Subst.cvcompose; simp
  --       cases τ k <;> simp at *
  --     case all_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih, <-lem6]; simp
  --     case lam_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih, <-lem6]; simp
  --     case lam_mf_erased _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih, <-lem6]; simp
  --     case lam_m0_erased _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih, <-lem6]; simp
  --     case prod_congr _ _ _ ih => rw [<-subst_cvlift_is_ren_cvlift, ih, <-lem6]; simp
  --   }
  --   have lem8 σ τ : σ ⊙ (cr#rS ⊙ τ) = σ ⊙ cr#rS ⊙ τ := by {
  --     funext; case _ x =>
  --       unfold Subst.cvcompose; simp
  --       cases τ x <;> simp at *
  --       rw [lem3]; unfold Subst.cvcompose; simp
  --   }
  --   have lem9 σ τ : cr#rS ⊙ (σ ⊙ τ) = cr#rS ⊙ σ ⊙ τ := by {
  --     funext; case _ x =>
  --       unfold Subst.cvcompose; simp
  --       cases τ x <;> simp at *
  --       rw [lem7]; unfold Subst.cvcompose; simp
  --   }
  --   have lem10 (σ τ : Subst CvTerm) : ^σ ⊙ ^τ = ^(σ ⊙ τ) := by {
  --     funext; case _ x =>
  --     cases x
  --     case _ => unfold Subst.cvcompose; unfold Subst.cvlift; simp
  --     case _ n =>
  --       have lem : ((^σ ⊙ ^τ) ⊙ cr#rS) n = (^(σ ⊙ τ) ⊙ cr#rS) n := by {
  --         rw [lem1, lem4, lem1, lem8, lem1, lem9]
  --       }
  --       unfold Subst.cvcompose at lem; unfold rS at lem; unfold Subst.from_ren at lem
  --       unfold Subst.cvcompose
  --       simp at lem; simp [*]
  --   }
  --   induction s generalizing τ σ
  --   any_goals simp [*]
  --   case bound k =>
  --     unfold Subst.cvcompose; simp
  --     cases σ k <;> simp
  -- }

  @[simp]
  theorem subst_apply_compose_commute {s : Term} {σ τ} : [τ][σ]s = [τ ⊙ σ]s := by {
    have lem1 τ : ^τ ⊙ r#rS = r#rS ⊙ τ := by {
      funext
      unfold Subst.compose; unfold Subst.from_ren; unfold rS; simp
      unfold Subst.lift; unfold rS; simp
      unfold Subst.from_ren; simp
    }
    have lem2 (σ:Subst Term) e : ^(σ ⊙ r#e) = ^σ ⊙ ^(r#e) := by {
      funext; case _ n =>
      cases n
      . unfold Subst.from_ren; unfold Subst.compose; unfold Subst.lift; simp
      case _ n =>
        generalize lhsdef : (^σ ⊙ ^(r#e)) (n + 1) = lhs
        unfold Subst.lift; simp
        unfold Subst.compose; unfold Subst.from_ren; unfold rS; simp
        subst lhs; unfold Subst.compose; unfold Subst.lift; simp
        unfold Subst.from_ren; unfold rS; simp
    }
    have lem3 σ e s : [σ][r#e]s = [σ ⊙ r#e]s := by {
      induction s generalizing σ e
      any_goals simp [*]
      case bound => unfold Subst.compose; simp
      case lam _ _ _ ih => rw [<-subst_lift_is_ren_lift, ih]
      case all _ _ _ ih => rw [<-subst_lift_is_ren_lift, ih]
      case prod _ _ _ ih => rw [<-subst_lift_is_ren_lift, ih]
    }
    have lem4 σ τ : σ ⊙ τ ⊙ r#rS = σ ⊙ (τ ⊙ r#rS) := by {
      funext; case _ x =>
      cases x
      any_goals (unfold Subst.compose; unfold Subst.from_ren; unfold rS; simp)
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
        have lem : ((^(r#e) ⊙ ^τ) ⊙ r#rS) n = (^(r#e ⊙ τ) ⊙ r#rS) n := by {
          rw [lem1, lem4, lem1]
          rw [<-subst_lift_is_ren_lift, lem5]; simp
          rw [lem1, lem5]
        }
        unfold Subst.compose at lem; unfold rS at lem; unfold Subst.from_ren at lem
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
    have lem8 σ τ : σ ⊙ (r#rS ⊙ τ) = σ ⊙ r#rS ⊙ τ := by {
      funext; case _ x =>
        unfold Subst.compose; simp
        cases τ x <;> simp at *
        rw [lem3]; unfold Subst.compose; simp
    }
    have lem9 σ τ : r#rS ⊙ (σ ⊙ τ) = r#rS ⊙ σ ⊙ τ := by {
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
        have lem : ((^σ ⊙ ^τ) ⊙ r#rS) n = (^(σ ⊙ τ) ⊙ r#rS) n := by {
          rw [lem1, lem4, lem1, lem8, lem1, lem9]
        }
        unfold Subst.compose at lem; unfold rS at lem; unfold Subst.from_ren at lem
        unfold Subst.compose
        simp at lem; simp [*]
    }
    induction s generalizing τ σ
    any_goals simp [*]
    case bound k =>
      unfold Subst.compose; simp
      cases σ k <;> simp
  }


  theorem subst_valid1 : s β[t] = [.replace t :: I]s
  := by simp

  @[simp] -- 0[s.σ ] = s
  theorem subst_valid2_replace
    : [.replace s :: σ]bound c 0 = s
  := by unfold Subst.cons; simp

  @[simp] -- 0[s.σ ] = s
  theorem subst_valid2_rename
    : [.rename k :: σ]bound c 0 = bound c k
  := by unfold Subst.cons; simp

  -- @[simp]
  -- theorem cvsubst_valid2_replace
  --   : [.replace s :: σ]CvTerm.bound 0 = s
  -- := by unfold Subst.cons; simp

  -- @[simp]
  -- theorem cvsubst_valid2_rename
  --   : [.rename k :: σ]CvTerm.bound 0 = CvTerm.bound k
  -- := by unfold Subst.cons; simp

  @[simp] -- ⇑σ = 0.(σ ◦ S)
  theorem subst_valid3 {σ : Subst Term} : ^σ = .rename 0 :: (S ⊙ σ) := by {
    funext; case _ x =>
      unfold Subst.lift; simp
      unfold Subst.compose; simp
      unfold S; unfold Subst.from_ren; simp
      cases x
      case _ => simp
      case _ n => simp
  }

  -- @[simp]
  -- theorem cvsubst_valid3 {σ : Subst CvTerm} : ^σ = .rename 0 :: (S ⊙ σ) := by {
  --   funext; case _ x =>
  --     unfold Subst.cvlift; simp
  --     unfold Subst.cvcompose; simp
  --     unfold S; unfold Subst.from_ren; simp
  --     cases x
  --     case _ => simp
  --     case _ n => simp
  -- }

  @[simp] -- 0.S = I
  theorem subst_valid4 : .rename 0 :: S = I := by {
    funext; case _ x =>
    cases x
    case _ =>
      unfold Subst.cons; unfold S; simp
    case _ n =>
      unfold Subst.cons; unfold S; simp
  }

  -- @[simp]
  -- theorem cvsubst_valid4 : .rename 0 :: S = @I CvTerm := by {
  --   funext; case _ x =>
  --   cases x
  --   case _ =>
  --     unfold Subst.cons; unfold S; simp
  --   case _ n =>
  --     unfold Subst.cons; unfold S; simp
  -- }

  @[simp] -- σ ◦ I = σ
  theorem subst_valid5 {σ : Subst Term} : σ ⊙ I = σ := by {
    funext; case _ x =>
    unfold Subst.compose; unfold I; simp
  }

  -- @[simp]
  -- theorem cvsubst_valid5 {σ : Subst CvTerm} : σ ⊙ I = σ := by {
  --   funext; case _ x =>
  --   unfold Subst.cvcompose; unfold I; simp
  -- }

  @[simp] -- I ◦ σ = σ
  theorem subst_valid6 {σ : Subst Term} : I ⊙ σ = σ := by {
    funext; case _ x =>
    unfold Subst.compose; simp
    cases x
    all_goals (split; simp [*])
    case _ _ _ e => rw [e]
    case _ _ _ e => rw [e]
  }

  -- @[simp]
  -- theorem cvsubst_valid6 {σ : Subst CvTerm} : I ⊙ σ = σ := by {
  --   funext; case _ x =>
  --   unfold Subst.cvcompose; simp
  --   cases x
  --   all_goals (split; simp [*])
  --   case _ _ _ e => rw [e]
  --   case _ _ _ e => rw [e]
  -- }

  @[simp] -- (σ ◦ τ) ◦ μ = σ ◦ (τ ◦ μ)
  theorem subst_valid7 {σ : Subst Term} : σ ⊙ (τ ⊙ μ) = σ ⊙ τ ⊙ μ := by {
    funext; case _ x =>
      unfold Subst.compose; simp
      cases μ x <;> simp
      . unfold Subst.compose; simp
  }

  -- @[simp]
  -- theorem cvsubst_valid7 {σ : Subst CvTerm} : σ ⊙ (τ ⊙ μ) = σ ⊙ τ ⊙ μ := by {
  --   funext; case _ x =>
  --     unfold Subst.cvcompose; simp
  --     cases μ x <;> simp
  --     . unfold Subst.cvcompose; simp
  -- }

  @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
  theorem subst_valid8_replace {s : Term}
    : τ ⊙ (.replace s :: σ) = .replace ([τ]s) :: (τ ⊙ σ)
  := by {
    funext; case _ x =>
    cases x
    all_goals (unfold Subst.compose; unfold Subst.cons; simp)
  }

  -- @[simp]
  -- theorem cvsubst_valid8_replace {s : CvTerm}
  --   : τ ⊙ (.replace s :: σ) = .replace ([τ]s) :: (τ ⊙ σ)
  -- := by {
  --   funext; case _ x =>
  --   cases x
  --   all_goals (unfold Subst.cvcompose; unfold Subst.cons; simp)
  -- }

  @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
  theorem subst_valid8_rename {σ : Subst Term}
    : τ ⊙ (.rename s :: σ) = (τ s) :: (τ ⊙ σ)
  := by {
    funext; case _ x =>
    cases x
    all_goals (unfold Subst.compose; unfold Subst.cons; simp)
  }

  -- @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
  -- theorem cvsubst_valid8_rename {σ : Subst CvTerm}
  --   : τ ⊙ (.rename s :: σ) = (τ s) :: (τ ⊙ σ)
  -- := by {
  --   funext; case _ x =>
  --   cases x
  --   all_goals (unfold Subst.cvcompose; unfold Subst.cons; simp)
  -- }

  @[simp] -- S ◦ (s.σ ) = σ
  theorem subst_valid9 : (s :: σ) ⊙ S = σ := by {
    funext; case _ x =>
    cases x
    all_goals {
      unfold Subst.compose; unfold Subst.cons; unfold S; simp
    }
  }

  -- @[simp]
  -- theorem cvsubst_valid9 : (s :: σ) ⊙ cr#S = σ := by {
  --   funext; case _ x =>
  --   cases x
  --   all_goals {
  --     unfold Subst.cvcompose; unfold Subst.cons; unfold Subst.from_ren
  --     unfold S; simp
  --   }
  -- }

  @[simp] -- 0[σ ].(S ◦ σ ) = σ
  theorem subst_valid10 : σ 0 :: (σ ⊙ S) = σ := by {
    funext
    case _ x =>
      cases x
      case _ =>
        simp
      case _ =>
        simp; unfold S; unfold Subst.compose; simp
  }

  @[simp]
  theorem liftn_I : ^{n}I = I := by {
    induction n <;> simp
    case _ x ih =>
      rw [ih]; simp
  }

  @[simp]
  theorem liftn_unfold : ^{n+1}σ = ^(^{n}σ) := by {
    simp
  }

  @[simp]
  theorem liftn_compose : ^{n}(σ ⊙ τ) = (^{n}σ) ⊙ (^{n}τ) := by {
    induction n
    case _ => simp
    case _ n ih => simp; rw [ih]; simp
  }

  @[simp]
  theorem Sn_0_is_I : Sn 0 = I := by
  funext
  case _ x =>
    cases x <;> simp

  @[simp]
  theorem Sn_bound : [Sn n](bound K m) = bound K (m + n) := by {
    simp
  }

  @[simp]
  theorem Sn_succ : Sn (n + 1) = S ⊙ Sn n := by {
    funext
    case _ x =>
      cases x
      all_goals (simp; unfold Sn; unfold S; unfold Subst.compose; simp)
      case _ => omega
  }

  @[simp]
  theorem liftn_beta_eq a K : x = n -> [^{n}(beta a)](bound K x) = [Sn n]a := by
    intro h
    induction n generalizing x
    case _ =>
      simp; cases x <;> simp
      case _ => exfalso; omega
    case _ n h2 =>
      subst h; simp
      generalize σdef : rep n Subst.lift (SubstAction.replace a::I) = σ
      unfold Subst.compose; simp
      generalize bdef : σ n = b at *
      cases b
      case _ y =>
        simp at *; rw [σdef, bdef] at h2; simp at h2
        have h3 : [S](bound K y) = [S][Sn n]a := by rw [h2]
        simp at h3; rw [h3]; unfold S; unfold Sn; unfold Subst.compose
        simp
      case _ t =>
        simp at *; rw [σdef, bdef] at h2; simp at h2
        rw [h2]; unfold S; unfold Sn; simp; unfold Subst.compose; simp

  @[simp]
  theorem liftn_beta_lt a K : x < n -> [^{n}(beta a)](bound K x) = bound K x := by
    intro h
    induction n generalizing x
    case _ =>
      simp; cases x <;> simp
      all_goals exfalso; omega
    case _ n ih =>
      simp; generalize σdef : rep n Subst.lift (SubstAction.replace a::I) = σ
      unfold Subst.compose; simp
      cases x <;> simp
      case _ x =>
        generalize bdef : σ x = b at *
        cases b <;> simp
        case _ y =>
          replace h : x < n := by omega
          replace ih := ih h
          simp at ih; rw [σdef, bdef] at ih; simp at ih
          exact ih
        case _ t =>
          replace h : x < n := by omega
          replace ih := ih h
          simp at ih; rw [σdef, bdef] at ih; simp at ih
          subst ih; simp

  @[simp]
  theorem liftn_beta_gt a K : x > n -> [^{n}(beta a)](bound K x) = bound K (x - 1) := by
    intro h
    induction n generalizing x
    case _ =>
      simp; cases x <;> simp
      case _ => exfalso; omega
    case _ n ih =>
      simp; generalize σdef : rep n Subst.lift (SubstAction.replace a::I) = σ
      unfold Subst.compose; simp
      cases x <;> simp
      case _ x =>
        generalize bdef : σ x = b at *
        cases b <;> simp
        case _ y =>
          replace h : x > n := by omega
          replace ih := ih h
          simp at ih; rw [σdef, bdef] at ih; simp at ih
          cases x
          case _ => exfalso; omega
          case _ x => simp at ih; omega
        case _ t =>
          replace h : x > n := by omega
          replace ih := ih h
          simp at ih; rw [σdef, bdef] at ih; simp at ih
          rw [ih]; simp
          cases x
          case _ => exfalso; omega
          case _ => simp

  -- (βst)[σ ] = β(s[⇑σ ])(t[σ ])
  theorem subst_beta_distr : [σ](s β[t]) = ([^σ]s) β[ [σ]t ] := by simp

  -- s[σ ][S] = s[S][⇑σ ]
  theorem subst_rw_ex1 : [S][σ]s = [^σ][S]s := by simp
  -- -- s[⇑σ ][t.I] = s[t.σ ]
  theorem subst_rw_ex2 : [t::I][^σ]s = [t::σ]s := by simp
  -- s[⇑σ ][t[σ ].I] = s[t.I][σ ]
  theorem subst_rw_ex3 : [(.replace ([σ]t))::I][^σ]s = [σ][.replace t::I]s := by simp

  -- -- s[σ ][S] = s[S][⇑σ ]
  -- theorem cvsubst_rw_ex1 : [cr#S][σ]s = [^σ][cr#S]s := by simp
  -- -- -- s[⇑σ ][t.I] = s[t.σ ]
  -- theorem cvsubst_rw_ex2 : [t::cr#I][^σ]s = [t::σ]s := by simp
  -- -- s[⇑σ ][t[σ ].I] = s[t.I][σ ]
  -- theorem cvsubst_rw_ex3 : [(.replace ([σ]t))::cr#I][^σ]s = [σ][.replace t::cr#I]s := by simp

  @[simp]
  def mode_to_sort : Mode -> Const
  | mt => .kind
  | mf => .type
  | m0 => .type

  @[simp]
  def eta : Mode -> Term -> Term -> Term
  | m, A, t => lam m A (app m ([S]t) (bound (mode_to_sort m) 0))

  @[simp high]
  theorem P_after_S : (P ⊙ S) n = .rename n := by {
    cases n
    case _ => unfold Subst.compose; simp
    case _ x => unfold Subst.compose; simp
  }

  @[simp high]
  theorem P_after_S_subst : [P ⊙ S]t = t := by {
    induction t <;> simp [*]
    case lam t1 t2 ih1 _ih2 =>
      unfold Subst.compose; simp
      have lem : [.rename 0 :: S]t2 = t2 := by simp
      unfold S at lem; rw [lem]
    case all t1 t2 ih1 _ih2 =>
      unfold Subst.compose; simp
      have lem : [.rename 0 :: S]t2 = t2 := by simp
      unfold S at lem; rw [lem]
    case prod t1 t2 ih1 _ih2 =>
      unfold Subst.compose; simp
      have lem : [.rename 0 :: S]t2 = t2 := by simp
      unfold S at lem; rw [lem]
  }

  @[simp high]
  theorem P_lift_n_after_S_lift_n : ((^{n}P) ⊙ ^{n}S) x = .rename x := by
  induction n generalizing x <;> simp
  case _ n ih =>
    generalize σdef : rep n Subst.lift P ⊙ rep n Subst.lift S = σ at *
    rw [<-subst_valid7, σdef]
    cases x <;> simp
    case _ x =>
      unfold Subst.compose; simp; rw [ih]

  @[simp high]
  theorem P_lift_n_after_S_lift_n_subst : [(^{n}P) ⊙ ^{n}S]t = t := by
  induction t generalizing n <;> simp [*]
  case lam t1 t2 ih1 ih2 =>
    have ih2' := @ih2 (n + 1)
    simp at ih2'; rw [ih2']
  case all t1 t2 ih1 ih2 =>
    have ih2' := @ih2 (n + 1)
    simp at ih2'; rw [ih2']
  case prod t1 t2 ih1 ih2 =>
    have ih2' := @ih2 (n + 1)
    simp at ih2'; rw [ih2']

  @[simp]
  theorem S_after_Pn : (S ⊙ (Pn n)) (n + k) = .rename (k + 1) := by {
    cases n
    case _ => unfold Subst.compose; simp
    case _ n => unfold Subst.compose; simp; omega
  }

  @[simp]
  theorem S_after_Pn_1 : (S ⊙ (Pn 1)) 1 = .rename 1 := by {
    unfold Subst.compose; simp
  }

  theorem rep_n_P_lt : n < x -> rep n Subst.lift P x = .rename (x - 1) := by
  intro h
  induction n generalizing x <;> simp
  case _ n ih =>
    cases x <;> simp
    case _ x =>
      unfold Subst.compose; simp
      have nh : n < x := by omega
      rw [ih nh]; simp
      cases x <;> simp at *

  theorem rep_n_P_ge : n ≥ x -> rep n Subst.lift P x = .rename x := by
  intro h
  induction n generalizing x <;> simp
  case _ => omega
  case _ n ih =>
    cases x <;> simp
    case _ x =>
      have nh : n ≥ x := by omega
      unfold Subst.compose; simp
      rw [ih nh]

  theorem rep_n_S_le : n ≤ x -> rep n Subst.lift S x = .rename (x + 1) := by
  intro h
  induction n generalizing x <;> simp
  case _ n ih =>
    cases x <;> simp
    case _ => omega
    case _ x =>
      unfold Subst.compose; simp
      have nh : n ≤ x := by omega
      rw [ih nh]

  theorem rep_n_S_gt : n > x -> rep n Subst.lift S x = .rename x := by
  intro h
  induction n generalizing x <;> simp
  case _ => omega
  case _ n ih =>
    cases x <;> simp
    case _ x =>
      have nh : n > x := by omega
      unfold Subst.compose; simp
      rw [ih nh]

  theorem rep_n_S_exists : ∃ y, rep n Subst.lift S x = .rename y := by
  cases (Nat.decLe n x)
  case _ h =>
    cases (Nat.decLt x n)
    case _ h2 => omega
    case _ h2 => exists x; apply rep_n_S_gt h2
  case _ h => exists (x + 1); apply rep_n_S_le h

  theorem n_not_in_lift_S (t : Term) : ¬ (n ∈ ([^{n}S]t)) := by
  intro h
  induction t generalizing n <;> simp at h
  case bound K x =>
    cases (Nat.decLe n x)
    case _ h2 =>
      cases (Nat.decLt x n)
      case _ h3 => omega
      case _ h3 =>
        rw [rep_n_S_gt h3] at h; simp at h
        cases h; omega
    case _ h2 =>
      rw [rep_n_S_le h2] at h; simp at h
      cases h; omega
  case none => cases h
  case const => cases h
  case lam t1 t2 ih1 ih2 =>
    cases h
    case _ h => apply ih1 h
    case _ h =>
      have lem : (n + 1) ∈ ([^{n + 1}S]t2) := by simp; exact h
      apply ih2 lem
  case app t1 t2 ih1 ih2 =>
    cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
  case all t1 t2 ih1 ih2 =>
    cases h
    case _ h => apply ih1 h
    case _ h =>
      have lem : (n + 1) ∈ ([^{n + 1}S]t2) := by simp; exact h
      apply ih2 lem
  case pair t1 t2 t3 ih1 ih2 ih3 =>
    cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
    case _ h => apply ih3 h
  case fst t ih =>
    cases h
    case _ h => apply ih h
  case snd t ih =>
    cases h
    case _ h => apply ih h
  case prod t1 t2 ih1 ih2 =>
    cases h
    case _ h => apply ih1 h
    case _ h =>
      have lem : (n + 1) ∈ ([^{n + 1}S]t2) := by simp; exact h
      apply ih2 lem
  case refl t ih =>
    cases h
    case _ h => apply ih h
  case subst t1 t2 ih1 ih2 =>
    cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
  case phi t1 t2 t3 ih1 ih2 ih3 =>
    cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
    case _ h => apply ih3 h
  case eq t1 t2 t3 ih1 ih2 ih3 =>
    cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
    case _ h => apply ih3 h
  case conv t1 t2 _ ih1 ih2 =>
    cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h

  @[simp]
  theorem zero_not_in_S {t : Term} : ¬ (0 ∈ ([S]t)) := by
  have lem := @n_not_in_lift_S 0 t
  simp at lem; exact lem

  @[simp]
  theorem S_on_bound : [S](.bound K n) = .bound K (n + 1) := by
  unfold S; unfold Subst.apply; simp

  theorem rS_injective : ∀ x y, rS x = rS y -> x = y := by
  intro x y h
  induction x
  case _ =>
    cases y <;> simp at h; simp
  case _ x ih =>
    cases y <;> simp at h
    case _ y =>
      subst h; simp

  theorem rename_injective_lift r :
    (∀ x y, r x = r y -> x = y) ->
    ∀ x y, Ren.lift r x = Ren.lift r y -> x = y
  := by
  intro h1 x y h2
  induction x generalizing r y
  case _ =>
    cases y <;> simp at *
    case _ y => unfold Ren.lift at h2; simp at h2
  case _ x ih =>
    cases y <;> simp at *
    case _ => unfold Ren.lift at h2; simp at h2
    case _ y =>
      unfold Ren.lift at h2; simp at h2
      apply ih r h1
      replace h2 := h1 x y h2
      subst h2; rfl

  theorem rename_injective r :
    (∀ x y, r x = r y -> x = y) ->
    [r#r]t = [r#r]s ->
    t = s
  := by
  intro rinj h
  induction t generalizing s r
  case bound K x =>
    simp at h
    cases s <;> simp at h
    case _ K' x' =>
      rw [h.1, rinj x x' h.2]
  case none => cases s <;> simp at h; simp
  case const => cases s <;> simp at h; simp [*]
  case lam m t1 t2 ih1 ih2 =>
    cases s <;> simp at h
    case _ m' r1 r2 =>
      rw [h.1, ih1 r rinj h.2.1]
      have rlinj := rename_injective_lift r rinj
      replace ih2 := @ih2 r2 (Ren.lift r) rlinj
      simp at ih2; rw [ih2 h.2.2]
  case app m t1 t2 ih1 ih2 =>
    cases s <;> simp at h
    case _ m' r1 r2 =>
      rw [h.1, ih1 r rinj h.2.1, ih2 r rinj h.2.2]
  case all m t1 t2 ih1 ih2 =>
    cases s <;> simp at h
    case _ m' r1 r2 =>
      rw [h.1, ih1 r rinj h.2.1]
      have rlinj := rename_injective_lift r rinj
      replace ih2 := @ih2 r2 (Ren.lift r) rlinj
      simp at ih2; rw [ih2 h.2.2]
  case pair t1 t2 t3 ih1 ih2 ih3 =>
    cases s <;> simp at h
    case _ r1 r2 r3 =>
      rw [ih1 r rinj h.1, ih2 r rinj h.2.1, ih3 r rinj h.2.2]
  case fst t ih =>
    cases s <;> simp at h
    case _ r1 =>
      rw [ih r rinj h]
  case snd t ih =>
    cases s <;> simp at h
    case _ r1 =>
      rw [ih r rinj h]
  case prod t1 t2 ih1 ih2 =>
    cases s <;> simp at h
    case _ r1 r2 =>
      rw [ih1 r rinj h.1]
      have rlinj := rename_injective_lift r rinj
      replace ih2 := @ih2 r2 (Ren.lift r) rlinj
      simp at ih2; rw [ih2 h.2]
  case refl t ih =>
    cases s <;> simp at h
    case _ r1 =>
      rw [ih r rinj h]
  case subst t1 t2 ih1 ih2 =>
    cases s <;> simp at h
    case _ r1 r2 =>
      rw [ih1 r rinj h.1, ih2 r rinj h.2]
  case phi t1 t2 t3 ih1 ih2 ih3 =>
    cases s <;> simp at h
    case _ r1 r2 r3 =>
      rw [ih1 r rinj h.1, ih2 r rinj h.2.1, ih3 r rinj h.2.2]
  case eq t1 t2 t3 ih1 ih2 ih3 =>
    cases s <;> simp at h
    case _ r1 r2 r3 =>
      rw [ih1 r rinj h.1, ih2 r rinj h.2.1, ih3 r rinj h.2.2]
  case conv t1 t2 t3 ih1 ih2 =>
    cases s <;> simp at h
    case _ r1 r2 r3 =>
      rw [ih1 r rinj h.1, ih2 r rinj h.2.1, h.2.2]

  -- theorem rename_injective_liftn n r :
  --   (∀ x y, r x = r y -> x = y) ->
  --   [^{n}r#r]t = [^{n}r#r]s ->
  --   t = s
  -- := by sorry

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
