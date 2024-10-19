
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold

namespace Cedille

  @[simp] lemma shift_bind
    : shift (Syntax.bind k t1 t2) a c = Syntax.bind k (shift t1 a c) (shift t2 a (Nat.succ c))
  := by congr
  @[simp] lemma shift_ctor
    : shift (Syntax.ctor k t1 t2 t3) a c = Syntax.ctor k (shift t1 a c) (shift t2 a c) (shift t3 a c)
  := by congr

  @[simp] lemma shift_const : shift (const c) a c' = const c := by congr
  @[simp] lemma shift_bound
    : shift (bound j) a c = if j < c then bound j else bound (j + a)
  := by congr
  @[simp] lemma shift_free : shift (free x) a c = free x := by congr

  @[simp] lemma shift_typeu : shift typeu a c = typeu := by congr
  @[simp] lemma shift_kindu : shift kindu a c = kindu := by congr
  @[simp] lemma shift_lam : shift (lam m t1 t2) a c = lam m (shift t1 a c) (shift t2 a (Nat.succ c)) := by congr
  @[simp] lemma shift_pi : shift (pi m t1 t2) a c = pi m (shift t1 a c) (shift t2 a (Nat.succ c)) := by congr
  @[simp] lemma shift_inter : shift (inter t1 t2) a c = inter (shift t1 a c) (shift t2 a (Nat.succ c)) := by congr
  @[simp] lemma shift_app : shift (app m t1 t2) a c = app m (shift t1 a c) (shift t2 a c) := by congr
  @[simp] lemma shift_pair : shift (pair t1 t2 t3) a c = pair (shift t1 a c) (shift t2 a c) (shift t3 a c)
    := by congr
  @[simp] lemma shift_fst : shift (proj p t) a c = proj p (shift t a c) := by congr
  @[simp] lemma shift_eq : shift (eq t1 t2 t3) a c = eq (shift t1 a c) (shift t2 a c) (shift t3 a c) := by congr
  @[simp] lemma shift_refl : shift (refl t) a c = refl (shift t a c) := by congr
  @[simp] lemma shift_Jh : shift (subst t1 t2) a c = subst (shift t1 a c) (shift t2 a c) := by congr
  @[simp] lemma shift_promote : shift (promote t) a c = promote (shift t a c) := by congr
  @[simp] lemma shift_delta : shift (delta t) a c = delta (shift t a c) := by congr
  @[simp] lemma shift_phi : shift (phi t1 t2) a c = phi (shift t1 a c) (shift t2 a c)
    := by congr

  @[simp] lemma opn_const : [i := v](const c) = const c := by congr
  @[simp] lemma opn_free : [i := v](free x) = free x := by congr
  @[simp] lemma opn_bound
    : [i := v](bound j) = if j == i then v else bound j
  := by congr

  @[simp] lemma opn_typeu : [i := v]typeu = typeu := by congr
  @[simp] lemma opn_kindu : [i := v]kindu = kindu := by congr
  @[simp] lemma opn_lam : [i := v]lam m t1 t2 = lam m ([i := v]t1) ([Nat.succ i := v]t2) := by congr
  @[simp] lemma opn_pi : [i := v]pi m t1 t2 = pi m ([i := v]t1) ([Nat.succ i := v]t2) := by congr
  @[simp] lemma opn_inter : [i := v]inter t1 t2 = inter ([i := v]t1) ([Nat.succ i := v]t2) := by congr
  @[simp] lemma opn_app : [i := v]app m t1 t2 = app m ([i := v]t1) ([i := v]t2) := by congr
  @[simp] lemma opn_pair : [i := v]pair t1 t2 t3 = pair ([i := v]t1) ([i := v]t2) ([i := v]t3)
    := by congr
  @[simp] lemma opn_fst : [i := v]proj p t = proj p ([i := v]t) := by congr
  @[simp] lemma opn_eq : [i := v]eq t1 t2 t3 = eq ([i := v]t1) ([i := v]t2) ([i := v]t3) := by congr
  @[simp] lemma opn_refl : [i := v]refl t = refl ([i := v]t) := by congr
  @[simp] lemma opn_Jh : [i := v]subst t1 t2 = subst ([i := v]t1) ([i := v]t2) := by congr
  @[simp] lemma opn_promote : [i := v]promote t = promote ([i := v]t) := by congr
  @[simp] lemma opn_delta : [i := v]delta t = delta ([i := v]t) := by congr
  @[simp] lemma opn_phi : [i := v]phi t1 t2 = phi ([i := v]t1) ([i := v]t2) := by congr

  @[simp] lemma cls_const : [i =: v](const c) = const c := by congr
  @[simp] lemma cls_bound : [i =: v](bound j) = bound j := by congr
  @[simp] lemma cls_free
    : {i <-| v}(free x) = if x == v then bound i else free x
  := by congr

  @[simp] lemma cls_typeu : [i =: v]typeu = typeu := by congr
  @[simp] lemma cls_kindu : [i =: v]kindu = kindu := by congr
  @[simp] lemma cls_lam : [i =: v]lam m t1 t2 = lam m ([i =: v]t1) ([shift i 1 0 =: v]t2) := by congr
  @[simp] lemma cls_pi : [i =: v]pi m t1 t2 = pi m ([i =: v]t1) ([shift i 1 0 =: v]t2) := by congr
  @[simp] lemma cls_inter : [i =: v]inter t1 t2 = inter ([i =: v]t1) ([shift i 1 0 =: v]t2) := by congr
  @[simp] lemma cls_app : [i =: v]app m t1 t2 = app m ([i =: v]t1) ([i =: v]t2) := by congr
  @[simp] lemma cls_pair : [i =: v]pair t1 t2 t3 = pair ([i =: v]t1) ([i =: v]t2) ([i =: v]t3)
    := by congr
  @[simp] lemma cls_fst : [i =: v]proj p t = proj p ([i =: v]t) := by congr
  @[simp] lemma cls_eq : [i =: v]eq t1 t2 t3 = eq ([i =: v]t1) ([i =: v]t2) ([i =: v]t3) := by congr
  @[simp] lemma cls_refl : [i =: v]refl t = refl ([i =: v]t) := by congr
  @[simp] lemma cls_Jh : [i =: v]subst t1 t2 = subst ([i =: v]t1) ([i =: v]t2) := by congr
  @[simp] lemma cls_promote : [i =: v]promote t = promote ([i =: v]t) := by congr
  @[simp] lemma cls_delta : [i =: v]delta t = delta ([i =: v]t) := by congr
  @[simp] lemma cls_phi : [i =: v]phi t1 t2 = phi ([i =: v]t1) ([i =: v]t2)
    := by congr

  @[simp] lemma shift_lc : lc c t -> shift t a c = t := by {
    intro h
    induction t generalizing c <;> simp at *
    case bound k => {
      intro h2; exfalso; linarith
    }
    case bind k t1 t2 ih1 ih2 => {
      cases h; case _ h1 h2 =>
      rw [ih1 h1, ih2 h2]; simp
    }
    case ctor k t1 t2 t3 ih1 ih2 ih3 => {
      casesm* _ ∧ _; case _ h1 h2 h3 =>
      rw [ih1 h1, ih2 h2, ih3 h3]; simp
    }
  }

  @[simp] lemma shift_lc0 : lc 0 t -> shift t a c = t := by {
    intro h
    have h := Syntax.lc0 h c
    apply shift_lc h
  }

  lemma var_not_in_close {t : Term} : x ∉ fv ({i <-| x}t) := by sorry

  lemma fv_close_var : y ≠ x -> y ∉ fv ({i <-| x}t) -> y ∉ fv t := by sorry

  lemma fv_close (i : Nat) (x : Name) (t : Term) : fv ({i <-| x}t) ⊆ fv t := by sorry

  lemma fv_open1 (i : Nat) (x : Name) (t : Term) : fv ({i |-> x}t) ⊆ x :: fv t
  := by sorry

  lemma fv_open2 (i : Nat) (x : Name) (t : Term) : fv t ⊆ fv ({i |-> x}t)
  := by sorry

  @[simp] lemma fv_open (t1 t2 : Term)
  : fv ([0 := t1]t2) ⊆ fv t1 ++ fv t2
  := by sorry

  lemma fv_open_shrink {t1 t2 : Term}
    : x ∉ fv t1 -> fv ({i |-> x}t1) ⊆ fv ({i |-> x}t2) -> fv t1 ⊆ fv t2
  := by sorry

  -- @[simp↓ high] lemma rename_bound : {i |-> x}{_<-| y}(@bound n i) = bound i
  -- := by unfold bound; rw [Syntax.rename_bound]

  -- lemma rename_free_neq : z ≠ y -> {_|-> x}{_<-| y}(@free n z) = free z
  -- := by intro h; unfold free; rw [Syntax.rename_free_neq h]

  -- lemma rename_free_eq : {_|-> x}{_<-| y}(@free n y) = free x
  -- := by unfold free; rw [Syntax.rename_free_eq]

  -- @[simp] lemma rename_subst_commute (x y) {n} {t1 : Term n} {t2 : Term (n + 1)} :
  --   {_|-> y}{_<-| x}[_:= t1]t2 = [_:= {_|-> y}{_<-| x}t1]({_|-> y}{_<-| x}t2)
  -- := @Nat.rec
  --   (λ m => ∀ n (t1 : Term n) (t2 : Term (n + 1)),
  --     size t2 ≤ m ->
  --     {_|-> y}{_<-| x}[_:= t1]t2 = [_:= {_|-> y}{_<-| x}t1]({_|-> y}{_<-| x}t2))
  --   (by {
  --     intros m t1 t2 h
  --     cases t2 <;> simp at h
  --     case bound i => {
  --       unfold HasHSubst.hsubst; unfold Syntax.instHasHSubstSyntax; simp
  --       unfold Syntax.hsubst; unfold bound; simp
  --       split; simp
  --       rw [rename_bound]
  --     }
  --     case free z => simp; split <;> simp
  --     case const => simp
  --   })
  --   (by {
  --     intro m ih n t1 t2 h
  --     cases t2 <;> simp at h
  --     case bound => apply ih n t1 (bound _) (by simp)
  --     case free => apply ih n t1 (free _) (by simp)
  --     case const => apply ih n t1 (const _) (by simp)
  --     case bind b u1 u2 => {
  --       have s1 : size u1 ≤ m := by linarith
  --       have s2 : size u2 ≤ m := by linarith
  --       simp; apply And.intro _ _
  --       apply ih n t1 u1 s1
  --       have lem := ih (n + 1) (Syntax.weaken t1 1) u2 s2
  --       simp at lem
  --       rw [lem]
  --     }
  --     case ctor c u1 u2 u3 => {
  --       have s1 : size u1 ≤ m := by linarith
  --       have s2 : size u2 ≤ m := by linarith
  --       have s3 : size u3 ≤ m := by linarith
  --       simp; apply And.intro _ _
  --       apply ih n t1 u1 s1
  --       apply And.intro _ _
  --       apply ih n t1 u2 s2
  --       apply ih n t1 u3 s3
  --     }
  --   })
  --   (size t2)
  --   n
  --   t1
  --   t2
  --   (by simp)

  -- lemma rename_open_commute {t : Term (n + 1)} : z ≠ x ->
  --   {_|-> z}{_|-> y}{_<-| x}t = {_|-> y}{_<-| x}{_|-> z}t
  -- := λ h1 => @Nat.rec
  --   (λ m => ∀ n (t : Term (n + 1)),
  --     size t ≤ m ->
  --     {_|-> z}{_|-> y}{_<-| x}t = {_|-> y}{_<-| x}{_|-> z}t)
  --   (by {
  --     intro n t s
  --     cases t <;> simp at s
  --     case bound i => {
  --       simp
  --       generalize hdef : {_|-> z}bound i = h
  --       unfold HasHOpen.hopn at hdef; unfold Syntax.instHasHOpenSyntax at hdef
  --       simp at hdef; unfold Syntax.opn_head at hdef; unfold bound at hdef; simp at hdef
  --       split at hdef
  --       case _ h => {
  --         rw [<-hdef]; simp
  --         rw [Name.beq_of_not_eq h1]; simp
  --       }
  --       case _ h => rw [<-hdef]; simp
  --     }
  --     case free w => {
  --       generalize hdef : {_|-> z}Syntax.free w = h
  --       simp at hdef; rw [<-hdef]; unfold free
  --       cases Name.decEq w x
  --       case isFalse h => {
  --         rw [Syntax.rename_free_neq h, Syntax.rename_free_neq h]
  --         simp
  --       }
  --       case isTrue h => {
  --         subst h
  --         rw [Syntax.rename_free_eq, Syntax.rename_free_eq]
  --         simp
  --       }
  --     }
  --     case const => simp
  --   })
  --   (by {
  --     intro m ih n t s
  --     cases t
  --     case bound => apply ih n (bound _) (by simp)
  --     case free => apply ih n (free _) (by simp)
  --     case const => apply ih n (const _) (by simp)
  --     case bind b u1 u2 => {
  --       simp at *
  --       have s1 : size u1 ≤ m := by linarith
  --       have s2 : size u2 ≤ m := by linarith
  --       apply And.intro _ _
  --       apply ih n u1 s1; apply ih (n + 1) u2 s2
  --     }
  --     case ctor c u1 u2 u3 => {
  --       simp at *
  --       have s1 : size u1 ≤ m := by linarith
  --       have s2 : size u2 ≤ m := by linarith
  --       have s3 : size u3 ≤ m := by linarith
  --       apply And.intro _ _
  --       apply ih n u1 s1
  --       apply And.intro _ _
  --       apply ih n u2 s2; apply ih n u3 s3
  --     }
  --   })
  --   (size t)
  --   n
  --   t
  --   (by simp)

  -- mutual
  --   def Infer.size : Γ ⊢ t : A -> Nat
  --   | .ax wf => Wf.size wf + 1
  --   | .var wf xn => sorry
  --   | .pi j1 S j2 =>
  --     have xn := @Name.fresh_is_fresh S
  --     let x := @Name.fresh S
  --     ConInfer.size j1 + ConInfer.size (j2 x xn) + 1
  --   | .lam j S1 j1 S2 j2 S3 j3 => sorry
  --   | .app j1 j2 => sorry
  --   | .inter j S1 j1=> sorry
  --   | .pair j1 j2 j3 _ => sorry
  --   | .fst j => sorry
  --   | .snd j => sorry
  --   | .eq j1 j2 j3 => sorry
  --   | .refl j1 j2 => sorry
  --   | .subst j1 j2 => sorry
  --   | .promote j1 j2 j3 => sorry
  --   | .phi j1 j2 j3 j4 => sorry
  --   | .delta j => sorry

  --   def ConInfer.size : Γ ⊢ t >: A -> Nat
  --   | .Infer j _ => Infer.size j + 1

  --   def Check.size : Γ ⊢ t =: A -> Nat
  --   | .check j1 j2 _ => Infer.size j1 + ConInfer.size j2 + 1

  --   def Wf.size : ⊢ Γ -> Nat
  --   | .nil => 0
  --   | .append _ wf j => Wf.size wf + ConInfer.size j + 1
  -- end
  -- termination_by
  --   Infer.size j => List.length Γ + size t + size A
  --   ConInfer.size j => List.length Γ + size t + size A + 1
  --   --Check.size j => size t + 1
  --   Wf.size j => List.length Γ
  -- decreasing_by
  --   simp_wf
  --   any_goals try simp at *; linarith

end Cedille
