
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold

namespace Cedille

  @[simp] lemma opn_const : {i |-> x}(const c) = const c := by congr
  @[simp] lemma opn_free : {i |-> y}(free x) = free x := by congr
  @[simp] lemma opn_bound
    : {i |-> x}(bound j) = if j == i then free x else bound j
  := by congr

  @[simp] lemma opn_typeu : {i |-> x}typeu = typeu := by congr
  @[simp] lemma opn_kindu : {i |-> x}kindu = kindu := by congr
  @[simp] lemma opn_lam : {i |-> x}lam m t1 t2 = lam m ({i |-> x}t1) ({Nat.succ i |-> x}t2) := by congr
  @[simp] lemma opn_pi : {i |-> x}pi m t1 t2 = pi m ({i |-> x}t1) ({Nat.succ i |-> x}t2) := by congr
  @[simp] lemma opn_inter : {i |-> x}inter t1 t2 = inter ({i |-> x}t1) ({Nat.succ i |-> x}t2) := by congr
  @[simp] lemma opn_app : {i |-> x}app m t1 t2 = app m ({i |-> x}t1) ({i |-> x}t2) := by congr
  @[simp] lemma opn_pair : {i |-> x}pair t1 t2 t3 = pair ({i |-> x}t1) ({i |-> x}t2) ({i |-> x}t3)
    := by congr
  @[simp] lemma opn_fst : {i |-> x}proj p t = proj p ({i |-> x}t) := by congr
  @[simp] lemma opn_eq : {i |-> x}eq t1 t2 t3 = eq ({i |-> x}t1) ({i |-> x}t2) ({i |-> x}t3) := by congr
  @[simp] lemma opn_refl : {i |-> x}refl t = refl ({i |-> x}t) := by congr
  @[simp] lemma opn_Jh : {i |-> x}Jh t1 t2 t3 = Jh ({i |-> x}t1) ({i |-> x}t2) ({i |-> x}t3) := by congr
  @[simp] lemma opn_J0 : {i |-> x}J0 t1 t2 = J0 ({i |-> x}t1) ({i |-> x}t2) := by congr
  @[simp] lemma opn_Jω : {i |-> x}Jω t1 t2 = Jω ({i |-> x}t1) ({i |-> x}t2) := by congr
  @[simp] lemma opn_J
    : {i |-> x}J t1 t2 t3 t4 t5 t6
      = J ({i |-> x}t1) ({i |-> x}t2) ({i |-> x}t3) ({i |-> x}t4) ({i |-> x}t5) ({i |-> x}t6)
    := by congr
  @[simp] lemma opn_promote : {i |-> x}promote t = promote ({i |-> x}t) := by congr
  @[simp] lemma opn_delta : {i |-> x}delta t = delta ({i |-> x}t) := by congr
  @[simp] lemma opn_phi : {i |-> x}phi t1 t2 t3 = phi ({i |-> x}t1) ({i |-> x}t2) ({i |-> x}t3)
    := by congr

  @[simp] lemma cls_const : {i <-| x}(const c) = const c := by congr
  @[simp] lemma cls_bound : {i <-| x}(bound i) = bound i := by congr
  @[simp] lemma cls_free
    : {i <-| v}(free x) = if x == v then bound i else free x
  := by congr

  @[simp] lemma cls_typeu : {i <-| x}typeu = typeu := by congr
  @[simp] lemma cls_kindu : {i <-| x}kindu = kindu := by congr
  @[simp] lemma cls_lam : {i <-| x}lam m t1 t2 = lam m ({i <-| x}t1) ({Nat.succ i <-| x}t2) := by congr
  @[simp] lemma cls_pi : {i <-| x}pi m t1 t2 = pi m ({i <-| x}t1) ({Nat.succ i <-| x}t2) := by congr
  @[simp] lemma cls_inter : {i <-| x}inter t1 t2 = inter ({i <-| x}t1) ({Nat.succ i <-| x}t2) := by congr
  @[simp] lemma cls_app : {i <-| x}app m t1 t2 = app m ({i <-| x}t1) ({i <-| x}t2) := by congr
  @[simp] lemma cls_pair : {i <-| x}pair t1 t2 t3 = pair ({i <-| x}t1) ({i <-| x}t2) ({i <-| x}t3)
    := by congr
  @[simp] lemma cls_fst : {i <-| x}proj p t = proj p ({i <-| x}t) := by congr
  @[simp] lemma cls_eq : {i <-| x}eq t1 t2 t3 = eq ({i <-| x}t1) ({i <-| x}t2) ({i <-| x}t3) := by congr
  @[simp] lemma cls_refl : {i <-| x}refl t = refl ({i <-| x}t) := by congr
  @[simp] lemma cls_Jh : {i <-| x}Jh t1 t2 t3 = Jh ({i <-| x}t1) ({i <-| x}t2) ({i <-| x}t3) := by congr
  @[simp] lemma cls_J0 : {i <-| x}J0 t1 t2 = J0 ({i <-| x}t1) ({i <-| x}t2) := by congr
  @[simp] lemma cls_Jω : {i <-| x}Jω t1 t2 = Jω ({i <-| x}t1) ({i <-| x}t2) := by congr
  @[simp] lemma cls_J
    : {i <-| x}J t1 t2 t3 t4 t5 t6
      = J ({i <-| x}t1) ({i <-| x}t2) ({i <-| x}t3) ({i <-| x}t4) ({i <-| x}t5) ({i <-| x}t6)
    := by congr
  @[simp] lemma cls_promote : {i <-| x}promote t = promote ({i <-| x}t) := by congr
  @[simp] lemma cls_delta : {i <-| x}delta t = delta ({i <-| x}t) := by congr
  @[simp] lemma cls_phi : {i <-| x}phi t1 t2 t3 = phi ({i <-| x}t1) ({i <-| x}t2) ({i <-| x}t3)
    := by congr

  @[simp] lemma subst_const {v : Term} : [x := v](const c) = const c := by congr
  @[simp] lemma subst_bound {v : Term} : [x := v](bound j) = bound j := by congr
  @[simp] lemma subst_free : [x := v](free x) = v
    := by unfold free; rw [Syntax.subst_free]

  @[simp] lemma subst_typeu {v : Term} : [x := v]typeu = typeu := by congr
  @[simp] lemma subst_kindu {v : Term} : [x := v]kindu = kindu := by congr
  @[simp] lemma subst_lam {v : Term}
    : [x := v]lam m t1 t2 = lam m ([x := v]t1) ([x := v]t2)
    := by unfold lam; rw [Syntax.subst_bind]
  @[simp] lemma subst_pi {v : Term}
    : [x := v]pi m t1 t2 = pi m ([x := v]t1) ([x := v]t2)
    := by unfold pi; rw [Syntax.subst_bind]
  @[simp] lemma subst_inter {v : Term}
    : [x := v]inter t1 t2 = inter ([x := v]t1) ([x := v]t2)
    := by unfold inter; rw [Syntax.subst_bind]
  @[simp] lemma subst_app {v : Term} : [x := v]app m t1 t2 = app m ([x := v]t1) ([x := v]t2)
    := by unfold app; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_pair {v : Term}
    : [x := v]pair t1 t2 t3 = pair ([x := v]t1) ([x := v]t2) ([x := v]t3)
    := by unfold pair; rw [Syntax.subst_ctor]
  @[simp] lemma subst_fst {v : Term} : [x := v]proj p t = proj p ([x := v]t)
    := by congr
  @[simp] lemma subst_eq {v : Term}
    : [x := v]eq t1 t2 t3 = eq ([x := v]t1) ([x := v]t2) ([x := v]t3)
    := by unfold eq; rw [Syntax.subst_ctor]
  @[simp] lemma subst_refl {v : Term} : [x := v]refl t = refl ([x := v]t)
    := by unfold refl; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_head_Jh {v : Term}
    : [x := v]Jh t1 t2 t3 = Jh ([x := v]t1) ([x := v]t2) ([x := v]t3)
    := by unfold Jh; rw [Syntax.subst_ctor]
  @[simp] lemma subst_head_J0 {v : Term} : [x := v]J0 t1 t2 = J0 ([x := v]t1) ([x := v]t2)
    := by unfold J0; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_head_Jω {v : Term} : [x := v]Jω t1 t2 = Jω ([x := v]t1) ([x := v]t2)
    := by unfold Jω; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_head_J {v : Term}
    : [x := v]J t1 t2 t3 t4 t5 t6
      = J ([x := v]t1) ([x := v]t2) ([x := v]t3) ([x := v]t4) ([x := v]t5) ([x := v]t6)
    := by unfold J; rw [subst_head_Jh, subst_head_J0, subst_head_J0, subst_head_Jω]
  @[simp] lemma subst_promote {v : Term} : [x := v]promote t = promote ([x := v]t)
    := by unfold promote; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_delta {v : Term} : [x := v]delta t = delta ([x := v]t)
    := by unfold delta; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_phi {v : Term}
    : [x := v]phi t1 t2 t3 = phi ([x := v]t1) ([x := v]t2) ([x := v]t3)
    := by unfold phi; rw [Syntax.subst_ctor]

  lemma subst_free_neq {v : Term} : x ≠ y -> [x := v](free y) = free y := by {
    intro h
    unfold HasSubst.subst; unfold Syntax.instHasSubstSyntax; simp
    unfold Syntax.subst; unfold free; simp
    intro h2; exfalso; apply h; rw [h2]
  }

  -- lemma open_to_close {t1 : Term} {t2 : Term}
  --   : x ∉ fv t1 -> {i |-> x}t1 = t2 -> t1 = {i <-| x}t2
  -- := by {
  --   intro xn h
  --   have h2 : {_<-| x}{_|-> x}t1 = {_<-| x}t2 := by congr
  --   rw [close_open_cancel xn] at h2
  --   exact h2
  -- }

  -- lemma to_open {n} (t : Term n) (x : Name) : ∃ s, t = {_|-> x}s := by {
  --   sorry
  -- }

  lemma var_not_in_close {t : Term} : x ∉ fv ({i <-| x}t) := by sorry

  lemma fv_close_var : y ≠ x -> y ∉ fv ({i <-| x}t) -> y ∉ fv t := by sorry

  lemma fv_close (i : Nat) (x : Name) (t : Term) : fv ({i <-| x}t) ⊆ fv t := by sorry

  lemma fv_open1 (i : Nat) (x : Name) (t : Term) : fv ({i |-> x}t) ⊆ x :: fv t
  := by sorry

  lemma fv_open2 (i : Nat) (x : Name) (t : Term) : fv t ⊆ fv ({i |-> x}t)
  := by sorry

  @[simp] lemma fv_subst (t1 t2 : Term)
  : fv ([x := t1]{0 |-> x}t2) ⊆ fv t1 ++ fv t2
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

end Cedille
