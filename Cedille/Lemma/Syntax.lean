
import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold

namespace Cedille

  @[simp] lemma opn_head_const {n} : {_|-> x}(@const (n + 1) c) = @const n c := by congr
  @[simp] lemma opn_head_free {n} : {_|-> y}(@free (n + 1) x) = free x := by congr

  @[simp] lemma opn_head_bound {n} {j : Fin n}
    : {_|-> x}(@bound (n + 1) j) = if j == n then free x else bound j
  := by {
    unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
    unfold Syntax.opn_head; unfold bound; simp
  }

  @[simp] lemma opn_head_bound2 {n}
    : {_|-> x}(@bound (n + 1) ↑n) = free x
  := by {
    unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
    unfold Syntax.opn_head; unfold bound; simp
  }

  @[simp] lemma opn_head_bound3 {n}
    : {_|-> x}(@bound (n + 2) (↑n + 1)) = free x
  := by {
    unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
    unfold Syntax.opn_head; unfold bound; simp
    intro h
    exfalso; apply h _
    rw [Fin.val_add]; simp
  }

  @[simp] lemma opn_head_typeu : {_|-> x}typeu = @typeu n
    := by unfold typeu; rw [Syntax.opn_head_const]
  @[simp] lemma opn_head_kindu : {_|-> x}kindu = @kindu n
    := by unfold kindu; rw [Syntax.opn_head_const]
  @[simp] lemma opn_head_lam : {_|-> x}lam m t1 t2 = lam m ({_|-> x}t1) ({_|-> x}t2)
    := by unfold lam; rw [Syntax.opn_head_bind]
  @[simp] lemma opn_head_pi : {_|-> x}pi m t1 t2 = pi m ({_|-> x}t1) ({_|-> x}t2)
    := by unfold pi; rw [Syntax.opn_head_bind]
  @[simp] lemma opn_head_inter : {_|-> x}inter t1 t2 = inter ({_|-> x}t1) ({_|-> x}t2)
    := by unfold inter; rw [Syntax.opn_head_bind]
  @[simp] lemma opn_head_app : {_|-> x}app m t1 t2 = app m ({_|-> x}t1) ({_|-> x}t2)
    := by unfold app; rw [Syntax.opn_head_ctor]; simp
  @[simp] lemma opn_head_pair : {_|-> x}pair t1 t2 t3 = pair ({_|-> x}t1) ({_|-> x}t2) ({_|-> x}t3)
    := by unfold pair; rw [Syntax.opn_head_ctor]
  @[simp] lemma opn_head_fst : {_|-> x}fst t = fst ({_|-> x}t)
    := by unfold fst; rw [Syntax.opn_head_ctor]; simp
  @[simp] lemma opn_head_snd :{_|-> x}snd t = snd ({_|-> x}t)
    := by unfold snd; rw [Syntax.opn_head_ctor]; simp
  @[simp] lemma opn_head_eq : {_|-> x}eq t1 t2 t3 = eq ({_|-> x}t1) ({_|-> x}t2) ({_|-> x}t3)
    := by unfold eq; rw [Syntax.opn_head_ctor]
  @[simp] lemma opn_head_refl : {_|-> x}refl t = refl ({_|-> x}t)
    := by unfold refl; rw [Syntax.opn_head_ctor]; simp
  @[simp] lemma opn_head_Jh : {_|-> x}Jh t1 t2 t3 = Jh ({_|-> x}t1) ({_|-> x}t2) ({_|-> x}t3)
    := by unfold Jh; rw [Syntax.opn_head_ctor]
  @[simp] lemma opn_head_J0 : {_|-> x}J0 t1 t2 = J0 ({_|-> x}t1) ({_|-> x}t2)
    := by unfold J0; rw [Syntax.opn_head_ctor]; simp
  @[simp] lemma opn_head_Jω : {_|-> x}Jω t1 t2 = Jω ({_|-> x}t1) ({_|-> x}t2)
    := by unfold Jω; rw [Syntax.opn_head_ctor]; simp
  @[simp] lemma opn_head_J : {_|-> x}J t1 t2 t3 t4 t5 t6 = J ({_|-> x}t1) ({_|-> x}t2) ({_|-> x}t3) ({_|-> x}t4) ({_|-> x}t5) ({_|-> x}t6)
    := by unfold J; rw [opn_head_Jh, opn_head_J0, opn_head_J0, opn_head_Jω]
  @[simp] lemma opn_head_promote : {_|-> x}promote t = promote ({_|-> x}t)
    := by unfold promote; rw [Syntax.opn_head_ctor]; simp
  @[simp] lemma opn_head_delta : {_|-> x}delta t = delta ({_|-> x}t)
    := by unfold delta; rw [Syntax.opn_head_ctor]; simp
  @[simp] lemma opn_head_phi : {_|-> x}phi t1 t2 t3 = phi ({_|-> x}t1) ({_|-> x}t2) ({_|-> x}t3)
    := by unfold phi; rw [Syntax.opn_head_ctor]

  @[simp] lemma cls_head_const : {_<-| x}(@const n c) = const c := by congr
  @[simp] lemma cls_head_bound : {_<-| x}(@bound n i) = @bound (n + 1) i := by congr

  @[simp] lemma cls_head_free
    : {_<-| v}(@free n x) = if x == v then bound n else free x
  := by {
    unfold HasHClose.hcls; unfold Syntax.instHasHCloseSyntax; simp
    unfold Syntax.cls_head; unfold free; simp
  }

  @[simp] lemma cls_head_typeu : {_<-| x}@typeu n = typeu
    := by unfold typeu; rw [Syntax.cls_head_const]
  @[simp] lemma cls_head_kindu : {_<-| x}@kindu n = kindu
    := by unfold kindu; rw [Syntax.cls_head_const]
  @[simp] lemma cls_head_lam : {_<-| x}lam m t1 t2 = lam m ({_<-| x}t1) ({_<-| x}t2)
    := by unfold lam; rw [Syntax.cls_head_bind]
  @[simp] lemma cls_head_pi : {_<-| x}pi m t1 t2 = pi m ({_<-| x}t1) ({_<-| x}t2)
    := by unfold pi; rw [Syntax.cls_head_bind]
  @[simp] lemma cls_head_inter : {_<-| x}inter t1 t2 = inter ({_<-| x}t1) ({_<-| x}t2)
    := by unfold inter; rw [Syntax.cls_head_bind]
  @[simp] lemma cls_head_app : {_<-| x}app m t1 t2 = app m ({_<-| x}t1) ({_<-| x}t2)
    := by unfold app; rw [Syntax.cls_head_ctor]; simp
  @[simp] lemma cls_head_pair : {_<-| x}pair t1 t2 t3 = pair ({_<-| x}t1) ({_<-| x}t2) ({_<-| x}t3)
    := by unfold pair; rw [Syntax.cls_head_ctor]
  @[simp] lemma cls_head_fst : {_<-| x}fst t = fst ({_<-| x}t)
    := by unfold fst; rw [Syntax.cls_head_ctor]; simp
  @[simp] lemma cls_head_snd :{_<-| x}snd t = snd ({_<-| x}t)
    := by unfold snd; rw [Syntax.cls_head_ctor]; simp
  @[simp] lemma cls_head_eq : {_<-| x}eq t1 t2 t3 = eq ({_<-| x}t1) ({_<-| x}t2) ({_<-| x}t3)
    := by unfold eq; rw [Syntax.cls_head_ctor]
  @[simp] lemma cls_head_refl : {_<-| x}refl t = refl ({_<-| x}t)
    := by unfold refl; rw [Syntax.cls_head_ctor]; simp
  @[simp] lemma cls_head_Jh : {_<-| x}Jh t1 t2 t3 = Jh ({_<-| x}t1) ({_<-| x}t2) ({_<-| x}t3)
    := by unfold Jh; rw [Syntax.cls_head_ctor]
  @[simp] lemma cls_head_J0 : {_<-| x}J0 t1 t2 = J0 ({_<-| x}t1) ({_<-| x}t2)
    := by unfold J0; rw [Syntax.cls_head_ctor]; simp
  @[simp] lemma cls_head_Jω : {_<-| x}Jω t1 t2 = Jω ({_<-| x}t1) ({_<-| x}t2)
    := by unfold Jω; rw [Syntax.cls_head_ctor]; simp
  @[simp] lemma cls_head_J : {_<-| x}J t1 t2 t3 t4 t5 t6 = J ({_<-| x}t1) ({_<-| x}t2) ({_<-| x}t3) ({_<-| x}t4) ({_<-| x}t5) ({_<-| x}t6)
    := by unfold J; rw [cls_head_Jh, cls_head_J0, cls_head_J0, cls_head_Jω]
  @[simp] lemma cls_head_promote : {_<-| x}promote t = promote ({_<-| x}t)
    := by unfold promote; rw [Syntax.cls_head_ctor]; simp
  @[simp] lemma cls_head_delta : {_<-| x}delta t = delta ({_<-| x}t)
    := by unfold delta; rw [Syntax.cls_head_ctor]; simp
  @[simp] lemma cls_head_phi : {_<-| x}phi t1 t2 t3 = phi ({_<-| x}t1) ({_<-| x}t2) ({_<-| x}t3)
    := by unfold phi; rw [Syntax.cls_head_ctor]

  @[simp] lemma hsubst_const {v : Term n} : [_:= v](@const (n + 1) c) = const c := by congr
  @[simp] lemma hsubst_free {v : Term n} : [_:= v](@free (n + 1) x) = free x
  := by unfold free; rw [Syntax.hsubst_free]

  @[simp] lemma hsubst_typeu {v : Term n} : [_:= v]@typeu (n + 1) = typeu
    := by unfold typeu; rw [Syntax.hsubst_const]
  @[simp] lemma hsubst_kindu {v : Term n} : [_:= v]@kindu (n + 1) = kindu
    := by unfold kindu; rw [Syntax.hsubst_const]
  @[simp] lemma hsubst_lam {v : Term n}
    : [_:= v]lam m t1 t2 = lam m ([_:= v]t1) ([_:= (Syntax.weaken v 1)]t2)
    := by unfold lam; rw [Syntax.hsubst_bind]
  @[simp] lemma hsubst_pi {v : Term n}
    : [_:= v]pi m t1 t2 = pi m ([_:= v]t1) ([_:= (Syntax.weaken v 1)]t2)
    := by unfold pi; rw [Syntax.hsubst_bind]
  @[simp] lemma hsubst_inter {v : Term n}
    : [_:= v]inter t1 t2 = inter ([_:= v]t1) ([_:= (Syntax.weaken v 1)]t2)
    := by unfold inter; rw [Syntax.hsubst_bind]
  @[simp] lemma hsubst_app {v : Term n} : [_:= v]app m t1 t2 = app m ([_:= v]t1) ([_:= v]t2)
    := by unfold app; rw [Syntax.hsubst_ctor]; simp
  @[simp] lemma hsubst_pair {v : Term n}
    : [_:= v]pair t1 t2 t3 = pair ([_:= v]t1) ([_:= v]t2) ([_:= v]t3)
    := by unfold pair; rw [Syntax.hsubst_ctor]
  @[simp] lemma hsubst_fst {v : Term n} : [_:= v]fst t = fst ([_:= v]t)
    := by unfold fst; rw [Syntax.hsubst_ctor]; simp
  @[simp] lemma hsubst_snd {v : Term n} : [_:= v]snd t = snd ([_:= v]t)
    := by unfold snd; rw [Syntax.hsubst_ctor]; simp
  @[simp] lemma hsubst_eq {v : Term n} : [_:= v]eq t1 t2 t3 = eq ([_:= v]t1) ([_:= v]t2) ([_:= v]t3)
    := by unfold eq; rw [Syntax.hsubst_ctor]
  @[simp] lemma hsubst_refl {v : Term n} : [_:= v]refl t = refl ([_:= v]t)
    := by unfold refl; rw [Syntax.hsubst_ctor]; simp
  @[simp] lemma hsubst_head_Jh {v : Term n} : [_:= v]Jh t1 t2 t3 = Jh ([_:= v]t1) ([_:= v]t2) ([_:= v]t3)
    := by unfold Jh; rw [Syntax.hsubst_ctor]
  @[simp] lemma hsubst_head_J0 {v : Term n} : [_:= v]J0 t1 t2 = J0 ([_:= v]t1) ([_:= v]t2)
    := by unfold J0; rw [Syntax.hsubst_ctor]; simp
  @[simp] lemma hsubst_head_Jω {v : Term n} : [_:= v]Jω t1 t2 = Jω ([_:= v]t1) ([_:= v]t2)
    := by unfold Jω; rw [Syntax.hsubst_ctor]; simp
  @[simp] lemma hsubst_head_J {v : Term n} : [_:= v]J t1 t2 t3 t4 t5 t6 = J ([_:= v]t1) ([_:= v]t2) ([_:= v]t3) ([_:= v]t4) ([_:= v]t5) ([_:= v]t6)
    := by unfold J; rw [hsubst_head_Jh, hsubst_head_J0, hsubst_head_J0, hsubst_head_Jω]
  @[simp] lemma hsubst_promote {v : Term n} : [_:= v]promote t = promote ([_:= v]t)
    := by unfold promote; rw [Syntax.hsubst_ctor]; simp
  @[simp] lemma hsubst_delta {v : Term n} : [_:= v]delta t = delta ([_:= v]t)
    := by unfold delta; rw [Syntax.hsubst_ctor]; simp
  @[simp] lemma hsubst_phi {v : Term n} : [_:= v]phi t1 t2 t3 = phi ([_:= v]t1) ([_:= v]t2) ([_:= v]t3)
    := by unfold phi; rw [Syntax.hsubst_ctor]

  @[simp] lemma subst_const {v : Term n} : [x := v](@const n c) = const c := by congr
  @[simp] lemma subst_bound {v : Term n} : [x := v](@bound n j) = bound j := by congr
  @[simp] lemma subst_free {v : Term n} : [x := v](@free n x) = v
    := by unfold free; rw [Syntax.subst_free]

  @[simp] lemma subst_typeu {v : Term n} : [x := v]@typeu n = typeu
    := by unfold typeu; rw [Syntax.subst_const]
  @[simp] lemma subst_kindu {v : Term n} : [x := v]@kindu n = kindu
    := by unfold kindu; rw [Syntax.subst_const]
  @[simp] lemma subst_lam {v : Term n} {t2 : Term (n + 1)}
    : [x := v]lam m t1 t2 = lam m ([x := v]t1) ([x := (Syntax.weaken v 1)]t2)
    := by unfold lam; rw [Syntax.subst_bind]
  @[simp] lemma subst_pi {v : Term n} {t2 : Term (n + 1)}
    : [x := v]pi m t1 t2 = pi m ([x := v]t1) ([x := (Syntax.weaken v 1)]t2)
    := by unfold pi; rw [Syntax.subst_bind]
  @[simp] lemma subst_inter {v : Term n} {t2 : Term (n + 1)}
    : [x := v]inter t1 t2 = inter ([x := v]t1) ([x := (Syntax.weaken v 1)]t2)
    := by unfold inter; rw [Syntax.subst_bind]
  @[simp] lemma subst_app {v t2 : Term n} : [x := v]app m t1 t2 = app m ([x := v]t1) ([x := v]t2)
    := by unfold app; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_pair {v t3 : Term n}
    : [x := v]pair t1 t2 t3 = pair ([x := v]t1) ([x := v]t2) ([x := v]t3)
    := by unfold pair; rw [Syntax.subst_ctor]
  @[simp] lemma subst_fst {v t : Term n} : [x := v]fst t = fst ([x := v]t)
    := by unfold fst; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_snd {v t : Term n} : [x := v]snd t = snd ([x := v]t)
    := by unfold snd; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_eq {v t1 : Term n}
    : [x := v]eq t1 t2 t3 = eq ([x := v]t1) ([x := v]t2) ([x := v]t3)
    := by unfold eq; rw [Syntax.subst_ctor]
  @[simp] lemma subst_refl {v t : Term n} : [x := v]refl t = refl ([x := v]t)
    := by unfold refl; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_head_Jh {v t3 : Term n}
    : [x := v]Jh t1 t2 t3 = Jh ([x := v]t1) ([x := v]t2) ([x := v]t3)
    := by unfold Jh; rw [Syntax.subst_ctor]
  @[simp] lemma subst_head_J0 {v t2 : Term n} : [x := v]J0 t1 t2 = J0 ([x := v]t1) ([x := v]t2)
    := by unfold J0; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_head_Jω {v t2 : Term n} : [x := v]Jω t1 t2 = Jω ([x := v]t1) ([x := v]t2)
    := by unfold Jω; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_head_J {v t6 : Term n}
    : [x := v]J t1 t2 t3 t4 t5 t6
      = J ([x := v]t1) ([x := v]t2) ([x := v]t3) ([x := v]t4) ([x := v]t5) ([x := v]t6)
    := by unfold J; rw [subst_head_Jh, subst_head_J0, subst_head_J0, subst_head_Jω]
  @[simp] lemma subst_promote {v t : Term n} : [x := v]promote t = promote ([x := v]t)
    := by unfold promote; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_delta {v t : Term n} : [x := v]delta t = delta ([x := v]t)
    := by unfold delta; rw [Syntax.subst_ctor]; simp
  @[simp] lemma subst_phi {v t3 : Term n}
    : [x := v]phi t1 t2 t3 = phi ([x := v]t1) ([x := v]t2) ([x := v]t3)
    := by unfold phi; rw [Syntax.subst_ctor]

  lemma subst_free_neq {v : Term n} : x ≠ y -> [x := v](@free n y) = free y := by {
    intro h
    unfold HasSubst.subst; unfold Syntax.instHasSubstSyntax; simp
    unfold Syntax.subst; unfold free; simp
    intro h2; exfalso; apply h; rw [h2]
  }

  @[simp] lemma hsubst_close_to_subst {v t : Term n} : [_:= v]{_<-| x}t = [x := v]t := by {
    induction t
    case bound m j => {
      simp; unfold HasHSubst.hsubst; unfold Syntax.instHasHSubstSyntax; simp
      unfold Syntax.hsubst; unfold bound; simp
      intro h; cases j; case _ v lt =>
      simp at h; subst h; exfalso; linarith
    }
    case const => simp
    case free m y => {
      simp
      cases (Name.decEq y x)
      case _ h => {
        have h2 := Name.beq_of_not_eq h
        have h3 : x ≠ y := ne_sym h
        rw [h2]; simp
        rw [subst_free_neq h3]
      }
      case _ h => {
        subst h; simp
        unfold HasHSubst.hsubst; unfold Syntax.instHasHSubstSyntax; simp
        unfold Syntax.hsubst; unfold bound; simp
      }
    }
    case bind m k t1 t2 ih1 ih2 => {
      simp; apply And.intro _ _
      apply ih1; apply ih2
    }
    case ctor m k t1 t2 t3 ih1 ih2 ih3 => {
      simp; apply And.intro ih1 (And.intro ih2 ih3)
    }
  }


  lemma close_open_cancel {n} {t : Term (n + 1)} : x ∉ fv t -> {_<-| x}{_|-> x}t = t
    := λ h => @Nat.rec
      (λ n =>
        ∀ x m (t : Term (m + 1)),
        size t ≤ n ->
        x ∉ fv t ->
        {_<-| x}{_|-> x}t = t)
      (by {
        intro x m t e h
        cases t <;> simp at *
        case bound i => {
          unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax
          unfold Syntax.opn_head; unfold bound; simp
          split
          case _ h => {
            simp; cases i; case _ iv il =>
            simp at *; subst h
            rw [fin_cast il]
          }
          case _ h => simp; rw [<-fin_cast2]
        }
        case free y => {
          intro h2
          have h3 : x = y := by rw [h2]
          exfalso; apply h h3
        }
      })
      (by {
        intro m ih x k t e h
        cases t <;> simp at *
        case bound i => {
          unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax
          unfold Syntax.opn_head; unfold bound; simp
          split
          case _ h => {
            simp; cases i; case _ iv il =>
            simp at *; subst h
            rw [fin_cast il]
          }
          case _ h => simp; rw [<-fin_cast2]
        }
        case free y => {
          intro h2
          have h3 : x = y := by rw [h2]
          exfalso; apply h h3
        }
        case bind b u1 u2 => {
          have e1 : size u1 ≤ m := by linarith
          have e2 : size u2 ≤ m := by linarith
          have h := demorgan h
          cases h; case _ l r =>
          rw [ih x k u1 e1 l, ih x (k + 1) u2 e2 r]
          simp
        }
        case ctor c u1 u2 u3 => {
          have e1 : size u1 ≤ m := by linarith
          have e2 : size u2 ≤ m := by linarith
          have e3 : size u3 ≤ m := by linarith
          have h := demorgan h
          cases h; case _ l r =>
          have h := demorgan r
          cases h; case _ r1 r2 =>
          rw [ih x k u1 e1 l, ih x k u2 e2 r1, ih x k u3 e3 r2]
          simp
        }
      })
      (size t)
      x
      n
      t
      (by simp)
      h

  lemma open_to_close {n} {t1 : Term (n + 1)} {t2 : Term n}
    : x ∉ fv t1 -> {_|-> x}t1 = t2 -> t1 = {_<-| x}t2
  := by {
    intro xn h
    have h2 : {_<-| x}{_|-> x}t1 = {_<-| x}t2 := by congr
    rw [close_open_cancel xn] at h2
    exact h2
  }

  lemma to_open {n} (t : Term n) (x : Name) : ∃ s, t = {_|-> x}s := by {
    sorry
  }

  lemma var_not_in_close {n} {t : Term n} : x ∉ fv ({_<-| x}t) := by {
    intro h
    induction t <;> simp at *
    case free m y => {
      split at h
      case _ => simp at h
      case _ h2 => {
        simp at h
        subst h; simp at h2
      }
    }
    case bind m b u1 u2 ih1 ih2 => {
      cases h
      case inl h => apply ih1 h
      case inr h => apply ih2 h
    }
    case ctor m c u1 u2 u3 ih1 ih2 ih3 => {
      cases h
      case _ h => apply ih1 h
      case _ h => {
        cases h
        case _ h => apply ih2 h
        case _ h => apply ih3 h
      }
    }
  }

  @[simp] lemma fv_open {n} {t : Term (n + 1)} : fv ({_|-> x}t) ⊆ x :: fv t
  := @Nat.rec
    (λ m => ∀ n (t : Term (n + 1)),
      size t ≤ m ->
      fv ({_|-> x}t) ⊆ x :: fv t)
    (by {
      intro m t s
      cases t <;> simp at *
      case bound i => {
        unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
        unfold Syntax.opn_head; unfold bound; simp
        split <;> simp
      }
    })
    (by {
      intro m ih n t s
      cases t
      case bound => apply ih _ (bound _) (by simp)
      case free => apply ih _ (free _) (by simp)
      case const => apply ih _ (const _) (by simp)
      case bind k u1 u2 => {
        simp at *
        have s1 : size u1 ≤ m := by linarith
        have s2 : size u2 ≤ m := by linarith
        have ih1 := ih _ u1 s1
        have ih2 := ih _ u2 s2
        simp at *
        apply And.intro _ _
        apply FvSet.subset_append.2 _; apply FvSet.subset_left _; apply ih1
        apply FvSet.subset_append.2 _; apply FvSet.subset_right _; apply ih2
      }
      case ctor k u1 u2 u3 => {
        simp at *
        have s1 : size u1 ≤ m := by linarith
        have s2 : size u2 ≤ m := by linarith
        have s3 : size u3 ≤ m := by linarith
        have ih1 := ih _ u1 s1
        have ih2 := ih _ u2 s2
        have ih3 := ih _ u3 s3
        apply And.intro _ _
        apply FvSet.subset_append.2 _; apply FvSet.subset_left; apply ih1
        apply And.intro _ _
        apply FvSet.subset_append.2 _; apply FvSet.subset_right
        apply FvSet.subset_append.2 _; apply FvSet.subset_left; apply ih2
        apply FvSet.subset_append.2 _; apply FvSet.subset_right
        apply FvSet.subset_append.2 _; apply FvSet.subset_right; apply ih3
      }
    })
    (size t)
    n
    t
    (by simp)

  @[simp] lemma fv_subst {n} {t1 : Term n} {t2 : Term (n + 1)}
  : fv ([_:= t1]t2) ⊆ fv t1 ++ fv t2
  := @Nat.rec
    (λ s => ∀ n (t1 : Term n) (t2 : Term (n + 1)),
      size t2 ≤ s ->
      fv ([_:= t1]t2) ⊆ fv t1 ++ fv t2)
    (by {
      intro n t1 t2 sh
      cases t2 <;> simp at *
      case bound i => {
        unfold HasHSubst.hsubst; unfold Syntax.instHasHSubstSyntax; simp
        unfold Syntax.hsubst; unfold bound; simp
        split <;> simp
      }
    })
    (by {
      intro s ih n t1 t2 sh
      cases t2
      case bound => apply ih _ _ (bound _) (by simp)
      case free => apply ih _ _ (free _) (by simp)
      case const => apply ih _ _ (const _) (by simp)
      case bind k u1 u2 => {
        simp at *
        have s1 : size u1 ≤ s := by linarith
        have s2 : size u2 ≤ s := by linarith
        apply And.intro _ _
        rw [<-List.append_assoc]; apply FvSet.subset_left _; apply ih _ _ u1 s1
        apply FvSet.subset_comm _; simp; apply FvSet.subset_right _
        apply FvSet.subset_comm _
        have lem := ih (n + 1) (Syntax.weaken t1 1) u2 s2
        unfold fv at lem; simp at lem
        apply lem
      }
      case ctor k u1 u2 u3 => {
        simp at *
        have s1 : size u1 ≤ s := by linarith
        have s2 : size u2 ≤ s := by linarith
        have s3 : size u3 ≤ s := by linarith
        apply And.intro _ _
        rw [<-List.append_assoc]; apply FvSet.subset_left _; apply ih _ _ u1 s1
        apply And.intro _ _
        apply FvSet.subset_comm _; simp; apply FvSet.subset_right _
        apply FvSet.subset_comm _; simp; apply FvSet.subset_right _; apply ih _ _ u2 s2
        apply FvSet.subset_comm _; rw [<-List.append_assoc]; simp
        apply FvSet.subset_right _; apply FvSet.subset_right _
        apply FvSet.subset_comm _; apply ih _ _ u3 s3
      }
    })
    (size t2)
    n
    t1
    t2
    (by simp)

  lemma fv_open_shrink {n} {t1 t2 : Term (n + 1)}
    : x ∉ fv t1 -> fv ({_|-> x}t1) ⊆ fv ({_|-> x}t2) -> fv t1 ⊆ fv t2
  := λ h1 h2 => @Nat.rec
    (λ n =>
      ∀ m1 m2 (t1 : Term (m1 + 1)) (t2 : Term (m2 + 1)),
      size t1 ≤ n ->
      x ∉ fv t1 ->
      fv ({_|-> x}t1) ⊆ fv ({_|-> x}t2) ->
      fv t1 ⊆ fv t2)
    (by {
      intro m1 m2 t1 t2 e h1 h2
      cases t1 <;> simp at *
      case free y z => {
        have lem := fv_open h2
        cases lem <;> simp at *
        case _ h => exact h
      }
    })
    (by {
      intro n ih m1 m2 t1 t2 e h1 h2
      cases t1
      case bound i => apply ih m1 m2 (bound i) t2 (by simp) h1 h2
      case free x => apply ih m1 m2 (free x) t2 (by simp) h1 h2
      case const k => apply ih m1 m2 (const k) t2 (by simp) h1 h2
      case bind b u1 u2 => {
        simp at *
        have e1 : size u1 ≤ n := by linarith
        have e2 : size u2 ≤ n := by linarith
        cases h2; case _ h21 h22 =>
        cases (demorgan h1); case _ h11 h12 =>
        apply And.intro _ _
        apply ih _ _ _ _ e1 h11 h21
        apply ih _ _ u2 t2 e2 h12 h22
      }
      case ctor c u1 u2 u3 => {
        simp at *
        have e1 : size u1 ≤ n := by linarith
        have e2 : size u2 ≤ n := by linarith
        have e3 : size u3 ≤ n := by linarith
        have h1 := demorgan h1
        cases h1; case _ h11 h1 =>
        cases (demorgan h1); case _ h12 h13 =>
        cases h2; case _ h21 h2 =>
        cases h2; case _ h22 h23 =>
        apply And.intro _ _
        apply ih _ _ _ _ e1 h11 h21
        apply And.intro _ _
        apply ih _ _ _ _ e2 h12 h22
        apply ih _ _ _ _ e3 h13 h23
      }
    })
    (size t1)
    n
    n
    t1
    t2
    (by simp)
    h1
    h2

  @[simp↓ high] lemma rename_bound {i : Fin n} : {_|-> x}{_<-| y}(@bound n i) = bound i
  := by unfold bound; rw [Syntax.rename_bound]

  lemma rename_free_neq : z ≠ y -> {_|-> x}{_<-| y}(@free n z) = free z
  := by intro h; unfold free; rw [Syntax.rename_free_neq h]

  lemma rename_free_eq : {_|-> x}{_<-| y}(@free n y) = free x
  := by unfold free; rw [Syntax.rename_free_eq]

  @[simp] lemma rename_subst_commute (x y) {n} {t1 : Term n} {t2 : Term (n + 1)} :
    {_|-> y}{_<-| x}[_:= t1]t2 = [_:= {_|-> y}{_<-| x}t1]({_|-> y}{_<-| x}t2)
  := @Nat.rec
    (λ m => ∀ n (t1 : Term n) (t2 : Term (n + 1)),
      size t2 ≤ m ->
      {_|-> y}{_<-| x}[_:= t1]t2 = [_:= {_|-> y}{_<-| x}t1]({_|-> y}{_<-| x}t2))
    (by {
      intros m t1 t2 h
      cases t2 <;> simp at h
      case bound i => {
        unfold HasHSubst.hsubst; unfold Syntax.instHasHSubstSyntax; simp
        unfold Syntax.hsubst; unfold bound; simp
        split; simp
        rw [rename_bound]
      }
      case free z => simp; split <;> simp
      case const => simp
    })
    (by {
      intro m ih n t1 t2 h
      cases t2 <;> simp at h
      case bound => apply ih n t1 (bound _) (by simp)
      case free => apply ih n t1 (free _) (by simp)
      case const => apply ih n t1 (const _) (by simp)
      case bind b u1 u2 => {
        have s1 : size u1 ≤ m := by linarith
        have s2 : size u2 ≤ m := by linarith
        simp; apply And.intro _ _
        apply ih n t1 u1 s1
        have lem := ih (n + 1) (Syntax.weaken t1 1) u2 s2
        simp at lem
        rw [lem]
      }
      case ctor c u1 u2 u3 => {
        have s1 : size u1 ≤ m := by linarith
        have s2 : size u2 ≤ m := by linarith
        have s3 : size u3 ≤ m := by linarith
        simp; apply And.intro _ _
        apply ih n t1 u1 s1
        apply And.intro _ _
        apply ih n t1 u2 s2
        apply ih n t1 u3 s3
      }
    })
    (size t2)
    n
    t1
    t2
    (by simp)

  lemma rename_open_commute {t : Term (n + 1)} : z ≠ x ->
    {_|-> z}{_|-> y}{_<-| x}t = {_|-> y}{_<-| x}{_|-> z}t
  := λ h1 => @Nat.rec
    (λ m => ∀ n (t : Term (n + 1)),
      size t ≤ m ->
      {_|-> z}{_|-> y}{_<-| x}t = {_|-> y}{_<-| x}{_|-> z}t)
    (by {
      intro n t s
      cases t <;> simp at s
      case bound i => {
        simp
        generalize hdef : {_|-> z}bound i = h
        unfold HasHOpen.hopn at hdef; unfold Syntax.instHasHOpenSyntax at hdef
        simp at hdef; unfold Syntax.opn_head at hdef; unfold bound at hdef; simp at hdef
        split at hdef
        case _ h => {
          rw [<-hdef]; simp
          rw [Name.beq_of_not_eq h1]; simp
        }
        case _ h => rw [<-hdef]; simp
      }
      case free w => {
        generalize hdef : {_|-> z}Syntax.free w = h
        simp at hdef; rw [<-hdef]; unfold free
        cases Name.decEq w x
        case isFalse h => {
          rw [Syntax.rename_free_neq h, Syntax.rename_free_neq h]
          simp
        }
        case isTrue h => {
          subst h
          rw [Syntax.rename_free_eq, Syntax.rename_free_eq]
          simp
        }
      }
      case const => simp
    })
    (by {
      intro m ih n t s
      cases t
      case bound => apply ih n (bound _) (by simp)
      case free => apply ih n (free _) (by simp)
      case const => apply ih n (const _) (by simp)
      case bind b u1 u2 => {
        simp at *
        have s1 : size u1 ≤ m := by linarith
        have s2 : size u2 ≤ m := by linarith
        apply And.intro _ _
        apply ih n u1 s1; apply ih (n + 1) u2 s2
      }
      case ctor c u1 u2 u3 => {
        simp at *
        have s1 : size u1 ≤ m := by linarith
        have s2 : size u2 ≤ m := by linarith
        have s3 : size u3 ≤ m := by linarith
        apply And.intro _ _
        apply ih n u1 s1
        apply And.intro _ _
        apply ih n u2 s2; apply ih n u3 s3
      }
    })
    (size t)
    n
    t
    (by simp)

end Cedille
