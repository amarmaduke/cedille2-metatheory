
import Cedille.Def

namespace Cedille

  @[simp low] lemma refold_const : Syntax.const k = const k := by congr
  @[simp low] lemma refold_typeu : Syntax.const Constant.typeU = typeu := by congr
  @[simp low] lemma refold_kindu : Syntax.const Constant.kindU = kindu := by congr
  @[simp low] lemma refold_free : Syntax.free x = free x := by congr
  @[simp low] lemma refold_bound {i : Nat} : Syntax.bound i = bound i := by congr
  @[simp low] lemma refold_lam : Syntax.bind (Binder.lam m) t1 t2 = lam m t1 t2 := by congr
  @[simp low] lemma refold_pi : Syntax.bind (Binder.pi m) t1 t2 = pi m t1 t2 := by congr
  @[simp low] lemma refold_inter : Syntax.bind Binder.inter t1 t2 = inter t1 t2 := by congr
  @[simp low] lemma refold_app : Syntax.ctor (Constructor.app m) t1 t2 kindu = app m t1 t2 := by congr
  @[simp low] lemma refold_pair : Syntax.ctor Constructor.pair t1 t2 t3 = pair t1 t2 t3 := by congr
  @[simp low] lemma refold_proj : Syntax.ctor (Constructor.proj i) t kindu kindu = proj i t := by congr
  @[simp low] lemma refold_eq : Syntax.ctor Constructor.eq t1 t2 t3 = eq t1 t2 t3 := by congr
  @[simp low] lemma refold_refl : Syntax.ctor Constructor.refl t kindu kindu = refl t := by congr
  @[simp low] lemma refold_subst : Syntax.ctor Constructor.subst t1 t2 kindu = subst t1 t2 := by congr
  @[simp low] lemma refold_promote : Syntax.ctor Constructor.promote t kindu kindu = promote t := by congr
  @[simp low] lemma refold_delta : Syntax.ctor Constructor.delta t kindu kindu = delta t := by congr
  @[simp low] lemma refold_phi : Syntax.ctor Constructor.phi t1 t2 kindu = phi t1 t2 := by congr

  @[simp low] lemma const_to_typeu : const Constant.typeU = typeu := by congr
  @[simp low] lemma const_to_kindu : const Constant.kindU = kindu := by congr

  @[simp] lemma shift_shift : Syntax.shift t a c = shift t a c := by rfl

  @[simp] lemma size_const : size (const k) = 0 := by congr
  @[simp] lemma size_typeu : size (typeu) = 0 := by congr
  @[simp] lemma size_kindu : size (kindu) = 0 := by congr
  @[simp] lemma size_free : size (free x) = 0 := by congr
  @[simp] lemma size_bound {i : Nat} : size (bound i) = 0 := by congr
  @[simp] lemma size_lam : size (lam m t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma size_pi : size (pi m t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma size_inter : size (inter t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma size_app : size (app m t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma size_pair : size (pair t1 t2 t3) = size t1 + size t2 + size t3 + 1 := by congr
  @[simp] lemma size_fst : size (proj i t) = size t + 1 := by congr
  @[simp] lemma size_eq : size (eq t1 t2 t3) = size t1 + size t2 + size t3 + 1 := by congr
  @[simp] lemma size_refl : size (refl t) = size t + 1 := by congr
  @[simp] lemma size_subst : size (subst t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma size_promote : size (promote t) = size t + 1 := by congr
  @[simp] lemma size_delta : size (delta t) = size t + 1 := by congr
  @[simp] lemma size_phi : size (phi t1 t2) = size t1 + size t2 + 1 := by congr

  @[simp] lemma size_bind : size (Syntax.bind k t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma size_ctor : size (Syntax.ctor k t1 t2 t3) = size t1 + size t2 + size t3 + 1 := by congr
  @[simp low] lemma size_size : Syntax.size t = size t := by congr
  -- @[simp] lemma size_open : size ({_|-> x}t) = size t := by {
  --   unfold size; rewrite [Syntax.size_opn_head]; rfl
  -- }

  @[simp low] lemma fv_fv : Syntax.fv t = fv t := by congr
  @[simp] lemma fv_ctor : fv (Syntax.ctor k t1 t2 t3) = fv t1 ++ fv t2 ++ fv t3 := by {
    generalize h : fv t1 ++ fv t2 ++ fv t3 = t
    unfold fv; unfold Syntax.fv; unfold fv at h; rw [h]
  }
  @[simp] lemma fv_bind : fv (Syntax.bind k t1 t2) = fv t1 ++ fv t2 := by {
    generalize h : fv t1 ++ fv t2 = t
    unfold fv; unfold Syntax.fv; simp [*]
  }
  @[simp] lemma fv_const : fv (const K) = [] := by congr
  @[simp] lemma fv_typeu : fv (typeu) = [] := by congr
  @[simp] lemma fv_kindu : fv (kindu) = [] := by congr
  @[simp] lemma fv_free : fv (free x) = [x] := by congr
  @[simp] lemma fv_bound : fv (bound i) = [] := by congr
  @[simp] lemma fv_lam : fv (lam m t1 t2) = fv t1 ++ fv t2 := by congr
  @[simp] lemma fv_pi : fv (pi m t1 t2) = fv t1 ++ fv t2 := by congr
  @[simp] lemma fv_inter : fv (inter t1 t2) = fv t1 ++ fv t2 := by congr
  @[simp] lemma fv_app : fv (app m t1 t2) = fv t1 ++ fv t2 :=  by {
    unfold app; rw [@fv_ctor _ t1 t2 _]; simp
  }
  @[simp] lemma fv_pair : fv (pair t1 t2 t3) = fv t1 ++ fv t2 ++ fv t3 := by congr
  @[simp] lemma fv_proj : fv (proj i t) = fv t := by {
    unfold proj; rw [@fv_ctor _ t _ _]; simp; repeat rw [List.append_nil]
  }
  @[simp] lemma fv_eq : fv (eq t1 t2 t3) = fv t1 ++ fv t2 ++ fv t3 := by congr
  @[simp] lemma fv_refl : fv (refl t) = fv t := by {
    unfold refl; rw [@fv_ctor _ t _ _]; simp; repeat rw [List.append_nil]
  }
  @[simp] lemma fv_subst: fv (subst t1 t2) = fv t1 ++ fv t2 := by {
    unfold subst; rw [@fv_ctor _ t1 t2 _]; simp; repeat rw [List.append_nil]
  }
  @[simp] lemma fv_promote : fv (promote t) = fv t := by {
    unfold promote; rw [@fv_ctor _ t _ _]; simp; repeat rw [List.append_nil]
  }
  @[simp] lemma fv_delta : fv (delta t) = fv t := by {
    unfold delta; rw [@fv_ctor _ t _ _]; simp; repeat rw [List.append_nil]
  }
  @[simp] lemma fv_phi : fv (phi t1 t2) = fv t1 ++ fv t2 := by {
    unfold phi; rw [@fv_ctor _ t1 t2 _]; simp; repeat rw [List.append_nil]
  }

  @[simp low] lemma lc_lc : Syntax.lc i t = lc i t := by congr
  @[simp] lemma lc_ctor : lc i (Syntax.ctor k t1 t2 t3) = (lc i t1 ∧ lc i t2 ∧ lc i t3) := by {
    unfold lc; unfold Syntax.lc; simp
    apply Iff.intro _ _
    {
      intro h1; apply And.intro _ _
      {
        intro j h; have lem := h1 j h; cases lem; case _ a lem =>
        exists a; exact lem.1
      }
      {
        apply And.intro _ _
        {
          intro j h; have lem := h1 j h; cases lem; case _ a lem =>
          exists a; exact lem.2.1
        }
        {
          intro j h; have lem := h1 j h; cases lem; case _ a lem =>
          exists a; exact lem.2.2
        }
      }
    }
    {
      intro h1 j h
      casesm* _ ∧ _; case _ h1 h2 h3 =>
      replace h1 := h1 j h
      replace h2 := h2 j h
      replace h3 := h3 j h
      casesm* ∃ _, _; case _ a1 h1 a2 h2 a3 h3 =>
      exists a1; simp [*]; apply And.intro _ _
      apply Syntax.unbounded h2
      apply Syntax.unbounded h3
    }
  }
  @[simp] lemma lc_bind : lc i (Syntax.bind k t1 t2) = (lc i t1 ∧ lc (Nat.succ i) t2) := by {
    unfold lc; unfold Syntax.lc; simp
    apply Iff.intro _ _
    {
      intro h1; apply And.intro _ _
      {
        intro j h; have lem := h1 j h; cases lem; case _ a lem =>
        exists a; exact lem.1
      }
      {
        intro j h
        cases j
        case zero => exfalso; linarith
        case succ j => {
          replace h : i ≤ j := by linarith
          have lem := h1 j h; cases lem; case _ a lem =>
          exists a; exact lem.2
        }
      }
    }
    {
      intro h1 j h
      cases h1; case _ h1 h2 =>
      replace h1 := h1 j h
      replace h2 := h2 (Nat.succ j) (by linarith)
      casesm* ∃ _, _; case _ a1 h1 a2 h2 =>
      exists a1; simp [*]; apply Syntax.unbounded h2
    }
  }
  @[simp] lemma lc_const : lc i (const K) = True := by {
    unfold lc; unfold Syntax.lc; simp; intro j _
    exists @Name.fresh []
  }
  @[simp] lemma lc_typeu : lc i typeu = True := by {
    unfold lc; unfold Syntax.lc; simp; intro j _
    exists @Name.fresh []
  }
  @[simp] lemma lc_kindu : lc i kindu = True := by {
    unfold lc; unfold Syntax.lc; simp; intro j _
    exists @Name.fresh []
  }
  @[simp] lemma lc_free : lc i (free x) = True := by {
    unfold lc; unfold Syntax.lc; simp; intro j _
    exists @Name.fresh []
  }
  lemma lc_bound_lt : j < i -> lc i (bound j) = True := by {
    intro h; unfold lc; unfold Syntax.lc; simp
    intro k gt; exists @Name.fresh []
    unfold Syntax.opn; unfold bound; simp
    intro h2
    exfalso; linarith
  }
  lemma lc_bound_le : i ≤ j -> lc i (bound j) = False := by {
    intro h; unfold lc; unfold Syntax.lc; simp
    exists j; simp [*]; intro x
    unfold Syntax.opn; unfold bound; simp
    intro h; injection h
  }
  @[simp] lemma lc_bound : lc i (bound j) = (j < i) := by {
    cases (Nat.decLt j i)
    case _ h => {
      simp [*]; simp at h;
      have lem := lc_bound_le h
      intro h2; rw [lem] at h2; exact h2
    }
    case _ h => {
      simp; apply Iff.intro (by simp [*])
      intro h; have lem := lc_bound_lt h
      rw [lem]; simp
    }
  }

  @[simp] lemma lc_lam : lc i (lam m t1 t2) = (lc i t1 ∧ lc (Nat.succ i) t2)
    := by unfold lam; rw [lc_bind]
  @[simp] lemma lc_pi : lc i (pi m t1 t2) = (lc i t1 ∧ lc (Nat.succ i) t2)
    := by unfold pi; rw [lc_bind]
  @[simp] lemma lc_inter : lc i (inter t1 t2) = (lc i t1 ∧ lc (Nat.succ i) t2)
    := by unfold inter; rw [lc_bind]
  @[simp] lemma lc_app : lc i (app m t1 t2) = (lc i t1 ∧ lc i t2) :=  by {
    unfold app; rw [lc_ctor]; simp
  }
  @[simp] lemma lc_pair : lc i (pair t1 t2 t3) = (lc i t1 ∧ lc i t2 ∧ lc i t3)
    := by unfold pair; rw [lc_ctor]
  @[simp] lemma lc_proj : lc i (proj p t) = lc i t := by {
    unfold proj; rw [lc_ctor]; simp
  }
  @[simp] lemma lc_eq : lc i (eq t1 t2 t3) = (lc i t1 ∧ lc i t2 ∧ lc i t3)
    := by unfold eq; rw [lc_ctor]
  @[simp] lemma lc_refl : lc i (refl t) = lc i t := by {
    unfold refl; rw [lc_ctor]; simp
  }
  @[simp] lemma lc_subst : lc i (subst t1 t2) = (lc i t1 ∧ lc i t2)
    := by unfold subst; rw [lc_ctor]; simp

  @[simp] lemma lc_promote : lc i (promote t) = lc i t := by {
    unfold promote; rw [lc_ctor]; simp
  }
  @[simp] lemma lc_delta : lc i (delta t) = lc i t := by {
    unfold delta; rw [lc_ctor]; simp
  }
  @[simp] lemma lc_phi : lc i (phi t1 t2) = (lc i t1 ∧ lc i t2)
    := by unfold phi; rw [lc_ctor]; simp

end Cedille
