
import Common
import Cedille.Def
import Cedille.Lemma.Refold

namespace Cedille

  @[simp] lemma erase_bound : erase (bound i) = bound i := by congr
  @[simp] lemma erase_free {n} : erase (@free n x) = free x := by congr
  @[simp] lemma erase_const {n} : erase (@const n c) = const c := by congr
  @[simp] lemma erase_typeu {n} : erase (@typeu n) = typeu := by congr
  @[simp] lemma erase_kindu {n} : erase (@kindu n) = kindu := by congr
  
  @[simp] lemma erase_lam_mf : erase (lam mf a b) = lam mf kindu (erase b) := by congr
  @[simp] lemma erase_lam_mf_unfolded
    : erase (Syntax.bind (Binder.lam mf) a b) = lam mf kindu (erase b)
  := by congr

  @[simp] lemma erase_lam_mt : erase (lam mt a b) = lam mt (erase a) (erase b) := by congr
  @[simp] lemma erase_lam_mt_unfolded
    : erase (Syntax.bind (Binder.lam mt) a b) = lam mt (erase a) (erase b)
  := by congr

  @[simp] lemma erase_pi : erase (pi m a b) = pi m (erase a) (erase b) := by congr
  @[simp] lemma erase_pi_unfolded
    : erase (Syntax.bind (Binder.pi m) a b) = pi m (erase a) (erase b)
  := by congr

  @[simp] lemma erase_inter : erase (inter a b) = inter (erase a) (erase b) := by congr
  @[simp] lemma erase_inter_unfolded
    : erase (Syntax.bind Binder.inter a b) = inter (erase a) (erase b)
  := by congr

  @[simp] lemma erase_lam_m0 {n} {a : Term n} {b : Term (n + 1)}
    : erase (lam m0 a b) = let x := Name.fresh (fv b); erase ({_|-> x}b)
  := by {
    unfold lam; simp only
    generalize erase ({_|-> Name.fresh (fv b)}b) = t
    rfl
  }

  @[simp] lemma erase_app_m0 : erase (t1 @0 t2) = erase t1 := by generalize erase t1 = t; rfl
  @[simp] lemma erase_app_m0_unfolded
    : erase (Syntax.ctor (Constructor.app m0) t1 t2 t3) = erase t1
  := by generalize erase t1 = t; rfl

  @[simp] lemma erase_app_mf : erase (t1 @ω t2) = (erase t1) @ω (erase t2) := by congr
  @[simp] lemma erase_app_mf_unfolded
    : erase (Syntax.ctor (Constructor.app mf) t1 t2 t3) = app mf (erase t1) (erase t2)
  := by {
    generalize h : (erase t1) @ω (erase t2) = t
    unfold erase; simp only; subst h; rfl
  }

  @[simp] lemma erase_app_mt : erase (t1 @τ t2) = (erase t1) @τ (erase t2) := by congr
  @[simp] lemma erase_app_mt_unfolded
    : erase (Syntax.ctor (Constructor.app mt) t1 t2 t3) = app mt (erase t1) (erase t2)
  := by {
    generalize h : (erase t1) @τ (erase t2) = t
    unfold erase; simp only; subst h; rfl
  }

  @[simp] lemma erase_pair : erase (pair t1 t2 t3) = erase t1 := by generalize erase t1 = t; rfl
  @[simp] lemma erase_pair_unfolded
    : erase (Syntax.ctor Constructor.pair t1 t2 t3) = erase t1
  := by generalize erase t1 = t; rfl

  @[simp] lemma erase_fst : erase (fst t) = erase t := by generalize erase t = s; rfl
  @[simp] lemma erase_fst_unfolded
    : erase (Syntax.ctor Constructor.fst t1 t2 t3) = erase t1
  := by generalize erase t1 = t; rfl

  @[simp] lemma erase_snd : erase (snd t) = erase t := by generalize erase t = s; rfl
  @[simp] lemma erase_snd_unfolded
    : erase (Syntax.ctor Constructor.snd t1 t2 t3) = erase t1
  := by generalize erase t1 = t; rfl

  @[simp] lemma erase_eq : erase (eq t1 t2 t3) = eq (erase t1) (erase t2) (erase t3) := by congr
  @[simp] lemma erase_eq_unfolded
    : erase (Syntax.ctor Constructor.eq t1 t2 t3) = eq (erase t1) (erase t2) (erase t3)
  := by {
    generalize h : eq (erase t1) (erase t2) (erase t3) = t
    unfold erase; subst h; rfl
  }

  @[simp] lemma erase_refl : erase (refl t) = lam mf kindu (bound 0) := by congr
  @[simp] lemma erase_refl_unfolded
    : erase (Syntax.ctor Constructor.refl t1 t2 t3) = lam mf kindu (bound 0)
  := by congr

  @[simp] lemma erase_eqind {n} : erase (@J n) = lam mf kindu (bound 0) := by congr
  @[simp] lemma erase_eqind_unfolded
    : erase (Syntax.ctor Constructor.eqind t1 t2 t3) = lam mf kindu (bound 0)
  := by congr

  @[simp] lemma erase_promote : erase (promote t) = erase t := by generalize erase t = t; rfl
  @[simp] lemma erase_promote_unfolded
    : erase (Syntax.ctor Constructor.promote t1 t2 t3) = erase t1
  := by generalize erase t1 = t; rfl

  @[simp] lemma erase_deltatop : erase (deltatop t) = erase t := by generalize erase t = s; rfl
  @[simp] lemma erase_deltatop_unfolded
    : erase (Syntax.ctor Constructor.deltatop t1 t2 t3) = erase t1
  := by generalize erase t1 = t; rfl

  @[simp] lemma erase_deltabot : erase (deltabot t) = erase t := by generalize erase t = s; rfl
  @[simp] lemma erase_deltabot_unfolded
    : erase (Syntax.ctor Constructor.deltabot t1 t2 t3) = erase t1
  := by generalize erase t1 = t; rfl

  @[simp] lemma erase_phi : erase (phi t1 t2 t3) = erase t1 := by generalize erase t1 = t; rfl

  @[simp] lemma erase_idem {m} {t : Term m} : erase (erase t) = erase t := @Nat.rec
    (λ n => {m : Nat} -> (t : Term m) -> size t ≤ n -> erase (erase t) = erase t)
    (by {
      intro m t h
      cases t <;> simp <;> simp at h
    })
    (by {
      intros n ih m t h
      cases t <;> simp <;> simp at h
      case bind k t1 t2 => {
        have h := Nat.le_of_succ_le_succ h
        have h := nat_add_le h
        casesm* _ ∧ _
        case _ h1 h2 =>
        have lem1 := ih t1 h1
        have lem2 := ih t2 h2
        cases k <;> simp [*]
        case lam k =>
        cases k <;> simp [*]
        case erased =>
        have lem := @Syntax.size_opn_head _ _ _ _ (Name.fresh (fv t2)) t2
        rewrite [Cedille.size_size, Cedille.size_size] at lem
        rewrite [<-lem] at h2
        have lem := ih _ h2
        rewrite [lem]
        rfl
      }
      case ctor k t1 t2 t3 => {
        have h := Nat.le_of_succ_le_succ h
        have h := nat_add_le h
        casesm* _ ∧ _
        case _ h1 _ =>
        have h := nat_add_le h1
        casesm* _ ∧ _
        case _ h1 h2 =>
        cases k <;> simp [*]
        case app m =>
        cases m <;> simp [*]
      }
    })
    (size t)
    m
    t
    (by simp)

  @[simp] lemma erase_subst : erase ([_:= a]f) = [_:= erase a](erase f) := sorry

  lemma erase_close_open : erase t = {_|-> x}s -> erase ({_<-| x}t) = s := sorry

  lemma erase_forces_lam_mt : erase f = lam mt t1 t2 ->
    ∃ t1' t2', erase t1' = t1 ∧ erase t2' = t2 ∧ f = lam mt t1' t2'
  := sorry

  lemma erase_forces_lam_mf : erase f = lam mf t1 t2 ->
    ∃ t1' t2', erase t1' = t1 ∧ erase t2' = t2 ∧ f = lam mf t1' t2'
  := sorry

  lemma erase_no_eqind : erase f ≠ J @τ t1 @τ t2 @0 t3 @0 t4 @ω t5 := sorry

  lemma erase_free_invariant :
    x ∉ (fv ∘ erase) ({_|-> x}t) ->
    (y : Name) -> y ∉ fv t ->
    erase ({_|-> x}t) = erase ({_|-> y}t)
  := sorry

  lemma erase_ctt_eq : erase t = erase ctt -> t = lam mf kindu (lam mf kindu (bound 0)) := sorry
  lemma erase_cff_eq : erase t = erase cff -> t = lam mf kindu (lam mf kindu (bound 1)) := sorry

end Cedille
