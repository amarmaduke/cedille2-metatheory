
import Cedille.Def

namespace Cedille

  @[simp low] lemma refold_const {n} : Syntax.const k = @const n k := by congr
  @[simp low] lemma refold_typeu {n} : Syntax.const Constant.typeU = @typeu n := by congr
  @[simp low] lemma refold_kindu {n} : Syntax.const Constant.kindU = @kindu n := by congr
  @[simp low] lemma refold_free {n} : Syntax.free x = @free n x := by congr
  @[simp low] lemma refold_bound {n} {i : Fin n} : Syntax.bound i = @bound n i := by congr
  @[simp low] lemma refold_lam : Syntax.bind (Binder.lam m) t1 t2 = lam m t1 t2 := by congr
  @[simp low] lemma refold_pi : Syntax.bind (Binder.pi m) t1 t2 = pi m t1 t2 := by congr
  @[simp low] lemma refold_inter : Syntax.bind Binder.inter t1 t2 = inter t1 t2 := by congr
  @[simp low] lemma refold_app : Syntax.ctor (Constructor.app m) t1 t2 kindu = app m t1 t2 := by congr
  @[simp low] lemma refold_pair : Syntax.ctor Constructor.pair t1 t2 t3 = pair t1 t2 t3 := by congr
  @[simp low] lemma refold_fst : Syntax.ctor Constructor.fst t kindu kindu = fst t := by congr
  @[simp low] lemma refold_snd : Syntax.ctor Constructor.snd t kindu kindu = snd t := by congr
  @[simp low] lemma refold_eq : Syntax.ctor Constructor.eq t1 t2 t3 = eq t1 t2 t3 := by congr
  @[simp low] lemma refold_refl : Syntax.ctor Constructor.refl t kindu kindu = refl t := by congr
  @[simp low] lemma refold_J {n} : Syntax.ctor Constructor.eqind kindu kindu kindu = @J n := by congr
  @[simp low] lemma refold_promote : Syntax.ctor Constructor.promote t kindu kindu = promote t := by congr
  @[simp low] lemma refold_delta : Syntax.ctor Constructor.delta t kindu kindu = delta t := by congr
  @[simp low] lemma refold_phi : Syntax.ctor Constructor.phi t1 t2 t3 = phi t1 t2 t3 := by congr

  @[simp low] lemma const_to_typeu {n} : const Constant.typeU = @typeu n := by congr
  @[simp low] lemma const_to_kindu {n} : const Constant.kindU = @kindu n := by congr

  @[simp] lemma size_const {n} : size (@const n k) = 0 := by congr
  @[simp] lemma size_typeu {n} : size (@typeu n) = 0 := by congr
  @[simp] lemma size_kindu {n} : size (@kindu n) = 0 := by congr
  @[simp] lemma size_free {n} : size (@free n x) = 0 := by congr
  @[simp] lemma size_bound {n} {i : Fin n} : size (@bound n i) = 0 := by congr
  @[simp] lemma size_lam : size (lam m t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma size_pi : size (pi m t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma size_inter : size (inter t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma size_app : size (app m t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma size_pair : size (pair t1 t2 t3) = size t1 + size t2 + size t3 + 1 := by congr
  @[simp] lemma size_fst : size (fst t) = size t + 1 := by congr
  @[simp] lemma size_snd : size (snd t) = size t + 1 := by congr
  @[simp] lemma size_eq : size (eq t1 t2 t3) = size t1 + size t2 + size t3 + 1 := by congr
  @[simp] lemma size_refl : size (refl t) = size t + 1 := by congr
  @[simp] lemma size_J {n} : size (@J n) = 1 := by congr
  @[simp] lemma size_promote : size (promote t) = size t + 1 := by congr
  @[simp] lemma size_delta : size (delta t) = size t + 1 := by congr
  @[simp] lemma size_phi : size (phi t1 t2 t3) = size t1 + size t2 + size t3 + 1 := by congr

  @[simp] lemma size_bind : size (Syntax.bind k t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma size_ctor : size (Syntax.ctor k t1 t2 t3) = size t1 + size t2 + size t3 + 1 := by congr
  @[simp low] lemma size_size : Syntax.size t = size t := by congr
  @[simp] lemma size_open : size ({_|-> x}t) = size t := by {
    unfold size; rewrite [Syntax.size_opn_head]; rfl
  }

  @[simp low] lemma fv_fv : Syntax.fv t = fv t := by congr
  @[simp] lemma fv_ctor : fv (Syntax.ctor k t1 t2 t3) = fv t1 ++ fv t2 ++ fv t3 := by {
    generalize h : fv t1 ++ fv t2 ++ fv t3 = t
    unfold fv; unfold Syntax.fv; unfold fv at h; rw [h]
  }
  @[simp] lemma fv_bind : fv (Syntax.bind k t1 t2) = fv t1 ++ fv t2 := by {
    generalize h : fv t1 ++ fv t2 = t
    unfold fv; unfold Syntax.fv; simp [*]
  }
  @[simp] lemma fv_const {n} : fv (@const n K) = [] := by congr
  @[simp] lemma fv_typeu {n} : fv (@typeu n) = [] := by congr
  @[simp] lemma fv_kindu {n} : fv (@kindu n) = [] := by congr
  @[simp] lemma fv_free {n} : fv (@free n x) = [x] := by congr
  @[simp] lemma fv_bound {n} {i : Fin n} : fv (@bound n i) = [] := by congr
  @[simp] lemma fv_lam : fv (lam m t1 t2) = fv t1 ++ fv t2 := by congr
  @[simp] lemma fv_pi : fv (pi m t1 t2) = fv t1 ++ fv t2 := by congr
  @[simp] lemma fv_inter : fv (inter t1 t2) = fv t1 ++ fv t2 := by congr
  @[simp] lemma fv_app : fv (app m t1 t2) = fv t1 ++ fv t2 :=  by {
    unfold app; rw [@fv_ctor _ _ t1 t2 _]; simp
  }
  @[simp] lemma fv_pair : fv (pair t1 t2 t3) = fv t1 ++ fv t2 ++ fv t3 := by congr
  @[simp] lemma fv_fst : fv (fst t) = fv t := by {
    unfold fst; rw [@fv_ctor _ _ t _ _]; simp; repeat rw [List.append_nil]
  }
  @[simp] lemma fv_snd : fv (snd t) = fv t := by {
    unfold snd; rw [@fv_ctor _ _ t _ _]; simp; repeat rw [List.append_nil]
  }
  @[simp] lemma fv_eq : fv (eq t1 t2 t3) = fv t1 ++ fv t2 ++ fv t3 := by congr
  @[simp] lemma fv_refl : fv (refl t) = fv t := by {
    unfold refl; rw [@fv_ctor _ _ t _ _]; simp; repeat rw [List.append_nil]
  }
  @[simp] lemma fv_J {n} : fv (@J n) = [] := by congr
  @[simp] lemma fv_promote : fv (promote t) = fv t := by {
    unfold promote; rw [@fv_ctor _ _ t _ _]; simp; repeat rw [List.append_nil]
  }
  @[simp] lemma fv_delta : fv (delta t) = fv t := by {
    unfold delta; rw [@fv_ctor _ _ t _ _]; simp; repeat rw [List.append_nil]
  }
  @[simp] lemma fv_phi : fv (phi t1 t2 t3) = fv t1 ++ fv t2 ++ fv t3 := by congr

end Cedille
