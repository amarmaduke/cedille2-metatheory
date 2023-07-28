
import Cedille.Def

namespace Cedille

  @[simp] lemma const_refold {n} : Syntax.const k = @const n k := by congr
  @[simp] lemma typeu_refold {n} : Syntax.const Constant.typeU = @typeu n := by congr
  @[simp] lemma kindu_refold {n} : Syntax.const Constant.kindU = @kindu n := by congr
  @[simp] lemma free_refold {n} : Syntax.free x = @free n x := by congr
  @[simp] lemma bound_refold {n} {i : Fin n} : Syntax.bound i = @bound n i := by congr
  @[simp] lemma lam_refold : Syntax.bind (Binder.lam m) t1 t2 = lam m t1 t2 := by congr
  @[simp] lemma pi_refold : Syntax.bind (Binder.pi m) t1 t2 = pi m t1 t2 := by congr
  @[simp] lemma inter_refold : Syntax.bind Binder.inter t1 t2 = inter t1 t2 := by congr
  @[simp] lemma app_refold : Syntax.ctor (Constructor.app m) t1 t2 kindu = app m t1 t2 := by congr
  @[simp] lemma pair_refold : Syntax.ctor Constructor.pair t1 t2 kindu = pair t1 t2 := by congr
  @[simp] lemma fst_refold : Syntax.ctor Constructor.fst t kindu kindu = fst t := by congr
  @[simp] lemma snd_refold : Syntax.ctor Constructor.snd t kindu kindu = snd t := by congr
  @[simp] lemma eq_refold : Syntax.ctor Constructor.eq t1 t2 kindu = eq t1 t2 := by congr
  @[simp] lemma refl_refold : Syntax.ctor Constructor.refl t kindu kindu = refl t := by congr
  @[simp] lemma J_refold {n} : Syntax.ctor Constructor.eqind kindu kindu kindu = @J n := by congr
  @[simp] lemma promote_refold : Syntax.ctor Constructor.promote t kindu kindu = promote t := by congr
  @[simp] lemma delta_refold : Syntax.ctor Constructor.delta t kindu kindu = delta t := by congr
  @[simp] lemma phi_refold : Syntax.ctor Constructor.phi t1 t2 t3 = phi t1 t2 t3 := by congr

  @[simp] lemma const_size {n} : size (@const n k) = 0 := by congr
  @[simp] lemma typeu_size {n} : size (@typeu n) = 0 := by congr
  @[simp] lemma kindu_size {n} : size (@kindu n) = 0 := by congr
  @[simp] lemma free_size {n} : size (@free n x) = 0 := by congr
  @[simp] lemma bound_size {n} {i : Fin n} : size (@bound n i) = 0 := by congr
  @[simp] lemma lam_size : size (lam m t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma pi_size : size (pi m t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma inter_size : size (inter t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma app_size : size (app m t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma pair_size : size (pair t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma fst_size : size (fst t) = size t + 1 := by congr
  @[simp] lemma snd_size : size (snd t) = size t + 1 := by congr
  @[simp] lemma eq_size : size (eq t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma refl_size : size (refl t) = size t + 1 := by congr
  @[simp] lemma J_size {n} : size (@J n) = 1 := by congr
  @[simp] lemma promote_size : size (promote t) = size t + 1 := by congr
  @[simp] lemma delta_size : size (delta t) = size t + 1 := by congr
  @[simp] lemma phi_size : size (phi t1 t2 t3) = size t1 + size t2 + size t3 + 1 := by congr

  @[simp] lemma bind_size : size (Syntax.bind k t1 t2) = size t1 + size t2 + 1 := by congr
  @[simp] lemma ctor_size : size (Syntax.ctor k t1 t2 t3) = size t1 + size t2 + size t3 + 1 := by congr
  @[simp] lemma size_size : Syntax.size t = size t := by congr

end Cedille
