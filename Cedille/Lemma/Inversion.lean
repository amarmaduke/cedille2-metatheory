
import Cedille.Def
import Cedille.Lemma.Refold

namespace Cedille

  lemma ctor_eq (k1 k2 : Constructor) {t1 t2 t3 t4 t5 t6 : Term n}
    : Syntax.ctor k1 t1 t2 t3 = Syntax.ctor k2 t4 t5 t6 -> k1 = k2
  := by {
    intro h
    injection h
  }

  lemma ctor_inv (k1 k2 : Constructor) {t1 t2 t3 t4 t5 t6 : Term n}
    : k1 ≠ k2 -> Syntax.ctor k1 t1 t2 t3 ≠ Syntax.ctor k2 t4 t5 t6
  := contra (ctor_eq k1 k2)

  @[simp] lemma bind_not_app : Syntax.bind b t1 t2 ≠ app m t3 t4 := by {
    unfold app; intro h; injection h
  }
  @[simp] lemma app_not_bind : app m t1 t2 ≠ Syntax.bind b t3 t4 := ne_sym bind_not_app 

  @[simp] lemma app_not_inter : app m t1 t2 ≠ inter t3 t4 := by apply app_not_bind

  @[simp] lemma bound_not_app : bound i ≠ app m t1 t2 := by {
    intro h
    unfold bound at h; unfold app at h
    injection h
  }
  @[simp] lemma app_not_bound : app m t1 t2 ≠ bound i := ne_sym bound_not_app

  @[simp] lemma free_not_app : free x ≠ app m t1 t2 := by {
    intro h
    unfold free at h; unfold app at h
    injection h
  }
  @[simp] lemma app_not_free : app m t1 t2 ≠ free x := ne_sym free_not_app

  @[simp] lemma const_not_app : const c ≠ app m t1 t2 := by {
    intro h
    unfold const at h; unfold app at h
    injection h
  }
  @[simp] lemma app_not_const : app m t1 t2 ≠ const c := ne_sym const_not_app

  @[simp] lemma fst_not_app : fst t1 ≠ app m t2 t3 := by {
    intro h
    unfold fst at h; unfold app at h
    apply (@ctor_inv _ Constructor.fst (Constructor.app m) t1 kindu kindu t2 t3 kindu)
    intro h2; injection h2
    rewrite [h]; rfl
  }

  @[simp] lemma snd_not_app : snd t1 ≠ app m t2 t3 := by {
    intro h
    unfold snd at h; unfold app at h
    apply (@ctor_inv _ Constructor.snd (Constructor.app m) t1 kindu kindu t2 t3 kindu)
    intro h2; injection h2
    rewrite [h]; rfl
  }

  @[simp] lemma promote_not_app : promote t1 ≠ app m t2 t3 := by {
    intro h
    unfold promote at h; unfold app at h
    apply (@ctor_inv _ Constructor.promote (Constructor.app m) t1 kindu kindu t2 t3 kindu)
    intro h2; injection h2
    rewrite [h]; rfl
  }

  @[simp] lemma deltatop_not_app : deltatop t1 ≠ app m t2 t3 := by {
    intro h
    unfold deltatop at h; unfold app at h
    apply (@ctor_inv _ Constructor.deltatop (Constructor.app m) t1 kindu kindu t2 t3 kindu)
    intro h2; injection h2
    rewrite [h]; rfl
  }

  @[simp] lemma deltabot_not_app : deltabot t1 ≠ app m t2 t3 := by {
    intro h
    unfold deltabot at h; unfold app at h
    apply (@ctor_inv _ Constructor.deltabot (Constructor.app m) t1 kindu kindu t2 t3 kindu)
    intro h2; injection h2
    rewrite [h]; rfl
  }

  @[simp] lemma phi_not_app : phi t1 t2 t3 ≠ app m t4 t5 := by {
    intro h
    unfold phi at h; unfold app at h
    apply (@ctor_inv _ Constructor.phi (Constructor.app m) t1 t2 t3 t4 t5 kindu)
    intro h2; injection h2
    rewrite [h]; rfl
  }

  @[simp] lemma app_mf_not_app_mt : t1 @ω t2 ≠ t3 @τ t4 := by {
    intro h
    unfold app at h
    apply (@ctor_inv _ (Constructor.app mf) (Constructor.app mt) t1 t2 kindu t3 t4 kindu)
    intro h; injection h with h2; injection h2
    rewrite [h]; rfl
  }

  @[simp] lemma app_m0_not_app_mt : t1 @0 t2 ≠ t3 @τ t4 := by {
    intro h
    unfold app at h
    apply (@ctor_inv _ (Constructor.app m0) (Constructor.app mt) t1 t2 kindu t3 t4 kindu)
    intro h; injection h with h2; injection h2
    rewrite [h]; rfl
  }

  @[simp] lemma app_mt_not_app_mf : t1 @τ t2 ≠ t3 @ω t4 := by {
    intro h
    unfold app at h
    apply (@ctor_inv _ (Constructor.app mt) (Constructor.app mf) t1 t2 kindu t3 t4 kindu)
    intro h; injection h with h2; injection h2
    rewrite [h]; rfl
  }

  @[simp] lemma app_m0_not_app_mf : t1 @0 t2 ≠ t3 @ω t4 := by {
    intro h
    unfold app at h
    apply (@ctor_inv _ (Constructor.app m0) (Constructor.app mf) t1 t2 kindu t3 t4 kindu)
    intro h; injection h with h2; injection h2
    rewrite [h]; rfl
  }

  @[simp] lemma typeu_not_cbool : typeu ≠ cbool := by {
    intro h; unfold cbool at h; unfold typeu at h; injection h
  }

  @[simp] lemma kindu_not_cbool : kindu ≠ cbool := by {
    intro h; unfold cbool at h; unfold kindu at h; injection h
  }

  @[simp] lemma inter_not_cbool : inter A B ≠ cbool := by {
    intro h; unfold cbool at h; unfold inter at h; injection h with _ e; injection e
  }

  @[simp] lemma eq_not_cbool : eq A t1 t2 ≠ cbool := by {
    intro h; unfold cbool at h; unfold eq at h; injection h
  }

  @[simp] lemma eqind_t_not_cbool : eqind_t ≠ cbool := by sorry

  @[simp] lemma idt_not_cbool : idt ≠ cbool := by {
    intro h; unfold cbool at h; unfold idt at h; injection h with _ _ _ e
    injection e with _ _ _ e; injection e
  }

end Cedille
