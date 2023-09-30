
import Cedille.Def
import Cedille.Lemma.Refold

namespace Cedille

  @[simp] def open_bound_1_0 : {_|-> x}(@bound 1 0) = free x := by {
      unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
      unfold Syntax.opn_head; simp; unfold bound; simp
  }

  @[simp] def open_bound_2_0 : {_|-> x}(@bound 2 0) = @bound 1 0 := by {
    unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
    unfold Syntax.opn_head; simp; unfold bound; simp;
  }

  @[simp] def open_bound_2_1 : {_|-> x}(@bound 2 1) = free x := by {
    unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
    unfold Syntax.opn_head; simp; unfold bound; simp
  }

  @[simp] lemma fv_id_empty : @fv n (lam mf kindu (bound 0)) = [] := by {
    unfold lam; unfold fv; unfold Syntax.fv;
    unfold Syntax.fv; unfold kindu; simp
    unfold bound; simp;
  }

  @[simp] lemma mode_pi_domain_mf : Mode.pi_domain mf K = @typeu n := by congr
  @[simp] lemma mode_pi_domain_m0 : Mode.pi_domain m0 K = @const n K := by congr
  @[simp] lemma mode_pi_domain_mt : Mode.pi_domain mt K = @const n K := by congr

  @[simp] lemma mode_pi_codomain_mf : Mode.pi_codomain mf = @typeu n := by congr
  @[simp] lemma mode_pi_codomain_m0 : Mode.pi_codomain m0 = @typeu n := by congr
  @[simp] lemma mode_pi_codomain_mt : Mode.pi_codomain mt = @kindu n := by congr

  @[simp] lemma refl_erased_is_normal : ¬ (lam mf kindu (bound 0) -β> t) := by {
    intro h
    cases h
    case bind1 _ step => cases step
    case bind2 _ S step => {
      have xfresh := @Name.fresh_is_fresh S
      generalize _xdef : Name.fresh S = x at *
      replace step := step x xfresh
      simp at *; cases step
    }
  }

end Cedille
