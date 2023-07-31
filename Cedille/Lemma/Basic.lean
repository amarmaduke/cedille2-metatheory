
import Cedille.Def

namespace Cedille

  @[simp] def open_bound_1_0 : {_|-> x}(@bound 1 0) = free x := by {
      unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
      unfold Syntax.opn_head; simp; unfold bound; simp; unfold free; simp
  }

  @[simp] def open_bound_2_0 : {_|-> x}(@bound 2 0) = @bound 1 0 := by {
    unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
    unfold Syntax.opn_head; simp; unfold bound; simp;
  }

  @[simp] def open_bound_2_1 : {_|-> x}(@bound 2 1) = free x := by {
    unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
    unfold Syntax.opn_head; simp; unfold bound; simp; unfold free; simp
  }
  
  @[simp] def open_free : {_|-> y}(@free (n + 1) x) = free x := by {
    unfold free; simp
  }

  @[simp] lemma fv_id_empty : @fv n (lam mf kindu (bound 0)) = [] := by {
    unfold lam; unfold fv; unfold Syntax.fv;
    unfold Syntax.fv; unfold kindu; simp
    unfold bound; simp;
  }

  @[simp] lemma mode_pi_domain_mf : Mode.pi_domain mf K = typeu := by congr
  @[simp] lemma mode_pi_domain_m0 : Mode.pi_domain m0 K = const K := by congr
  @[simp] lemma mode_pi_domain_mt : Mode.pi_domain mt K = const K := by congr

  lemma conv_mode_pi_domain : A =β= Mode.pi_domain m K -> A -β>* Mode.pi_domain m K := by {
    intros h; cases h; case _ t1 t2 s1 s2 e =>
    
  }

  @[simp] lemma mode_pi_codomain_mf : Mode.pi_codomain mf = typeu := by congr
  @[simp] lemma mode_pi_codomain_m0 : Mode.pi_codomain m0 = typeu := by congr
  @[simp] lemma mode_pi_codomain_mt : Mode.pi_codomain mt = kindu := by congr

  @[simp] lemma mode_lam_domain_mf : Mode.lam_domain mf = typeu := by congr
  @[simp] lemma mode_lam_domain_m0 : Mode.lam_domain m0 = typeu := by congr
  @[simp] lemma mode_lam_domain_mt : Mode.lam_domain mt = kindu := by congr

  @[simp] lemma open_lambda : {_|-> x}lam m t1 t2 = lam m ({_|-> x}t1) ({_|-> x}t2) := by {
    unfold lam; simp
  }

  @[simp] lemma open_pi : {_|-> x}pi m t1 t2 = pi m ({_|-> x}t1) ({_|-> x}t2) := by {
    unfold pi; simp
  }

end Cedille
