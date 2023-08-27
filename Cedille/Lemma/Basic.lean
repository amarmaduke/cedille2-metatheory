
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

  @[simp] lemma mode_lam_domain_mf : Mode.lam_domain mf = @typeu n := by congr
  @[simp] lemma mode_lam_domain_m0 : Mode.lam_domain m0 = @typeu n := by congr
  @[simp] lemma mode_lam_domain_mt : Mode.lam_domain mt = @kindu n := by congr

  lemma subset_mem {x : Name} {A B : FvSet!} : A ⊆ B -> x ∈ A -> x ∈ B := sorry
  @[simp] lemma fv_subst : fv ([_:= t1]t2) = fv t1 ++ fv t2 := sorry
  @[simp] lemma fv_open : fv ({_|-> x}t) = [x] ++ fv t := sorry

  lemma subset_left {A B C : FvSet!} : A ⊆ B -> A ⊆ B ++ C := sorry
  lemma subset_right {A B C : FvSet!} : A ⊆ C -> A ⊆ B ++ C := sorry
  lemma subset_cons {A B : FvSet!} : x ∉ A -> A ⊆ x :: B -> A ⊆ B := sorry
  lemma subset_trans {A B C : FvSet!} : A ⊆ B -> B ⊆ C -> A ⊆ C := sorry 

  lemma not_mem_subset_not_mem {A B : FvSet!} : x ∉ A -> B ⊆ A -> x ∉ B := sorry

end Cedille
