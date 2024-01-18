
import Cedille.Def
import Cedille.Lemma.Refold

namespace Cedille

  macro "inv" : tactic => `(tactic| {
      try intro h
      try unfold const at *
      try unfold typeu at *
      try unfold kindu at *
      try unfold free at *
      try unfold bound at *
      try unfold lam at *
      try unfold pi at *
      try unfold inter at *
      try unfold app at *
      try unfold pair at *
      try unfold fst at *
      try unfold snd at *
      try unfold eq at *
      try unfold refl at *
      try unfold J at *
      try unfold promote at *
      try unfold delta at *
      try unfold phi at *
      try {
        injection h
      }
      try {
        injection h with h1 h2 h3
        injection h1
      }
      try {
        injection h with h1 h2 h3
        injection h1 with h1
        injection h1
      }
      try {
        injection h with h1 h2 h3
        injection h2
      }
      try {
        injection h with h1 h2 h3
        injection h2 with h4
        injection h4
      }
  })

  @[simp] lemma inv_binder_m0 : ¬ (Binder.lam m0 ≠ Binder.lam m0) := by intro h; apply h (by simp)

  @[simp] lemma const_not_free : const k ≠ free x := by inv
  @[simp] lemma const_not_bound : const k ≠ bound i := by inv
  @[simp] lemma const_not_lam : const k ≠ lam m t1 t2 := by inv
  @[simp] lemma const_not_pi : const k ≠ pi m t1 t2 := by inv
  @[simp] lemma const_not_inter : const k ≠ inter t1 t2 := by inv
  @[simp] lemma const_not_app : const k ≠ app m t1 t2 := by inv
  @[simp] lemma const_not_pair : const k ≠ pair t1 t2 t3 := by inv
  @[simp] lemma const_not_fst : const k ≠ proj i t := by inv
  @[simp] lemma const_not_eq : const k ≠ eq t1 t2 t3 := by inv
  @[simp] lemma const_not_refl : const k ≠ refl t := by inv
  @[simp] lemma const_not_Jh : const k ≠ Jh t1 t2 t3 := by inv
  @[simp] lemma const_not_J0 : const k ≠ J0 t1 t2 := by inv
  @[simp] lemma const_not_Jω : const k ≠ Jω t1 t2 := by inv
  @[simp] lemma const_not_J : const k ≠ J t1 t2 t3 t4 t5 t6 := by inv
  @[simp] lemma const_not_promote : const k ≠ promote t := by inv
  @[simp] lemma const_not_delta : const k ≠ delta t := by inv
  @[simp] lemma const_not_phi : const k ≠ phi t1 t2 t3 := by inv
  @[simp] lemma const_not_bind : const k ≠ Syntax.bind b t1 t2 := by inv
  @[simp] lemma const_not_ctor : const k ≠ Syntax.ctor c t1 t2 t3 := by inv

  @[simp] lemma typeu_not_free : typeu ≠ free x := by inv
  @[simp] lemma typeu_not_bound : typeu ≠ bound i := by inv
  @[simp] lemma typeu_not_lam : typeu ≠ lam m t1 t2 := by inv
  @[simp] lemma typeu_not_pi : typeu ≠ pi m t1 t2 := by inv
  @[simp] lemma typeu_not_inter : typeu ≠ inter t1 t2 := by inv
  @[simp] lemma typeu_not_app : typeu ≠ app m t1 t2 := by inv
  @[simp] lemma typeu_not_pair : typeu ≠ pair t1 t2 t3 := by inv
  @[simp] lemma typeu_not_fst : typeu ≠ proj i t := by inv
  @[simp] lemma typeu_not_eq : typeu ≠ eq t1 t2 t3 := by inv
  @[simp] lemma typeu_not_refl : typeu ≠ refl t := by inv
  @[simp] lemma typeu_not_Jh : typeu ≠ Jh t1 t2 t3 := by inv
  @[simp] lemma typeu_not_J0 : typeu ≠ J0 t1 t2 := by inv
  @[simp] lemma typeu_not_Jω : typeu ≠ Jω t1 t2 := by inv
  @[simp] lemma typeu_not_J : typeu ≠ J t1 t2 t3 t4 t5 t6 := by inv
  @[simp] lemma typeu_not_promote : typeu ≠ promote t := by inv
  @[simp] lemma typeu_not_delta : typeu ≠ delta t := by inv
  @[simp] lemma typeu_not_phi : typeu ≠ phi t1 t2 t3 := by inv
  @[simp] lemma typeu_not_bind : typeu ≠ Syntax.bind b t1 t2 := by inv
  @[simp] lemma typeu_not_ctor : typeu ≠ Syntax.ctor c t1 t2 t3 := by inv

  @[simp] lemma kindu_not_free : kindu ≠ free x := by inv
  @[simp] lemma kindu_not_bound : kindu ≠ bound i := by inv
  @[simp] lemma kindu_not_lam : kindu ≠ lam m t1 t2 := by inv
  @[simp] lemma kindu_not_pi : kindu ≠ pi m t1 t2 := by inv
  @[simp] lemma kindu_not_inter : kindu ≠ inter t1 t2 := by inv
  @[simp] lemma kindu_not_app : kindu ≠ app m t1 t2 := by inv
  @[simp] lemma kindu_not_pair : kindu ≠ pair t1 t2 t3 := by inv
  @[simp] lemma kindu_not_fst : kindu ≠ proj i t := by inv
  @[simp] lemma kindu_not_eq : kindu ≠ eq t1 t2 t3 := by inv
  @[simp] lemma kindu_not_refl : kindu ≠ refl t := by inv
  @[simp] lemma kindu_not_Jh : kindu ≠ Jh t1 t2 t3 := by inv
  @[simp] lemma kindu_not_J0 : kindu ≠ J0 t1 t2 := by inv
  @[simp] lemma kindu_not_Jω : kindu ≠ Jω t1 t2 := by inv
  @[simp] lemma kindu_not_J : kindu ≠ J t1 t2 t3 t4 t5 t6 := by inv
  @[simp] lemma kindu_not_promote : kindu ≠ promote t := by inv
  @[simp] lemma kindu_not_delta : kindu ≠ delta t := by inv
  @[simp] lemma kindu_not_phi : kindu ≠ phi t1 t2 t3 := by inv
  @[simp] lemma kindu_not_bind : kindu ≠ Syntax.bind b t1 t2 := by inv
  @[simp] lemma kindu_not_ctor : kindu ≠ Syntax.ctor c t1 t2 t3 := by inv

  @[simp] lemma free_not_const : free x ≠ const k := by inv
  @[simp] lemma free_not_typeu : free x ≠ typeu := by inv
  @[simp] lemma free_not_kindu : free x ≠ kindu := by inv
  @[simp] lemma free_not_bound : free x ≠ bound i := by inv
  @[simp] lemma free_not_lam : free x ≠ lam m t1 t2 := by inv
  @[simp] lemma free_not_pi : free x ≠ pi m t1 t2 := by inv
  @[simp] lemma free_not_inter : free x ≠ inter t1 t2 := by inv
  @[simp] lemma free_not_app : free x ≠ app m t1 t2 := by inv
  @[simp] lemma free_not_pair : free x ≠ pair t1 t2 t3 := by inv
  @[simp] lemma free_not_fst : free x ≠ proj i t := by inv
  @[simp] lemma free_not_eq : free x ≠ eq t1 t2 t3 := by inv
  @[simp] lemma free_not_refl : free x ≠ refl t := by inv
  @[simp] lemma free_not_Jh : free x ≠ Jh t1 t2 t3 := by inv
  @[simp] lemma free_not_J0 : free x ≠ J0 t1 t2 := by inv
  @[simp] lemma free_not_Jω : free x ≠ Jω t1 t2 := by inv
  @[simp] lemma free_not_J : free x ≠ J t1 t2 t3 t4 t5 t6 := by inv
  @[simp] lemma free_not_promote : free x ≠ promote t := by inv
  @[simp] lemma free_not_delta : free x ≠ delta t := by inv
  @[simp] lemma free_not_phi : free x ≠ phi t1 t2 t3 := by inv
  @[simp] lemma free_not_bind : free x ≠ Syntax.bind b t1 t2 := by inv
  @[simp] lemma free_not_ctor : free x ≠ Syntax.ctor c t1 t2 t3 := by inv

  @[simp] lemma bound_not_const : bound i ≠ const k := by inv
  @[simp] lemma bound_not_typeu : bound i ≠ typeu := by inv
  @[simp] lemma bound_not_kindu : bound i ≠ kindu := by inv
  @[simp] lemma bound_not_free : bound i ≠ free x := by inv
  @[simp] lemma bound_not_lam : bound i ≠ lam m t1 t2 := by inv
  @[simp] lemma bound_not_pi : bound i ≠ pi m t1 t2 := by inv
  @[simp] lemma bound_not_inter : bound i ≠ inter t1 t2 := by inv
  @[simp] lemma bound_not_app : bound i ≠ app m t1 t2 := by inv
  @[simp] lemma bound_not_pair : bound i ≠ pair t1 t2 t3 := by inv
  @[simp] lemma bound_not_fst : bound i ≠ proj p t := by inv
  @[simp] lemma bound_not_eq : bound i ≠ eq t1 t2 t3 := by inv
  @[simp] lemma bound_not_refl : bound i ≠ refl t := by inv
  @[simp] lemma bound_not_Jh : bound i ≠ Jh t1 t2 t3 := by inv
  @[simp] lemma bound_not_J0 : bound i ≠ J0 t1 t2 := by inv
  @[simp] lemma bound_not_Jω : bound i ≠ Jω t1 t2 := by inv
  @[simp] lemma bound_not_J : bound i ≠ J t1 t2 t3 t4 t5 t6 := by inv
  @[simp] lemma bound_not_promote : bound i ≠ promote t := by inv
  @[simp] lemma bound_not_delta : bound i ≠ delta t := by inv
  @[simp] lemma bound_not_phi : bound i ≠ phi t1 t2 t3 := by inv
  @[simp] lemma bound_not_bind : bound i ≠ Syntax.bind b t1 t2 := by inv
  @[simp] lemma bound_not_ctor : bound i ≠ Syntax.ctor c t1 t2 t3 := by inv

  @[simp] lemma lam_not_const : lam m t1 t2 ≠ const k := by inv
  @[simp] lemma lam_not_typeu : lam m t1 t2 ≠ typeu := by inv
  @[simp] lemma lam_not_kindu : lam m t1 t2 ≠ kindu := by inv
  @[simp] lemma lam_not_free : lam m t1 t2 ≠ free x := by inv
  @[simp] lemma lam_not_bound : lam m t1 t2 ≠ bound i := by inv
  @[simp] lemma lam_not_pi : lam m1 t1 t2 ≠ pi m2 t3 t4 := by inv
  @[simp] lemma lam_not_inter : lam m t1 t2 ≠ inter t3 t4 := by inv
  @[simp] lemma lam_not_app : lam m1 t1 t2 ≠ app m2 t3 t4 := by inv
  @[simp] lemma lam_not_pair : lam m t1 t2 ≠ pair t3 t4 t5 := by inv
  @[simp] lemma lam_not_fst : lam m t1 t2 ≠ proj i t := by inv
  @[simp] lemma lam_not_eq : lam m t1 t2 ≠ eq t3 t4 t5 := by inv
  @[simp] lemma lam_not_refl : lam m t1 t2 ≠ refl t := by inv
  @[simp] lemma lam_not_Jh : lam m t1 t2 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma lam_not_J0 : lam m t1 t2 ≠ J0 u1 u2 := by inv
  @[simp] lemma lam_not_Jω : lam m t1 t2 ≠ Jω u1 u2 := by inv
  @[simp] lemma lam_not_J : lam m t1 t2 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma lam_not_promote : lam m t1 t2 ≠ promote t := by inv
  @[simp] lemma lam_not_delta : lam m t1 t2 ≠ delta t := by inv
  @[simp] lemma lam_not_phi : lam m t1 t2 ≠ phi t3 t4 t5 := by inv
  @[simp] lemma lam_not_ctor : lam m t1 t2 ≠ Syntax.ctor c q1 q2 q3 := by inv

  @[simp] lemma lam_m0_not_lam_mf : lam m0 t1 t2 ≠ lam mf t3 t4 := by inv
  @[simp] lemma lam_m0_not_lam_mt : lam m0 t1 t2 ≠ lam mt t3 t4 := by inv
  @[simp] lemma lam_mf_not_lam_m0 : lam mf t1 t2 ≠ lam m0 t3 t4 := by inv
  @[simp] lemma lam_mf_not_lam_mt : lam mf t1 t2 ≠ lam mt t3 t4 := by inv
  @[simp] lemma lam_mt_not_lam_m0 : lam mt t1 t2 ≠ lam m0 t3 t4 := by inv
  @[simp] lemma lam_mt_not_lam_mf : lam mt t1 t2 ≠ lam mf t3 t4 := by inv

  @[simp] lemma pi_not_const : pi m t1 t2 ≠ const k := by inv
  @[simp] lemma pi_not_typeu : pi m t1 t2 ≠ typeu := by inv
  @[simp] lemma pi_not_kindu : pi m t1 t2 ≠ kindu := by inv
  @[simp] lemma pi_not_free : pi m t1 t2 ≠ free x := by inv
  @[simp] lemma pi_not_bound : pi m t1 t2 ≠ bound i := by inv
  @[simp] lemma pi_not_lam : pi m1 t1 t2 ≠ lam m2 t3 t4 := by inv
  @[simp] lemma pi_not_inter : pi m t1 t2 ≠ inter t3 t4 := by inv
  @[simp] lemma pi_not_app : pi m1 t1 t2 ≠ app m2 t3 t4 := by inv
  @[simp] lemma pi_not_pair : pi m t1 t2 ≠ pair t3 t4 t5 := by inv
  @[simp] lemma pi_not_fst : pi m t1 t2 ≠ proj i t := by inv
  @[simp] lemma pi_not_eq : pi m t1 t2 ≠ eq t3 t4 t5 := by inv
  @[simp] lemma pi_not_refl : pi m t1 t2 ≠ refl t := by inv
  @[simp] lemma pi_not_Jh : pi m t1 t2 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma pi_not_J0 : pi m t1 t2 ≠ J0 u1 u2 := by inv
  @[simp] lemma pi_not_Jω : pi m t1 t2 ≠ Jω u1 u2 := by inv
  @[simp] lemma pi_not_J : pi m t1 t2 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma pi_not_promote : pi m t1 t2 ≠ promote t := by inv
  @[simp] lemma pi_not_delta : pi m t1 t2 ≠ delta t := by inv
  @[simp] lemma pi_not_phi : pi m t1 t2 ≠ phi t3 t4 t5 := by inv
  @[simp] lemma pi_not_ctor : pi m t1 t2 ≠ Syntax.ctor c q1 q2 q3 := by inv

  @[simp] lemma pi_m0_not_pi_mf : pi m0 t1 t2 ≠ pi mf t3 t4 := by inv
  @[simp] lemma pi_m0_not_pi_mt : pi m0 t1 t2 ≠ pi mt t3 t4 := by inv
  @[simp] lemma pi_mf_not_pi_m0 : pi mf t1 t2 ≠ pi m0 t3 t4 := by inv
  @[simp] lemma pi_mf_not_pi_mt : pi mf t1 t2 ≠ pi mt t3 t4 := by inv
  @[simp] lemma pi_mt_not_pi_m0 : pi mt t1 t2 ≠ pi m0 t3 t4 := by inv
  @[simp] lemma pi_mt_not_pi_mf : pi mt t1 t2 ≠ pi mf t3 t4 := by inv

  @[simp] lemma inter_not_const : inter t1 t2 ≠ const k := by inv
  @[simp] lemma inter_not_typeu : inter t1 t2 ≠ typeu := by inv
  @[simp] lemma inter_not_kindu : inter t1 t2 ≠ kindu := by inv
  @[simp] lemma inter_not_free : inter t1 t2 ≠ free x := by inv
  @[simp] lemma inter_not_bound : inter t1 t2 ≠ bound i := by inv
  @[simp] lemma inter_not_lam : inter t1 t2 ≠ lam m t3 t4 := by inv
  @[simp] lemma inter_not_pi : inter t1 t2 ≠ pi m t3 t4 := by inv
  @[simp] lemma inter_not_app : inter t1 t2 ≠ app m t3 t4 := by inv
  @[simp] lemma inter_not_pair : inter t1 t2 ≠ pair t3 t4 t5 := by inv
  @[simp] lemma inter_not_fst : inter t1 t2 ≠ proj i t := by inv
  @[simp] lemma inter_not_eq : inter t1 t2 ≠ eq t3 t4 t5 := by inv
  @[simp] lemma inter_not_refl : inter t1 t2 ≠ refl t := by inv
  @[simp] lemma inter_not_Jh : inter t1 t2 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma inter_not_J0 : inter t1 t2 ≠ J0 u1 u2 := by inv
  @[simp] lemma inter_not_Jω : inter t1 t2 ≠ Jω u1 u2 := by inv
  @[simp] lemma inter_not_J : inter t1 t2 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma inter_not_promote : inter t1 t2 ≠ promote t := by inv
  @[simp] lemma inter_not_delta : inter t1 t2 ≠ delta t := by inv
  @[simp] lemma inter_not_phi : inter t1 t2 ≠ phi t3 t4 t5 := by inv
  @[simp] lemma inter_not_ctor : inter t1 t2 ≠ Syntax.ctor c q1 q2 q3 := by inv

  @[simp] lemma app_not_const : app m t1 t2 ≠ const k := by inv
  @[simp] lemma app_not_typeu : app m t1 t2 ≠ typeu := by inv
  @[simp] lemma app_not_kindu : app m t1 t2 ≠ kindu := by inv
  @[simp] lemma app_not_free : app m t1 t2 ≠ free x := by inv
  @[simp] lemma app_not_bound : app m t1 t2 ≠ bound i := by inv
  @[simp] lemma app_not_lam : app m1 t1 t2 ≠ lam m2 t3 t4 := by inv
  @[simp] lemma app_not_pi : app m1 t1 t2 ≠ pi m2 t3 t4 := by inv
  @[simp] lemma app_not_inter : app m t1 t2 ≠ inter t3 t4 := by inv
  @[simp] lemma app_not_pair : app m t1 t2 ≠ pair t3 t4 t5 := by inv
  @[simp] lemma app_not_fst : app m t1 t2 ≠ proj i t := by inv
  @[simp] lemma app_not_eq : app m t1 t2 ≠ eq t3 t4 t5 := by inv
  @[simp] lemma app_not_refl : app m t1 t2 ≠ refl t := by inv
  @[simp] lemma app_not_Jh : app m t1 t2 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma app_not_J0 : app m t1 t2 ≠ J0 u1 u2 := by inv
  @[simp] lemma app_not_Jω : app m t1 t2 ≠ Jω u1 u2 := by inv
  @[simp] lemma app_not_J : app m t1 t2 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma app_not_promote : app m t1 t2 ≠ promote t := by inv
  @[simp] lemma app_not_delta : app m t1 t2 ≠ delta t := by inv
  @[simp] lemma app_not_phi : app m t1 t2 ≠ phi t3 t4 t5 := by inv
  @[simp] lemma app_not_bind : app m t1 t2 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma app_m0_not_app_mf : app m0 t1 t2 ≠ app mf t3 t4 := by inv
  @[simp] lemma app_m0_not_app_mt : app m0 t1 t2 ≠ app mt t3 t4 := by inv
  @[simp] lemma app_mf_not_app_m0 : app mf t1 t2 ≠ app m0 t3 t4 := by inv
  @[simp] lemma app_mf_not_app_mt : app mf t1 t2 ≠ app mt t3 t4 := by inv
  @[simp] lemma app_mt_not_app_m0 : app mt t1 t2 ≠ app m0 t3 t4 := by inv
  @[simp] lemma app_mt_not_app_mf : app mt t1 t2 ≠ app mf t3 t4 := by inv

  @[simp] lemma pair_not_const : pair t1 t2 t3 ≠ const k := by inv
  @[simp] lemma pair_not_typeu : pair t1 t2 t3 ≠ typeu := by inv
  @[simp] lemma pair_not_kindu : pair t1 t2 t3 ≠ kindu := by inv
  @[simp] lemma pair_not_free : pair t1 t2 t3 ≠ free x := by inv
  @[simp] lemma pair_not_bound : pair t1 t2 t3 ≠ bound i := by inv
  @[simp] lemma pair_not_lam : pair t1 t2 t3 ≠ lam m q1 q2 := by inv
  @[simp] lemma pair_not_pi : pair t1 t2 t3 ≠ pi m q1 q2 := by inv
  @[simp] lemma pair_not_inter : pair t1 t2 t3 ≠ inter q1 q2 := by inv
  @[simp] lemma pair_not_app : pair t1 t2 t3 ≠ app m q1 q2 := by inv
  @[simp] lemma pair_not_fst : pair t1 t2 t3 ≠ proj i q1 := by inv
  @[simp] lemma pair_not_eq : pair t1 t2 t3 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma pair_not_refl : pair t1 t2 t3 ≠ refl q1 := by inv
  @[simp] lemma pair_not_Jh : pair t1 t2 t3 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma pair_not_J0 : pair t1 t2 t3 ≠ J0 u1 u2 := by inv
  @[simp] lemma pair_not_Jω : pair t1 t2 t3 ≠ Jω u1 u2 := by inv
  @[simp] lemma pair_not_J : pair t1 t2 t3 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma pair_not_promote : pair t1 t2 t3 ≠ promote q1 := by inv
  @[simp] lemma pair_not_delta : pair t1 t2 t3 ≠ delta q1 := by inv
  @[simp] lemma pair_not_phi : pair t1 t2 t3 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma pair_not_bind : pair t1 t2 t3 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma proj_not_const : proj i t1 ≠ const k := by inv
  @[simp] lemma proj_not_typeu : proj i t1 ≠ typeu := by inv
  @[simp] lemma proj_not_kindu : proj i t1 ≠ kindu := by inv
  @[simp] lemma proj_not_free : proj i t1 ≠ free x := by inv
  @[simp] lemma proj_not_bound : proj i t1 ≠ bound j := by inv
  @[simp] lemma proj_not_lam : proj i t1 ≠ lam m q1 q2 := by inv
  @[simp] lemma proj_not_pi : proj i t1 ≠ pi m q1 q2 := by inv
  @[simp] lemma proj_not_inter : proj i t1 ≠ inter q1 q2 := by inv
  @[simp] lemma proj_not_app : proj i t1 ≠ app m q1 q2 := by inv
  @[simp] lemma proj_not_pair : proj i t1 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma proj_not_eq : proj i t1 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma proj_not_refl : proj i t1 ≠ refl q1 := by inv
  @[simp] lemma proj_not_Jh : proj i t1 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma proj_not_J0 : proj i t1 ≠ J0 u1 u2 := by inv
  @[simp] lemma proj_not_Jω : proj i t1 ≠ Jω u1 u2 := by inv
  @[simp] lemma proj_not_J : proj i t1 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma proj_not_promote : proj i t1 ≠ promote q1 := by inv
  @[simp] lemma proj_not_delta : proj i t1 ≠ delta q1 := by inv
  @[simp] lemma proj_not_phi : proj i t1 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma proj_not_bind : proj i t1 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma fst_not_const : proj 1 t1 ≠ const k := by inv
  @[simp] lemma fst_not_typeu : proj 1 t1 ≠ typeu := by inv
  @[simp] lemma fst_not_kindu : proj 1 t1 ≠ kindu := by inv
  @[simp] lemma fst_not_free : proj 1 t1 ≠ free x := by inv
  @[simp] lemma fst_not_bound : proj 1 t1 ≠ bound i := by inv
  @[simp] lemma fst_not_lam : proj 1 t1 ≠ lam m q1 q2 := by inv
  @[simp] lemma fst_not_pi : proj 1 t1 ≠ pi m q1 q2 := by inv
  @[simp] lemma fst_not_inter : proj 1 t1 ≠ inter q1 q2 := by inv
  @[simp] lemma fst_not_app : proj 1 t1 ≠ app m q1 q2 := by inv
  @[simp] lemma fst_not_pair : proj 1 t1 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma fst_not_snd : proj 1 t1 ≠ proj 2 q1 := by inv
  @[simp] lemma fst_not_eq : proj 1 t1 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma fst_not_refl : proj 1 t1 ≠ refl q1 := by inv
  @[simp] lemma fst_not_Jh : proj 1 t1 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma fst_not_J0 : proj 1 t1 ≠ J0 u1 u2 := by inv
  @[simp] lemma fst_not_Jω : proj 1 t1 ≠ Jω u1 u2 := by inv
  @[simp] lemma fst_not_J : proj 1 t1 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma fst_not_promote : proj 1 t1 ≠ promote q1 := by inv
  @[simp] lemma fst_not_delta : proj 1 t1 ≠ delta q1 := by inv
  @[simp] lemma fst_not_phi : proj 1 t1 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma fst_not_bind : proj 1 t1 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma snd_not_const : proj 2 t1 ≠ const k := by inv
  @[simp] lemma snd_not_typeu : proj 2 t1 ≠ typeu := by inv
  @[simp] lemma snd_not_kindu : proj 2 t1 ≠ kindu := by inv
  @[simp] lemma snd_not_free : proj 2 t1 ≠ free x := by inv
  @[simp] lemma snd_not_bound : proj 2 t1 ≠ bound i := by inv
  @[simp] lemma snd_not_lam : proj 2 t1 ≠ lam m q1 q2 := by inv
  @[simp] lemma snd_not_pi : proj 2 t1 ≠ pi m q1 q2 := by inv
  @[simp] lemma snd_not_inter : proj 2 t1 ≠ inter q1 q2 := by inv
  @[simp] lemma snd_not_app : proj 2 t1 ≠ app m q1 q2 := by inv
  @[simp] lemma snd_not_pair : proj 2 t1 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma snd_not_fst : proj 2 t1 ≠ proj 1 q1 := by inv
  @[simp] lemma snd_not_eq : proj 2 t1 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma snd_not_refl : proj 2 t1 ≠ refl q1 := by inv
  @[simp] lemma snd_not_Jh : proj 2 t1 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma snd_not_J0 : proj 2 t1 ≠ J0 u1 u2 := by inv
  @[simp] lemma snd_not_Jω : proj 2 t1 ≠ Jω u1 u2 := by inv
  @[simp] lemma snd_not_J : proj 2 t1 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma snd_not_promote : proj 2 t1 ≠ promote q1 := by inv
  @[simp] lemma snd_not_delta : proj 2 t1 ≠ delta q1 := by inv
  @[simp] lemma snd_not_phi : proj 2 t1 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma snd_not_bind : proj 2 t1 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma eq_not_const : eq t1 t2 t3 ≠ const k := by inv
  @[simp] lemma eq_not_typeu : eq t1 t2 t3 ≠ typeu := by inv
  @[simp] lemma eq_not_kindu : eq t1 t2 t3 ≠ kindu := by inv
  @[simp] lemma eq_not_free : eq t1 t2 t3 ≠ free x := by inv
  @[simp] lemma eq_not_bound : eq t1 t2 t3 ≠ bound i := by inv
  @[simp] lemma eq_not_lam : eq t1 t2 t3 ≠ lam m q1 q2 := by inv
  @[simp] lemma eq_not_pi : eq t1 t2 t3 ≠ pi m q1 q2 := by inv
  @[simp] lemma eq_not_inter : eq t1 t2 t3 ≠ inter q1 q2 := by inv
  @[simp] lemma eq_not_app : eq t1 t2 t3 ≠ app m q1 q2 := by inv
  @[simp] lemma eq_not_pair : eq t1 t2 t3 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma eq_not_fst : eq t1 t2 t3 ≠ proj i q1 := by inv
  @[simp] lemma eq_not_refl : eq t1 t2 t3 ≠ refl q1 := by inv
  @[simp] lemma eq_not_Jh : eq t1 t2 t3 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma eq_not_J0 : eq t1 t2 t3 ≠ J0 u1 u2 := by inv
  @[simp] lemma eq_not_Jω : eq t1 t2 t3 ≠ Jω u1 u2 := by inv
  @[simp] lemma eq_not_J : eq t1 t2 t3 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma eq_not_promote : eq t1 t2 t3 ≠ promote q1 := by inv
  @[simp] lemma eq_not_delta : eq t1 t2 t3 ≠ delta q1 := by inv
  @[simp] lemma eq_not_phi : eq t1 t2 t3 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma eq_not_bind : eq t1 t2 t3 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma refl_not_const : refl t1 ≠ const k := by inv
  @[simp] lemma refl_not_typeu : refl t1 ≠ typeu := by inv
  @[simp] lemma refl_not_kindu : refl t1 ≠ kindu := by inv
  @[simp] lemma refl_not_free : refl t1 ≠ free x := by inv
  @[simp] lemma refl_not_bound : refl t1 ≠ bound i := by inv
  @[simp] lemma refl_not_lam : refl t1 ≠ lam m q1 q2 := by inv
  @[simp] lemma refl_not_pi : refl t1 ≠ pi m q1 q2 := by inv
  @[simp] lemma refl_not_inter : refl t1 ≠ inter q1 q2 := by inv
  @[simp] lemma refl_not_app : refl t1 ≠ app m q1 q2 := by inv
  @[simp] lemma refl_not_pair : refl t1 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma refl_not_fst : refl t1 ≠ proj i q1 := by inv
  @[simp] lemma refl_not_eq : refl t1 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma refl_not_Jh : refl t1 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma refl_not_J0 : refl t1 ≠ J0 u1 u2 := by inv
  @[simp] lemma refl_not_Jω : refl t1 ≠ Jω u1 u2 := by inv
  @[simp] lemma refl_not_J : refl t1 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma refl_not_promote : refl t1 ≠ promote q1 := by inv
  @[simp] lemma refl_not_delta : refl t1 ≠ delta q1 := by inv
  @[simp] lemma refl_not_phi : refl t1 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma refl_not_bind : refl t1 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma Jh_not_const : Jh t1 t2 t3 ≠ const k := by inv
  @[simp] lemma Jh_not_typeu : Jh t1 t2 t3 ≠ typeu := by inv
  @[simp] lemma Jh_not_kindu : Jh t1 t2 t3 ≠ kindu := by inv
  @[simp] lemma Jh_not_free : Jh t1 t2 t3 ≠ free x := by inv
  @[simp] lemma Jh_not_bound : Jh t1 t2 t3 ≠ bound i := by inv
  @[simp] lemma Jh_not_lam : Jh t1 t2 t3 ≠ lam m q1 q2 := by inv
  @[simp] lemma Jh_not_pi : Jh t1 t2 t3 ≠ pi m q1 q2 := by inv
  @[simp] lemma Jh_not_inter : Jh t1 t2 t3 ≠ inter q1 q2 := by inv
  @[simp] lemma Jh_not_app : Jh t1 t2 t3 ≠ app m q1 q2 := by inv
  @[simp] lemma Jh_not_pair : Jh t1 t2 t3 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma Jh_not_fst : Jh t1 t2 t3 ≠ proj i q1 := by inv
  @[simp] lemma Jh_not_eq : Jh t1 t2 t3 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma Jh_not_J0 : Jh t1 t2 t3 ≠ J0 u1 u2 := by inv
  @[simp] lemma Jh_not_Jω : Jh t1 t2 t3 ≠ Jω u1 u2 := by inv
  @[simp] lemma Jh_not_refl : Jh t1 t2 t3 ≠ refl q1 := by inv
  @[simp] lemma Jh_not_promote : Jh t1 t2 t3 ≠ promote q1 := by inv
  @[simp] lemma Jh_not_delta : Jh t1 t2 t3 ≠ delta q1 := by inv
  @[simp] lemma Jh_not_phi : Jh t1 t2 t3 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma Jh_not_bind : Jh t1 t2 t3 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma J0_not_const : J0 t1 t2 ≠ const k := by inv
  @[simp] lemma J0_not_typeu : J0 t1 t2 ≠ typeu := by inv
  @[simp] lemma J0_not_kindu : J0 t1 t2 ≠ kindu := by inv
  @[simp] lemma J0_not_free : J0 t1 t2 ≠ free x := by inv
  @[simp] lemma J0_not_bound : J0 t1 t2 ≠ bound i := by inv
  @[simp] lemma J0_not_lam : J0 t1 t2 ≠ lam m q1 q2 := by inv
  @[simp] lemma J0_not_pi : J0 t1 t2 ≠ pi m q1 q2 := by inv
  @[simp] lemma J0_not_inter : J0 t1 t2 ≠ inter q1 q2 := by inv
  @[simp] lemma J0_not_app : J0 t1 t2 ≠ app m q1 q2 := by inv
  @[simp] lemma J0_not_pair : J0 t1 t2 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma J0_not_fst : J0 t1 t2 ≠ proj i q1 := by inv
  @[simp] lemma J0_not_eq : J0 t1 t2 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma J0_not_Jh : J0 t1 t2 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma J0_not_Jω : J0 t1 t2 ≠ Jω u1 u2 := by inv
  @[simp] lemma J0_not_J : J0 t1 t2 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma J0_not_refl : J0 t1 t2 ≠ refl q1 := by inv
  @[simp] lemma J0_not_promote : J0 t1 t2 ≠ promote q1 := by inv
  @[simp] lemma J0_not_delta : J0 t1 t2 ≠ delta q1 := by inv
  @[simp] lemma J0_not_phi : J0 t1 t2 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma J0_not_bind : J0 t1 t2 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma Jω_not_const : Jω t1 t2 ≠ const k := by inv
  @[simp] lemma Jω_not_typeu : Jω t1 t2 ≠ typeu := by inv
  @[simp] lemma Jω_not_kindu : Jω t1 t2 ≠ kindu := by inv
  @[simp] lemma Jω_not_free : Jω t1 t2 ≠ free x := by inv
  @[simp] lemma Jω_not_bound : Jω t1 t2 ≠ bound i := by inv
  @[simp] lemma Jω_not_lam : Jω t1 t2 ≠ lam m q1 q2 := by inv
  @[simp] lemma Jω_not_pi : Jω t1 t2 ≠ pi m q1 q2 := by inv
  @[simp] lemma Jω_not_inter : Jω t1 t2 ≠ inter q1 q2 := by inv
  @[simp] lemma Jω_not_app : Jω t1 t2 ≠ app m q1 q2 := by inv
  @[simp] lemma Jω_not_pair : Jω t1 t2 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma Jω_not_fst : Jω t1 t2 ≠ proj i q1 := by inv
  @[simp] lemma Jω_not_eq : Jω t1 t2 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma Jω_not_Jh : Jω t1 t2 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma Jω_not_J0 : Jω t1 t2 ≠ J0 u1 u2 := by inv
  @[simp] lemma Jω_not_J : Jω t1 t2 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma Jω_not_refl : Jω t1 t2 ≠ refl q1 := by inv
  @[simp] lemma Jω_not_promote : Jω t1 t2 ≠ promote q1 := by inv
  @[simp] lemma Jω_not_delta : Jω t1 t2 ≠ delta q1 := by inv
  @[simp] lemma Jω_not_phi : Jω t1 t2 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma Jω_not_bind : Jω t1 t2 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma J_not_const : J t1 t2 t3 t4 t5 t6 ≠ const k := by inv
  @[simp] lemma J_not_typeu : J t1 t2 t3 t4 t5 t6 ≠ typeu := by inv
  @[simp] lemma J_not_kindu : J t1 t2 t3 t4 t5 t6 ≠ kindu := by inv
  @[simp] lemma J_not_free : J t1 t2 t3 t4 t5 t6 ≠ free x := by inv
  @[simp] lemma J_not_bound : J t1 t2 t3 t4 t5 t6 ≠ bound i := by inv
  @[simp] lemma J_not_lam : J t1 t2 t3 t4 t5 t6 ≠ lam m q1 q2 := by inv
  @[simp] lemma J_not_pi : J t1 t2 t3 t4 t5 t6 ≠ pi m q1 q2 := by inv
  @[simp] lemma J_not_inter : J t1 t2 t3 t4 t5 t6 ≠ inter q1 q2 := by inv
  @[simp] lemma J_not_app : J t1 t2 t3 t4 t5 t6 ≠ app m q1 q2 := by inv
  @[simp] lemma J_not_pair : J t1 t2 t3 t4 t5 t6 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma J_not_fst : J t1 t2 t3 t4 t5 t6 ≠ proj i q1 := by inv
  @[simp] lemma J_not_eq : J t1 t2 t3 t4 t5 t6 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma J_not_J0 : J t1 t2 t3 t4 t5 t6 ≠ J0 u1 u2 := by inv
  @[simp] lemma J_not_Jω : J t1 t2 t3 t4 t5 t6 ≠ Jω u1 u2 := by inv
  @[simp] lemma J_not_refl : J t1 t2 t3 t4 t5 t6 ≠ refl q1 := by inv
  @[simp] lemma J_not_promote : J t1 t2 t3 t4 t5 t6 ≠ promote q1 := by inv
  @[simp] lemma J_not_delta : J t1 t2 t3 t4 t5 t6 ≠ delta q1 := by inv
  @[simp] lemma J_not_phi : J t1 t2 t3 t4 t5 t6 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma J_not_bind : J t1 t2 t3 t4 t5 t6 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma promote_not_const : promote t1 ≠ const k := by inv
  @[simp] lemma promote_not_typeu : promote t1 ≠ typeu := by inv
  @[simp] lemma promote_not_kindu : promote t1 ≠ kindu := by inv
  @[simp] lemma promote_not_free : promote t1 ≠ free x := by inv
  @[simp] lemma promote_not_bound : promote t1 ≠ bound i := by inv
  @[simp] lemma promote_not_lam : promote t1 ≠ lam m q1 q2 := by inv
  @[simp] lemma promote_not_pi : promote t1 ≠ pi m q1 q2 := by inv
  @[simp] lemma promote_not_inter : promote t1 ≠ inter q1 q2 := by inv
  @[simp] lemma promote_not_app : promote t1 ≠ app m q1 q2 := by inv
  @[simp] lemma promote_not_pair : promote t1 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma promote_not_fst : promote t1 ≠ proj i q1 := by inv
  @[simp] lemma promote_not_eq : promote t1 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma promote_not_refl : promote t1 ≠ refl q1 := by inv
  @[simp] lemma promote_not_Jh : promote t1 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma promote_not_J0 : promote t1 ≠ J0 u1 u2 := by inv
  @[simp] lemma promote_not_Jω : promote t1 ≠ Jω u1 u2 := by inv
  @[simp] lemma promote_not_J : promote t1 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma promote_not_delta : promote t1 ≠ delta q1 := by inv
  @[simp] lemma promote_not_phi : promote t1 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma promote_not_bind : promote t1 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma delta_not_const : delta t1 ≠ const k := by inv
  @[simp] lemma delta_not_typeu : delta t1 ≠ typeu := by inv
  @[simp] lemma delta_not_kindu : delta t1 ≠ kindu := by inv
  @[simp] lemma delta_not_free : delta t1 ≠ free x := by inv
  @[simp] lemma delta_not_bound : delta t1 ≠ bound i := by inv
  @[simp] lemma delta_not_lam : delta t1 ≠ lam m q1 q2 := by inv
  @[simp] lemma delta_not_pi : delta t1 ≠ pi m q1 q2 := by inv
  @[simp] lemma delta_not_inter : delta t1 ≠ inter q1 q2 := by inv
  @[simp] lemma delta_not_app : delta t1 ≠ app m q1 q2 := by inv
  @[simp] lemma delta_not_pair : delta t1 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma delta_not_fst : delta t1 ≠ proj i q1 := by inv
  @[simp] lemma delta_not_eq : delta t1 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma delta_not_refl : delta t1 ≠ refl q1 := by inv
  @[simp] lemma delta_not_Jh : delta t1 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma delta_not_J0 : delta t1 ≠ J0 u1 u2 := by inv
  @[simp] lemma delta_not_Jω : delta t1 ≠ Jω u1 u2 := by inv
  @[simp] lemma delta_not_J : delta t1 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma delta_not_promote : delta t1 ≠ promote q1 := by inv
  @[simp] lemma delta_not_phi : delta t1 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma delta_not_bind : delta t1 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma phi_not_const : phi t1 t2 t3 ≠ const k := by inv
  @[simp] lemma phi_not_typeu : phi t1 t2 t3 ≠ typeu := by inv
  @[simp] lemma phi_not_kindu : phi t1 t2 t3 ≠ kindu := by inv
  @[simp] lemma phi_not_free : phi t1 t2 t3 ≠ free x := by inv
  @[simp] lemma phi_not_bound : phi t1 t2 t3 ≠ bound i := by inv
  @[simp] lemma phi_not_lam : phi t1 t2 t3 ≠ lam m q1 q2 := by inv
  @[simp] lemma phi_not_pi : phi t1 t2 t3 ≠ pi m q1 q2 := by inv
  @[simp] lemma phi_not_inter : phi t1 t2 t3 ≠ inter q1 q2 := by inv
  @[simp] lemma phi_not_app : phi t1 t2 t3 ≠ app m q1 q2 := by inv
  @[simp] lemma phi_not_pair : phi t1 t2 t3 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma phi_not_fst : phi t1 t2 t3 ≠ proj i q1 := by inv
  @[simp] lemma phi_not_eq : phi t1 t2 t3 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma phi_not_refl : phi t1 t2 t3 ≠ refl q1 := by inv
  @[simp] lemma phi_not_Jh : phi t1 t2 t3 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma phi_not_J0 : phi t1 t2 t3 ≠ J0 u1 u2 := by inv
  @[simp] lemma phi_not_Jω : phi t1 t2 t3 ≠ Jω u1 u2 := by inv
  @[simp] lemma phi_not_J : phi t1 t2 t3 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma phi_not_promote : phi t1 t2 t3 ≠ promote q1 := by inv
  @[simp] lemma phi_not_delta : phi t1 t2 t3 ≠ delta q1 := by inv
  @[simp] lemma phi_not_bind : phi t1 t2 t3 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma bind_not_const : Syntax.bind b t1 t2 ≠ const k := by inv
  @[simp] lemma bind_not_typeu : Syntax.bind b t1 t2 ≠ typeu := by inv
  @[simp] lemma bind_not_kindu : Syntax.bind b t1 t2 ≠ kindu := by inv
  @[simp] lemma bind_not_free : Syntax.bind b t1 t2 ≠ free x := by inv
  @[simp] lemma bind_not_bound : Syntax.bind b t1 t2 ≠ bound i := by inv
  @[simp] lemma bind_not_app : Syntax.bind b t1 t2 ≠ app m q1 q2 := by inv
  @[simp] lemma bind_not_pair : Syntax.bind b t1 t2 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma bind_not_fst : Syntax.bind b t1 t2 ≠ proj i q1 := by inv
  @[simp] lemma bind_not_eq : Syntax.bind b t1 t2 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma bind_not_refl : Syntax.bind b t1 t2 ≠ refl q1 := by inv
  @[simp] lemma bind_not_Jh : Syntax.bind b t1 t2 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma bind_not_J0 : Syntax.bind b t1 t2 ≠ J0 u1 u2 := by inv
  @[simp] lemma bind_not_Jω : Syntax.bind b t1 t2 ≠ Jω u1 u2 := by inv
  @[simp] lemma bind_not_J : Syntax.bind b t1 t2 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma bind_not_promote : Syntax.bind b t1 t2 ≠ promote q1 := by inv
  @[simp] lemma bind_not_delta : Syntax.bind b t1 t2 ≠ delta q1 := by inv
  @[simp] lemma bind_not_phi : Syntax.bind b t1 t2 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma bind_not_ctor : Syntax.bind b t1 t2 ≠ Syntax.ctor c q1 q2 q3 := by inv

  @[simp] lemma ctor_not_const : Syntax.ctor c t1 t2 t3 ≠ const k := by inv
  @[simp] lemma ctor_not_typeu : Syntax.ctor c t1 t2 t3 ≠ typeu := by inv
  @[simp] lemma ctor_not_kindu : Syntax.ctor c t1 t2 t3 ≠ kindu := by inv
  @[simp] lemma ctor_not_free : Syntax.ctor c t1 t2 t3 ≠ free x := by inv
  @[simp] lemma ctor_not_bound : Syntax.ctor c t1 t2 t3 ≠ bound i := by inv
  @[simp] lemma ctor_not_lam : Syntax.ctor c t1 t2 t3 ≠ lam m q1 q2 := by inv
  @[simp] lemma ctor_not_pi : Syntax.ctor c t1 t2 t3 ≠ pi m q1 q2 := by inv
  @[simp] lemma ctor_not_inter : Syntax.ctor c t1 t2 t3 ≠ inter q1 q2 := by inv
  @[simp] lemma ctor_not_bind : Syntax.ctor c t1 t2 t3 ≠ Syntax.bind b q1 q2 := by inv

end Cedille
