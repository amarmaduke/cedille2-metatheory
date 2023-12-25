
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
        injection h2
      }
      try {
        injection h with h1 h2 h3
        injection h2 with h4
        injection h4
      }
  })

  @[simp] lemma inv_binder_m0 : ¬ (Binder.lam m0 ≠ Binder.lam m0) := by intro h; apply h (by simp)

  @[simp] lemma const_not_free : @const n k ≠ free x := by inv
  @[simp] lemma const_not_bound : @const n k ≠ bound i := by inv
  @[simp] lemma const_not_lam : @const n k ≠ lam m t1 t2 := by inv
  @[simp] lemma const_not_pi : @const n k ≠ pi m t1 t2 := by inv
  @[simp] lemma const_not_inter : @const n k ≠ inter t1 t2 := by inv
  @[simp] lemma const_not_app : @const n k ≠ app m t1 t2 := by inv
  @[simp] lemma const_not_pair : @const n k ≠ pair t1 t2 t3 := by inv
  @[simp] lemma const_not_fst : @const n k ≠ fst t := by inv
  @[simp] lemma const_not_snd : @const n k ≠ snd t := by inv
  @[simp] lemma const_not_eq : @const n k ≠ eq t1 t2 t3 := by inv
  @[simp] lemma const_not_refl : @const n k ≠ refl t := by inv
  @[simp] lemma const_not_Jh : @const n k ≠ Jh t1 t2 t3 := by inv
  @[simp] lemma const_not_J0 : @const n k ≠ J0 t1 t2 := by inv
  @[simp] lemma const_not_Jω : @const n k ≠ Jω t1 t2 := by inv
  @[simp] lemma const_not_J : @const n k ≠ J t1 t2 t3 t4 t5 t6 := by inv
  @[simp] lemma const_not_promote : @const n k ≠ promote t := by inv
  @[simp] lemma const_not_delta : @const n k ≠ delta t := by inv
  @[simp] lemma const_not_phi : @const n k ≠ phi t1 t2 t3 := by inv
  @[simp] lemma const_not_bind : @const n k ≠ Syntax.bind b t1 t2 := by inv
  @[simp] lemma const_not_ctor : @const n k ≠ Syntax.ctor c t1 t2 t3 := by inv

  @[simp] lemma typeu_not_free : @typeu n ≠ free x := by inv
  @[simp] lemma typeu_not_bound : @typeu n ≠ bound i := by inv
  @[simp] lemma typeu_not_lam : @typeu n ≠ lam m t1 t2 := by inv
  @[simp] lemma typeu_not_pi : @typeu n ≠ pi m t1 t2 := by inv
  @[simp] lemma typeu_not_inter : @typeu n ≠ inter t1 t2 := by inv
  @[simp] lemma typeu_not_app : @typeu n ≠ app m t1 t2 := by inv
  @[simp] lemma typeu_not_pair : @typeu n ≠ pair t1 t2 t3 := by inv
  @[simp] lemma typeu_not_fst : @typeu n ≠ fst t := by inv
  @[simp] lemma typeu_not_snd : @typeu n ≠ snd t := by inv
  @[simp] lemma typeu_not_eq : @typeu n ≠ eq t1 t2 t3 := by inv
  @[simp] lemma typeu_not_refl : @typeu n ≠ refl t := by inv
  @[simp] lemma typeu_not_Jh : @typeu n ≠ Jh t1 t2 t3 := by inv
  @[simp] lemma typeu_not_J0 : @typeu n ≠ J0 t1 t2 := by inv
  @[simp] lemma typeu_not_Jω : @typeu n ≠ Jω t1 t2 := by inv
  @[simp] lemma typeu_not_J : @typeu n ≠ J t1 t2 t3 t4 t5 t6 := by inv
  @[simp] lemma typeu_not_promote : @typeu n ≠ promote t := by inv
  @[simp] lemma typeu_not_delta : @typeu n ≠ delta t := by inv
  @[simp] lemma typeu_not_phi : @typeu n ≠ phi t1 t2 t3 := by inv
  @[simp] lemma typeu_not_bind : @typeu n ≠ Syntax.bind b t1 t2 := by inv
  @[simp] lemma typeu_not_ctor : @typeu n ≠ Syntax.ctor c t1 t2 t3 := by inv

  @[simp] lemma kindu_not_free : @kindu n ≠ free x := by inv
  @[simp] lemma kindu_not_bound : @kindu n ≠ bound i := by inv
  @[simp] lemma kindu_not_lam : @kindu n ≠ lam m t1 t2 := by inv
  @[simp] lemma kindu_not_pi : @kindu n ≠ pi m t1 t2 := by inv
  @[simp] lemma kindu_not_inter : @kindu n ≠ inter t1 t2 := by inv
  @[simp] lemma kindu_not_app : @kindu n ≠ app m t1 t2 := by inv
  @[simp] lemma kindu_not_pair : @kindu n ≠ pair t1 t2 t3 := by inv
  @[simp] lemma kindu_not_fst : @kindu n ≠ fst t := by inv
  @[simp] lemma kindu_not_snd : @kindu n ≠ snd t := by inv
  @[simp] lemma kindu_not_eq : @kindu n ≠ eq t1 t2 t3 := by inv
  @[simp] lemma kindu_not_refl : @kindu n ≠ refl t := by inv
  @[simp] lemma kindu_not_Jh : @kindu n ≠ Jh t1 t2 t3 := by inv
  @[simp] lemma kindu_not_J0 : @kindu n ≠ J0 t1 t2 := by inv
  @[simp] lemma kindu_not_Jω : @kindu n ≠ Jω t1 t2 := by inv
  @[simp] lemma kindu_not_J : @kindu n ≠ J t1 t2 t3 t4 t5 t6 := by inv
  @[simp] lemma kindu_not_promote : @kindu n ≠ promote t := by inv
  @[simp] lemma kindu_not_delta : @kindu n ≠ delta t := by inv
  @[simp] lemma kindu_not_phi : @kindu n ≠ phi t1 t2 t3 := by inv
  @[simp] lemma kindu_not_bind : @kindu n ≠ Syntax.bind b t1 t2 := by inv
  @[simp] lemma kindu_not_ctor : @kindu n ≠ Syntax.ctor c t1 t2 t3 := by inv

  @[simp] lemma free_not_const : @free n x ≠ const k := by inv
  @[simp] lemma free_not_typeu : @free n x ≠ typeu := by inv
  @[simp] lemma free_not_kindu : @free n x ≠ kindu := by inv
  @[simp] lemma free_not_bound : @free n x ≠ bound i := by inv
  @[simp] lemma free_not_lam : @free n x ≠ lam m t1 t2 := by inv
  @[simp] lemma free_not_pi : @free n x ≠ pi m t1 t2 := by inv
  @[simp] lemma free_not_inter : @free n x ≠ inter t1 t2 := by inv
  @[simp] lemma free_not_app : @free n x ≠ app m t1 t2 := by inv
  @[simp] lemma free_not_pair : @free n x ≠ pair t1 t2 t3 := by inv
  @[simp] lemma free_not_fst : @free n x ≠ fst t := by inv
  @[simp] lemma free_not_snd : @free n x ≠ snd t := by inv
  @[simp] lemma free_not_eq : @free n x ≠ eq t1 t2 t3 := by inv
  @[simp] lemma free_not_refl : @free n x ≠ refl t := by inv
  @[simp] lemma free_not_Jh : @free n x ≠ Jh t1 t2 t3 := by inv
  @[simp] lemma free_not_J0 : @free n x ≠ J0 t1 t2 := by inv
  @[simp] lemma free_not_Jω : @free n x ≠ Jω t1 t2 := by inv
  @[simp] lemma free_not_J : @free n x ≠ J t1 t2 t3 t4 t5 t6 := by inv
  @[simp] lemma free_not_promote : @free n x ≠ promote t := by inv
  @[simp] lemma free_not_delta : @free n x ≠ delta t := by inv
  @[simp] lemma free_not_phi : @free n x ≠ phi t1 t2 t3 := by inv
  @[simp] lemma free_not_bind : @free n x ≠ Syntax.bind b t1 t2 := by inv
  @[simp] lemma free_not_ctor : @free n x ≠ Syntax.ctor c t1 t2 t3 := by inv

  @[simp] lemma bound_not_const : @bound n i ≠ const k := by inv
  @[simp] lemma bound_not_typeu : @bound n i ≠ typeu := by inv
  @[simp] lemma bound_not_kindu : @bound n i ≠ kindu := by inv
  @[simp] lemma bound_not_free : @bound n i ≠ free x := by inv
  @[simp] lemma bound_not_lam : @bound n i ≠ lam m t1 t2 := by inv
  @[simp] lemma bound_not_pi : @bound n i ≠ pi m t1 t2 := by inv
  @[simp] lemma bound_not_inter : @bound n i ≠ inter t1 t2 := by inv
  @[simp] lemma bound_not_app : @bound n i ≠ app m t1 t2 := by inv
  @[simp] lemma bound_not_pair : @bound n i ≠ pair t1 t2 t3 := by inv
  @[simp] lemma bound_not_fst : @bound n i ≠ fst t := by inv
  @[simp] lemma bound_not_snd : @bound n i ≠ snd t := by inv
  @[simp] lemma bound_not_eq : @bound n i ≠ eq t1 t2 t3 := by inv
  @[simp] lemma bound_not_refl : @bound n i ≠ refl t := by inv
  @[simp] lemma bound_not_Jh : @bound n x ≠ Jh t1 t2 t3 := by inv
  @[simp] lemma bound_not_J0 : @bound n x ≠ J0 t1 t2 := by inv
  @[simp] lemma bound_not_Jω : @bound n x ≠ Jω t1 t2 := by inv
  @[simp] lemma bound_not_J : @bound n x ≠ J t1 t2 t3 t4 t5 t6 := by inv
  @[simp] lemma bound_not_promote : @bound n i ≠ promote t := by inv
  @[simp] lemma bound_not_delta : @bound n i ≠ delta t := by inv
  @[simp] lemma bound_not_phi : @bound n i ≠ phi t1 t2 t3 := by inv
  @[simp] lemma bound_not_bind : @bound n i ≠ Syntax.bind b t1 t2 := by inv
  @[simp] lemma bound_not_ctor : @bound n i ≠ Syntax.ctor c t1 t2 t3 := by inv

  @[simp] lemma lam_not_const : lam m t1 t2 ≠ const k := by inv
  @[simp] lemma lam_not_typeu : lam m t1 t2 ≠ typeu := by inv
  @[simp] lemma lam_not_kindu : lam m t1 t2 ≠ kindu := by inv
  @[simp] lemma lam_not_free : lam m t1 t2 ≠ free x := by inv
  @[simp] lemma lam_not_bound : lam m t1 t2 ≠ bound i := by inv
  @[simp] lemma lam_not_pi : lam m1 t1 t2 ≠ pi m2 t3 t4 := by inv
  @[simp] lemma lam_not_inter : lam m t1 t2 ≠ inter t3 t4 := by inv
  @[simp] lemma lam_not_app : lam m1 t1 t2 ≠ app m2 t3 t4 := by inv
  @[simp] lemma lam_not_pair : lam m t1 t2 ≠ pair t3 t4 t5 := by inv
  @[simp] lemma lam_not_fst : lam m t1 t2 ≠ fst t := by inv
  @[simp] lemma lam_not_snd : lam m t1 t2 ≠ snd t := by inv
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
  @[simp] lemma pi_not_fst : pi m t1 t2 ≠ fst t := by inv
  @[simp] lemma pi_not_snd : pi m t1 t2 ≠ snd t := by inv
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
  @[simp] lemma inter_not_fst : inter t1 t2 ≠ fst t := by inv
  @[simp] lemma inter_not_snd : inter t1 t2 ≠ snd t := by inv
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
  @[simp] lemma app_not_fst : app m t1 t2 ≠ fst t := by inv
  @[simp] lemma app_not_snd : app m t1 t2 ≠ snd t := by inv
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
  @[simp] lemma pair_not_fst : pair t1 t2 t3 ≠ fst q1 := by inv
  @[simp] lemma pair_not_snd : pair t1 t2 t3 ≠ snd q1 := by inv
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

  @[simp] lemma fst_not_const : fst t1 ≠ const k := by inv
  @[simp] lemma fst_not_typeu : fst t1 ≠ typeu := by inv
  @[simp] lemma fst_not_kindu : fst t1 ≠ kindu := by inv
  @[simp] lemma fst_not_free : fst t1 ≠ free x := by inv
  @[simp] lemma fst_not_bound : fst t1 ≠ bound i := by inv
  @[simp] lemma fst_not_lam : fst t1 ≠ lam m q1 q2 := by inv
  @[simp] lemma fst_not_pi : fst t1 ≠ pi m q1 q2 := by inv
  @[simp] lemma fst_not_inter : fst t1 ≠ inter q1 q2 := by inv
  @[simp] lemma fst_not_app : fst t1 ≠ app m q1 q2 := by inv
  @[simp] lemma fst_not_pair : fst t1 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma fst_not_snd : fst t1 ≠ snd q1 := by inv
  @[simp] lemma fst_not_eq : fst t1 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma fst_not_refl : fst t1 ≠ refl q1 := by inv
  @[simp] lemma fst_not_Jh : fst t1 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma fst_not_J0 : fst t1 ≠ J0 u1 u2 := by inv
  @[simp] lemma fst_not_Jω : fst t1 ≠ Jω u1 u2 := by inv
  @[simp] lemma fst_not_J : fst t1 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma fst_not_promote : fst t1 ≠ promote q1 := by inv
  @[simp] lemma fst_not_delta : fst t1 ≠ delta q1 := by inv
  @[simp] lemma fst_not_phi : fst t1 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma fst_not_bind : fst t1 ≠ Syntax.bind b q1 q2 := by inv

  @[simp] lemma snd_not_const : snd t1 ≠ const k := by inv
  @[simp] lemma snd_not_typeu : snd t1 ≠ typeu := by inv
  @[simp] lemma snd_not_kindu : snd t1 ≠ kindu := by inv
  @[simp] lemma snd_not_free : snd t1 ≠ free x := by inv
  @[simp] lemma snd_not_bound : snd t1 ≠ bound i := by inv
  @[simp] lemma snd_not_lam : snd t1 ≠ lam m q1 q2 := by inv
  @[simp] lemma snd_not_pi : snd t1 ≠ pi m q1 q2 := by inv
  @[simp] lemma snd_not_inter : snd t1 ≠ inter q1 q2 := by inv
  @[simp] lemma snd_not_app : snd t1 ≠ app m q1 q2 := by inv
  @[simp] lemma snd_not_pair : snd t1 ≠ pair q1 q2 q3 := by inv
  @[simp] lemma snd_not_fst : snd t1 ≠ fst q1 := by inv
  @[simp] lemma snd_not_eq : snd t1 ≠ eq q1 q2 q3 := by inv
  @[simp] lemma snd_not_refl : snd t1 ≠ refl q1 := by inv
  @[simp] lemma snd_not_Jh : snd t1 ≠ Jh u1 u2 u3 := by inv
  @[simp] lemma snd_not_J0 : snd t1 ≠ J0 u1 u2 := by inv
  @[simp] lemma snd_not_Jω : snd t1 ≠ Jω u1 u2 := by inv
  @[simp] lemma snd_not_J : snd t1 ≠ J u1 u2 u3 u4 u5 u6 := by inv
  @[simp] lemma snd_not_promote : snd t1 ≠ promote q1 := by inv
  @[simp] lemma snd_not_delta : snd t1 ≠ delta q1 := by inv
  @[simp] lemma snd_not_phi : snd t1 ≠ phi q1 q2 q3 := by inv
  @[simp] lemma snd_not_bind : snd t1 ≠ Syntax.bind b q1 q2 := by inv

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
  @[simp] lemma eq_not_fst : eq t1 t2 t3 ≠ fst q1 := by inv
  @[simp] lemma eq_not_snd : eq t1 t2 t3 ≠ snd q1 := by inv
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
  @[simp] lemma refl_not_fst : refl t1 ≠ fst q1 := by inv
  @[simp] lemma refl_not_snd : refl t1 ≠ snd q1 := by inv
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
  @[simp] lemma Jh_not_fst : Jh t1 t2 t3 ≠ fst q1 := by inv
  @[simp] lemma Jh_not_snd : Jh t1 t2 t3 ≠ snd q1 := by inv
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
  @[simp] lemma J0_not_fst : J0 t1 t2 ≠ fst q1 := by inv
  @[simp] lemma J0_not_snd : J0 t1 t2 ≠ snd q1 := by inv
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
  @[simp] lemma Jω_not_fst : Jω t1 t2 ≠ fst q1 := by inv
  @[simp] lemma Jω_not_snd : Jω t1 t2 ≠ snd q1 := by inv
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
  @[simp] lemma J_not_fst : J t1 t2 t3 t4 t5 t6 ≠ fst q1 := by inv
  @[simp] lemma J_not_snd : J t1 t2 t3 t4 t5 t6 ≠ snd q1 := by inv
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
  @[simp] lemma promote_not_fst : promote t1 ≠ fst q1 := by inv
  @[simp] lemma promote_not_snd : promote t1 ≠ snd q1 := by inv
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
  @[simp] lemma delta_not_fst : delta t1 ≠ fst q1 := by inv
  @[simp] lemma delta_not_snd : delta t1 ≠ snd q1 := by inv
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
  @[simp] lemma phi_not_fst : phi t1 t2 t3 ≠ fst q1 := by inv
  @[simp] lemma phi_not_snd : phi t1 t2 t3 ≠ snd q1 := by inv
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
  @[simp] lemma bind_not_fst : Syntax.bind b t1 t2 ≠ fst q1 := by inv
  @[simp] lemma bind_not_snd : Syntax.bind b t1 t2 ≠ snd q1 := by inv
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
