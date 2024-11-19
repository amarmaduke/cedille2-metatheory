
import Common
import Fomega.Ctx
import Fomega.Proof
import Fomega.PreProof

namespace Fomega.Conv

  theorem refl : IsPreProof A -> A === A := by
  intro j
  induction j <;> (constructor <;> simp [*])

  theorem sym :
    A === B ->
    B === A
  := by
  intro h
  induction h
  case ax => constructor
  case bound => constructor
  all_goals (constructor <;> simp at * <;> simp [*])

  -- theorem sym :
  --   IsPreProof A ->
  --   IsPreProof B ->
  --   A === B ->
  --   B === A
  -- := by
  -- intro p1 p2 j
  -- induction j
  -- case ax => constructor
  -- case bound => constructor
  -- case all_congr ih1 ih2 =>
  --   cases p1
  --   case _ p11 p12 =>
  --     cases p2
  --     case _ p21 p22 =>
  --       constructor
  --       case _ => apply ih1 p11 p21
  --       case _ => apply ih2 p12 p22
  -- case lam_congr ih1 ih2 =>
  --   cases p1
  --   case _ p11 p12 =>
  --     cases p2
  --     case _ p21 p22 =>
  --       constructor
  --       case _ => apply ih1 p11 p21
  --       case _ => apply ih2 p12 p22
  -- -- case lam_eta1 ih =>
  -- --   apply Conv.lam_eta2; apply ih p1
  -- --   unfold Term.eta; simp; constructor
  -- --   case _ => cases p1; simp [*]
  -- --   case _ =>
  -- --     constructor
  -- --     case _ => apply IsPreProof.ren p2
  -- --     case _ => constructor
  -- -- case lam_eta2 ih =>
  -- --   apply Conv.lam_eta1; apply ih _ p2
  -- --   unfold Term.eta; simp; constructor
  -- --   case _ => cases p2; simp [*]
  -- --   case _ =>
  -- --     constructor
  -- --     case _ => apply IsPreProof.ren p1
  -- --     case _ => constructor
  -- case app_congr ih1 ih2 =>
  --   cases p1
  --   case _ p11 p12 =>
  --     cases p2
  --     case _ p21 p22 =>
  --       constructor
  --       case _ => apply ih1 p11 p21
  --       case _ => apply ih2 p12 p22
  -- case app_beta1 h1 h2 ih1 ih2 =>
  --   apply Conv.app_beta2
  --   -- cases p1
  --   -- case _ p11 p12 =>
  --   --   cases p11
  --   --   case _ p111 p112 =>
  --   --     apply Conv.app_beta2;
  --   --     apply IsPreProof.beta p112 p12
  -- case app_beta2 ih =>
  --   cases p2
  --   case _ p11 p12 =>
  --     cases p11
  --     case _ p111 p112 =>
  --       apply Conv.app_beta1; apply ih p1
  --       apply IsPreProof.beta p112 p12

  theorem rename : A === B -> ([r#r]A) === ([r#r]B) := by
  intro j; induction j generalizing r <;> simp
  case ax => constructor
  case bound K x => constructor
  case all_congr A1 A2 B1 B2 _j1 _j2 ih1 ih2 =>
    constructor; apply ih1
    replace ih2 := @ih2 (Term.Ren.lift r); simp at ih2
    apply ih2
  case lam_congr A1 A2 t1 t2 _j1 _j2 ih1 ih2 =>
    constructor; apply ih1
    replace ih2 := @ih2 (Term.Ren.lift r); simp at ih2
    apply ih2
  -- case lam_eta1 A' t1 t2 _j ih =>
  --   apply Conv.lam_eta1; simp at *; apply ih
  -- case lam_eta2 A' t1 t2 _j ih =>
  --   apply Conv.lam_eta2; simp at *; apply ih
  case app_congr f1 f2 a1 a2 m _j1 _j2 ih1 ih2 =>
    constructor; apply ih1; apply ih2
  case app_beta1 ih => apply Conv.app_beta1; simp at *; apply ih
  case app_beta2 ih => apply Conv.app_beta2; simp at *; apply ih

  theorem subst : (∀ n s, σ n = .replace s -> IsPreProof s) -> A === B -> ([σ]A) === ([σ]B) := by
  intro h j
  induction j generalizing σ <;> simp
  case ax => constructor
  case bound _ x =>
    generalize ydef : σ x = y at *
    cases y <;> simp at *
    case _ => constructor
    case _ => apply refl; apply h x _ ydef
  case all_congr _j1 _j2 ih1 ih2 =>
    constructor; apply ih1 h
    replace ih2 := @ih2 (^σ) (IsPreProof.lift h); simp at ih2; exact ih2
  case lam_congr _j1 _j2 ih1 ih2 =>
    constructor; apply ih1 h
    replace ih2 := @ih2 (^σ) (IsPreProof.lift h); simp at ih2; exact ih2
  -- case lam_eta1 _j ih =>
  --   constructor; simp at ih; unfold Term.eta; simp
  --   apply ih h
  -- case lam_eta2 _j ih =>
  --   constructor; simp at ih; unfold Term.eta; simp
  --   apply ih h
  case app_congr _j1 _j2 ih1 ih2 =>
    constructor; apply ih1 h; apply ih2 h
  case app_beta1 ih => apply Conv.app_beta1; simp at *; apply ih h
  case app_beta2 ih => apply Conv.app_beta2; simp at *; apply ih h

  theorem beta : IsPreProof t -> A === B -> (A β[t]) === (B β[t]) := by
  intro p h; simp; apply subst
  case _ =>
    intro n t' h2
    cases n <;> simp at h2
    subst h2; exact p
  case _ => exact h

  theorem congr :
    IsPreProof A -> IsPreProof A' -> IsPreProof B ->
    A === B -> A === A' -> A' === B
  := by
  intro p1 p2 p3 h1 h2
  induction h2 generalizing B
  case ax => sorry
  case bound => sorry
  case all_congr => sorry
  case lam_congr => sorry
  case app_congr => sorry
  case app_beta1 h ih => sorry
  case app_beta2 => sorry

  theorem congr2_1 (f : Term -> Term -> Term) :
    (∀ {t1 t1' t2 t2'}, t1 === t1' -> t2 === t2' -> f t1 t2 === f t1' t2') ->
    t1 === t1' -> f t1 t2 === B -> f t1' t2 === B
  := by
  intro fh h1 h2
  induction h1 generalizing t2 B
  case ax => sorry
  case bound => sorry
  case all_congr => sorry
  case lam_congr => sorry
  case app_congr => sorry
  case app_beta1 => sorry
  case app_beta2 => sorry

  theorem red2 : IsPreProof A' -> A === B -> A' -β>* A -> A' === B := by
  intro p1 h1 h2
  induction h1 generalizing A'
  case ax => sorry
  case bound => sorry
  case all_congr => sorry
  case lam_congr => sorry
  case app_congr => sorry
  case app_beta1 h ih => sorry
  case app_beta2 h ih => constructor; apply ih p1 h2

  theorem red : IsPreProof A' -> A === B -> A' -β> A -> A' === B := by
  intro p1 h1 h2
  induction h2 generalizing B
  case beta m _ _ _ => sorry
  case lam_congr1 m t h ih =>
    cases m <;> try cases p1
    case _ p4 p5 => sorry
  case lam_congr2 => sorry
  case app_congr1 => sorry
  case app_congr2 => sorry
  case all_congr1 => sorry
  case all_congr2 => sorry
  all_goals cases p1

  theorem trans2 :
    IsPreProof A -> Γ ⊢ B : T -> IsPreProof C ->
    A === B -> B === C -> A === C
  := by
  intro p1 j p3 h1 h2
  induction j generalizing A C
  case ax => sorry
  case var => sorry
  case pi => sorry
  case tpi => sorry
  case lam => sorry
  case app ih1 ih2 => sorry
  case conv h ih1 ih2 => apply ih1 p1 p3 h1 h2

  theorem trans :
    IsPreProof A -> IsPreProof B -> IsPreProof C ->
    A === B -> B === C -> A === C
  := by
  intro p1 p2 p3 h1 h2
  induction h1 generalizing C
  case _ => simp [*]
  case _ => simp [*]
  case all_congr => sorry
  case lam_congr => sorry
  case app_congr r1 r2 ih1 ih2 => sorry
  case app_beta1 h ih => sorry
  case app_beta2 => sorry


end Fomega.Conv
