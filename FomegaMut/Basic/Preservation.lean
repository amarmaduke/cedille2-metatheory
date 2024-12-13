import Common
import FomegaMut.Ctx
import FomegaMut.Proof
import FomegaMut.PreProof
import FomegaMut.Basic.Weaken
import FomegaMut.Basic.Substitution
import FomegaMut.Basic.Inversion
import FomegaMut.Basic.Classification

namespace FomegaMut.Proof

  -- theorem wf_type : t ⊢ Γ -> Γ ⊢ t : A -> A ⊢ Γ := by
  -- intro j1 j2
  -- induction j2
  -- case ax => constructor
  -- case var => cases j1; simp [*]
  -- case pi => constructor
  -- case tpi => constructor
  -- case lam _ih1 ih2 =>
  --   cases j1
  --   case _ j1 j2 =>
  --     constructor; apply j1; apply ih2 j2
  -- case app _j1 j2' sh ih1 _ih2 =>
  --   cases j1
  --   case _ j1 j2 =>
  --     replace ih1 := ih1 j1
  --     cases ih1
  --     case _ j3 j4 =>
  --       subst sh; apply beta_wf;
  --       apply j4; apply j2'; apply j2
  -- case econv => cases j1; simp [*]
  -- case iconv =>  sorry

  def mk (t A : Term) : Subst Term := sorry
  theorem mk_law1 : Γ ⊢ t : A -> [mk t A]t = t ∧ [mk t A]A = A := by sorry
  theorem mk_law2 : ∀ n, ∃ x K, mk t A n = .replace (.bound x K) := by sorry

  theorem ctx_conv2 : Jud .prf (A::Γ) t T -> B =β= A -> Jud .prf Γ A (.const K) -> Jud .prf (B::Γ) t T := by
  intro j1 cv j2
  have lem : Jud .prf (B::Γ) ([mk t T]t) ([mk t T]T) := by
    apply subst _ _ _ j1
    case _ => sorry
    case _ =>
      intro n y h;
      sorry
    case _ =>
      intro n t' h
      have lem : ∃ i, ∃ K, t' = .bound K i := by sorry
      cases lem
      case _ i lem =>
      cases lem
      case _ K lem => sorry
  simp at lem; rw [(mk_law1 j1).1, (mk_law1 j1).2] at lem
  apply lem

  theorem ctx_conv :
    Jud jk Γ t T ->
    (∀ n K, Γ ⊢ Γ d@ n : .const K -> Γ d@ n =β= Δ d@ n) ->
    Jud jk Δ t T
  := by
  intro j h
  induction j generalizing Δ
  case wf_ax => constructor
  case wf_var Γ x K ξ h' ih =>
    constructor
    replace ih := ih h
    have h2 := h x K h'
    sorry

  case wf_pi => sorry
  case wf_lam => sorry
  case wf_app => sorry
  case wf_conv => sorry
  case ax => sorry
  case var => sorry
  case pi => sorry
  case tpi => sorry
  case lam => sorry
  case app => sorry
  case econv => sorry
  case iconv => sorry

  abbrev ctx_red Γ Γ' := ∃ x, ∀ n, Γ d@ x -β> Γ' d@ x ∧ (n ≠ x -> Γ d@ n = Γ' d@ n)

  theorem ctx_red_lift : ctx_red Γ Γ' -> ctx_red (A::Γ) (A::Γ') := by sorry

  theorem preservation_jud : Jud jk Γ t A ->
    (∀ jk t', t -β> t' -> Jud jk Γ t' A)
    ∧ (∀ jk Γ', ctx_red Γ Γ' -> Jud jk Γ' t A)
    -- ∧ (∀ A', A -β> A' -> Jud jk Γ t A')
  := by
  intro j
  induction j
  case wf_ax => sorry
  case wf_var => sorry
  case wf_pi j1 j2 ih1 ih2 => sorry
  case wf_lam j1 j2 ih1 ih2 =>
    apply And.intro
    intro t' r
    cases r
    case _ A' r =>
      constructor; apply ih1.1 A' r
      apply ih2.2
    case _ t' r =>
    sorry
  case wf_app => sorry
  case wf_conv => sorry
  case ax => sorry
  case var Γ K x ξ h ih =>
    apply And.intro
    intro jk t' r; cases r
    intro jk Γ' r
    have r' := r
    cases r
    case _ y r =>
      cases Nat.decEq x y
      case _ hd =>
        rw [(r x).2 hd];
        cases jk
        constructor; apply ih.2 _ _ r'
        constructor; sorry
      case _ hd =>
        subst hd
        cases jk
  case pi => sorry
  case tpi => sorry
  case lam Γ A B K t j1 j2 ih1 ih2 =>
    apply And.intro
    intro t' r
    cases r
    case lam_congr1 A' r =>
      have j0 := all_destruct j1 Term.RedConv.refl
      cases j0.2.1
      case _ AK j0 =>
        constructor; constructor
        apply ih1.1 (.all mf A' B) (Term.Red.all_congr1 r)
        apply ih2.2
        exists 0; exists AK; intro n; simp
        apply And.intro
        have lem := weaken A' j0; simp at lem; apply lem
        apply And.intro
        apply Term.Red.subst1_same; apply r
        intro h; cases n; exfalso; apply h rfl; simp
        apply j1; exists .all mf A' B
        apply And.intro; apply Term.RedStar.refl
        apply Term.RedStar.step; apply Term.Red.all_congr1 r; apply Term.RedStar.refl
    case lam_congr2 t' r =>
      constructor; apply j1
      apply ih2.1 t' r
    intro Γ' r
    constructor; apply ih1.2 Γ' r; apply ih2.2; apply ctx_red_lift r
  case app Γ f A' B a B' j1 j2 j3 ih1 ih2 => sorry
  case econv j1 j2 j3 ih1 ih2 => sorry
  case iconv => sorry

  -- theorem preservation1 : t ⊢ Γ -> Γ ⊢ t : A -> t -β> t' -> Γ ⊢ t' : A := by
  -- intro cj j r
  -- induction j generalizing t'
  -- case ax => cases r
  -- case var => cases r
  -- case pi => sorry
  -- case tpi => sorry
  -- case lam Γ A B K t j1 j2 ih1 ih2 =>
  --   cases r
  --   case lam_congr1 A' r =>
  --     constructor; apply Proof.lam
  --   case lam_congr2 => sorry
  -- case app Γ f A' B a B' j1 j2 j3 ih1 ih2 =>
  --   cases r
  --   case beta C d => sorry
  --   case app_congr1 f' r => sorry
  --   case app_congr2 => sorry
  -- case econv j1 j2 j3 ih1 ih2 => sorry
  -- case iconv => sorry

  -- theorem preservation_wf1 : t ⊢ Γ -> Γ ⊢ t : A -> t -β> t' -> t' ⊢ Γ := by
  -- intro j1 j2 r
  -- induction j2 generalizing t'
  -- case ax => cases r
  -- case var => cases r
  -- case pi => sorry
  -- case tpi => sorry
  -- case lam => sorry
  -- case app j2 j3 j4 ih1 ih2 =>
  --   cases j1
  --   case _ cj1 cj2 =>
  --   cases r
  --   case beta =>
  --     cases cj1
  --     case _ cj1 cj3 =>
  --       sorry
  --   case app_congr1 => sorry
  --   case app_congr2 => sorry
  -- case econv ih1 ih2 => sorry
  -- case iconv => sorry


  -- theorem preservation : Γ ⊢ t : A -> t -β>* t' -> Γ ⊢ t' : A := by
  -- intro j r
  -- induction r generalizing Γ A
  -- case _ => exact j
  -- case _ r1 _r2 ih => apply ih (preservation1 j r1)

  theorem preservation_type : Γ ⊢ t : A -> A -β>* A' -> Γ ⊢ t : A' := by sorry

end FomegaMut.Proof
