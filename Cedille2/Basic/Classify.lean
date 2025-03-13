import Common
import Cedille2.Proof
import Cedille2.Basic.Weaken
import Cedille2.Basic.Substitution
import Cedille2.Basic.Inversion
import Cedille2.Basic.Preservation

namespace Cedille2.Proof

  @[simp]
  abbrev ClassifyKindLemmaType (_ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, A) => t.classify = .kind -> A = □
  | .wf => λ () => True

  theorem classify_kind_lemma : Judgment v Γ ix -> ClassifyKindLemmaType Γ v ix := by
  intro j; induction j <;> simp at *
  case var K _ _ _ _ => cases K <;> simp at *
  case pi m K B j1 j2 ih1 ih2 =>
    cases m <;> simp at *
    all_goals apply ih2
  case lam m K B t j1 j2 j3 j4 ih1 ih2 ih3 =>
    cases m <;> simp at *
    all_goals
      intro h; replace ih1 := ih1 h; subst ih1
      apply kind_not_proof j2
  case app f m A B a B' j1 j2 j3 ih1 ih2 => sorry
    -- cases f <;> simp at *
    -- case var K _ => cases K <;> simp at *
    -- case const K => cases K <;> simp at *
    -- case lam m f t =>
    --   split <;> simp at *
    --   all_goals
    --     case _ e1 e2 =>
    --       split <;> try simp
    --       case _ h1 =>
    --         intro h2; exfalso
    --         apply ih2 h2
    -- case app =>
    --   intro h; exfalso
    --   apply ih2 h
    -- case all =>
    --   intro h; exfalso
    --   apply ih2 h
  case iconv t A B K j1 j2 j3 ih1 ih2 =>
    intro h; replace ih1 := ih1 h; subst ih1
    cases j3; case _ w r =>
      have lem := Red.red_const_forces_const r.1; subst lem
      replace j2 := preservation_term j2 r.2
      exfalso; apply kind_not_proof j2
  all_goals
    intro h; try simp at h
  all_goals sorry

  theorem classify_kind : Γ ⊢ t : A -> t.classify = .kind -> A = □ := by
  intro h1 h2; have lem := classify_kind_lemma h1; simp at lem
  apply lem h2

  theorem is_kind_forces_classify : Γ ⊢ t : A -> A = □ -> t.classify = .kind := by sorry

  @[simp]
  abbrev ClassifyTypeLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, A) => t.classify = .type -> Γ ⊢ A : □
  | .wf => λ () => True

  theorem classify_type_lemma : Judgment v Γ ix -> ClassifyTypeLemmaType Γ v ix := by
  intro j; induction j <;> simp at *
  case _ K T j1 j2 ih =>
    cases K <;> simp at *
    subst j2; apply j1
  case _ m K B j1 j2 ih1 ih2 =>
    cases m <;> simp at *
    case _ =>
      intro h; constructor
      apply judgment_ctx_wf j1
    case _ =>
      intro h; constructor
      apply judgment_ctx_wf j1
    case _ =>
      intro h; replace ih2 := ih2 h
      exfalso; apply kind_not_proof ih2
  case _ Γ A m K B t j1 j2 j3 j4 ih1 ih2 ih3 =>
    cases m <;> simp at *
    case _ =>
      intro h; replace ih3 := ih3 h
      sorry
    case _ =>
      intro h; replace ih3 := ih3 h
      sorry
    case _ =>
      have lem := @Judgment.pi Γ A mt K B
      intro h; simp at lem
      apply lem j1 j2
  case _ Γ f m A B a B' j1 j2 j3 ih1 ih2 => sorry
  case _ j _ _ _ =>
    constructor
    apply judgment_ctx_wf j
  case _ j _ _ _ => sorry
  case _ j1 j2 j3 ih1 ih2 =>
    sorry
  all_goals sorry

  theorem classify_type : Γ ⊢ t : A -> t.classify = .type -> Γ ⊢ A : □ := by
  intro h1 h2; have lem := classify_type_lemma h1; simp at lem
  apply lem h2

  theorem is_type_forces_classify : Γ ⊢ t : A -> Γ ⊢ A : □ -> t.classify = .type := by sorry

  @[simp]
  abbrev ClassifyTermLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, A) => t.classify = .term -> Γ ⊢ A : ★
  | .wf => λ () => True

  theorem classify_term_lemma : Judgment v Γ ix -> ClassifyTermLemmaType Γ v ix := by
  intro j; induction j <;> simp at *
  case _ K T j1 j2 ih =>
    cases K <;> simp at *
    subst j2; apply j1
  case _ Γ A m K B j1 j2 ih1 ih2 =>
    cases m <;> simp at *
    case _ h =>
      intro h; sorry
    case _ h => sorry
    case _ h => sorry
  case _ Γ A m K B t j1 j2 j3 j4 ih1 ih2 ih3 =>
    cases m <;> simp at *
    case _ =>
      have lem := @Judgment.pi Γ A mf K B
      intro h; simp at lem
      apply lem j1 j2
    case _ =>
      have lem := @Judgment.pi Γ A m0 K B
      intro h; simp at lem
      apply lem j1 j2
    case _ => sorry
  case _ => sorry
  case _ j1 j2 j3 j4 j5 ih1 ih2 ih3 ih4 => sorry
  case _ => sorry
  case _ => sorry
  case _ j1 j2 ih1 ih2 => sorry
  case _ => sorry
  case _ => sorry
  case _ j1 j2 j3 ih1 ih2 =>
    intro h; replace ih1 := ih1 h

    sorry
  case _ => sorry

  theorem classify_term : Γ ⊢ t : A -> t.classify = .term -> Γ ⊢ A : ★ := by
  intro h1 h2; have lem := classify_term_lemma h1; simp at lem
  apply lem h2


  theorem is_term_forces_classify : Γ ⊢ t : A -> Γ ⊢ A : ★ -> t.classify = .term := by sorry


end Cedille2.Proof
