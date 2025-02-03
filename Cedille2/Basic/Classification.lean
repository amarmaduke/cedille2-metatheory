import Common
import Cedille2.Proof
import Cedille2.Basic.Weaken
import Cedille2.Basic.Substitution

namespace Cedille2.Proof

  @[simp]
  abbrev AllDestructLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, T) => ∀ m (A : Term) B K, t = `∀(m)[A] B -> T =β= .const K -> (A::Γ) ⊢ B : .const K
  | .wf => λ () => True

  theorem all_destruct_lemma : Judgment v Γ ix -> AllDestructLemmaType Γ v ix := by
  intro j; induction j <;> simp at *
  case pi K1 K2 _ j1 j2 _ _ => sorry
    -- intro A B K h1 h2 h3; subst h2; subst h1
    -- cases h3; case _ T r =>
    -- have lem := Red.Conv.const_conv_implies_eq K2 K (by exists T); subst lem
    -- apply j2
  case iconv A' B' _ _ _ cv ih1 _ih2 => sorry
    -- intro A B K h1 h2
    -- cases h2; case _ T h2 =>
    -- have lem : A' =β= .const K := by apply Red.Conv.trans cv (by exists T)
    -- cases lem; case _ q r =>
    --   apply ih1 _ _ _ h1 (by exists q)

  @[simp]
  abbrev InterTyDestructLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, T) => ∀ (A : Term) B K, t = [A]∩ B -> T =β= .const K -> Γ ⊢ A : ★ ∧ Γ ⊢ B : ★
  | .wf => λ () => True

  theorem times_destruct_lemma : Judgment v Γ ix -> InterTyDestructLemmaType Γ v ix := by
  intro j; induction j <;> simp at *
  case inter_ty j1 j2 _ _ => sorry
    -- intro A B K h1 h2 h3; subst h1; subst h2
    -- cases h3; case _ T h3 =>
    --   have lem := Red.Conv.const_conv_implies_eq .type K (by exists T)
    --   subst lem; apply And.intro; apply j1; apply j2
  case iconv A' B' _ _ _ cv ih1 _ih2 =>
    intro A B K h1 h2
    have lem : A' =β= .const K := by apply Red.Conv.trans cv h2
    cases lem; case _ q r =>
      apply ih1 _ _ _ h1 (by exists q)

  @[simp]
  abbrev class_idx (t A : Term) : JudgmentIndex v :=
    match v with
    | .prf => (t, A)
    | .wf => ()

  @[simp]
  abbrev ClassType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (_, A) => A = (□ : Term) ∨ (∃ K, Γ ⊢ A : .const K)
  | .wf => λ () => ∀ x, ∃ K, Γ ⊢ Γ d@ x : .const K

  theorem classification_lemma : Judgment v Γ ix -> ClassType Γ v ix := by
  intro j; induction j <;> simp at *
  case nil =>
    unfold default; unfold instInhabited_Term; simp
    exists .kind; constructor; constructor
  case cons A K j1 j2 ih1 _ =>
    intro x; cases x <;> simp at *
    case _ =>
      exists K; have lem := weaken j2 j2; simp at lem
      apply lem
    case _ x =>
      replace ih1 := ih1 x; cases ih1; case _ K ih1 =>
        exists K; have lem := weaken j2 ih1; simp at lem
        apply lem
  case var Γ _ x j1 j2 ih => sorry
    -- subst j2; apply Or.inr; apply ih x
  case pi K1 K2 _ j1 _ ih1 ih2 => sorry
    -- cases ih1
    -- case _ h =>
    --   cases K2; simp at *; apply Or.inr; exists .kind
    --   constructor; apply judgment_ctx_wf j1
    -- case _ h =>
    --   cases K2; simp at *; apply Or.inr; exists .kind
    --   constructor; apply judgment_ctx_wf j1
  case lam K1 K2 _ _ j1 j2 j3 _ _ _ => sorry
    -- exists K2; constructor; apply j1; apply j2
  case app Γ f A B a B' j1 j2 j3 _ ih2 => sorry
    -- cases ih2; case _ K ih2 =>
    --   have lem := all_destruct_lemma ih2; simp at lem
    --   replace lem := lem A B K rfl rfl Red.Conv.refl
    --   replace lem := Proof.beta lem j2; simp at lem
    --   apply Or.inr; exists K
    --   rw [j3]; apply lem
  case inter_ty j _ _ => sorry
    -- exists .kind; constructor; apply judgment_ctx_wf j
  case inter j1 j2 _ _ _ _=> sorry
    -- exists .type; constructor; apply j1; apply j2
  case fst t A B j ih =>
    cases ih; case _ K ih =>
      have lem := times_destruct_lemma ih; simp at lem
      replace lem := lem A B K rfl rfl Red.Conv.refl
      apply Or.inr; exists .type; apply lem.1
  case snd t A B j ih => sorry
    -- cases ih; case _ K ih =>
    --   have lem := times_destruct_lemma ih; simp at lem
    --   replace lem := lem A B K rfl rfl Red.Conv.refl
    --   apply Or.inr; exists .type; apply lem.2
  case eq => sorry
  case refl => sorry
  case subst => sorry
  case phi => sorry
  case iconv K _h1 h2 _h3 _ih1 _ih2 =>
    apply Or.inr; exists K
  case econv => sorry

  theorem classification {t : Term} : Γ ⊢ t : A -> A = (□ : Term) ∨ (∃ K, Γ ⊢ A : .const K) := by
  intro j
  have lem := classification_lemma j; simp at lem
  apply lem

end Cedille2.Proof
