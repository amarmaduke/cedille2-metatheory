import Common
import Fomega.Proof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution

namespace Fomega.Proof

  @[simp]
  abbrev AllDestructLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, T) => ∀ A B K, t = Π[A] B -> T =β= .const K -> (A::Γ) ⊢ B : .const K
  | .wf => λ () => True

  theorem all_destruct_lemma : Judgment v Γ ix -> AllDestructLemmaType Γ v ix := by
  intro j; induction j <;> simp at *
  case pi K1 K2 _ j1 j2 _ _ =>
    intro A B K h1 h2 h3; subst h2; subst h1
    cases h3; case _ T r =>
    have lem := Red.const_conv_implies_eq K2 K (by exists T); subst lem
    apply j2
  case conv A' B' _ _ _ cv ih1 _ih2 =>
    intro A B K h1 h2
    cases h2; case _ T h2 =>
    have lem : A' =β= .const K := by apply Red.trans cv (by exists T)
    cases lem; case _ q r =>
      apply ih1 _ _ _ h1 (by exists q)

  @[simp]
  abbrev TimesDestructLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, T) => ∀ A B K, t = .times A B -> T =β= .const K -> Γ ⊢ A : ★ ∧ Γ ⊢ B : ★
  | .wf => λ () => True

  theorem times_destruct_lemma : Judgment v Γ ix -> TimesDestructLemmaType Γ v ix := by
  intro j; induction j <;> simp at *
  case prod j1 j2 _ _ =>
    intro A B K h1 h2 h3; subst h1; subst h2
    cases h3; case _ T h3 =>
      have lem := Red.const_conv_implies_eq .type K (by exists T)
      subst lem; apply And.intro; apply j1; apply j2
  case conv A' B' _ _ _ cv ih1 _ih2 =>
    intro A B K h1 h2
    have lem : A' =β= .const K := by apply Red.trans cv h2
    cases lem; case _ q r =>
      apply ih1 _ _ _ h1 (by exists q)

  @[simp]
  abbrev class_idx (t A : Term) : JudgmentIndex v :=
    match v with
    | .prf => (t, A)
    | .wf => ()

  @[simp]
  abbrev ClassType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (_, A) => A = □ ∨ (∃ K, Γ ⊢ A : .const K)
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
  case var Γ _ x j1 j2 ih =>
    subst j2; apply Or.inr; apply ih x
  case pi K1 K2 _ j1 _ ih1 ih2 =>
    cases ih1
    case _ h =>
      cases K2; simp at *; apply Or.inr; exists .kind
      constructor; apply judgment_ctx_wf j1
    case _ h =>
      cases K2; simp at *; apply Or.inr; exists .kind
      constructor; apply judgment_ctx_wf j1
  case lam K1 K2 _ _ j1 j2 j3 _ _ _ =>
    exists K2; constructor; apply j1; apply j2
  case app Γ f A B a B' j1 j2 j3 _ ih2 =>
    cases ih2; case _ K ih2 =>
      have lem := all_destruct_lemma ih2; simp at lem
      replace lem := lem A B K rfl rfl Red.refl
      replace lem := Proof.beta lem j2; simp at lem
      apply Or.inr; exists K
      rw [j3]; apply lem
  case prod j _ _ => exists .kind; constructor; apply judgment_ctx_wf j
  case pair j1 j2 _ _ _ _=> exists .type; constructor; apply j1; apply j2
  case fst t A B j ih =>
    cases ih; case _ K ih =>
      have lem := times_destruct_lemma ih; simp at lem
      replace lem := lem A B K rfl rfl Red.refl
      apply Or.inr; exists .type; apply lem.1
  case snd t A B j ih =>
    cases ih; case _ K ih =>
      have lem := times_destruct_lemma ih; simp at lem
      replace lem := lem A B K rfl rfl Red.refl
      apply Or.inr; exists .type; apply lem.2
  case unit j _ => exists .type; constructor; apply j
  case unit_ty j _ => exists .kind; constructor; apply j
  case unit_rec j _ _ _ => apply Or.inr; exists .type
  case conv K _h1 h2 _h3 _ih1 _ih2 =>
    apply Or.inr; exists K

  theorem classification : Γ ⊢ t : A -> A = □ ∨ (∃ K, Γ ⊢ A : .const K) := by
  intro j
  have lem := classification_lemma j; simp at lem
  apply lem

end Fomega.Proof
