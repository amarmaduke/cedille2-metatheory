import Common
import Fomega.Proof
import Fomega.PreProof
import Fomega.Basic.Weaken
import Fomega.Basic.Substitution

namespace Fomega.Proof

  @[simp]
  abbrev AllDestructLemmaType (Γ : Ctx) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, T) => ∀ A B K, t = .all mf A B -> T =β= .const K -> (A::Γ) ⊢ B : .const K
  | .wf => λ () => True

  theorem all_destruct_lemma : Judgment v Γ ix -> AllDestructLemmaType Γ v ix := by
  intro j; induction j <;> simp at *
  case pi K1 K2 _ j1 j2 _ _ =>
    intro A B K h1 h2 T h3 h4
    have lem := @RedConv.const_conv_implies_eq K2 K (by exists T); subst lem
    subst h2; subst h1; apply j2
  case conv A' B' _ _ _ cv ih1 _ih2 =>
    intro A B K h1 T h2 h3
    have lem : A' =β= .const K := by apply RedConv.trans cv (by exists T)
    cases lem; case _ q r =>
      apply ih1 _ _ _ h1 q r.1 r.2

  @[simp]
  abbrev ProdDestructLemmaType (Γ : Ctx) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, T) => ∀ A B K, t = .times A B -> T =β= .const K -> Γ ⊢ A : ★ ∧ Γ ⊢ B : ★
  | .wf => λ () => True

  theorem prod_destruct_lemma : Judgment v Γ ix -> ProdDestructLemmaType Γ v ix := by
  intro j; induction j <;> simp at *
  case prod j1 j2 _ _ =>
    intro A B K h1 h2 x r1 r2; subst h1; subst h2
    have lem := @RedConv.const_conv_implies_eq K .type (by exists x)
    subst lem; apply And.intro; apply j1; apply j2
  case conv A' B' _ _ _ cv ih1 _ih2 =>
    intro A B K h1 T h2 h3
    have lem : A' =β= .const K := by apply RedConv.trans cv (by exists T)
    cases lem; case _ q r =>
      apply ih1 _ _ _ h1 q r.1 r.2

  @[simp]
  abbrev class_idx (t A : Term) : JudgmentIndex v :=
    match v with
    | .prf => (t, A)
    | .wf => ()

  @[simp]
  abbrev ClassType (Γ : Ctx) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (_, A) => A = □ ∨ (∃ K, Γ ⊢ A : .const K)
  | .wf => λ () => True

  theorem classification_lemma : Judgment v Γ ix -> ClassType Γ v ix := by
  intro j; induction j <;> simp at *
  case var K _ j1 j2 _ih =>
    apply Or.inr; exists K; rw [j2]; apply j1
  case pi K1 K2 _ j1 _ ih1 ih2 =>
    cases ih1
    case _ h =>
      cases K2; simp at *; exists .kind
      constructor; apply judgment_ctx_wf j1
      simp
    case _ h =>
      cases K2; simp at *; exists .kind
      constructor; apply judgment_ctx_wf j1
      simp
  case lam K1 K2 _ _ j1 j2 j3 _ _ _ =>
    exists K2; constructor; apply j1; apply j2
  case app Γ f A B a B' j1 j2 j3 _ ih2 =>
    cases ih2; case _ K ih2 =>
      have lem := all_destruct_lemma ih2; simp at lem
      replace lem := lem A B K rfl rfl (.const K) Red.refl Red.refl
      replace lem := Proof.beta lem j2; simp at lem
      apply Or.inr; exists K
      rw [j3]; apply lem
  case prod j _ _ => exists .kind; constructor; apply judgment_ctx_wf j
  case pair j1 j2 _ _ _ _=> exists .type; constructor; apply j1; apply j2
  case fst t A B j ih =>
    cases ih; case _ K ih =>
      have lem := prod_destruct_lemma ih; simp at lem
      replace lem := lem A B K rfl rfl (.const K) Red.refl Red.refl
      apply Or.inr; exists .type; apply lem.1
  case snd t A B j ih =>
    cases ih; case _ K ih =>
      have lem := prod_destruct_lemma ih; simp at lem
      replace lem := lem A B K rfl rfl (.const K) Red.refl Red.refl
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
