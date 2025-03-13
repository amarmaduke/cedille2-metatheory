
import Common
import Cedille2.Proof
import Cedille2.Basic.Weaken

namespace Cedille2.Proof

  inductive ConstSubExpr (sub : Const) : Term -> Prop
  | const : sub = K -> ConstSubExpr sub (.const K)
  | app1 : ConstSubExpr sub f -> ConstSubExpr sub (.app m f a)
  | app2 : ConstSubExpr sub a -> ConstSubExpr sub (.app m f a)
  | lam1 : ConstSubExpr sub A -> ConstSubExpr sub (.lam m A t)
  | lam2 : ConstSubExpr sub t -> ConstSubExpr sub (.lam m A t)
  | all1 : ConstSubExpr sub A -> ConstSubExpr sub (.all m A B)
  | all2 : ConstSubExpr sub B -> ConstSubExpr sub (.all m A B)
  | inter1 : ConstSubExpr sub T -> ConstSubExpr sub (.inter g1 g2 T t s)
  | inter2 : ConstSubExpr sub t -> ConstSubExpr sub (.inter g1 g2 T t s)
  | inter3 : ConstSubExpr sub s -> ConstSubExpr sub (.inter g1 g2 T t s)
  | fst : ConstSubExpr sub t -> ConstSubExpr sub (.fst t)
  | snd : ConstSubExpr sub t -> ConstSubExpr sub (.snd t)
  | inter_ty1 : ConstSubExpr sub A -> ConstSubExpr sub (.inter_ty A B)
  | inter_ty2 : ConstSubExpr sub B -> ConstSubExpr sub (.inter_ty A B)
  | refl1 : ConstSubExpr sub a -> ConstSubExpr sub (.refl g1 g2 a b)
  | refl2 : ConstSubExpr sub b -> ConstSubExpr sub (.refl g1 g2 a b)
  | eq1 : ConstSubExpr sub a -> ConstSubExpr sub (.eq a b)
  | eq2 : ConstSubExpr sub b -> ConstSubExpr sub (.eq a b)
  | subst1 : ConstSubExpr sub Pr -> ConstSubExpr sub (.subst Pr e t)
  | subst2 : ConstSubExpr sub e -> ConstSubExpr sub (.subst Pr e t)
  | subst3 : ConstSubExpr sub t -> ConstSubExpr sub (.subst Pr e t)
  | phi1 : ConstSubExpr sub a -> ConstSubExpr sub (.phi a b e)
  | phi2 : ConstSubExpr sub b -> ConstSubExpr sub (.phi a b e)
  | phi3 : ConstSubExpr sub e -> ConstSubExpr sub (.phi a b e)
  | conv1 : ConstSubExpr sub T -> ConstSubExpr sub (.conv g1 g2 T t)
  | conv2 : ConstSubExpr sub t -> ConstSubExpr sub (.conv g1 g2 T t)

  @[simp]
  abbrev KindNotSubExprLemma (_ : Ctx Term) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
  | .prf => λ (t, _) => ¬ ConstSubExpr .kind t
  | .wf => λ () => True

  theorem kind_not_subexpr_lemma : Judgment v Γ ix -> KindNotSubExprLemma Γ v ix := by
  intro j; induction j <;> simp at *
  case _ =>
    intro h; cases h
    case _ h => injection h
  case _ => intro h; cases h
  case _ ih1 ih2 =>
    intro h; cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
  case _ ih1 ih2 ih3 =>
    intro h; cases h
    case _ h => apply ih1 h
    case _ h => apply ih3 h
  case _ ih1 ih2 =>
    intro h; cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
  case _ ih1 ih2 =>
    intro h; cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
  case _ ih1 ih2 ih3 ih4 =>
    intro h; cases h
    case _ h => apply ih3 h
    case _ h => apply ih1 h
    case _ h => apply ih4 h
  case _ ih =>
    intro h; cases h
    case _ h => apply ih h
  case _ ih =>
    intro h; cases h
    case _ h => apply ih h
  case _ ih1 ih2 ih3 =>
    intro h; cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
  case _ ih1 ih2 ih3 =>
    intro h; cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
  case _ ih1 ih2 ih3 ih4 =>
    intro h; cases h
    case _ h => apply ih3 h
    case _ h => apply ih1 h
    case _ h => apply ih4 h
  case _ ih1 ih2 ih3 =>
    intro h; cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
    case _ h => apply ih3 h
  case _ ih1 ih2 => apply ih1
  case _ ih1 ih2 =>
    intro h; cases h
    case _ h => apply ih2 h
    case _ h => apply ih1 h

  theorem kind_not_subexpr : Γ ⊢ t : A -> ConstSubExpr .kind t -> False := by
  intro h1 h2
  have lem := kind_not_subexpr_lemma h1; simp at lem
  apply lem h2

  theorem kind_not_proof : ¬ (Γ ⊢ □ : A) := by
  intro h; apply kind_not_subexpr h; constructor; rfl

  -- theorem lam_destruct_conv :
  --   Γ ⊢ .lam mf A t : T ->
  --   T =β= .all mf C D ->
  --   ∃ B, A =β= C ∧ B =β= D ∧ Γ ⊢ .lam mf A t : .all mf A B
  -- := by
  -- intro j hc
  -- generalize sdef : Term.lam mf A t = s at *
  -- induction j generalizing A C D t
  -- case ax => simp at sdef
  -- case var => simp at sdef
  -- case pi => simp at sdef
  -- case tpi => simp at sdef
  -- case lam A' B' K' t' j3 j4 ih1 ih2 => sorry
  --   -- replace hc := Term.RedConv.all_congr hc
  --   -- injection sdef with e1 e2 e3
  --   -- subst e2; subst e3; exists B'
  --   -- apply And.intro hc.2.1
  --   -- apply And.intro hc.2.2
  --   -- constructor; apply j3; apply j4
  -- case app => simp at sdef
  -- case econv Γ t' A' B' _K' h1 _h2 h3 ih1 _ih2 =>
  --   cases t' <;> simp at sdef
  -- case iconv Γ t' A' B' _K' h1 _h2 h3 ih1 _ih2 => sorry

  -- theorem lam_destruct_body :
  --   Γ ⊢ .lam mf A t : T ->
  --   Γ ⊢ .all mf A B : .const K ->
  --   T =β= .all mf A B ->
  --   (A::Γ) ⊢ t : B
  -- := by
  -- intro j1 j2 hc
  -- generalize sdef : Term.lam mf A t = s at *
  -- induction j1 generalizing A B t K
  -- case ax => simp at sdef
  -- case var => simp at sdef
  -- case pi => simp at sdef
  -- case tpi => simp at sdef
  -- case lam Γ' A' B' K' t' j3 j4 ih1 ih2 =>
  --   injection sdef with e1 e2 e3
  --   subst e2; subst e3
  --   replace j3 := all_destruct j2 Term.RedConv.refl
  --   have lem := Term.RedConv.all_congr hc
  --   apply Proof.conv; apply j4
  --   apply j3.2.2; apply lem.2.2
  -- case app => simp at sdef
  -- case conv Γ t' A' B' _K' h1 _h2 h3 ih1 _ih2 =>
  --   cases t' <;> simp at sdef
  --   case _ m r1 r2 =>
  --     cases sdef
  --     case _ e1 sdef =>
  --     cases sdef
  --     case _ e2 e3 =>
  --       subst e1; subst e2; subst e3
  --       apply @ih1 A t B K j2 (Term.RedConv.trans h3 hc) rfl

end Cedille2.Proof
