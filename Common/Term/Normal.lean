
import Common.Term
import Common.Reduction

namespace Term

  def Reducible (t : Term) := ∃ t', t -β> t'
  def Normal (t : Term) := ¬ (Reducible t)
  abbrev NormalForm (t : Term) (t' : Term) := t -β>* t' ∧ Normal t'
  def WN (t : Term) := ∃ t', NormalForm t t'

  theorem reducible_decidable : ∀ t, (Reducible t) ∨ ¬ (Reducible t) := by
  intro t
  induction t
  case bound =>
    apply Or.inr; intro h
    cases h; case _ _ r => cases r
  case none =>
    apply Or.inr; intro h
    cases h; case _ _ r => cases r
  case const =>
    apply Or.inr; intro h
    cases h; case _ _ r => cases r
  case lam m A t ih1 ih2 =>
    cases ih1
    case _ h =>
      apply Or.inl
      cases h
      case _ A' r =>
        exists (.lam m A' t)
        apply Red.lam_congr1 r
    case _ h1 =>
      cases ih2
      case _ h =>
        apply Or.inl
        cases h
        case _ t' r =>
          exists (.lam m A t')
          apply Red.lam_congr2 r
      case _ h2 =>
        apply Or.inr; intro h
        cases h; case _ w r =>
          cases r
          case _ f' r => apply h1; exists f'
          case _ a' r => apply h2; exists a'
  case app m f a ih1 ih2 =>
    cases ih1
    case _ h =>
      cases h; case _ f' r =>
        apply Or.inl; exists (.app m f' a)
        apply Red.app_congr1 r
    case _ h1 =>
      cases ih2
      case _ h =>
        cases h; case _ a' r =>
          apply Or.inl; exists .app m f a'
          apply Red.app_congr2 r
      case _ h2 =>
        cases f
        case lam m2 A t =>
          apply Or.inl; exists (t β[a])
          apply Red.beta
        case conv => sorry
        all_goals (
          apply Or.inr; intro h
          cases h; case _ w r =>
          cases r
          case _ w r => apply h1; exists w
          case _ w r => apply h2; exists w
        )
  case all => sorry
  case pair => sorry
  case fst => sorry
  case snd => sorry
  case prod => sorry
  case refl => sorry
  case subst => sorry
  case phi => sorry
  case eq => sorry
  case conv => sorry

  inductive SN : Term -> Prop where
  | sn : (∀ y, x -β> y -> SN y) -> SN x

  theorem sn_preimage (f : Term -> Term) x :
    (∀ x y, x -β> y -> (f x) -β> (f y)) ->
    SN (f x) ->
    SN x
  := by
  intro h sh
  generalize zdef : f x = z at sh
  induction sh generalizing f x
  case _ x' h' ih =>
    subst zdef; constructor
    intro y r
    apply ih (f y) (h _ _ r) f y h rfl

  theorem sn_preservation_step : SN t -> t -β> t' -> SN t' := by
  intro h red
  induction h
  case _ z h1 _h2 =>
    apply h1 _ red

  theorem sn_preservation : SN t -> t -β>* t' -> SN t' := by
  intro h red
  induction red
  case _ => simp [*]
  case _ r1 _ ih =>
    replace h := sn_preservation_step h r1
    apply ih h

  theorem sn_star : (∀ y, t -β>* y -> SN y) -> SN t := by
  intro h
  constructor
  intro y r
  apply h y (RedStar.step r Red.refl)


  theorem sn_conv : SN t -> t =β= t' -> SN t' := by sorry
  -- intro h cv
  -- induction h
  -- case _ z h ih =>
  --   constructor
  --   intro y r
  --   cases cv
  --   case _ w rh =>
  --     cases rh.1
  --     case _ =>

  --     case _ z' r1 r2 =>
  --       have lem : z' =β= t' := by sorry
  --       replace ih := ih _ r1 lem
  --       apply sn_preservation_step ih r

  theorem sn_expansion_step : SN t' -> t -β> t' -> SN t := by
  intro h red
  induction h generalizing t
  case _ z h ih =>
    have lem := reducible_decidable z
    sorry


  theorem sn_closed : SN (.app m f a) -> SN f := by
  apply sn_preimage (λ f => .app m f a);
  intro f f'; apply Red.app_congr1

  theorem sn_subst : SN ([σ]t) -> SN t := by
  apply sn_preimage (Subst.apply σ)
  intro x y r; apply Red.subst1_same σ r

  theorem sn_implies_wn : SN t -> WN t := by
  intro h
  induction h
  case sn t' _ ih =>
    have lem : Reducible t' ∨ Normal t' := reducible_decidable t'
    cases lem
    case _ h' =>
      cases h'
      case _ t'' h' =>
        have lem := ih _ h'
        cases lem
        case _ z lem =>
          exists z; apply And.intro
          apply RedStar.step; apply h'; apply lem.1
          apply lem.2
    case _ h' =>
      exists t'; apply And.intro; apply Red.refl
      apply h'

  -- theorem normal_lam : Normal (.lam m A t) -> Normal A ∧ Normal t := by sorry
  -- theorem normal_app : Normal (.app m f a) -> Normal f ∧ Normal a ∧ (∀ A t, f ≠ .lam m A t) := by sorry
  -- theorem normal_all : Normal (.all m A B) -> Normal A ∧ Normal B := by sorry
  -- theorem normal_pair : Normal (.pair B t s) -> Normal B ∧ Normal t ∧ Normal s := by sorry
  -- theorem normal_fst : Normal (.fst t) -> Normal t ∧ (∀ B f s, t ≠ .pair B f s) := by sorry
  -- theorem normal_snd : Normal (.snd t) -> Normal t ∧ (∀ B f s, t ≠ .pair B f s) := by sorry
  -- theorem normal_prod : Normal (.prod A B) -> Normal A ∧ Normal B := by sorry
  -- theorem normal_refl : Normal (.refl t) -> Normal t := by sorry
  -- theorem normal_subst : Normal (.subst Pr e) -> Normal Pr ∧ Normal e ∧ (∀ t, e ≠ refl t) := by sorry
  -- theorem normal_phi : Normal (.phi a b e) -> Normal a ∧ Normal b ∧ Normal e ∧ (∀ t, e ≠ refl t) := by sorry
  -- theorem normal_eq : Normal (.eq A a b) -> Normal A ∧ Normal a ∧ Normal b := by sorry
  -- theorem normal_conv : Normal (.conv B t n) -> Normal B ∧ Normal t := by sorry

  inductive ValueVariant where
  | nf : ValueVariant
  | ne : ValueVariant

  inductive Value : ValueVariant -> Term -> Prop where
  -- Neutral Forms
  | bound : Value .ne (.bound c k)
  | app : Value .ne f -> Value .nf a -> Value .ne (.app m f a)
  | fst : Value .ne t -> Value .ne (.fst t)
  | snd : Value .ne t -> Value .ne (.snd t)
  | subst : Value .nf Pr -> Value .ne e -> Value .ne (.subst Pr e)
  | phi : Value .nf a -> Value .nf b -> Value .ne e -> Value .ne (.phi a b e)
  -- Normal Forms
  | const : Value .nf (.const K)
  | lam : Value .nf A -> Value .nf t -> Value .nf (.lam m A t)
  | all : Value .nf A -> Value .nf B -> Value .nf (.all m A B)
  | pair : Value .nf T -> Value .nf t -> Value .nf s -> Value .nf (.pair n T t s)
  | prod : Value .nf A -> Value .nf B -> Value .nf (.prod A B)
  | refl : Value .nf t -> Value .nf (.refl t)
  | eq : Value .nf A -> Value .nf a -> Value .nf b -> Value .nf (.eq A a b)
  | conv : Value .nf B -> Value .nf t -> Value .nf (.conv n B t)
  | neutral : Value .ne t -> Value .nf t

end Term
