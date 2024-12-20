
import Common.Term
import Common.Term.Reduction

namespace Term

  def Reducible (t : Term) := ∃ t', t -β> t'
  def Normal (t : Term) := ¬ (Reducible t)
  abbrev NormalForm (t : Term) (t' : Term) := t -β>* t' ∧ Normal t'
  def WN (t : Term) := ∃ t', NormalForm t t'

  inductive SN : Term -> Prop where
  | sn : (∀ y, x -β> y -> SN y) -> SN x

  theorem sn_preimage (f : Term -> Term) x : (∀ x y, x -β> y -> (f x) -β> (f y)) -> SN (f x) -> SN x := by
  intro h sh
  generalize zdef : f x = z at sh
  induction sh generalizing f x
  case _ x' h' ih =>
    subst zdef; constructor
    intro y r
    apply ih (f y) (h _ _ r) f y h rfl

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
    have lem : Reducible t' ∨ Normal t' := by apply Classical.em
    cases lem
    case _ h' =>
      cases h'
      case _ t'' h' =>
        have lem := ih _ h'
        cases lem
        case _ z lem =>
          exists z; apply And.intro
          apply Term.RedStar.step; apply h'; apply lem.1
          apply lem.2
    case _ h' =>
      exists t'; apply And.intro; apply Term.Red.refl
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
