
import Common.Mathlib

inductive Mode where
| free
| erased
| type
deriving BEq

notation "m0" => Mode.erased
notation "mt" => Mode.type
notation "mf" => Mode.free

inductive Const : Type where
| type : Const
| kind : Const
deriving BEq

inductive CvTerm : Type where
| sym : CvTerm -> CvTerm
| ax : CvTerm
| var : CvTerm
| pi : CvTerm -> CvTerm -> CvTerm
| lam_mt : CvTerm -> CvTerm -> CvTerm
| lam_mf : CvTerm -> CvTerm
| lam_eta : CvTerm -> CvTerm
| lam_m0 : CvTerm -> CvTerm
| app : CvTerm -> CvTerm -> CvTerm
| app_beta : CvTerm -> CvTerm
| app_m0 : CvTerm -> CvTerm
| prod : CvTerm -> CvTerm -> CvTerm
| pair : CvTerm -> CvTerm
| fst : CvTerm -> CvTerm
| snd : CvTerm -> CvTerm
| eq : CvTerm -> CvTerm -> CvTerm -> CvTerm
| refl : CvTerm -> CvTerm
| subst : CvTerm -> CvTerm
| conv : CvTerm -> CvTerm
deriving BEq

inductive Term : Type where
| bound : Const -> Nat -> Term
| none : Term
| const : Const -> Term
| lam : Mode -> Term -> Term -> Term
| app : Mode -> Term -> Term -> Term
| all : Mode -> Term -> Term -> Term
| pair : Term -> Term -> Term -> Term
| fst : Term -> Term
| snd : Term -> Term
| prod : Term -> Term -> Term
| refl : Term -> Term
| subst : Term -> Term -> Term
| phi : Term -> Term -> Term -> Term
| eq : Term -> Term -> Term -> Term
| conv : Term -> Term -> CvTerm -> Term
deriving BEq

notation "★" => Term.const Const.type
notation "□" => Term.const Const.kind

instance : Inhabited Term where
  default := Term.none

namespace Term

  -- templates
  -- | i, bound k => sorry
  -- | i, none => sorry
  -- | i, type => sorry
  -- | i, kind => sorry
  -- | i, lam t1 t2 => sorry
  -- | i, app t1 t2 => sorry
  -- | i, all t1 t2 => sorry
  -- | i, pair t1 t2 => sorry
  -- | i, fst t => sorry
  -- | i, snd t => sorry
  -- | i, prod t1 t2 => sorry
  -- | i, eq t1 t2 t3 => sorry
  -- | i, int t1 t2 => sorry
  -- case bound => sorry
  -- case none => sorry
  -- case type => sorry
  -- case kind => sorry
  -- case lam t1 t2 ih1 ih2 => sorry
  -- case app t1 t2 ih1 ih2 => sorry
  -- case all t1 t2 ih1 ih2 => sorry
  -- case pair t1 t2 ih1 ih2 => sorry
  -- case fst t ih => sorry
  -- case snd t ih => sorry
  -- case prod t1 t2 ih1 ih2 => sorry
  -- case eq t1 t2 t3 ih1 ih2 ih3 => sorry
  -- case int t1 t2 ih1 ih2 => sorry

  @[simp]
  def size : Term -> Nat
  | bound _ _ => 0
  | none => 0
  | const _ => 0
  | lam _ t1 t2 => size t1 + size t2 + 1
  | app _ t1 t2 => size t1 + size t2 + 1
  | all _ t1 t2 => size t1 + size t2 + 1
  | pair t1 t2 t3 => size t1 + size t2 + size t3 + 1
  | fst t => size t + 1
  | snd t => size t + 1
  | prod t1 t2 => size t1 + size t2 + 1
  | refl t => size t + 1
  | subst t1 t2 => size t1 + size t2 + 1
  | phi t1 t2 t3 => size t1 + size t2 + size t3 + 1
  | eq t1 t2 t3 => size t1 + size t2 + size t3 + 1
  | conv t1 t2 _ => size t1 + size t2 + 1

end Term
