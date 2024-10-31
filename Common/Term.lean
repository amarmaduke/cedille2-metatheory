
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
| none : CvTerm
| const : CvTerm
| bound : Nat -> CvTerm
| all_congr : CvTerm -> CvTerm -> CvTerm
| lam_congr : CvTerm -> CvTerm -> CvTerm
| lam_eta : CvTerm -> CvTerm
| lam_mf_erased : CvTerm -> CvTerm
| lam_m0_erased : CvTerm -> CvTerm
| app_congr : CvTerm -> CvTerm -> CvTerm
| app_beta : CvTerm -> CvTerm
| app_m0_erased : CvTerm -> CvTerm
| prod_congr : CvTerm -> CvTerm -> CvTerm
| pair_congr : CvTerm -> CvTerm -> CvTerm -> CvTerm
| pair_erased : CvTerm -> CvTerm
| fst_congr : CvTerm -> CvTerm
| fst_erased : CvTerm -> CvTerm
| snd_congr : CvTerm -> CvTerm
| snd_erased : CvTerm -> CvTerm
| phi_congr : CvTerm -> CvTerm -> CvTerm -> CvTerm
| phi_erased : CvTerm -> CvTerm
| eq_congr : CvTerm -> CvTerm -> CvTerm -> CvTerm
| refl_congr : CvTerm -> CvTerm
| refl_erased : CvTerm -> CvTerm
| subst_congr : CvTerm -> CvTerm -> CvTerm
| subst_erased : CvTerm -> CvTerm
| conv_congr : CvTerm -> CvTerm -> CvTerm -> CvTerm
| conv_erased : CvTerm -> CvTerm
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

instance instInhabitedTerm : Inhabited Term where
  default := Term.none

namespace Term

  -- templates
  -- | i, bound c k => sorry
  -- | i, none => sorry
  -- | i, const k => sorry
  -- | i, lam m t1 t2 => sorry
  -- | i, app m t1 t2 => sorry
  -- | i, all m t1 t2 => sorry
  -- | i, pair t1 t2 t3 => sorry
  -- | i, fst t => sorry
  -- | i, snd t => sorry
  -- | i, prod t1 t2 => sorry
  -- | i, refl t => sorry
  -- | i, subst t1 t2 => sorry
  -- | i, phi t1 t2 t3 => sorry
  -- | i, eq t1 t2 t3 => sorry
  -- | i, conv t1 t2 c => sorry

  @[simp]
  def cvrefl : Term -> CvTerm
  | bound _ k => .bound k
  | none => .none
  | const _ => .const
  | lam _ t1 t2 => .lam_congr (cvrefl t1) (cvrefl t2)
  | app _ t1 t2 => .app_congr (cvrefl t1) (cvrefl t2)
  | all _ t1 t2 => .all_congr (cvrefl t1) (cvrefl t2)
  | pair t1 t2 t3 => .pair_congr (cvrefl t1) (cvrefl t2) (cvrefl t3)
  | fst t => .fst_congr (cvrefl t)
  | snd t => .snd_congr (cvrefl t)
  | prod t1 t2 => .prod_congr (cvrefl t1) (cvrefl t2)
  | refl t => .refl_congr (cvrefl t)
  | subst t1 t2 => .subst_congr (cvrefl t1) (cvrefl t2)
  | phi t1 t2 t3 => .phi_congr (cvrefl t1) (cvrefl t2) (cvrefl t3)
  | eq t1 t2 t3 => .eq_congr (cvrefl t1) (cvrefl t2) (cvrefl t3)
  | conv t1 t2 c => .conv_congr (cvrefl t1) (cvrefl t2) c

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
