
namespace Fomega
  inductive Const : Type where
  | kind | type
  deriving Repr

  inductive Term : Type where
  | var : Nat -> Term
  | const : Const -> Term
  | app : Term -> Term -> Term
  | lam : Term -> Term -> Term
  | all : Term -> Term -> Term
  | pair : Term -> Term -> Term
  | fst : Term -> Term
  | snd : Term -> Term
  | times : Term -> Term -> Term
  | unit : Term
  | unit_ty : Term
  | unit_rec : Term -> Term -> Term -> Term
  deriving Repr

  notation "★" => Term.const Const.type
  notation "□" => Term.const Const.kind
  infixl:15 " `@ " => Term.app
  notation "`λ[" A "]" t:50 => Term.lam A t
  notation "Π[" A "]" t:50 => Term.all A t
  infixl:15 "⊗" => Term.times
  notation "(u)" => Term.unit
  notation "(U)" => Term.unit_ty
  prefix:max "#" => Term.var

  instance instInhabited_Term : Inhabited Term where
  default := ★
end Fomega
