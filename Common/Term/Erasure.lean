import Common.Term

namespace Term

  def erase : Term -> Term
  | bound K i => bound K i
  | none => .none
  | const K => .const K
  | lam m0 _ t => erase t
  | lam mf _ t => lam mf none (erase t)
  | lam mt A t => lam mt (erase A) (erase t)
  | app m0 f _ => erase f
  | app mf f a => app mf (erase f) (erase a)
  | app mt f a => app mt (erase f) (erase a)
  | all m A B => all m (erase A) (erase B)
  | pair t s => pair (erase t) (erase s)
  | inter _ _ t _ => erase t
  | fst t => erase t
  | snd t => erase t
  | inter_ty A B => inter_ty (erase A) (erase B)
  | times A B => times (erase A) (erase B)
  | refl _ _ => lam mf none (bound .type 0)
  | subst _ e => erase e
  | phi _ a _ _ => erase a
  | eq A a b => eq (erase A) (erase a) (erase b)
  | conv _ t _ => erase t
  | unit => unit
  | unit_ty => unit_ty
  | unit_rec t1 t2 => unit_rec (erase t1) (erase t2)

end Term
