import Common
import Erased.Term
import Cedille2.Term

namespace Cedille2.Term
  def erase : Term -> Erased.Term
  | .var K x => .var K x
  | .const K => .const K
  | .app mt f a => .appt (erase f) (erase a)
  | .app mf f a => .app (erase f) (erase a)
  | .app m0 f _ => erase f
  | .lam mt A t => .lamt (erase A) (erase t)
  | .lam mf _ t => .lam (erase t)
  | .lam m0 _ t => erase t
  | .all m A B => .all m (erase A) (erase B)
  | .inter _ _ _ t _ => erase t
  | .fst t => erase t
  | .snd t => erase t
  | .inter_ty A B => .inter_ty (erase A) (erase B)
  | .refl _ => .lam (.var .type 0)
  | .eq a b => .eq (erase a) (erase b)
  | .subst _ _ t => erase t
  | .phi a _ _ => erase a
  | .conv _ _ _ t => erase t
end Cedille2.Term
