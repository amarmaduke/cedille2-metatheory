import Common.Term
import Common.Reduction

namespace Term

  def erase : Term -> Term
  | .bound K i => .bound K i
  | .none => .none
  | .const K => .const K
  | .lam m0 _ t => erase t
  | .lam mf _ t => .lam mf .none (erase t)
  | .lam mt A t => .lam mt (erase A) (erase t)
  | .app m0 f _ => erase f
  | .app mf f a => .app mf (erase f) (erase a)
  | .app mt f a => .app mt (erase f) (erase a)
  | .all m A B => .all m (erase A) (erase B)
  | .spair t s => .spair (erase t) (erase s)
  | .pair _ _ t _ => erase t
  | .fst t => erase t
  | .snd t => erase t
  | .prod A B => .prod (erase A) (erase B)
  | .sprod A B => .sprod (erase A) (erase B)
  | .refl _ => .lam mf .none (.bound .type 0)
  | .subst _ e => erase e
  | .phi a _ _ => erase a
  | .eq A a b => .eq (erase A) (erase a) (erase b)
  | .conv _ t _ => erase t
  | .id t => erase t

end Term
