
import WCCC.Proof
import Fomega.Basic.Derivations

namespace FomegaModel

  @[simp]
  def V : Term -> Term
  | □ | ★ => ★
  | .all _ A B =>
    if A.classify = .kind then .all mf (V A) (V B)
    else V B
  | _ => .none

  @[simp]
  def tyinp : Term -> Term
  | □ | ★ => .bound .kind 0
  | .bound .kind x => .bound .kind x
  | .all _ A B =>
    if A.classify = .kind then .all mf (V A) (.all mf (tyinp A) (tyinp B))
    else if A.classify = .type then .all mf (tyinp A) (tyinp B)
    else .none
  | .lam .type A t =>
    if A.classify = .kind then .lam mf (V A) (tyinp t)
    else if A.classify = .type then tyinp t
    else .none
  | .app .type f a =>
    if a.classify = .type then .app mf (tyinp f) (tyinp a)
    else if a.classify = .term then tyinp f
    else .none
  | .prod A B => .none
  | _ => .none


end FomegaModel
