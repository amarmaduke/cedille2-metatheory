
import Fomega.Basic

namespace Fomega

  inductive AlgorithmKind where
  | check | cinfer | infer | wf

  @[simp]
  abbrev CheckArgs : AlgorithmKind -> Type
  | .check => Term × Term
  | .cinfer => Term
  | .infer => Term
  | .wf => Unit

  @[simp]
  abbrev CheckRets : AlgorithmKind -> Type
  | .check => Option Unit
  | .cinfer => Option Term
  | .infer => Option Term
  | .wf => Option Unit

  def check : (k : AlgorithmKind) -> Ctx Term -> CheckArgs k -> CheckRets k
  | .wf, [], () => .some .unit
  | .wf, .cons A Γ, () => do
    let Ak <- check .infer Γ A
    let _ <- check .wf Γ ()
  | .infer, Γ, Π[A] B => sorry
  | .check, _, _ => .none
  | .cinfer, _, _ => .none
  | .infer, _, _ => .none

end Fomega
