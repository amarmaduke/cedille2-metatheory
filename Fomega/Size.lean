
import Common
import Fomega.Proof

namespace Fomega.Proof

  inductive Size : ∀ {Γ t A}, Nat -> Γ ⊢ t : A -> Prop where
  | ax : Size 0 (.ax)
  | var : Size 0 (.var)
  | pi : Size x1 p1 -> Size x2 p2 -> Size (x1 + x2) (.pi p1 p2)
  | tpi : Size x1 p1 -> Size x2 p2 -> Size (x1 + x2) (.tpi p1 p2)
  | lam : Size x1 p1 -> Size x2 p2 -> Size (x1 + x2) (.lam p1 p2)
  | app : Size x1 p1 -> Size x2 p2 -> Size (x1 + x2) (.app p1 p2 p3)
  | conv : Size x1 p1 -> Size x2 p2 -> Size (x1 + x2) (.conv p1 p2 p3)

  theorem proof_size : (j : Γ ⊢ t : A) -> ∃ n, Size n j := by
  intro j
  induction j
  case ax => exists 0; constructor
  case var => exists 0; constructor
  case pi ih1 ih2 =>
    cases ih1
    case _ n1 ih1 =>
      cases ih2
      case _ n2 ih2 =>
        exists (n1 + n2); constructor; apply ih1; apply ih2
  case tpi ih1 ih2 =>
    cases ih1
    case _ n1 ih1 =>
      cases ih2
      case _ n2 ih2 =>
        exists (n1 + n2); constructor; apply ih1; apply ih2
  case lam ih1 ih2 =>
    cases ih1
    case _ n1 ih1 =>
      cases ih2
      case _ n2 ih2 =>
        exists (n1 + n2); constructor; apply ih1; apply ih2
  case app p ih1 ih2  =>
    cases ih1
    case _ n1 ih1 =>
      cases ih2
      case _ n2 ih2 =>
        exists (n1 + n2); constructor; apply p; apply ih1; apply ih2
  case conv p ih1 ih2 =>
    cases ih1
    case _ n1 ih1 =>
      cases ih2
      case _ n2 ih2 =>
        exists (n1 + n2); constructor; apply p; apply ih1; apply ih2


end Fomega.Proof
