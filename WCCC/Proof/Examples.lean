
import Common
import WCCC.Proof

namespace WCCC.Example

  postfix:max "!" => Term.bound Const.type
  postfix:max "!!" => Term.bound Const.kind
  infixr:100 "-t>" => Term.all mt
  infixr:100 "-f>" => Term.all mf
  infixr:100 "-0>" => Term.all m0
  infixr:100 "|t>" => Term.lam mt
  infixr:100 "|f>" => Term.lam mf
  infixr:100 "|0>" => Term.lam m0
  infixl:100 "@t" => Term.app mt
  infixl:100 "@f" => Term.app mf
  infixl:100 "@0" => Term.app m0

  namespace Nat

    def PreNat : Term :=
      ★ -0> 0!! -f> (1!! -f> 2!!) -f> 2!!
    def PreZero : Term :=
      ★ |0> 0!! |f> (1!! -f> 2!!) |f> 1!
    def PreSucc : Term :=
      PreNat |f> ★ |0> 0!! |f> (1!! -f> 2!!) |f> 0! @f (3! @t 2! @f 1! @f 0!)

    theorem PreNat_is_proof Γ : Γ ⊢[mt] PreNat : ★ := by {
      unfold PreNat
      constructor
      case K => exact .kind
      constructor
      case _ =>
      constructor
      case K => exact .kind
      case _ =>
        constructor
        case m1 => exact mt
        all_goals try (unfold Mode.dom; simp [*] at *)
        constructor
        simp
      case _ =>
        constructor
        case K => exact .kind
        case _ =>
          constructor
          case K => exact .kind
          case _ =>
            unfold Mode.dom; simp
            constructor
            case m1 => exact mt
            all_goals try (simp [*])
            constructor
          case _ =>
            unfold Mode.codom; simp
            constructor
            case m1 => exact mt
            all_goals try (simp [*])
            constructor
        case _ =>
          unfold Mode.codom; simp
          constructor
          case m1 => exact mt
          all_goals try (simp [*])
          constructor
    }

    theorem PreZero_is_proof Γ : Γ ⊢[mf] PreZero : PreNat := by {
      unfold PreZero; unfold PreNat
      constructor
      case K => exact .kind
      constructor
      case _ =>
        constructor
        case K => exact .kind
        case _ =>
          constructor
          case m1 => exact m0
          all_goals simp [*]
          constructor
        case _ =>
          constructor
          case K => exact .type
          case _ =>
            constructor
            case K => exact .kind
            case _ =>
              constructor
              case m1 => exact m0
              all_goals simp [*]
              constructor
            case _ =>
              constructor
              case m1 => exact m0
              all_goals simp [*]
              constructor
          case _ =>
            constructor
            case m1 => exact mf
            all_goals simp [*]
            case _ =>
            constructor
            case m1 => exact m0
            all_goals simp [*]
            constructor
          case _ =>
            constructor
            case m1 => exact m0
            all_goals simp [*]
            constructor
        case _ =>
          constructor
          case K => exact .kind
          case _ =>
            constructor
            case K => exact .kind
            case _ =>
              constructor
              case m1 => exact m0
              all_goals simp [*]
              constructor
            case _ =>
              constructor
              case m1 => exact m0
              all_goals simp [*]
              constructor
          case _ =>
            constructor
            case m1 => exact m0
            all_goals simp [*]
            constructor
      case _ =>
        constructor
        case K => exact .kind
        case _ =>
          constructor
          case m1 => exact mt
          all_goals simp [*]
          constructor
        case _ =>
          constructor
          case K => exact .kind
          case _ =>
            constructor
            case K => exact .kind
            case _ =>
              constructor
              case m1 => exact mt
              all_goals simp [*]
              constructor
            case _ =>
              constructor
              case m1 => exact mt
              all_goals simp [*]
              constructor
          case _ =>
            constructor
            case m1 => exact mt
            all_goals simp [*]
            constructor
    }

    theorem PreSucc_is_proof Γ : Γ ⊢[mf] PreSucc : (PreNat -f> PreNat) := by {
      unfold PreSucc
      constructor
      case K => exact .kind
      case _ => apply PreNat_is_proof
      case _ =>
        constructor
        case K => exact .kind
        case _ => constructor
        case _ =>
          constructor
          case K => exact .type
          case _ =>
            constructor
            case m1 => exact m0
            all_goals simp [*]
            constructor
          case _ =>
            constructor
            case K => exact .type
            case _ =>
              sorry
            case _ =>
              generalize adef : (3! @t 2! @f 1! @f 0!) = a
              have lem1 : 2!! β[a] = 2!! := by sorry
              rw [<-lem1]
              constructor
              case A => exact 2!!
              case _ =>
                constructor
                case m1 => exact mf
                all_goals simp [*]
                case _ =>
                  sorry
              case _ =>
                subst adef

                sorry
            case _ =>
              sorry
          case _ =>
            sorry
        case _ =>
          sorry
      case _ => apply PreNat_is_proof
    }

  end Nat


end WCCC.Example
