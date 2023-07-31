
import Cedille.Def
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Red

namespace Cedille

  lemma red_erasure_step :
    erase t1 = erase t2 ->
    t1 -β> z1 ->
    ∃ z2, t2 -β>* z2 ∧ erase z1 = erase z2
  := λ h step => @Nat.subInduction
    (λ n1 n2 =>
      (t1 t2 z1 : _) ->
      size t1 ≤ n1  ->
      size t2 ≤ n2 ->
      erase t1 = erase t2 ->
      t1 -β> z1 ->
      ∃ z2, t2 -β>* z2 ∧ erase z1 = erase z2)
    (by {
      intros m t1 t2 z1 h1 h2 e step
      have lem : size t1 = 0 := sorry
      cases t1 <;> simp at lem <;> cases step
    })
    (by {
      intros n t1 t2 z1 h1 h2 e step
      sorry
    })
    (by {
      intros n m ih t1 t2 z1 h1 h2 e step
      cases t1 <;> cases t2 <;> simp at * <;> simp
      case bound.bound _ => cases step
      case bound.free _ => cases step
      case bound.const _ => cases step
      case bound.bind _ => cases step
      case bound.ctor _ => cases step
      case free.bound _ => cases step
      case free.free _ => cases step
      case free.const _ => cases step
      case free.bind _ => cases step
      case free.ctor _ => cases step
      case const.bound _ => cases step
      case const.free _ => cases step
      case const.const _ => cases step
      case const.bind _ => cases step
      case const.ctor _ => cases step
      case bind.bound _ q1 qstep k u1 u2 i => {
        cases k
        case lam m => {
          cases m <;> simp at * <;> simp [*]
        }
        case pi m => {

        }
        case inter => {

        }
      }
    })
    (size t1)
    (size t2)
    t1
    t2
    z1
    (by simp)
    (by simp)
    h
    step



  lemma red_erasure :
    erase t1 = erase t2 ->
    t1 -β>* z1 ->
    ∃ z2, t2 -β>* z2 ∧ erase z1 = erase z2
  := by {
    intro h step
    induction step generalizing t2
    case refl t' => {
      exists t2; simp [*]
      apply RedStar.refl
    }
    case step u1 u2 u3 s1 _s2 e => {
      have lem := red_erasure_step h s1
      casesm* ∃ _, _, _ ∧ _; case _ w step e2 =>
      have lem := @e w e2
      casesm* ∃ _, _, _ ∧ _; case _ w' step' e3 =>
      exists w'; simp [*]
      apply RedStar.trans step step'
    }
  }

end Cedille
