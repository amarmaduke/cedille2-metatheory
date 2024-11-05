
import Common
import Fomega.Ctx
import Fomega.Proof

namespace Fomega

  theorem weaken :
    Γ ⊢ t : A ->
    let (m, n) := (Δ1.length, Δ2.length)
    (Δ1 ++ [^{m}r#I]Γ ++ Δ2) ⊢ ([^{n}r#I]t) : ([^{n}r#I]A)
  := by {
    intro j
    induction j
    case ax Δ => simp; constructor
    case var Γ Γ1 A Γ2 K j1 j2 ih =>
      simp at *
    case pi => sorry
    case tpi => sorry
    case lam => sorry
    case app => sorry
    case conv => sorry
  }

  theorem proof_subst :
    Γ1 ⊢ a : A ->
    (Γ1 ++ [A] ++ Γ2) ⊢ t : T ->
    let n := Γ2.length
    (Γ1 ++ ([beta a]Γ2)) ⊢ ([^{n}beta a]t) : ([^{n}beta a]T)
  := by {
    intro h j
    generalize Γdef : Γ1 ++ [A] ++ Γ2 = Γ at j
    induction j
    case ax Δ => simp; constructor
    case var Δ Δ1 T Δ2 K j1 j2 ih =>
      sorry
    case pi => sorry
    case tpi => sorry
    case lam => sorry
    case app => sorry
    case conv => sorry
  }

end Fomega
