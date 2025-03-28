import Common
import CC.Term

namespace CC

  inductive Red : Term -> Term -> Prop where
  | beta : Red ((`λ[A] b) `@ t) (b β[t])
  | binder_congr1 : Red A A' -> Red (.binder b A t) (.binder b A' t)
  | binder_congr2 : Red t t' -> Red (.binder b A t) (.binder b A t')
  | app_congr1 : Red f f' -> Red (.app f a) (.app f' a)
  | app_congr2 : Red a a' -> Red (.app f a) (.app f a')

  def LocRed (ℓ ℓ' : Loc) : Prop := Red ℓ.it ℓ'.it

  infix:40 " -β> " => Red
  infix:39 " -β>* " => @Star Term Red
  infix:39 " -β>+ " => @Plus Term Red
  infix:38 " =β= " => @Conv Term Red

  inductive Proof : Loc -> Term -> Prop
  | ax : Proof (Γ ⊢ ★) □
  | var :
    Loc.get_type x Γ = .some (Δ ⊢ A) ->
    Proof (Δ ⊢ A) (.const K) ->
    Proof (Γ ⊢ #x) A
  | pi :
    Proof (pi1 Γ B ⊢ A) (.const K1) ->
    Proof (pi2 A Γ ⊢ B) (.const K2) ->
    Proof (Γ ⊢ Π[A] B) (.const K2)
  | lam :
    Proof (lam1 Γ t ⊢ A) (.const K) ->
    Proof (lam2 A Γ ⊢ t) B ->
    Proof (Γ ⊢ `λ[A] t) (Π[A] B)
  | app :
    Proof (.app1 Γ a ⊢ f) (Π[A] B) ->
    Proof (.app2 f Γ ⊢ a) A ->
    B' = B β[a] ->
    Proof (Γ ⊢ f `@ a) B'
  | conv :
    Proof (Γ ⊢ t) A ->
    A =β= B ->
    Proof (Γ ⊢ t) B

  notation ℓ " `: " A:100 => Proof ℓ A

  theorem beta : (.app1 Γ a ⊢ `λ[C] b) `: Π[A] B -> (Γ ⊢ (b β[a])) `: (B β[a]) := by
  sorry

  theorem preservation : ℓ `: A -> LocRed ℓ ℓ' -> ℓ' `: A := by
  intro j r
  induction j
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ Γ t A K B j1 j2 ih1 ih2 =>
    unfold LocRed at r; simp at r
    generalize sdef: ℓ'.it = s at r
    cases r
    case _ A' r =>

      sorry
    case _ => sorry
  case _ a f A B B' j1 j2 j3 ih1 ih2 => sorry
  case _ A B j1 j2 ih =>
    replace ih := ih r
    apply Proof.conv ih j2


end CC
