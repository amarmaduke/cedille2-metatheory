import Common
import Fomega.Proof
import Fomega.Ctx

namespace Fomega

  inductive IsFreeVar : Nat -> ∀ Γ t A, Proof Γ t A -> Prop where
  | var1 :
    (p1 : A = Γ d@ x) ->
    IsFreeVar n Γ A (.const K) p2 ->
    IsFreeVar n Γ (.bound K x) A (.var p1 p2)
  | var2 :
    (p1 : A = Γ d@ n) ->
    (p2 : Γ ⊢ A : Term.const K) ->
    IsFreeVar n Γ (.bound K n) A (.var p1 p2)
  | pi1 :
    IsFreeVar n Γ A (.const K) p1 ->
    (p2 : (A::Γ) ⊢ B : ★) ->
    IsFreeVar n Γ (.all mf A B) ★ (.pi p1 p2)
  | pi2 :
    (p1 : Γ ⊢ A : Term.const K) ->
    IsFreeVar (n + 1) (A::Γ) B ★ p2 ->
    IsFreeVar n Γ (.all mf A B) ★ (.pi p1 p2)
  | tpi1 :
    IsFreeVar n Γ A □ p1 ->
    (p2 : (A::Γ) ⊢ B : □) ->
    IsFreeVar n Γ (.all mf A B) □ (.tpi p1 p2)
  | tpi2 :
    (p1 : Γ ⊢ A : □) ->
    IsFreeVar (n + 1) (A::Γ) B □ p2 ->
    IsFreeVar n Γ (.all mf A B) □ (.tpi p1 p2)
  | lam1 :
    IsFreeVar n Γ (.all mf A B) (.const K) p1 ->
    (p2 : (A::Γ) ⊢ t : B) ->
    IsFreeVar n Γ (.lam mf A t) (.all mf A B) (.lam p1 p2)
  | lam2 :
    (p1 : Γ ⊢ Term.all mf A B : Term.const K) ->
    IsFreeVar (n + 1) (A::Γ) t B p2 ->
    IsFreeVar n Γ (.lam mf A t) (.all mf A B) (.lam p1 p2)
  | app1 :
    IsFreeVar n Γ f (.all mf A B) p1 ->
    (p2 : Γ ⊢ a : A) ->
    (p3 : B' = (B β[a])) ->
    IsFreeVar n Γ (.app mf f a) B' (.app p1 p2 p3)
  | app2 :
    (p1 : Γ ⊢ f : (.all mf A B)) ->
    IsFreeVar n Γ a A p2 ->
    (p3 : B' = (B β[a])) ->
    IsFreeVar n Γ (.app mf f a) B' (.app p1 p2 p3)
  | conv1 :
    IsFreeVar n Γ t A p1 ->
    (p2 : Γ ⊢ B : Term.const K) ->
    (p3 : A === B) ->
    IsFreeVar n Γ t B (.conv p1 p2 p3)
  | conv2 :
    (p1 : Γ ⊢ t : A) ->
    IsFreeVar n Γ B (.const K) p2 ->
    (p3 : A === B) ->
    IsFreeVar n Γ t B (.conv p1 p2 p3)


  theorem test :
    Γ ⊢ t : A ->
    [^{n}S]s = t ->
    ∃ T, [^{n}S]T = A
  := by
  intro j h
  induction j generalizing s n
  case ax => exists □
  case var A Γ x _ ih _ _ =>
    have h2 := @dnth_as_nth Γ x
    rw [h2] at ih; subst ih
    cases s <;> simp at h
    case _ _ y =>
      generalize σdef : (^{n}S) y = σ at *
      cases σ <;> simp at h
      case _ z =>
        sorry
      case _ => sorry
      -- cases Nat.decLe n y
      -- case _ h3 =>
      --   cases Nat.decLt y n
      --   case _ h4 => omega
      --   case _ h4 =>
      --     have h5 := Term.rep_n_S_gt h4
      --     rw [h5] at h; simp at h
      --     cases h
      --     case _ _ h =>
      --       subst h
      --       exists [Sn y]Γ @ y
      --       simp
      --       sorry
      -- case _ h3 =>
      --   have h4 := Term.rep_n_S_le h3
      --   rw [h4] at h; simp at h
      --   exists [Sn (x + 1)]Γ @ x
      --   simp; have h5 : n < x := by omega
      --   -- TODO: highly confident this checks out
      --   -- but requires a technical lemma about ^{n}
      --   sorry
  case pi => exists ★
  case tpi => exists □
  case lam Γ A B K t j1 j2 ih1 ih2 =>
    sorry
  case app Γ f A B a B' j1 j2 j3 ih1 ih2 =>
    sorry
  case conv => sorry

  theorem conv_subst_lemma : A === B -> [σ]U = A -> ∃ V, [σ]V = B := by sorry

  -- n ∈ ([^{n}S]t)
  theorem fv_missing : (p : Γ ⊢ ([^{n}S]t) : ([^{n}S]T)) -> ¬ (IsFreeVar n Γ ([^{n}S]t) ([^{n}S]T) p) := by
  intro j h
  generalize sdef : [^{n}S]t = s at j
  generalize Udef : [^{n}S]T = U at j
  induction h generalizing t T
  case var1 => sorry
  case var2 => sorry
  case pi1 n Γ' A' K p1 B h p2 ih =>
    cases t <;> simp at sdef
    case _ K' x =>
      have lem := @Term.rep_n_S_exists n x
      cases lem; case _ z h => rw [h] at sdef; simp at sdef
    case _ m r1 r2 => sorry
  case pi2 => sorry
  case tpi1 => sorry
  case tpi2 => sorry
  case lam1 => sorry
  case lam2 => sorry
  case app1 n Γ' f A' B p1 a B' h p2 p3 ih =>
    cases t <;> simp at sdef
    case _ K' x =>
      have lem := @Term.rep_n_S_exists n x
      cases lem; case _ z h => rw [h] at sdef; simp at sdef
    case _ m r1 r2 =>
      sorry
  case app2 Γ' f A' B n a p2 B' p1 fv p3 ih =>
    cases t <;> simp at sdef
    case _ => sorry
    case _ m r1 r2 =>
      sorry
  case conv1 n Γ' t' A p1 B K a p2 p3 ih =>
    sorry
  case conv2 Γ' t' A' n B K p2 p1 fv p3 ih =>
    sorry




end Fomega
