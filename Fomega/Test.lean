
@[simp]
def natLt (n m : Nat) : Decidable (n < m) := Nat.decLt n m

inductive Const : Type where
| type : Const
| kind : Const

namespace Const
  -- inductive Mem : Const -> Const -> Prop where
  -- | type : Mem .none .type
  -- | kind1 : Mem .none .kind
  -- | kind2 : Mem .type .kind

  -- @[simp]
  -- def size : Const -> Nat
  -- | .none => 0
  -- | .type => 1
  -- | .kind => 2

  @[simp]
  def to_nat : Const -> Nat
  | .type => 1
  | .kind => 2

  -- @[simp]
  -- instance : SizeOf Const where
  --   sizeOf := size

  -- theorem mem_trans : Mem x y -> Mem y z -> Mem x z := by
  -- intro h1 h2
  -- induction h2
  -- case _ => cases h1
  -- case _ => cases h1
  -- case _ => cases h1; constructor

  -- theorem mem_trichotomy : Mem u v ∨ Mem v u ∨ u = v := by sorry

  -- instance mem_decide : ∀ u v, Decidable (Const.Mem u v) := by sorry

  -- theorem mem_preserves_size : Mem K1 K2 -> size K1 < size K2 := by sorry
end Const

inductive Term : Type where
| bound : Nat -> Term
| const : Const -> Term
| bomb : Term
| explode : Term -> Term
| lam : Term -> Term -> Term
| app : Term -> Term -> Term
| all : Term -> Term -> Term

notation "★" => Term.const Const.type
notation "□" => Term.const Const.kind

abbrev Subst := Nat -> Term

namespace Subst
  def lift : Subst -> Subst
  | _, 0 => .bound 0
  | σ, n + 1 => sorry

  @[simp]
  def apply : Subst -> Term -> Term
  | σ, .bound k => σ k
  | _, .bomb => .bomb
  | σ, .explode t => .explode (apply σ t)
  | _, .const k => .const k
  | σ, .lam t1 t2 => .lam (apply σ t1) (apply (lift σ) t2)
  | σ, .app t1 t2 => .app (apply σ t1) (apply σ t2)
  | σ, .all t1 t2 => .all (apply σ t1) (apply (lift σ) t2)

  @[simp]
  def cons : Term -> Subst -> Subst
  | t, _, 0 => t
  | _, σ, n + 1 => σ n

  def compose : Subst -> Subst -> Subst
  | σ, τ, n => apply τ (σ n)
end Subst

@[simp] def I : Subst := λ n => .bound n
@[simp] def S : Subst := λ n => .bound (n + 1)

@[simp]
def beta : Term -> Subst
| t => .cons t I

infix:70 "::" => Subst.cons
prefix:max "^" => Subst.lift
notation:90 "[" σ "]" t:89 => Subst.apply σ t
notation:90 τ:90 " ⊙ " σ:91 => Subst.compose σ τ
notation:90 s:90 "β[" t "]" => Subst.apply (beta t) s

@[simp]
theorem subst_apply_I_is_id {s : Term} : [I]s = s := by sorry
@[simp]
theorem subst_apply_compose_commute {s : Term} {σ τ} : [τ][σ]s = [τ ⊙ σ]s := by sorry
@[simp]
theorem subst_valid2 : [s :: σ].bound 0 = s := by sorry
@[simp] -- ⇑σ = 0.(σ ◦ S)
theorem subst_valid3 {σ : Subst} : ^σ = .bound 0 :: (S ⊙ σ) := sorry
@[simp] -- 0.S = I
theorem subst_valid4 : .bound 0 :: S = I := sorry
@[simp] -- σ ◦ I = σ
theorem subst_valid5 {σ : Subst} : σ ⊙ I = σ := by sorry
@[simp] -- I ◦ σ = σ
theorem subst_valid6 {σ : Subst} : I ⊙ σ = σ := sorry
@[simp] -- (σ ◦ τ) ◦ μ = σ ◦ (τ ◦ μ)
theorem subst_valid7 {σ : Subst} : σ ⊙ (τ ⊙ μ) = σ ⊙ τ ⊙ μ := by sorry
@[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
theorem subst_valid8_replace {s : Term} : τ ⊙ (s :: σ) = ([τ]s) :: (τ ⊙ σ) := by sorry
@[simp] -- S ◦ (s.σ ) = σ
theorem subst_valid9 : (s :: σ) ⊙ S = σ := by sorry
@[simp] -- 0[σ ].(S ◦ σ ) = σ
theorem subst_valid10 : σ 0 :: (σ ⊙ S) = σ := by sorry

inductive ParRed : Term -> Term -> Prop where
inductive ParRedStar : Term -> Term -> Prop where
def ParRedConv : Term -> Term -> Prop := sorry

infix:40 " =β> " => ParRed
infix:39 " =β>* " => ParRedStar
infix:38 " ≡β≡ " => ParRedConv

namespace ParRed
  theorem beta : .app (.lam A b) t =β>* b β[t] := by sorry
  theorem refl : t =β>* t := by sorry
  theorem subst : A ≡β≡ B -> [σ]A ≡β≡ [σ]B := by sorry
end ParRed

abbrev Ctx := List Term

@[simp]
def dnth : Ctx -> Nat -> Term
| [], _ => ★
| .cons h _, 0 => [S]h
| .cons _ t, n + 1 => [S](dnth t n)

infix:1000 "d@" => dnth

inductive JudgmentVariant : Type where
| prf | wf

abbrev JudgmentIndex : JudgmentVariant -> Type
| .prf => Term × Term
| .wf => Unit

inductive Judgment : (v : JudgmentVariant) -> Ctx -> JudgmentIndex v -> Prop
| nil : Judgment .wf [] ()
| cons :
  Judgment .wf Γ () ->
  Judgment .prf Γ (A, (.const K)) ->
  Judgment .wf (A::Γ) ()
| ax :
  Judgment .wf Γ () ->
  Judgment .prf Γ (★, □)
| var :
  Judgment .wf Γ () ->
  x < List.length Γ ->
  Judgment .prf Γ (.bound x, Γ d@ x)
| pi :
  Judgment .prf Γ (A, .const K1) ->
  Judgment .prf (A::Γ) (B, .const K2) ->
  Judgment .prf Γ (.all A B, .const K2)
| bomb : Judgment .prf Γ (.bomb, ★)
| explode :
  Judgment .prf Γ (t, .bomb) ->
  Judgment .prf Γ (A, ★) ->
  Judgment .prf Γ (.explode t, A)
| lam :
  Judgment .prf Γ (.all A B, .const K) ->
  Judgment .prf (A::Γ) (t, B) ->
  Judgment .prf Γ (.lam A t, .all A B)
| app :
  Judgment .prf Γ (f, .all A B) ->
  Judgment .prf Γ (a, A) ->
  B' = (B β[a]) ->
  Judgment .prf Γ (.app f a, B')
| iconv :
  Judgment .prf Γ (t, A) ->
  Judgment .prf Γ (B, .const K) ->
  A ≡β≡ B ->
  Judgment .prf Γ (t, B)

notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Judgment JudgmentVariant.prf Γ (t, A)
notation:170 "⊢ " Γ:170 => Judgment JudgmentVariant.wf Γ ()

inductive LogRel : Nat -> (Nat -> Term -> Prop) -> Term -> (Term -> Prop) -> Prop
| univ :
  K.to_nat < u ->
  ξ = ι K.to_nat ->
  LogRel u ι (.const K) ξ
| none : LogRel u ι .bomb (λ _ => False)
| pi :
  LogRel u ι A ξ ->
  (F : Term -> (Term -> Prop) -> Prop) ->
  (∀ a, ξ a -> ∃ ζ, F a ζ) ->
  (∀ a ζ, ξ a -> F a ζ -> LogRel v ι (B β[a]) ζ) ->
  LogRel v ι (.all A B) (λ b => ∀ a ζ, ξ a -> F a ζ -> ζ (.app b a))
| par :
  A =β>* B ->
  LogRel u ι B ξ ->
  LogRel u ι A ξ

def LogRelI : Nat -> Term -> (Term -> Prop) -> Prop
| u => LogRel u (λ v A => match natLt v u with
  | .isTrue _ => ∃ ξ, LogRelI v A ξ
  | .isFalse _ => False)
decreasing_by
case _ x h => apply h

notation:170 "〚" A ";" ι "〛" u:170 " ↘ " ξ:170 => LogRel u ι A ξ
notation:170 "〚" A "〛" u:170 " ↘ " ξ:170 => LogRelI u A ξ

abbrev BetaExpansionClosed (ξ : Term -> Prop) := ∀ a b, ξ a -> b =β>* a -> ξ b

namespace LogRel

  -- theorem redundant1 : 〚A; ι〛u ↘ ξ ->
  --   〚A; (λ v A => match Const.mem_decide v u with
  --     | .isTrue _ => ι v A
  --     | .isFalse _ => False)〛u ↘ ξ
  -- := by sorry

  theorem redundant2 :
    〚A; (λ v A => match natLt v u with
      | .isTrue _ => ι v A
      | .isFalse _ => False)〛u ↘ ξ ->
    〚A; ι〛u ↘ ξ
  := by
  intro j
  generalize Tdef : (fun v A =>
    match natLt v u with
    | isTrue h => ι v A
    | isFalse h => False) = T at *
  induction j
  case univ u ι' K h => sorry
  --   rw [<-Tdef]; simp
  --   split
  --   case _ h1 h2 _h3 =>
  --     have lem : (fun A => ι v A) = ι v := by funext; simp
  --     rw [lem]; constructor; apply h2
  --   case _ h1 h2 _h3 => exfalso; apply h2 h
  case none => constructor
  case pi _j1 F j2 _j3 ih1 ih2 =>
    sorry
  case par j1 _j2 ih =>
    constructor; apply j1; apply ih Tdef

  theorem simplify_logreli : 〚A〛u ↘ ξ -> 〚A; (λ v t => ∃ ζ,〚t〛v ↘ ζ)〛u ↘ ξ := by
  intro j
  unfold LogRelI at j; simp at j
  apply @redundant2 u (λ v t => ∃ ζ,〚t〛v ↘ ζ) A ξ j

  theorem pi_alt :
    〚A; ι〛u ↘ ξ ->
    (∀ (a : Term), ξ a → ∃ ζ, 〚B β[a]; ι〛v ↘ ζ) ->
    〚.all A B; ι〛v ↘ (λ b => ∀ a ζ, ξ a -> 〚B β[a]; ι〛v ↘ ζ -> ζ (.app b a))
  := by
  intro h1 h2
  let F : Term -> (Term -> Prop) -> Prop := λ a ζ => 〚B β[a]; ι〛v ↘ ζ
  have lem := @LogRel.pi _ _ _ _ v B h1 F
  unfold F at lem; simp at lem; apply lem
  intro a ha; simp at h2; apply h2 a ha

  theorem inversion_univ : 〚.const K; ι〛u ↘ ξ -> K.to_nat < u ∧ ξ = ι K.to_nat
  := by
  intro h
  generalize Tdef : Term.const K = T at h
  induction h
  case univ v' u ι h1 h2 =>
    injection Tdef with e; subst e
    apply And.intro; apply h1; apply h2
  case none => injection Tdef
  case pi => injection Tdef
  case par A B u ι ξ r h ih =>
    rw [<-Tdef] at r
    have lem : B = Term.const K := by sorry
    subst lem; apply ih rfl

  theorem inversion_bomb : 〚.bomb; ι〛u ↘ ξ -> ξ = λ t => False := by sorry

  theorem inversion_pi : 〚.all A B; ι〛u ↘ ξ ->
    ∃ (ζ : Term -> Prop), ∃ (R : Term -> (Term -> Prop) -> Prop),
    〚A; ι〛u ↘ ζ
    ∧ (∀ a, ∃ ξ, R a ξ)
    ∧ (∀ a ξ, R a ξ -> 〚B β[a]; ι〛u ↘ ξ)
    ∧ ζ = (λ b => ∀ a ξ, R a ξ -> ξ (.app b a))
  := by
  intro h
  generalize Tdef : Term.all A B = T at h
  induction h generalizing A B
  case univ => sorry
  case none => sorry
  case pi => sorry
  case par A' B' ξ r j ih =>
    rw [<-Tdef] at r
    sorry

  theorem preservation : 〚A; ι〛u ↘ ξ -> A =β>* B -> 〚B; ι〛u ↘ ξ := by
  intro lr r
  induction lr
  case univ K => sorry
  case none => sorry
  case pi => sorry
  case par => sorry

  theorem irrelevance : 〚A; ι〛u ↘ ξ -> A ≡β≡ B -> 〚B; ι〛u ↘ ξ := by sorry

  theorem functional : 〚A; ι〛u ↘ ξ -> 〚A; ι〛u ↘ ζ -> ξ = ζ := by
  intro j1 j2
  induction j1
  case univ => sorry
  case none => sorry
  case pi => sorry
  case par => sorry

  theorem inversion_pi_alt : 〚.all A B; ι〛u ↘ ξ ->
    ∃ (ζ : Term -> Prop),
    〚A; ι〛u ↘ ζ
    ∧ (∀ a, ζ a -> ∃ ψ, 〚B β[a]; ι〛u ↘ ψ)
    ∧ ξ = λ b => ∀ a, ζ a -> ∀ ψ, 〚B β[a]; ι〛u ↘ ψ -> ψ (.app b a)
  := by sorry

  theorem cumulative : u < v -> 〚A; ι〛u ↘ ξ -> 〚A; ι〛v ↘ ξ := by
  intro h j
  induction j
  case univ v' u' ι h1 h2 =>
    constructor; apply Nat.lt_trans; apply h1; apply h; apply h2
  case none => constructor
  case pi h1 _h2 ih1 ih2 =>
    constructor; apply ih1 h
    apply h1; intro a ζ q1 q2
    apply ih2 a ζ q1 q2 h
  case par r _j ih =>
    constructor; apply r; apply ih h

  theorem functional_univ : 〚A; ι〛u ↘ ξ -> 〚A; ι〛v ↘ ζ -> ξ = ζ := by
  intro j1 j2
  have lem := Nat.lt_trichotomy u v
  cases lem
  case _ h =>
    replace j1 := cumulative h j1
    apply functional j1 j2
  case _ h =>
    cases h
    case _ h => subst h; apply functional j1 j2
    case _ h =>
      replace j2 := cumulative h j2
      apply functional j1 j2

  theorem functional_univ_interp : 〚A〛u ↘ ξ -> 〚A〛v ↘ ζ -> ξ = ζ := by
  intro j1 j2
  replace j1 := simplify_logreli j1
  replace j2 := simplify_logreli j2
  apply functional_univ j1 j2

  theorem beta_expansion_closed : 〚A; ι〛u ↘ ξ -> BetaExpansionClosed ξ := by
  intro j; unfold BetaExpansionClosed
  intro a b h r
  induction j generalizing a b
  case univ => sorry
  case none => sorry
  case pi => sorry
  case par => sorry

end LogRel

def SemaSubst σ Γ := ∀ i u ξ, i < List.length Γ -> 〚[σ](Γ d@ i)〛u ↘ ξ -> ξ (σ i)
notation:170 σ:170 " ⊨ " Γ:170 => SemaSubst σ Γ

theorem sema_subst_empty : σ ⊨ [] := by
intro i u ξ h; simp at h

theorem sema_subst_cons : 〚[σ]A〛u ↘ ξ -> ξ a -> σ ⊨ Γ -> (a::σ) ⊨ (A::Γ) := by
intro h1 h2 h3
intro x u' ζ h4 h5
cases x
case _ =>
  simp at *
  have lem := LogRel.functional_univ_interp h1 h5; subst lem
  apply h2
case _ x =>
  simp at *; apply h3 x u' ζ h4 h5

def SemaProof Γ t A := ∀ σ, σ ⊨ Γ -> ∃ u, ∃ ξ, 〚[σ]A〛u ↘ ξ ∧ ξ ([σ]t)
notation:170 Γ:170 " ⊨ " t:170 " : " A:170 => SemaProof Γ t A

def SemaWf Γ := ∀ x, x < List.length Γ -> ∃ K, Γ ⊨ Γ d@ x : .const K
notation:170 "⊨ " Γ:170 => SemaWf Γ

theorem sema_wf_empty : ⊨ [] := by
intro x h; simp at h

theorem sema_wf_cons : ⊨ Γ -> Γ ⊨ A : .const K -> ⊨ (A::Γ) := by
intro h1 h2 x h3
cases x
case _ =>
  simp; exists K; intro σ h; simp
  have lem : (σ ⊙ S) ⊨ Γ := by
    intro i u ξ q1 q2
    have lem := h (i + 1) u ξ (by simp; exact q1); simp at lem
    unfold Subst.compose; simp; apply lem q2
  replace h2 := h2 (σ ⊙ S) lem; simp at h2
  apply h2
case _ x =>
  simp; replace h3 : x < Γ.length := by simp at h3; exact h3
  replace h1 := h1 x h3
  cases h1; case _ K h1 =>
    exists K; intro σ h; simp
    have lem : (σ ⊙ S) ⊨ Γ := by
      intro i u ξ q1 q2
      have lem := h (i + 1) u ξ (by simp; exact q1); simp at lem
      unfold Subst.compose; simp; apply lem q2
    replace h1 := h1 (σ ⊙ S) lem; simp at h1
    apply h1

theorem classifier_inversion : (Γ ⊨ A : .const K) <-> (∀ σ, σ ⊨ Γ -> ∃ ξ, 〚[σ]A〛K.to_nat ↘ ξ) := by
constructor
case _ =>
  intro h1 σ h2
  have lem := h1 σ h2; simp at lem
  cases lem; case _ v lem =>
  cases lem; case _ ξ lem =>
    have lem2 := LogRel.simplify_logreli lem.1
    have lem3 := LogRel.inversion_univ lem2
    have lem4 := lem.2; rw [lem3.2] at lem4
    exact lem4
case _ =>
  intro h1 σ h2
  have lem := h1 σ h2
  cases lem; case _ ξ lem =>
    simp; exists (K.to_nat + 1)
    exists (λ t => ∃ ζ, 〚t〛K.to_nat ↘ ζ)
    apply And.intro
    case _ =>
      simp; unfold LogRelI; simp
      apply LogRel.univ; simp
      funext; case _ t =>
        cases K <;> simp <;> split <;> simp
        case _ h _ => exfalso; apply h; simp
        case _ h _ => exfalso; apply h; simp
    case _ => simp; exists ξ

@[simp]
abbrev SoundnessType (Γ:Ctx) : (v : JudgmentVariant) -> JudgmentIndex v -> Prop
| .prf, (t, A) => Γ ⊨ t : A
| .wf, () => ⊨ Γ

theorem soundness : Judgment v Γ ix -> SoundnessType Γ v ix := by
intro j
induction j <;> simp at *
case nil => apply sema_wf_empty
case cons ih1 ih2 => apply sema_wf_cons ih1 ih2
case ax Γ j _ih => sorry
  -- intro σ _
  -- exists (λ t => ∃ Γ t', t =β>* t' ∧ Γ ⊢ t' : .const .kind)
  -- apply And.intro; constructor
  -- simp; exists Γ; exists ★
  -- apply And.intro; apply ParRed.refl
  -- constructor; apply j
case var Γ x j1 j2 ih =>
  intro σ h; simp
  replace ih := ih x j2
  cases ih
  case _ K ih =>
    have lem := classifier_inversion.1 ih σ h
    cases lem
    case _ ξ lem =>
      exists K.to_nat; exists ξ; apply And.intro; apply lem
      apply h _ _ _ j2 lem
case pi Γ A K1 B K2 j1 j2 ih1 ih2 =>
  apply classifier_inversion.2; intro σ h
  have lem1 := classifier_inversion.1 ih1 σ h
  cases lem1; case _ ξ lem1 =>
    have lem2 : ∀ a, ξ a -> ∃ ζ, 〚([^σ]B) β[a]〛K2.to_nat ↘ ζ := by
      intro a ah; simp
      have lem2 := sema_subst_cons lem1 ah h
      have lem3 := classifier_inversion.1 ih2 (a::σ) lem2
      exact lem3
    have lem3 := LogRel.pi_alt lem1 lem2
    simp; simp at lem3; apply Exists.intro; apply lem3
case bomb Γ => sorry
  -- intro σ _
  -- exists (λ t => ∃ Γ t', t =β>* t' ∧ Γ ⊢ t' : .const .type)
  -- apply And.intro; constructor
  -- simp; exists Γ; exists .bomb
  -- apply And.intro; apply ParRed.refl
  -- constructor
case explode Γ t A j1 j2 ih1 _ih2 => sorry
  -- intro σ h
  -- replace ih1 := ih1 σ h
  -- cases ih1; case _ w ih1 =>
  --   have lem := LogRel.inversion_bomb ih1.1
  --   subst lem; simp at ih1
case lam Γ A B K t j1 j2 ih1 ih2 => sorry
  -- intro σ h
  -- have lem2 := classifier_inversion.1 ih1 σ h
  -- cases lem2
  -- case _ ξ lem2 =>
  --   have lem3 := LogRel.inversion_pi_alt lem2
  --   cases lem3
  --   case _ ζ lem3 =>
  --     exists ξ; apply And.intro; apply lem2
  --     rw [lem3.2.2]; simp
  --     intro a ha ψ ih3
  --     have r : (([σ]A).lam ([Term.bound 0::S ⊙ σ]t)).app a
  --       =β>* ([Term.bound 0::S ⊙ σ]t) β[a]
  --     := by
  --       apply ParRed.beta
  --     have lem4 := LogRel.beta_expansion_closed ih3
  --     unfold BetaExpansionClosed at lem4
  --     apply lem4 _ _ _ r; simp
  --     replace ih2 := ih2 (a::σ) (sema_subst_cons lem3.1 ha h)
  --     cases ih2
  --     case _ ξ' ih2 =>
  --       have lem5 := LogRel.functional ih3 ih2.1
  --       subst lem5; apply ih2.2
case app Γ f A B a B' j1 j2 j3 ih1 ih2 => sorry
  -- intro σ h; rw [j3]; simp
  -- replace ih1 := ih1 σ h
  -- cases ih1; case _ ξ ih1 =>
  --   have lem := LogRel.inversion_pi_alt ih1.1
  --   cases lem; case _ ζ lem =>
  --     have lem2 := ih1.2; rw [lem.2.2] at lem2; simp at lem2
  --     replace ih2 := ih2 σ h
  --     cases ih2; case _ ξ' ih2 =>
  --       have lem3 := LogRel.functional lem.1 ih2.1; subst lem3
  --       have lem4 := lem.2.1 ([σ]a) ih2.2; simp at lem4
  --       cases lem4; case _ ψ lem4 =>
  --         have lem5 := lem2 ([σ]a) ih2.2 ψ lem4
  --         exists ψ
case iconv Γ t A B K j1 j2 j3 ih1 _ih2 => sorry
  -- intro σ h
  -- replace ih1 := ih1 σ h
  -- cases ih1
  -- case _ ξ ih1 =>
  --   exists ξ; apply And.intro
  --   apply LogRel.irrelevance ih1.1
  --   apply ParRed.subst; apply j3
  --   apply ih1.2

theorem consistency : ¬ ([] ⊢ t : .bomb) := by
intro j
have lem := soundness j I sema_subst_empty
cases lem; case _ u lem =>
cases lem; case _ ξ lem =>
  have lem2 := LogRel.simplify_logreli lem.1; simp at lem2
  have lem2 := LogRel.inversion_bomb lem2
  subst lem2; simp at lem
