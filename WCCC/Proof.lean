
import Common

namespace WCCC

  namespace Mode
    @[simp]
    def dom (m : Mode) (K : Const) : Term :=
      match m with
      | mf => .const .type
      | mt => .const K
      | m0 => .const K

    @[simp]
    def codom (m : Mode) : Term :=
      match m with
      | mf => .const .type
      | mt => .const .kind
      | m0 => .const .type

    @[simp]
    def mul : Mode -> Mode -> Mode
    | mt, m2 => m2
    | mf, m0 => m0
    | mf, _ => mf
    | m0, _ => m0

    @[simp]
    def mem : Mode -> Mode -> Bool
    | _, mt => true
    | m0, m0 => true
    | mf, m0 => true
    | mf, mf => true
    | _, _ => false
  end Mode

  @[simp]
  instance : Membership Mode Mode where
    mem m2 m1 := Mode.mem m1 m2 = true

  instance : Mul Mode where
    mul := Mode.mul

  instance : HMul Mode (List (Mode × A)) (List (Mode × A)) where
    hMul m Γ := List.map (λ (m2, a) => (Mode.mul m m2, a)) Γ

  notation "#" m => Term.bound (Term.mode_to_sort m) 0

  -- namespace Mode
  --   @[simp]
  --   def mem_simp : m1 ∈ m2 -> mem m1 m2 = true := by {
  --     intro h; unfold Membership.mem at h
  --     unfold instMembershipMode_wCCC at h; simp at h
  --     exact h
  --   }
  -- end Mode

  def infer_cvterm : Nat -> Term -> Term -> Option CvTerm
  | 0, _, _ => none
  | _, ★, ★ => some .ax
  | _, (.bound K1 x1), (.bound K2 x2) =>
    if K1 == K2 && x1 == x2 then some .var else none
  | n, (.all m1 A1 B1), (.all m2 A2 B2) => do
    let A ← infer_cvterm n A1 A2
    let B ← infer_cvterm n B1 B2
    if m1 == m2 then some (.pi A B) else none
  | n, (.lam mt A1 t1), (.lam mt A2 t2) => do
    let A ← infer_cvterm n A1 A2
    let t ← infer_cvterm n t1 t2
    some (.lam_mt A t)
  | n, (.lam mf _ t1), (.lam mf _ t2) => do
    let t ← infer_cvterm n t1 t2
    some (.lam_mf t)
  | n, (.lam m0 _ t1), t2 => do
    let t ← infer_cvterm n t1 t2
    some (.lam_m0 t)
  | n+1, (.lam m _ t1), t2 => do
    let t ← infer_cvterm n (t1 β[#m]) (.app m t2 (#m))
    some (.lam_eta t)
  | _, _, _ => none

  def check_cvterm : CvTerm -> Term -> Term -> Bool := sorry

  inductive Conv : CvTerm -> Term -> Term -> Prop
  | sym : Conv c t2 t1 -> Conv (.sym c) t1 t2
  | ax : Conv .ax ★ ★
  | var : Conv .var (.bound K x) (.bound K x)
  | pi : Conv c1 A1 A2 -> Conv c2 B1 B2 ->
    Conv (.pi c1 c2) (.all m A1 B1) (.all m A2 B2)
  | lam_mt : Conv c1 A1 A2 -> Conv c2 t1 t2 ->
    Conv (.lam_mt c1 c2) (.lam mt A1 t1) (.lam mt A2 t2)
  | lam_mf : Conv c t1 t2 ->
    Conv (.lam_mf c) (.lam mf A1 t1) (.lam mf A2 t2)
  | lam_eta : m ≠ m0 ->
    Conv c (t1 β[ #m ]) (.app m t2 (#m)) ->
    Conv (.lam_eta c) (.lam m A t1) t2
  | lam_m0 : Conv c t1 t2 -> Conv (.lam_m0 c) (.lam m0 A t1) t2
  | app : Conv c1 f1 f2 -> Conv c2 a1 a2 ->
    Conv (.app c1 c2) (.app m f1 f2) (.app m a1 a2)
  | app_beta :
    Conv c (b β[t]) t2 ->
    Conv (.app_beta c) (.app m (.lam m A b) t) t2
  | app_m0 : Conv c t1 t2 -> Conv (.app_m0 c) (.app m0 t1 a) t2
  | prod : Conv c1 A1 A2 -> Conv c2 B1 B2 ->
    Conv (.prod c1 c2) (.prod A1 B1) (.prod A2 B2)
  | pair : Conv c t1 t2 -> Conv (.pair c) (.pair T1 t1 s1) t2
  | fst : Conv c t1 t2 -> Conv (.fst c) (.fst t1) t2
  | snd : Conv c t1 t2 -> Conv (.snd c) (.snd t1) t2
  | eq : Conv c1 A1 A2 -> Conv c2 a1 a2 -> Conv c3 b1 b2 ->
    Conv (.eq c1 c2 c3) (.eq A1 a1 b1) (.eq A2 a2 b2)
  | refl : Conv c (.lam mf .none (.bound .type 0)) t2 ->
    Conv (.refl c) (.refl t1) t2
  | subst : Conv c e1 t2 -> Conv (.subst c) (.subst P1 e1) t2
  | conv : Conv c t1 t2 -> Conv (.conv c) (.conv A1 t1 c1) t2

  notation:100 c:101 " : " A:99 " === " B:98 => Conv c A B

  def infer' (Γ : List (Mode × Term)) (m : Mode) : Term -> Option Term := λ t =>
    let match_dom t m :=
      match t with
      | some (Term.const K) => if Term.const K == Mode.dom m K
        then some (Term.const K)
        else none
      | _ => none
    let match_codom t m :=
      match t with
      | some (Term.const K) => if Term.const K == Mode.codom m
        then some (Term.const K)
        else none
      | _ => none
    let match_type t :=
      match t with
      | some ★ => some ★
      | _ => none
    let match_const t :=
      match t with
      | some (Term.const K) => some (Term.const K)
      | _ => none
    match m, t with
    | mt, ★ => □
    | m, .bound _ x =>
      if Nat.blt x (List.length Γ) then
        let (m', A) := List.getD Γ x (mf, .none)
        if m == m' then A else none
      else none
    | mt, (.all m A B) => do
      let _ ← match_dom (infer' Γ mt A) m
      let K ← match_codom (infer' ((mt, A) :: Γ) mt B) m
      K
    | m1, (.lam m2 A t) => do
      let _ ← match_dom (infer' Γ mt A) m2
      let B ← infer' ((m2, A) :: Γ) m1 t
      let cB := Term.classify B
      match m1, cB with
      | mf, .type | m0, .type | mt, .kind => Term.all m A B
      | _, _ => none
    | m1, (.app m2 f a) => do
      let A' ← infer' Γ m2 a
      if let (.all m3 A B) ← infer' Γ m1 f then
        if m2 == m3 && A == A' then B β[a]
        else none
      else none
    | mt, (.prod A B) => do
      let _ ← match_type (infer' Γ mt A)
      let _ ← match_type (infer' ((mt, A) :: Γ) mt B)
      ★
    | m, (.pair B a b) => do
      let A ← infer' Γ m a
      let B2 ← infer' Γ m b
      if let (.all mt A2 ★) ← infer' ((mt, A) :: Γ) mt B then
        if A == A2 && B β[a] == B2 then Term.prod A B
        else none
      else none
    | m, (.fst t) => do
      if let (.prod A _) ← infer' Γ m t then
        if m != mt then A else none
      else none
    | m0, (.snd t) => do
      if let (.prod _ B) ← infer' Γ m0 t then B β[.fst t]
      else none
    | mt, (.eq A a b) => do
      let A1 ← infer' Γ m0 a
      let A2 ← infer' Γ m0 b
      let _ ← match_type (infer' Γ mt A)
      if A== A1 && A == A2 then ★ else none
    | m, (.refl t) => do
      let A ← infer' Γ m0 t
      if m != mt then Term.eq A t t else none
    | m, (.subst P e) => match infer' Γ m e with
      | Term.eq A a b => do
        if let (.all m A2 B2) ← infer' Γ mt P then
          if m != mt && A == A2 && B2 == ★ then
            (Term.all mf (.app mt P a) (.app mt P b))
          else none
        else none
      | _ => none
    | m, (.phi a b e) => match infer' Γ m0 e with
      | Term.eq A u v => match infer' Γ m0 b with
        | Term.prod A1 B => do
          let A2 ← infer' Γ m a
          if m != mt && A == A1 && A == A2 && a == u && v == .fst b then
            Term.prod A B
          else none
        | _ => none
      | _ => none
    | m, (.conv B t c) => do
      let A ← infer' Γ m t
      let _ ← match_const (infer' Γ mt B)
      if check_cvterm c A B then B else none
    | _, _ => none
  --termination_by t => Term.size t

  def wf : List (Mode × Term) -> Mode -> Term -> Bool
  | _, mt, ★ => true
  | Γ, _, .bound K x =>
    if Nat.blt x (List.length Γ) then
      let (_, A) := List.getD Γ x (mf, .none)
      match infer' (List.take x Γ) mt A with
      | some (.const K') => K == K'
      | _ => false
    else false
  | Γ, mt, (.all m A B) => wf Γ m A && wf ((mt, A) :: Γ) m B
  | _, _, _ => false

  def infer : List (Mode × Term) -> Mode -> Term -> Option Term
  | Γ, m, t => if wf Γ m t then infer' Γ m t else none

  inductive Proof : List (Mode × Term) -> Mode -> Term -> Term -> Prop
  | ax : Proof Γ mt ★ □
  | var :
    List.getD Γ x (mf, .none) = (m1, [r#(Term.Pn (x + 1))]A) ->
    Proof (List.drop (x + 1) Γ) mt ([r#(Term.Pn (x + 1))]A) (.const K) ->
    m1 ∈ m2 ->
    Proof Γ m2 (.bound K x) A
  | pi :
    Proof Γ mt A (Mode.dom m K) ->
    Proof ((mt, A)::Γ) mt B (Mode.codom m) ->
    Proof Γ mt (.all m A B) (Mode.codom m)
  | lam :
    Proof Γ mt A (Mode.dom m2 K) ->
    Proof ((m2, A)::Γ) m1 t B ->
    Proof ((mt, A)::Γ) mt B (Mode.codom m2) ->
    Proof Γ m1 (.lam m2 A t) (.all m2 A B)
  | app :
    Proof Γ m1 f (.all m2 A B) ->
    Proof Γ (m1*m2) a A ->
    Proof Γ m1 (.app m2 f a) (B β[a])
  | prod :
    Proof Γ mt A ★ ->
    Proof ((mt, A)::Γ) mt B ★ ->
    Proof Γ mt (.prod A B) ★
  | pair :
    Proof Γ mt B (.all mf A ★) ->
    Proof Γ m t A ->
    Proof Γ m0 s (B β[t]) ->
    Proof Γ m (.pair B t s) (.prod A B)
  | fst :
    Proof Γ m t (.prod A B) ->
    Proof Γ m (.fst t) A
  | snd :
    Proof Γ m0 t (.prod A B) ->
    Proof Γ m0 (.snd t) (B β[.fst t])
  | eq :
    Proof Γ mt A ★ ->
    Proof Γ mt a A ->
    Proof Γ mt b A ->
    Proof Γ mt (.eq A a b) ★
  | refl :
    Proof Γ m0 t A ->
    Proof Γ m (.refl t) (.eq A t t)
  | subst :
    Proof Γ m e (.eq A a b) ->
    Proof Γ mt P (.all mt A ★) ->
    Proof Γ m (.subst P e) (.all mf (.app mt P a) (.app mt P b))
  | conv :
    Proof Γ m t A ->
    Proof Γ mt B K ->
    c : A === B ->
    Proof Γ m (.conv B t c) B

  notation:170 Γ:170 " ⊢[" m:170 "] " t:170 " : " A:170 => Proof Γ m t A

end WCCC
