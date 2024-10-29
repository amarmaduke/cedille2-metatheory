
import Common
import WCCC.Mode

namespace WCCC

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
    let t ← infer_cvterm n (t1 β[#m]) (.app m t2 #m)
    some (.lam_eta t)
  | n, (.app m0 t1 _), t2 => do
    let t ← infer_cvterm n t1 t2
    some (.app_m0 t)
  | n, (.app m1 f1 a1), (.app m2 f2 a2) => do
    let f ← infer_cvterm n f1 f2
    let a ← infer_cvterm n a1 a2
    if m1 == m2 then some (.app f a) else none
  | n+1, (.app m1 (.lam m2 _ b) t1), t2 => do
    let t ← infer_cvterm n (b β[t1]) t2
    if m1 == m2 then some (.app_beta t) else none

  | _, _, _ => none

  def check_cvterm : CvTerm -> Term -> Term -> Bool := sorry

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

end WCCC
