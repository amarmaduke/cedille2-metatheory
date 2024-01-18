
import Common.Mathlib
import Common.Util
import Common.Name
import Common.Notation

inductive Syntax {α β γ : Sort _} : Sort _ where
| bound : Nat -> Syntax
| free : Name -> Syntax
| const : γ -> Syntax
| bind : α -> Syntax -> Syntax -> Syntax
| ctor : β -> Syntax -> Syntax -> Syntax -> Syntax

namespace Syntax

  def opn {α β γ} (i : Nat) (v : Name) (t : @Syntax α β γ) : @Syntax α β γ :=
    match t with
    | bound j => if j == i then free v else bound j
    | free x => free x
    | const c => const c
    | bind k t1 t2 => bind k (opn i v t1) (opn (Nat.succ i) v t2)
    | ctor k t1 t2 t3 =>
      ctor k (opn i v t1) (opn i v t2) (opn i v t3)

  def cls {α β γ} (i : Nat) (v : Name) (t : @Syntax α β γ) : @Syntax α β γ :=
    match t with
    | bound j => bound j
    | free x => if x == v then bound i else free x
    | const c => const c
    | bind k t1 t2 => bind k (cls i v t1) (cls (Nat.succ i) v t2)
    | ctor k t1 t2 t3 =>
      ctor k (cls i v t1) (cls i v t2) (cls i v t3)

  instance : HasOpen (@Syntax α β γ) where
    opn := opn

  instance : HasClose (@Syntax α β γ) where
    cls := cls

  @[simp] lemma opn_const {α β γ : Sort _}  (i : Nat) (x : Name) (c : γ)
    : @HasOpen.opn (@Syntax α β γ) _ i v (const c) = const c
  := by congr

  @[simp] lemma opn_free {α β γ : Sort _} (i : Nat) (x : Name)
    : @HasOpen.opn (@Syntax α β γ) _ i v (free x) = free x
  := by congr

  @[simp] lemma opn_bound {α β γ : Sort _} (i : Nat) (x : Name)
    : @HasOpen.opn (@Syntax α β γ) _ i v (bound j)
      = if j == i then free v else bound j
  := by congr

  @[simp] lemma opn_bind {α β γ} (k : α) (i : Nat) (v : Name)
    (t1 : @Syntax α β γ) (t2 : @Syntax α β γ)
    : {i |-> v} bind k t1 t2 = bind k ({i |-> v} t1) ({(Nat.succ i) |-> v} t2)
  := by {
    generalize h : {_|-> v} @bind α β γ k t1 t2 = t
    unfold HasOpen.opn at h; unfold instHasOpenSyntax at h; simp at h
    unfold opn at h
    unfold HasOpen.opn; unfold instHasOpenSyntax; simp
    rw [<-h]
  }

  @[simp] lemma opn_ctor {α β γ} (k : β) (i : Nat) (v : Name)
    (t1 t2 t3 : @Syntax α β γ)
    : {i |-> v} ctor k t1 t2 t3
      = ctor k ({i |-> v} t1) ({i |-> v} t2) ({i |-> v} t3)
  := by {
    generalize h : {_|-> v}ctor k t1 t2 t3 = t
    unfold HasOpen.opn at h; unfold instHasOpenSyntax at h; simp at h
    unfold opn at h
    unfold HasOpen.opn; unfold instHasOpenSyntax; simp
    rw [<-h]
  }

  @[simp] lemma cls_const {α β γ : Sort _} (i : Nat) (x : Name) (c : γ)
    : @HasClose.cls (@Syntax α β γ) _ i v (const c) = const c
  := by congr

  @[simp] lemma cls_free {α β γ : Sort _} (i : Nat) (v x : Name)
    : @HasClose.cls (@Syntax α β γ) _ i v (free x)
      = if x == v then bound i else free x
  := by congr

  @[simp] lemma cls_bound {α β γ : Sort _} (i : Nat) (v : Name)
    : @HasClose.cls (@Syntax α β γ) _ i v (bound j) = bound j
  := by {
    unfold HasClose.cls; unfold instHasCloseSyntax; simp
    unfold cls; simp
  }

  @[simp] lemma cls_bind {α β γ} (k : α) (i : Nat) (v : Name)
    (t1 : @Syntax α β γ) (t2 : @Syntax α β γ)
    : {i <-| v} bind k t1 t2 = bind k ({i <-| v} t1) ({(Nat.succ i) <-| v} t2)
  := by congr

  @[simp] lemma cls_ctor {α β γ} (k : β) (i : Nat) (v : Name)
    (t1 t2 t3 : @Syntax α β γ)
    : {i <-| v} ctor k t1 t2 t3
      = ctor k ({i <-| v} t1) ({i <-| v} t2) ({i <-| v} t3)
  := by congr

  @[simp] theorem oc1 {α β γ} (i : Nat) (a b : Name) (x : @Syntax α β γ)
    : {i |-> a}{i |-> b}x = {i |-> b}x
  := by {
    induction x generalizing i <;> simp
    case bound j => split <;> simp [*]
    case bind k t1 t2 ih1 ih2 => rw [ih1 i, ih2 (i + 1)]; simp
    case ctor k t1 t2 t3 ih1 ih2 ih3 => rw [ih1 i, ih2 i, ih3 i]; simp
  }

  @[simp] theorem oc2 {α β γ} (i j : Nat) (a : Name) (x : @Syntax α β γ)
    : {i <-| a}{j <-| a}x = {j <-| a}x
  := by {
    induction x generalizing i j <;> simp
    case free b => split <;> simp [*]
    case bind k t1 t2 ih1 ih2 => rw [ih1 i j, ih2 (i + 1) (j + 1)]; simp
    case ctor k t1 t2 t3 ih1 ih2 ih3 => rw [ih1 _ _, ih2 _ _, ih3 _ _]; simp
  }

  @[simp] theorem oc3 {α β γ} (i : Nat) (a : Name) (x : @Syntax α β γ)
    : {i <-| a}{i |-> a}x = {i <-| a}x
  := by {
    induction x generalizing i <;> simp
    case bound j => split <;> simp [*]
    case bind k t1 t2 ih1 ih2 => rw [ih1 i, ih2 (i + 1)]; simp
    case ctor k t1 t2 t3 ih1 ih2 ih3 => rw [ih1 i, ih2 i, ih3 i]; simp
  }
  @[simp] theorem oc4 {α β γ} (i : Nat) (a : Name) (x : @Syntax α β γ)
    : {i |-> a}{i <-| a}x = {i |-> a}x
  := by {
    induction x generalizing i <;> simp
    case free b => {
      split <;> simp [*]
      case _ h => rw [eq_of_beq h]
    }
    case bind k t1 t2 ih1 ih2 => rw [ih1 i, ih2 (i + 1)]; simp
    case ctor k t1 t2 t3 ih1 ih2 ih3 => rw [ih1 i, ih2 i, ih3 i]; simp
  }

  theorem oc5 {α β γ} (i j : Nat) (a b : Name) (x : @Syntax α β γ) (h : i ≠ j)
    : {i |-> a}{j |-> b}x = {j |-> b}{i |-> a}x
  := by {
    induction x generalizing i j <;> simp
    case bound k => {
      split <;> simp
      case _ h2 => {
        split <;> simp [*]
        case _ h3 => subst h2; subst h3; exfalso; apply h rfl
      }
      case _ h2 => split <;> simp [*]
    }
    case bind k t1 t2 ih1 ih2 => {
      have h2 : (i + 1) ≠ (j + 1) := by {
        intro h2; injection h2 with h2; simp at h2
        apply h h2
      }
      rw [ih1 i j h, ih2 (i + 1) (j + 1) h2]; simp
    }
    case ctor k t1 t2 t3 ih1 ih2 ih3 =>
      rw [ih1 _ _ h, ih2 _ _ h, ih3 _ _ h]; simp
  }

  theorem oc6 {α β γ} (i j : Nat) (a b : Name) (x : @Syntax α β γ) (h : a ≠ b)
    : {i <-| a}{j <-| b}x = {j <-| b}{i <-| a}x
  := by {
    induction x generalizing i j <;> simp
    case free c => {
      split <;> simp [*]
      case _ h2 => {
        split <;> simp [*]
        case _ h3 => {
          have lem1 := eq_of_beq h2
          have lem2 := eq_of_beq h3
          subst lem1; subst lem2
          exfalso; apply h rfl
        }
      }
      case _ h2 => split <;> simp [*]
    }
    case bind k t1 t2 ih1 ih2 => rw [ih1 i j, ih2 (i + 1) (j + 1)]; simp
    case ctor k t1 t2 t3 ih1 ih2 ih3 => rw [ih1 _ _, ih2 _ _, ih3 _ _]; simp
  }

  theorem oc7 {α β γ} (i j : Nat) (a b : Name) (x : @Syntax α β γ)
    : i ≠ j -> a ≠ b -> {i |-> a}{j <-| b}x = {j <-| b}{i |-> a}x
  := by {
    intro h1 h2
    induction x generalizing i j <;> simp
    case bound k => split <;> simp [*]
    case free c => {
      split <;> simp [*]
      intro h3; subst h3; exfalso
      apply h1 rfl
    }
    case bind k t1 t2 ih1 ih2 => {
      have h2 : (i + 1) ≠ (j + 1) := by {
        intro h2; injection h2 with h2; simp at h2
        apply h1 h2
      }
      rw [ih1 i j h1, ih2 (i + 1) (j + 1) h2]; simp
    }
    case ctor k t1 t2 t3 ih1 ih2 ih3 =>
      rw [ih1 _ _ h1, ih2 _ _ h1, ih3 _ _ h1]; simp
  }

  theorem oc8 {α β γ} (i j : Nat) (a b : Name) (x : @Syntax α β γ)
    : {i |-> b}{i <-| a}{j |-> b}x = {j |-> b}{j <-| a}{i |-> a}x
  := by {
    induction x generalizing i j <;> simp
    case bound k => {
      split <;> simp [*]
      case _ h1 => {
        split <;> simp [*]
        case _ h2 => split <;> simp [*]
        case _ h2 => split <;> simp [*]
      }
      case _ h2 => split <;> simp [*]
    }
    case free c => split <;> simp [*]
    case bind k t1 t2 ih1 ih2 => rw [ih1 i j, ih2 (i + 1) (j + 1)]; simp
    case ctor k t1 t2 t3 ih1 ih2 ih3 => rw [ih1 _ _, ih2 _ _, ih3 _ _]; simp
  }

  theorem oc9 {α β γ} (i j : Nat) (a b : Name) (x : @Syntax α β γ)
    : {j <-| a}{i |-> a}{j <-| b}x = {j <-| b}{i |-> b}{i <-| a}x
  := by {
    induction x generalizing i j <;> simp
    case bound k => split <;> simp [*]
    case free c => {
      split <;> simp [*]
      case _ h1 => {
        split <;> simp [*]
        case _ h2 => split <;> simp [*]
        case _ h2 => split <;> simp [*]
      }
      case _ h1 => split <;> simp [*]
    }
    case bind k t1 t2 ih1 ih2 => rw [ih1 i j, ih2 (i + 1) (j + 1)]; simp
    case ctor k t1 t2 t3 ih1 ih2 ih3 => rw [ih1 _ _, ih2 _ _, ih3 _ _]; simp
  }

  def fv {α β γ} (x : @Syntax α β γ) : FvSet! :=
    match x with
    | bound _ => List.nil
    | free x => [x]
    | const _ => List.nil
    | bind _ t1 t2 => (fv t1) ++ (fv t2)
    | ctor _ t1 t2 t3 => (fv t1) ++ (fv t2) ++ (fv t3)

  def fresh {α β γ} (a : Name) (x : @Syntax α β γ) : Prop := {0 <-| a}x = x

  lemma unfree {α β γ} {x : @Syntax α β γ}
    : {i <-| a}x = x -> {j <-| a}x = x
  := by intro h; rw [<-h]; simp

  theorem close_open_cancel {α β γ} (x : @Syntax α β γ)
    : fresh a x -> {i <-| a}{i |-> a}x = x
  := by intro h; simp; apply unfree h

  @[simp] theorem close_vanish : fresh a x -> {i <-| a}x = x := by {
    intro h; rw [unfree h]
  }

  def fresh_iff_nfv : fresh a x <-> a ∉ fv x := by {
    induction x generalizing a
    case bound => unfold fresh at *; unfold fv; simp
    case free b => {
      unfold fresh at *; unfold fv; simp
      apply Iff.intro
      intro h1 h2; subst h2; apply h1 (by simp)
      intro h1 h2; subst h2; apply h1 (by simp)
    }
    case const => unfold fresh at *; unfold fv; simp
    case bind k t1 t2 ih1 ih2 => {
      unfold fresh at *; unfold fv; simp
      apply Iff.intro
      {
        intro h; cases h; case _ h1 h2 =>
        intro h; cases h
        case _ h => apply ih1.1 h1 h
        case _ h => apply ih2.1 (unfree h2) h
      }
      {
        intro h; replace h := demorgan h
        cases h; case _ h1 h2 =>
        have ih2' : {1 <-| a}t2 = t2 := unfree (ih2.2 h2)
        rw [ih1.2 h1, ih2']; simp
      }
    }
    case ctor k t1 t2 t3 ih1 ih2 ih3 => {
      unfold fresh at *; unfold fv; simp
      apply Iff.intro
      {
        intro h; casesm* _ ∧ _; case _ h1 h2 h3 =>
        intro h; cases h
        case _ h => apply ih1.1 h1 h
        case _ h => {
          cases h
          case _ h => apply ih2.1 h2 h
          case _ h => apply ih3.1 h3 h
        }
      }
      {
        intro h; replace h := demorgan3 h
        casesm* _ ∧ _; case _ h1 h2 h3 =>
        rw [ih1.2 h1, ih2.2 h2, ih3.2 h3]; simp
      }
    }
  }

  @[simp] theorem close_vanish_fv : a ∉ fv x -> {i <-| a}x = x := by {
    intro h; have lem := fresh_iff_nfv.2 h; simp [*]
  }

  def closed {α β γ} (i : Nat) (x : @Syntax α β γ) :=
    match x with
    | bound j => !j == i
    | free _ => true
    | const _ => true
    | bind _ t1 t2 => closed i t1 && closed (Nat.succ i) t2
    | ctor _ t1 t2 t3 => closed i t1 && closed i t2 && closed i t3

  lemma unbounded {α β γ} {x : @Syntax α β γ}
    : {i |-> a}x = x -> {i |-> b}x = x
  := by intro h; rw [<-h]; simp

  def lc {α β γ} (i : Nat) (x : @Syntax α β γ) : Prop
  := ∀ j ≥ i, ∃ a, {j |-> a}x = x

  @[simp] theorem open_vanish : lc i x -> {i |-> a}x = x := by {
    intro h; unfold lc at h; have lem := h i (by simp)
    cases lem; case _ b lem =>
    rw [unbounded lem]
  }

  -- theorem lc_iff_closed : lc i x <-> closed i x := by {
  --   induction x generalizing i
  --   case bound j => sorry
  --   case free y => sorry
  --   case const k => sorry
  --   case bind k t1 t2 ih1 ih2 => {
  --     sorry
  --   }
  --   case ctor k t1 t2 t3 ih1 ih2 ih3 => sorry
  -- }

  theorem open_close_cancel {α β γ} (x : @Syntax α β γ)
    : lc i x -> {i |-> a}{i <-| a}x = x
  := by intro h; simp [*]

  theorem lc0 : lc 0 x -> ∀ i, lc i x := by {
    intro h i j _gt
    have lem := h j (by simp)
    exact lem
  }

  @[simp] theorem open_vanish_lc0 : lc 0 x -> {i |-> a}x = x := by {
    intro h; have lem := h i (by simp)
    cases lem; case _ b lem =>
    rw [unbounded lem]
  }

  def subst {α β γ} (v : Name) (w t : @Syntax α β γ) : @Syntax α β γ :=
    match t with
    | bound i => bound i
    | free x => if x == v then w else free x
    | const c => const c
    | bind k t1 t2 => bind k (subst v w t1) (subst v w t2)
    | ctor k t1 t2 t3 => ctor k
      (subst v w t1) (subst v w t2) (subst v w t3)

  instance {α β γ} : HasSubst (@Syntax α β γ) (@Syntax α β γ) where
    subst := subst

  @[simp] lemma subst_const {α β γ : Sort _} (c : γ) (x : Name) (v : @Syntax α β γ)
    : [x := v](@const α β γ c) = const c
  := by congr

  @[simp] lemma subst_free {α β γ : Sort _} (x : Name) (v : @Syntax α β γ)
    : [x := v](@free α β γ x) = v
  := by {
    unfold HasSubst.subst; unfold instHasSubstSyntax; simp
    unfold subst; simp
  }

  @[simp] lemma subst_bound {α β γ : Sort _} (x : Name) (j : Nat) (v : @Syntax α β γ)
    : [x := v](@bound α β γ j) = bound j
  := by congr

  @[simp] lemma subst_bind {α β γ} (k : α) (x : Name)
    (v : @Syntax α β γ) (t1 : @Syntax α β γ) (t2 : @Syntax α β γ)
    : [x := v] @bind α β γ k t1 t2 = @bind α β γ k ([x := v]t1) ([x := v]t2)
  := by {
    generalize rhsdef : bind k ([x := v]t1) ([x := v]t2) = u
    unfold HasSubst.subst; unfold instHasSubstSyntax; simp
    unfold HasSubst.subst at *; unfold instHasSubstSyntax at *; simp at *
    unfold subst; rw [rhsdef]
  }

  @[simp] lemma subst_ctor {α β γ} (k : β) (x : Name) (v : @Syntax α β γ)
    (t1 t2 t3 : @Syntax α β γ)
    : [x := v] @ctor α β γ k t1 t2 t3
      = @ctor α β γ k ([x := v]t1) ([x := v]t2) ([x := v]t3)
  := by {
    generalize rhsdef : ctor k ([x := v]t1) ([x := v]t2) ([x := v]t3) = u
    unfold HasSubst.subst; unfold instHasSubstSyntax; simp
    unfold HasSubst.subst at *; unfold instHasSubstSyntax at *; simp at *
    unfold subst; rw [rhsdef]
  }

  def size {α β γ} (t : @Syntax α β γ) : Nat :=
    match t with
    | bound _i => 0
    | free _x => 0
    | const _c => 0
    | bind _k t1 t2 => (size t1) + (size t2) + 1
    | ctor _k t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1

  @[simp] def size_bound : @size α β γ (bound i) = 0 := by congr
  @[simp] def size_free : @size α β γ (free x) = 0 := by congr
  @[simp] def size_const : @size α β γ (const c) = 0 := by congr
  @[simp] def size_bind : @size α β γ (bind k t1 t2) = (size t1) + (size t2) + 1 := by congr
  @[simp] def size_ctor : @size α β γ (ctor k t1 t2 t3)
    = (size t1) + (size t2) + (size t3) + 1
  := by congr

  @[simp] lemma size_opn_head : size ({i |-> x} t) = size t := by sorry

  @[simp↓ high] lemma rename_bound {α β γ} {i j : Nat}
    : {i |-> x}{i <-| y}(@bound α β γ j) = bound j
  := by sorry --{
  --   simp
  --   unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp at *
  --   unfold opn_head; simp at *
  --   intro h
  --   cases i; case _ iv il =>
  --   simp at h
  --   injection h with h
  --   rw [@Nat.mod_eq_of_lt 0 (n + 1) (by linarith)] at h
  --   linarith
  -- }

  lemma rename_free_neq {i : Nat}
    : z ≠ y -> {i |-> x}{i <-| y}(@free α β γ z) = free z
  := by sorry --{
  --   intro h; simp; split
  --   case _ h2 => {
  --     have h3 : z = y := LawfulBEq.eq_of_beq h2
  --     exfalso
  --     apply h h3
  --   }
  --   case _ h2 => {
  --     unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp at *
  --     unfold opn_head; simp at *
  --   }
  -- }

  lemma rename_free_eq {i : Nat} : {i |-> x}{i <-| y}(@free α β γ y) = free x := by {
    sorry
  }

  -- def hopn_swap {α β γ n}  (t : @Syntax α β γ (n + 2)) : @Syntax α β γ (n + 2) :=
  --   match t with
  --   | Syntax.bound i =>
  --     if i == n + 1 then Syntax.bound n
  --     else if i == n then Syntax.bound (n + 1)
  --     else Syntax.bound i
  --   | Syntax.free x => Syntax.free x
  --   | Syntax.const k => Syntax.const k
  --   | Syntax.bind k u1 u2 =>
  --     Syntax.bind k (hopn_swap u1) (hopn_swap u2)
  --   | Syntax.ctor k u1 u2 u3 =>
  --     Syntax.ctor k (hopn_swap u1) (hopn_swap u2) (hopn_swap u3)

  -- lemma hopn_swap_fact {α β γ n} (t : @Syntax α β γ (n + 2))
  --   : {_|-> x}{_|-> y}t = {_|-> y}{_|-> x}(hopn_swap t)
  -- := @Nat.rec
  --   (λ s => ∀ {n:Nat} {t:@Syntax α β γ (n + 2)},
  --     size t ≤ s ->
  --     {_|-> x}{_|-> y}t = {_|-> y}{_|-> x}(hopn_swap t))
  --   (by {
  --     intro s t sh
  --     cases t <;> simp at *
  --     case bound j => {
  --       unfold hopn_swap; simp
  --       unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp
  --       split
  --       case _ h => {
  --         rw [h]
  --         generalize step1def : opn_head y (bound (↑s + 1)) = step1
  --         unfold opn_head at step1def; simp at step1def
  --         have lem1 : @Phin.val (s + 2) ((Nat.cast s) + 1) = s + 1 := Phin_cast3
  --         split at step1def
  --         case _ => {
  --           rw [<-step1def]
  --           generalize step2def : opn_head x (bound ↑s) = step2
  --           unfold opn_head at step2def; simp at step2def
  --           have lem2 := (@Nat.mod_eq_iff_lt s (s + 1 + 1) (by linarith)).2 (by linarith)
  --           split at step2def
  --           case _ hx => rw [lem2] at hx; exfalso; linarith
  --           case _ => {
  --             rw [<-step2def]; unfold opn_head; simp
  --             split
  --             case _ => simp
  --             case _ => linarith
  --           }
  --         }
  --         case _ hx => exfalso; apply hx lem1
  --       }
  --       case _ h => {
  --         split
  --         case _ h2 => {
  --           subst h2
  --           generalize step1def : opn_head y (bound ↑s) = step1
  --           unfold opn_head at step1def; simp at step1def
  --           have lem1 := (@Nat.mod_eq_iff_lt s (s + 1 + 1) (by linarith)).2 (by linarith)
  --           split at step1def
  --           case _ hx => exfalso; rw [lem1] at hx; linarith
  --           case _ => {
  --             generalize step2def : opn_head x (bound (↑s + 1)) = step2
  --             unfold opn_head at step2def; simp at step2def
  --             split at step2def
  --             case _ => {
  --               rw [<-step2def, <-step1def]; unfold opn_head; simp
  --               linarith
  --             }
  --             case _ hx => exfalso; rw [Phin_cast3] at hx; apply hx; simp
  --           }
  --         }
  --         case _ h2 => {
  --           generalize step1def : opn_head y (bound j) = step1
  --           unfold opn_head at step1def; simp at step1def
  --           split at step1def
  --           case _ hx => exfalso; apply h; apply Phin_cast4 hx
  --           case _ => {
  --             generalize step2def : opn_head x (bound j) = step2
  --             unfold opn_head at step2def; simp at step2def
  --             split at step2def
  --             case _ hx => exfalso; apply h; apply Phin_cast4 hx
  --             case _ => {
  --               generalize step3def : opn_head x step1 = step3
  --               rw [<-step1def] at step3def; unfold opn_head at step3def; simp at step3def
  --               split at step3def
  --               case _ hx => exfalso; apply h2; apply Phin_cast5 hx
  --               case _ => {
  --                 rw [<-step2def]; unfold opn_head; simp
  --                 split
  --                 case _ hx => exfalso; apply h2; apply Phin_cast5 hx
  --                 case _ => rw [<-step3def]
  --               }
  --             }
  --           }
  --         }
  --       }
  --     }
  --     case free => unfold hopn_swap; simp
  --     case const => unfold hopn_swap; simp
  --   })
  --   (by {
  --     intro s ih n t sh
  --     cases t
  --     case bound => apply ih (by simp)
  --     case free => apply ih (by simp)
  --     case const => apply ih (by simp)
  --     case bind k u1 u2 => {
  --       simp at sh
  --       have sh1 : size u1 ≤ s := by linarith
  --       have sh2 : size u2 ≤ s := by linarith
  --       unfold hopn_swap; simp
  --       rw [ih sh1, ih sh2]; simp
  --     }
  --     case ctor k u1 u2 u3 => {
  --       simp at sh
  --       have sh1 : size u1 ≤ s := by linarith
  --       have sh2 : size u2 ≤ s := by linarith
  --       have sh3 : size u3 ≤ s := by linarith
  --       unfold hopn_swap; simp
  --       rw [ih sh1, ih sh2, ih sh3]; simp
  --     }
  --   })
  --   (size t)
  --   n
  --   t
  --   (by simp)


end Syntax
