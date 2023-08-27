
import Common.Mathlib
import Common.Util
import Common.Name
import Common.Notation

inductive Syntax {α β γ : Sort _} : Nat -> Sort _ where
| bound {n} : Fin n -> Syntax n
| free {n} : Name -> Syntax n
| const {n} : γ -> Syntax n
| bind {n} : α -> Syntax n -> Syntax (n + 1) -> Syntax n
| ctor {n} : β -> Syntax n -> Syntax n -> Syntax n -> Syntax n

namespace Syntax
  namespace Lemma
    def opn_head {n m : Nat} : ¬ n = m -> n ≤ m -> n < m := by
      intros h1 h2
      induction h2 with
      | refl => contradiction
      | @step k h _ih => {
        rewrite [<- Nat.lt_eq]
        unfold Nat.lt
        exact (Nat.succ_le_succ h)
      }
  end Lemma

  def weaken {α β γ n} (t : @Syntax α β γ n) (m : Nat) : @Syntax α β γ (n + m) :=
    match t with
    | bound i =>
      have := i.isLt
      bound (Fin.mk i.val (by linarith))
    | free x => free x
    | const c => const c
    | bind k a t => 
      have : n + m + 1 = n + 1 + m := by linarith
      bind k (weaken a m) (by rw [this]; exact (weaken t m))
    | ctor k t1 t2 t3 =>
      ctor k (weaken t1 m) (weaken t2 m) (weaken t3 m)

  def opn {α β γ n} (i : Fin n) (v : Name) (t : @Syntax α β γ n) : @Syntax α β γ n :=
    match t with
    | bound j => if j == i then free v else bound j
    | free x => free x
    | const c => const c
    | bind k t1 t2 => bind k (opn i v t1) (opn (Fin.succ i) v t2)
    | ctor k t1 t2 t3 =>
      ctor k (opn i v t1) (opn i v t2) (opn i v t3)

  def opn_head {α β γ n} (v : Name) (t : @Syntax α β γ (n + 1)) : @Syntax α β γ n :=
    match t with
    | bound j =>
      let k := j.val
      if h : k == n then free v else by {
      have lem0 : k < n + 1 := j.isLt
      have lem1 : k ≠ n := by {
        intros h2
        rewrite [h2] at h
        simp at h
      }
      have lem2 : j.val ≤ n := by linarith
      have lem3 : j.val < n := Lemma.opn_head lem1 lem2
      exact (bound (Fin.mk j.val lem3))
    }
    | free x => free x
    | const c => const c
    | bind k t1 t2 => bind k (opn_head v t1) (opn_head v t2)
    | ctor k t1 t2 t3 =>
      ctor k (opn_head v t1) (opn_head v t2) (opn_head v t3)

  def cls {α β γ n} (i : Fin n) (v : Name) (t : @Syntax α β γ n) : @Syntax α β γ n :=
    match t with
    | bound j => bound j
    | free x => if x == v then bound i else free x
    | const c => const c
    | bind k t1 t2 => bind k (cls i v t1) (cls (Fin.succ i) v t2)
    | ctor k t1 t2 t3 =>
      ctor k (cls i v t1) (cls i v t2) (cls i v t3)
  
  def cls_head {α β γ n} (v : Name) (t : @Syntax α β γ n) : @Syntax α β γ (n + 1) :=
    match t with
    | bound j => bound j
    | free x => if x == v then bound n else free x
    | const c => const c
    | bind k t1 t2 => bind k (cls_head v t1) (cls_head v t2)
    | ctor k t1 t2 t3 =>
      ctor k (cls_head v t1) (cls_head v t2) (cls_head v t3)

  instance : HasOpen (@Syntax α β γ) where
    opn := opn

  instance : HasHOpen (@Syntax α β γ) where
    hopn := opn_head

  instance : HasClose (@Syntax α β γ) where
    cls := cls

  instance : HasHClose (@Syntax α β γ) where
    hcls := cls_head

  @[simp] lemma opn_const {α β γ : Sort _} {n} (i : Fin n) (x : Name) (c : γ)
    : @HasOpen.opn (@Syntax α β γ) _ n i v (const c) = const c
    := by congr

  @[simp] lemma opn_free {α β γ : Sort _} {n} (i : Fin n) (x : Name)
    : @HasOpen.opn (@Syntax α β γ) _ n i v (free x) = free x
    := by congr
  
  @[simp] lemma opn_bound {α β γ : Sort _} {n} (i j : Fin n) (v : Name)
    : @HasOpen.opn (@Syntax α β γ) _ n i v (bound j) = if j == i then free v else bound j
    := by congr

  @[simp] lemma opn_bind {α β γ n} (k : α) (i : Fin n) (v : Name)
    (t1 : @Syntax α β γ n) (t2 : @Syntax α β γ (n + 1))
    : {i |-> v} bind k t1 t2 = bind k ({i |-> v} t1) ({(Fin.succ i) |-> v} t2)
    := by congr

  @[simp] lemma opn_ctor {α β γ n} (k : β) (i : Fin n) (v : Name)
    (t1 t2 t3 : @Syntax α β γ n)
    : {i |-> v} ctor k t1 t2 t3
      = ctor k ({i |-> v} t1) ({i |-> v} t2) ({i |-> v} t3)
    := by congr

  @[simp] lemma opn_head_const {α β γ : Sort _} {n} (x : Name) (c : γ)
    : @HasHOpen.hopn (@Syntax α β γ) _ n v (const c) = const c
    := by congr

  @[simp] lemma opn_head_free {α β γ : Sort _} {n} (x : Name)
    : @HasHOpen.hopn (@Syntax α β γ) _ n v (free x) = free x
    := by congr
  
  @[simp] lemma opn_head_bound {α β γ : Sort _} {n} (j : Fin n) (v : Name)
    : {_|-> v}(@bound α β γ (n + 1) j) = if j == n then free v else bound j
    := by {
      unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp
      unfold opn_head
      simp [*]
    }

  @[simp] lemma opn_head_bind {α β γ n} (k : α) (v : Name)
    (t1 : @Syntax α β γ (n + 1)) (t2 : @Syntax α β γ (n + 2))
    : {_|-> v} @bind α β γ (n + 1) k t1 t2 = @bind α β γ n k ({_|-> v} t1) ({_|-> v} t2)
    := by {
      generalize h : {_|-> v} @bind α β γ (n + 1) k t1 t2 = t
      unfold HasHOpen.hopn at h; unfold instHasHOpenSyntax at h; simp at h
      unfold opn_head at h
      unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp
      rw [<-h]
    }

  @[simp] lemma opn_head_ctor {α β γ n} (k : β) (v : Name)
    (t1 t2 t3 : @Syntax α β γ (n + 1))
    : {_|-> v} @ctor α β γ (n + 1) k t1 t2 t3
      = @ctor α β γ n k ({_|-> v} t1) ({_|-> v} t2) ({_|-> v} t3)
    := by {
      generalize h : {_|-> v}ctor k t1 t2 t3 = t
      unfold HasHOpen.hopn at h; unfold instHasHOpenSyntax at h; simp at h
      unfold opn_head at h
      unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp
      rw [<-h]
    }

  @[simp] lemma cls_const {α β γ : Sort _} {n} (i : Fin n) (x : Name) (c : γ)
    : @HasClose.cls (@Syntax α β γ) _ n i v (const c) = const c
    := by congr

  @[simp] lemma cls_free {α β γ : Sort _} {n} (i : Fin n) (v x : Name)
    : @HasClose.cls (@Syntax α β γ) _ n i v (free x) = if x == v then bound i else free x
    := by congr

  @[simp] lemma cls_bound {α β γ : Sort _} {n} (i j : Fin n) (v : Name)
    : @HasClose.cls (@Syntax α β γ) _ n i v (bound j) = bound j
    := by congr

  @[simp] lemma cls_bind {α β γ n} (k : α) (i : Fin n) (v : Name)
    (t1 : @Syntax α β γ n) (t2 : @Syntax α β γ (n + 1))
    : {i <-| v} bind k t1 t2 = bind k ({i <-| v} t1) ({(Fin.succ i) <-| v} t2)
    := by congr

  @[simp] lemma cls_ctor {α β γ n} (k : β) (i : Fin n) (v : Name)
    (t1 t2 t3 : @Syntax α β γ n)
    : {i <-| v} ctor k t1 t2 t3
      = ctor k ({i <-| v} t1) ({i <-| v} t2) ({i <-| v} t3)
    := by congr

  @[simp] lemma cls_head_const {α β γ : Sort _} {n} (x : Name) (c : γ)
    : {_<-| v}(@const α β γ n c) = const c
    := by congr

  @[simp] lemma cls_head_free {α β γ : Sort _} {n} (x : Name)
    : {_<-| v}(@free α β γ n x) = if x == v then bound n else free x
    := by {
      unfold HasHClose.hcls; unfold instHasHCloseSyntax; simp
      unfold cls_head
      simp [*]
    }
  
  @[simp] lemma cls_head_bound {α β γ : Sort _} {n} (j : Fin n) (v : Name)
    : {_<-| v}(@bound α β γ n j) = @bound α β γ (n + 1) j
    := by congr

  @[simp] lemma cls_head_bind {α β γ n} (k : α) (v : Name)
    (t1 : @Syntax α β γ n) (t2 : @Syntax α β γ (n + 1))
    : {_<-| v} @bind α β γ n k t1 t2 = @bind α β γ (n + 1) k ({_<-| v} t1) ({_<-| v} t2)
    := by {
      generalize h : {_<-| v} @bind α β γ n k t1 t2 = t
      unfold HasHClose.hcls at h; unfold instHasHCloseSyntax at h; simp at h
      unfold cls_head at h
      unfold HasHClose.hcls; unfold instHasHCloseSyntax; simp
      rw [<-h]
    }

  @[simp] lemma cls_head_ctor {α β γ n} (k : β) (v : Name)
    (t1 t2 t3 : @Syntax α β γ n)
    : {_<-| v} @ctor α β γ n k t1 t2 t3
      = @ctor α β γ (n + 1) k ({_<-| v} t1) ({_<-| v} t2) ({_<-| v} t3)
    := by {
      generalize h : {_<-| v}ctor k t1 t2 t3 = t
      unfold HasHClose.hcls at h; unfold instHasHCloseSyntax at h; simp at h
      unfold cls_head at h
      unfold HasHClose.hcls; unfold instHasHCloseSyntax; simp
      rw [<-h]
    }

  @[simp] theorem oc1 {α β γ n} (i : Fin n) (a b : Name) (x : @Syntax α β γ n)
    : {i |-> a}{i |-> b}x = {i |-> b}x := by
    induction x with
    | bound j => {
      cases (Nat.decEq j i) with
      | isTrue h => {
        have lem1 : j = i := by apply (Fin.mk_eq_mk.mpr h)
        rewrite [lem1]; simp
      }
      | isFalse h => {
        have lem1 : j ≠ i := by apply ((Fin.ne_iff_vne j i).mpr h)
        simp [lem1]
      }
    }
    | free f => { constructor } 
    | const c => { constructor }
    | bind k t1 t2 t1_ih t2_ih => {
      simp [t1_ih]
      exact (t2_ih (Fin.succ i))
    } 
    | ctor k t1 t2 t3 t4 t5 t6 => { simp [*] }

  @[simp] theorem oc2 {α β γ n} (i j : Fin n) (a : Name) (x : @Syntax α β γ n)
    : {i <-| a}{j <-| a}x = {j <-| a}x := by
    induction x with
    | bound j => { constructor }
    | free f => {
      cases (Name.decEq f a) with
      | isTrue h => {
        rewrite [h]
        simp [*]
      }
      | isFalse h => simp [*]
    } 
    | const c => { constructor }
    | bind k t1 t2 t1_ih t2_ih => {
      simp [t1_ih]
      exact (t2_ih (Fin.succ i) (Fin.succ j))
    } 
    | ctor k t1 t2 t3 t4 t5 t6 => { simp [*] }

  @[simp] theorem oc3 {α β γ n} (i : Fin n) (a : Name) (x : @Syntax α β γ n)
    : {i <-| a}{i |-> a}x = {i <-| a}x := by
    induction x with
    | bound j => {
      simp [*]
      simp
      cases (Nat.decEq j i) with
      | isTrue h => {
        have lem1 : j = i := by apply (Fin.mk_eq_mk.mpr h)
        rewrite [lem1]; simp
      }
      | isFalse h => {
        have lem1 : j ≠ i := by apply ((Fin.ne_iff_vne j i).mpr h)
        simp [*]
      }
    }
    | free f => { simp } 
    | const c => { constructor }
    | bind k t1 t2 t1_ih t2_ih => { simp [*] } 
    | ctor k t1 t2 t3 t4 t5 t6 => { simp [*] }

  @[simp] theorem oc4h {α β γ n} (a : Name) (x : @Syntax α β γ n)
    : {_|-> a}{_<-| a}x = x
  := @Syntax.rec α β γ
    (λ m s => {_|-> a}{_<-| a}s = s)
    (by {
      intros m i; simp
      unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp
      unfold opn_head; simp; intro h2
      have lem := i.isLt
      linarith
    })
    (by {
      intros m b; simp
      cases (Name.decEq b a)
      case isFalse h2 => {
        have lem : (b == a) = false := Name.beq_of_not_eq h2
        rewrite [lem]; simp
      }
      case isTrue h2 => {
        rewrite [h2]; simp
        unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp
        unfold opn_head; simp
      }
    })
    (by simp)
    (by {
      intros m k t1 t2 ih1 ih2; simp
      rewrite [ih1, ih2]; simp
    })
    (by {
      intros m k t2 t3 t4 ih1 ih2 ih3; simp
      rewrite [ih1, ih2, ih3]; simp
    })
    n
    x

  @[simp] theorem oc4 {α β γ n} (i : Fin n) (a : Name) (x : @Syntax α β γ n)
    : {i |-> a}{i <-| a}x = {i |-> a}x := by
    induction x with
    | bound j => { simp [*] }
    | free f => {
      simp
      cases (Name.decEq f a) with
      | isTrue h => { simp [*] }
      | isFalse h => { simp [*] }
    } 
    | const c => { constructor }
    | bind k t1 t2 t1_ih t2_ih => { simp [*] } 
    | ctor k t1 t2 t3 t4 t5 t6 => { simp [*] }

  theorem oc5 {α β γ n} (i j : Fin n) (a b : Name) (x : @Syntax α β γ n)
    : i ≠ j -> {i |-> a}{j |-> b}x = {j |-> b}{i |-> a}x := by
    intros h
    induction x with
    | bound k => {
      simp
      cases (Nat.decEq k j) with
      | isTrue h2 => {
        have lem1 : k = j := by apply (Fin.mk_eq_mk.mpr h2)
        have lem2 := h.symm
        simp [*]
      }
      | isFalse h2 => {
        have lem1 : k ≠ j := by apply ((Fin.ne_iff_vne k j).mpr h2)
        simp [*]
        cases (Nat.decEq k i) with
        | isTrue h3 => {
          have lem1 : k = i := by apply (Fin.mk_eq_mk.mpr h3)
          simp [*]
        }
        | isFalse h3 => {
          have lem1 : k ≠ i := by apply ((Fin.ne_iff_vne k i).mpr h3)
          simp [*]
        }
      }
    }
    | free f => { simp } 
    | const c => { simp }
    | bind k t1 t2 t1_ih t2_ih => { simp [*] } 
    | ctor k t1 t2 t3 t4 t5 t6 => { simp [*] }  

  theorem oc6 {α β γ n} (i j : Fin n) (a b : Name) (x : @Syntax α β γ n)
    : a ≠ b -> {i <-| a}{j <-| b}x = {j <-| b}{i <-| a}x := by
    intros h
    induction x with
    | bound k => { simp }
    | free f => {
      simp
      cases (Name.decEq f b) with
      | isTrue h2 => {
        simp [*]
        have lem1 : f ≠ a := by {
          intros h3
          have lem2 : a = b := by rw [<-h2, <-h3]
          contradiction
        }
        simp [*]
        have lem2 : (f == a) = false := by {
          cases (Name.decEq f a); simp [*]
          intro h3
          rewrite [h3] at h
          contradiction
          simp
          intro h3
          contradiction
        }
        rewrite [lem2]
        simp
      }
      | isFalse h2 => {
        simp [*]
        cases (f == a); simp [*]
        simp
      }
    } 
    | const c => { simp }
    | bind k t1 t2 t1_ih t2_ih => { simp [*] } 
    | ctor k t1 t2 t3 t4 t5 t6 => { simp [*] }  

  theorem oc7 {α β γ n} (i j : Fin n) (a b : Name) (x : @Syntax α β γ n)
    : i ≠ j -> a ≠ b -> {i |-> a}{j <-| b}x = {j <-| b}{i |-> a}x := by
    intros h1 h2
    induction x with
    | bound k => {
      simp
      cases (Nat.decEq k i) with
      | isTrue h3 => {
        have lem1 : k = i := by apply (Fin.mk_eq_mk.mpr h3)
        simp [*]
      }
      | isFalse h3 => {
        have lem1 : k ≠ i := by apply ((Fin.ne_iff_vne k i).mpr h3)
        simp [*]
      }
    }
    | free f => {
      simp
      cases (Name.decEq f b) with
      | isTrue h3 => {
        simp [*]
        intro h4
        rewrite [h4] at h1
        contradiction
      }
      | isFalse h3 => { simp [*] }
    }
    | const c => { simp }
    | bind k t1 t2 t1_ih t2_ih => { simp [*] } 
    | ctor k t1 t2 t3 t4 t5 t6 => { simp [*] }  

  theorem oc8 {α β γ n} (i j : Fin n) (a b : Name) (x : @Syntax α β γ n)
    : {i |-> b}{i <-| a}{j |-> b}x = {j |-> b}{j <-| a}{i |-> a}x := by
    induction x with
    | bound k => {
      simp
      cases (Nat.decEq k j) with
      | isTrue h => {
        have lem1 : k = j := by apply (Fin.mk_eq_mk.mpr h)
        simp [*]
        cases (Name.decEq b a) with
        | isTrue h2 => {
          simp [*]
          cases (Nat.decEq j i) with
          | isTrue h3 => {
            have lem2 : j = i := by apply (Fin.mk_eq_mk.mpr h3)
            simp [*]
          }
          | isFalse h3 => {
            have lem2 : j ≠ i := by apply ((Fin.ne_iff_vne j i).mpr h3)
            simp [*]
          }
        }
        | isFalse h2 => {
          simp [*]
          cases (Nat.decEq j i) with
          | isTrue h3 => {
            have lem2 : j = i := by apply (Fin.mk_eq_mk.mpr h3)
            simp [*]
          }
          | isFalse h3 => {
            have lem2 : j ≠ i := by apply ((Fin.ne_iff_vne j i).mpr h3)
            simp [*]
          }
        }
      }
      | isFalse h => {
        have lem1 : k ≠ j := by apply ((Fin.ne_iff_vne k j).mpr h)
        simp [*]
        cases (Nat.decEq k i) with
        | isTrue h2 => {
            have lem2 : k = i := by apply (Fin.mk_eq_mk.mpr h2)
            simp [*]
        }
        | isFalse h2 => {
            have lem2 : k ≠ i := by apply ((Fin.ne_iff_vne k i).mpr h2)
            simp [*]
        }
      }
    }
    | free f => {
      simp
      cases (Name.decEq f a) with
      | isTrue h => { simp [*] }
      | isFalse h => { simp [*] }
    }
    | const c => { simp }
    | bind k t1 t2 t1_ih t2_ih => { simp [*] } 
    | ctor k t1 t2 t3 t4 t5 t6 => { simp [*] }  

  theorem oc9 {α β γ n} (i j : Fin n) (a b : Name) (x : @Syntax α β γ n)
    : {j <-| a}{i |-> a}{j <-| b}x = {j <-| b}{i |-> b}{i <-| a}x := by
    induction x with
    | bound k => {
      simp [*]
      cases (Nat.decEq k i) with
      | isTrue h => {
        have lem1 : k = i := by apply (Fin.mk_eq_mk.mpr h)
        simp [*]
      }
      | isFalse h => {
        have lem1 : k ≠ i := by apply ((Fin.ne_iff_vne k i).mpr h)
        simp [*]
      }
    }
    | free f => {
      simp
      cases (Name.decEq f b) with
      | isTrue h1 => {
        simp [*]
        cases (Nat.decEq j i) with
        | isTrue h2 => {
          have lem1 : j = i := by apply (Fin.mk_eq_mk.mpr h2)
          simp [*]
          cases (Name.decEq f a) with
          | isTrue h3 => {
            rewrite [h3]
            simp [*]
          }
          | isFalse h3 => {
            cases (f == a); simp [*]
            simp
          }
        }
        | isFalse h2 => {
          have lem1 : j ≠ i := by apply ((Fin.ne_iff_vne j i).mpr h2)
          simp [*]
          cases (Name.decEq f a) with
          | isTrue h3 => {
            rewrite [h3]
            simp [*]
          }
          | isFalse h3 => {
            cases (f == a); simp [*]
            simp
          }
        }
      }
      | isFalse h1 => {
        have lem1 : (f == b) = false := by {
          have lem2 := contra LawfulBEq.eq_of_beq h1
          simp [*]
        }
        rewrite [lem1]; simp
        cases (Name.decEq f a) with
        | isTrue h2 => {
          rewrite [h2]
          simp
        }
        | isFalse h2 => {
          have lem2 : (f == a) = false := by { simp [*] }
          rewrite [lem2]
          simp
          rewrite [lem1]
          simp
        }
      }
    }
    | const c => { simp }
    | bind k t1 t2 t1_ih t2_ih => { simp [*] } 
    | ctor k t1 t2 t3 t4 t5 t6 => { simp [*] }  

  def fv {α β γ n} (x : @Syntax α β γ n) : FvSet! :=
    match x with
    | bound _ => List.nil
    | free x => [x]
    | const _ => List.nil
    | bind _ t1 t2 => (fv t1) ++ (fv t2)
    | ctor _ t1 t2 t3 => (fv t1) ++ (fv t2) ++ (fv t3) 

  def subst {α β γ n} (v : Name) (w t : @Syntax α β γ n) : @Syntax α β γ n :=
    match t with
    | bound i => bound i
    | free x => if x == v then w else free x
    | const c => const c
    | bind k t1 t2 => bind k (subst v w t1) (subst v (weaken w 1) t2)
    | ctor k t1 t2 t3 => ctor k
      (subst v w t1) (subst v w t2) (subst v w t3)

  instance {α β γ n} : HasSubst (@Syntax α β γ n) (@Syntax α β γ n) where
    subst := subst

  def hsubst {α β γ n} (w : @Syntax α β γ n) (t : @Syntax α β γ (n + 1)) : @Syntax α β γ n :=
    match t with
    | bound i =>
      let k := i.val
      if h : k == n then w else by {
      have lem0 : k < n + 1 := i.isLt
      have lem1 : k ≠ n := by {
        intros h2
        rewrite [h2] at h
        simp at h
      }
      have lem2 : i.val ≤ n := by linarith
      have lem3 : i.val < n := Lemma.opn_head lem1 lem2
      exact (bound (Fin.mk i.val lem3))
    }
    | free x => free x
    | const c => const c
    | bind k t1 t2 => bind k (hsubst w t1) (hsubst (weaken w 1) t2)
    | ctor k t1 t2 t3 => ctor k
      (hsubst w t1) (hsubst w t2) (hsubst w t3)


  instance {α β γ} : HasHSubst (@Syntax α β γ) (@Syntax α β γ) where
    hsubst := hsubst

  @[simp] lemma hsubst_const {α β γ : Sort _} {n} (c : γ) (v : @Syntax α β γ n)
    : [_:= v](@const α β γ (n + 1) c) = const c
  := by congr

  @[simp] lemma hsubst_free {α β γ : Sort _} {n} (x : Name) (v : @Syntax α β γ n)
    : [_:= v](@free α β γ (n + 1) x) = free x
  := by congr
  
  -- @[simp] lemma hsubst_bound {α β γ : Sort _} {n} (j : Fin n) (v : @Syntax α β γ n)
  --   : [_:= v](@bound α β γ (n + 1) n) = v
  -- := by {
  --   sorry
  -- }

  @[simp] lemma hsubst_bind {α β γ n} (k : α)
    (v : @Syntax α β γ n) (t1 : @Syntax α β γ (n + 1)) (t2 : @Syntax α β γ (n + 2))
    : [_:= v] @bind α β γ (n + 1) k t1 t2 = @bind α β γ n k ([_:= v]t1) ([_:= (weaken v 1)]t2)
  := by {
    generalize rhsdef : bind k ([_:= v]t1) ([_:= weaken v 1]t2) = u
    unfold HasHSubst.hsubst; unfold instHasHSubstSyntax; simp
    unfold HasHSubst.hsubst at *; unfold instHasHSubstSyntax at *; simp at *
    unfold hsubst; rw [rhsdef]
  }

  @[simp] lemma hsubst_ctor {α β γ n} (k : β) (v : @Syntax α β γ n)
    (t1 t2 t3 : @Syntax α β γ (n + 1))
    : [_:= v] @ctor α β γ (n + 1) k t1 t2 t3
      = @ctor α β γ n k ([_:= v]t1) ([_:= v]t2) ([_:= v]t3)
  := by {
    generalize rhsdef : ctor k ([_:= v]t1) ([_:= v]t2) ([_:= v]t3) = u
    unfold HasHSubst.hsubst; unfold instHasHSubstSyntax; simp
    unfold HasHSubst.hsubst at *; unfold instHasHSubstSyntax at *; simp at *
    unfold hsubst; rw [rhsdef]
  }

  -- @[simp] theorem open_subst {α β γ n} {N : @Syntax α β γ n} {B : @Syntax α β γ (n + 1)}
  --   : x ≠ y -> {_|-> y}[x := weaken N 1]B = [x := N]{_|-> y}B
  --   := sorry

  -- theorem subst_head_subst {α β γ n} {U V : @Syntax α β γ n} {B : @Syntax α β γ (n + 1)}
  --   : [x := U][_:= V]B = [_:= [x := U]V][x := weaken U 1]B
  --   := sorry

  def size {α β γ n} (t : @Syntax α β γ n) : Nat :=
    match t with
    | bound _i => 0
    | free _x => 0
    | const _c => 0
    | bind _k t1 t2 => (size t1) + (size t2) + 1
    | ctor _k t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1

  @[simp] def size_bound : @size α β γ n (bound i) = 0 := by congr
  @[simp] def size_free : @size α β γ n (free x) = 0 := by congr
  @[simp] def size_const : @size α β γ n (const c) = 0 := by congr
  @[simp] def size_bind : @size α β γ n (bind k t1 t2) = (size t1) + (size t2) + 1 := by congr
  @[simp] def size_ctor : @size α β γ n (ctor k t1 t2 t3)
    = (size t1) + (size t2) + (size t3) + 1
  := by congr

  lemma size_opn_head' {t : @Syntax α β γ m} : (h : m = n + 1)
    -> @size α β γ n ({_|-> x} (by rw [<-h]; exact t)) = @size α β γ m t
  := by {
    intros h
    induction t generalizing n <;> simp [*]
    case bound k i => {
      subst h
      rw [cast_eq]
      cases (Nat.decEq i n) with
      | isTrue h2 => {
        unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp; unfold opn_head
        simp [*]
      }
      | isFalse h2 => {
        unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp; unfold opn_head
        simp [*]
      }
    }
    case free k v => {
      subst h
      rw [cast_eq]
      simp
    }
    case const k c => {
      subst h
      rw [cast_eq]
      simp
    }
    case bind q k t1 t2 t1_ih t2_ih => {
      subst h
      simp
      have lem1 := @t1_ih n rfl
      simp at lem1
      have lem2 := @t2_ih (n + 1) rfl
      simp at lem2
      simp [*]
    }
    case ctor q k t1 t2 t3 t1_ih t2_ih t3_ih => {
      subst h
      rw [cast_eq]
      have lem1 := t1_ih rfl
      have lem2 := t2_ih rfl
      have lem3 := t3_ih rfl
      simp at lem1
      simp at lem2
      simp at lem3
      simp [*]
    }
  }

  @[simp] lemma size_opn_head : @size α β γ n ({_|-> x} t) = size t := size_opn_head' rfl

  @[simp↓ high] lemma rename_bound {α β γ n} {i : Fin n}
    : {_|-> x}{_<-| y}(@bound α β γ n i) = bound i
  := by {
    simp
    unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp at *
    unfold opn_head; simp at *
    intro h
    cases i; case _ iv il =>
    simp at h
    linarith
  }

  lemma rename_free_neq : z ≠ y -> {_|-> x}{_<-| y}(@free α β γ n z) = free z := by {
    intro h; simp; split
    case _ h2 => {
      have h3 : z = y := LawfulBEq.eq_of_beq h2
      exfalso
      apply h h3
    }
    case _ h2 => {
      unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp at *
      unfold opn_head; simp at *
    }
  }

  lemma rename_free_eq : {_|-> x}{_<-| y}(@free α β γ n y) = free x := by {
    simp
    unfold HasHOpen.hopn; unfold instHasHOpenSyntax; simp at *
    unfold opn_head; simp at *
  }

  @[simp] lemma weaken_rename
    : {_|-> x}{_<-| y}(weaken t 1) = weaken ({_|-> x}{_<-| y}t) 1
  := by {
    induction t
    case bound n i => unfold weaken; simp
    case free n z => {
      generalize hdef : weaken (free z) 1 = h
      unfold weaken at hdef; rw [<-hdef]
      cases Name.decEq z y
      case isFalse h => {
        rw [rename_free_neq h, rename_free_neq h]
        unfold weaken; simp
      }
      case isTrue h => {
        subst h
        rw [rename_free_eq, rename_free_eq]
        unfold weaken; simp
      }
    }
    case const => unfold weaken; simp
    case bind k u1 u2 ih1 ih2 => {
      simp; unfold weaken; simp
      rw [ih1, ih2]; simp
    }
    case ctor c u1 u2 u3 ih1 ih2 ih3 => {
      simp; unfold weaken; simp
      rw [ih1, ih2, ih3]; simp
    }
  }

end Syntax
