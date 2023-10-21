
import Common
import Cedille.Def
import Cedille.Lemma.Refold
import Cedille.Lemma.Inversion
import Cedille.Lemma.Syntax

namespace Cedille

  @[simp] lemma erase_bound : erase x (bound i) = bound i := by congr
  @[simp] lemma erase_free {n} : erase z (@free n x) = free x := by congr
  @[simp] lemma erase_const {n} : erase x (@const n c) = const c := by congr
  @[simp] lemma erase_typeu {n} : erase x (@typeu n) = typeu := by congr
  @[simp] lemma erase_kindu {n} : erase x (@kindu n) = kindu := by congr
  
  @[simp] lemma erase_lam_mf : erase x (lam mf a b) = lam mf kindu (erase x b) := by congr
  @[simp] lemma erase_lam_mf_unfolded
    : erase x (Syntax.bind (Binder.lam mf) a b) = lam mf kindu (erase x b)
  := by congr

  @[simp] lemma erase_lam_mt : erase x (lam mt a b) = lam mt (erase x a) (erase x b) := by congr
  @[simp] lemma erase_lam_mt_unfolded
    : erase x (Syntax.bind (Binder.lam mt) a b) = lam mt (erase x a) (erase x b)
  := by congr

  @[simp] lemma erase_pi : erase x (pi m a b) = pi m (erase x a) (erase x b) := by congr
  @[simp] lemma erase_pi_unfolded
    : erase x (Syntax.bind (Binder.pi m) a b) = pi m (erase x a) (erase x b)
  := by congr

  @[simp] lemma erase_inter : erase x (inter a b) = inter (erase x a) (erase x b) := by congr
  @[simp] lemma erase_inter_unfolded
    : erase x (Syntax.bind Binder.inter a b) = inter (erase x a) (erase x b)
  := by congr

  @[simp] lemma erase_lam_m0 {n} {a : Term n} {b : Term (n + 1)}
    : erase x (lam m0 a b) = erase x ({_|-> x}b)
  := by {
    unfold lam
    rfl
  }

  @[simp] lemma erase_app_m0 : erase x (t1 @0 t2) = erase x t1
    := by rfl
  @[simp] lemma erase_app_m0_unfolded
    : erase x (Syntax.ctor (Constructor.app m0) t1 t2 t3) = erase x t1
  := by rfl

  @[simp] lemma erase_app_mf : erase x (t1 @ω t2) = (erase x t1) @ω (erase x t2)
  := by congr
  @[simp] lemma erase_app_mf_unfolded
    : erase x (Syntax.ctor (Constructor.app mf) t1 t2 t3) = app mf (erase x t1) (erase x t2)
  := by congr

  @[simp] lemma erase_app_mt : erase x (t1 @τ t2) = (erase x t1) @τ (erase x t2)
  := by congr
  @[simp] lemma erase_app_mt_unfolded
    : erase x (Syntax.ctor (Constructor.app mt) t1 t2 t3) = app mt (erase x t1) (erase x t2)
  := by congr

  @[simp] lemma erase_pair : erase x (pair t1 t2 t3) = erase x t1
    := rfl
  @[simp] lemma erase_pair_unfolded
    : erase x (Syntax.ctor Constructor.pair t1 t2 t3) = erase x t1
  := rfl

  @[simp] lemma erase_fst : erase x (fst t) = erase x t := by generalize t = s; rfl
  @[simp] lemma erase_fst_unfolded
    : erase x (Syntax.ctor Constructor.fst t1 t2 t3) = erase x t1
  := rfl

  @[simp] lemma erase_snd : erase x (snd t) = erase x t := by generalize t = s; rfl
  @[simp] lemma erase_snd_unfolded
    : erase x (Syntax.ctor Constructor.snd t1 t2 t3) = erase x t1
  := rfl

  @[simp] lemma erase_eq : erase x (eq t1 t2 t3) = eq (erase x t1) (erase x t2) (erase x t3)
    := by congr
  @[simp] lemma erase_eq_unfolded
    : erase x (Syntax.ctor Constructor.eq t1 t2 t3) = eq (erase x t1) (erase x t2) (erase x t3)
  := by {
    generalize h : eq (erase x t1) (erase x t2) (erase x t3) = t
    unfold erase; subst h; rfl
  }

  @[simp] lemma erase_refl : erase x (refl t) = lam mf kindu (bound 0) := by congr
  @[simp] lemma erase_refl_unfolded
    : erase x (Syntax.ctor Constructor.refl t1 t2 t3) = lam mf kindu (bound 0)
  := by congr

  @[simp] lemma erase_Jh : erase x (Jh t1 t2 t3) = erase x t3 := by generalize erase x t3 = rhs; simp
  @[simp] lemma erase_Jh_unfolded
    : erase x (Syntax.ctor Constructor.eqind t1 t2 t3) = erase x t3
  := by generalize erase x t3 = rhs; simp

  @[simp] lemma erase_J0 : erase x (J0 t1 t2) = kindu := by congr
  @[simp] lemma erase_J0_unfolded
    : erase x (Syntax.ctor Constructor.j0 t1 t2 t3) = kindu
  := by congr

  @[simp] lemma erase_Jω : erase x (Jω t1 t2) = (erase x t1) @ω (erase x t2) := by congr
  @[simp] lemma erase_Jω_unfolded
    : erase x (Syntax.ctor Constructor.jω t1 t2 t3) = (erase x t1) @ω (erase x t2)
  := by congr

  @[simp] lemma erase_J : erase x (J t1 t2 t3 t4 t5 t6) = (erase x t5) @ω (erase x t6) := by {
    unfold J; rw [erase_Jh, erase_Jω]
  }

  @[simp] lemma erase_promote : erase x (promote t) = erase x t := by rfl
  @[simp] lemma erase_promote_unfolded
    : erase x (Syntax.ctor Constructor.promote t1 t2 t3) = erase x t1
  := rfl

  @[simp] lemma erase_delta : erase x (delta t) = erase x t := by rfl
  @[simp] lemma erase_delta_unfolded
    : erase x (Syntax.ctor Constructor.delta t1 t2 t3) = erase x t1
  := by rfl

  @[simp] lemma erase_phi : erase x (phi t1 t2 t3) = erase x t1 := by rfl

  @[simp] lemma erase_idem {m} {t : Term m} : erase y (erase x t) = erase x t := @Nat.rec
    (λ n => {m : Nat} -> (t : Term m) -> size t ≤ n -> erase y (erase x t) = erase x t)
    (by {
      intro m t h
      cases t <;> simp at h <;> try simp [*] 
    })
    (by {
      intros n ih m t h
      cases t <;> simp at h <;> try simp [*]
      case bind k t1 t2 => {
        have h1 : size t1 ≤ n := by linarith
        have h2 : size t2 ≤ n := by linarith
        cases k <;> simp [*]
        case lam k =>
        cases k <;> simp [*]
      }
      case ctor k t1 t2 t3 => {
        have h1 : size t1 ≤ n := by linarith
        have h2 : size t2 ≤ n := by linarith
        have h3 : size t3 ≤ n := by linarith
        cases k <;> try simp [*]
        case app m =>
        cases m <;> simp [*]
      }
    })
    (size t)
    m
    t
    (by simp)

  lemma erase_rename_commute (x y z) {n} {t : Term n} (h : x ≠ z)
    : {_|-> y}{_<-| x}(erase z t) = erase z ({_|-> y}{_<-| x}t)
  := @Nat.rec
    (λ s => ∀ n (t : Term n),
      size t ≤ s ->
      {_|-> y}{_<-| x}(erase z t) = erase z ({_|-> y}{_<-| x}t))
    (by {
      intro n t sh
      cases t <;> simp at *
      case bound i => {
        unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
        unfold Syntax.opn_head; unfold bound; simp
        intro h
        cases i; case _ iv il =>
        simp at h
        linarith
      }
      case free w => split <;> simp
    })
    (by {
      intro s ih n t sh
      cases t
      case bound => apply ih _ (bound _) (by simp)
      case free => apply ih _ (free _) (by simp)
      case const => apply ih _ (const _) (by simp)
      case bind k u1 u2 => {
        simp at *
        have s1 : size u1 ≤ s := by linarith
        have s2 : size u2 ≤ s := by linarith
        cases k <;> simp at *
        case lam m => {
          cases m <;> simp at *
          case free => rw [ih _ u2 s2]
          case erased => {
            have sh : size ({_|-> z}u2) ≤ s := by simp; linarith
            have lem := ih _ ({_|-> z}u2) sh
            rw [lem, @rename_open_commute _ z x y u2 (ne_sym h)]
          }
          case type => rw [ih _ u1 s1, ih _ u2 s2]
        }
        case pi m => rw [ih _ u1 s1, ih _ u2 s2]
        case inter => rw [ih _ u1 s1, ih _ u2 s2]
      }
      case ctor k u1 u2 u3 => {
        simp at *
        have s1 : size u1 ≤ s := by linarith
        have s2 : size u2 ≤ s := by linarith
        have s3 : size u3 ≤ s := by linarith
        cases k <;> simp at * <;> try rw [ih _ u1 s1] <;> try rw [ih _ u2 s2] <;> try rw [ih _ u3 s3]
        case app m => {
          cases m <;> simp at *
          case free => rw [ih _ u1 s1, ih _ u2 s2]
          case erased => rw [ih _ u1 s1]
          case type => rw [ih _ u1 s1, ih _ u2 s2]
        }
        case refl => {
          unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
          unfold Syntax.opn_head; unfold bound; simp
          split <;> try simp [*]
          exfalso; linarith
        }
        case eqind => rw [ih _ u3 s3]
      }
    })
    (size t)
    n
    t
    (by simp)

  -- lemma erase_rename {n} {t1 t2 : Term n} : erase z t1 = erase z t2 ->
  --   erase z ({_|-> y}{_<-| x}t1) = erase z ({_|-> y}{_<-| x}t2)
  -- := λ h => @Nat.rec
  --   (λ s => ∀ n (t1 t2 : Term n),
  --     size t1 + size t2 ≤ s ->
  --     erase x t1 = erase x t2 ->
  --     erase x ({_|-> y}{_<-| x}t1) = erase x ({_|-> y}{_<-| x}t2))
  --   (by {
  --     intro n t1 t2 sh h
  --     cases t1 <;> simp at *
  --     case bound i => {
  --       cases t2 <;> simp at *
  --       case bound i' => injection h; simp [*]
  --     }
  --     case free z => {
  --       cases t2 <;> simp at *
  --       case free z' => {
  --         injection h with _ e; subst e
  --         split <;> simp at *
  --       }
  --     }
  --     case const c => {
  --       cases t2 <;> simp at *
  --       case const k' => injection h; simp [*]
  --     }
  --   })
  --   (by {
  --     intro s ih n t1 t2 sh h
  --     cases t1
  --     case bound => sorry
  --     case free => sorry
  --     case const => sorry
  --     case bind k1 u1 u2 => {
  --       cases k1 <;> simp at *
  --       case lam m => {
  --         cases m <;> simp at *
  --         case free => sorry
  --         case erased => {
  --           generalize zdef : Name.fresh (fv u2) = z at *
  --           have sh : size ({_|-> z}u2) + size t2 ≤ s := by simp; linarith
  --           have lem := ih _ ({_|-> z}u2) t2 sh h
  --           rw [<-lem]
  --         }
  --         case type => sorry
  --       }
  --       case pi m => {
  --         cases t2 <;> simp at *
  --         case bind k2 v1 v2 => sorry
  --         case ctor k2 v1 v2 v3 => {
  --           cases k2 <;> simp at *
  --           case app m => {
  --             cases m <;> simp at *
  --             case erased => {
  --               have sh : size u1 + size u2 + 1 + size v1 ≤ s := by linarith
  --               have lem := ih _ (pi m u1 u2) v1 sh h
  --               rw [<-lem]; simp
  --             }
  --           }
  --           repeat sorry
  --         }
  --       }
  --       case inter => sorry
  --     }
  --     case ctor => sorry
  --   })
  --   (size t1 + size t2)
  --   n
  --   t1
  --   t2
  --   (by simp)
  --   h

  -- lemma erase_free_rename :
  --   ((x : Name) -> x ∉ fv t -> x ∉ (fv ∘ erase) ({_|-> x}t)) ->
  --   (x y : Name) -> x ∉ fv t -> y ∉ fv t -> erase x ({_|-> x}t) = erase x ({_|-> y}t)
  -- := by {
  --   intro h x y xnin ynin
  --   have hx := h x xnin
  --   have hy := h y ynin
  --   sorry
  -- }

  -- @[simp] lemma erase_subst : erase x ([_:= a]f) = [_:= erase x a](erase x f) := sorry

  -- lemma erase_close_open : erase x t = {_|-> x}s -> erase x ({_<-| x}t) = s := sorry

  -- lemma erase_forces_lam_mt : erase x f = lam mt t1 t2 ->
  --   ∃ t1' t2', erase x t1' = t1 ∧ erase x t2' = t2 ∧ f = lam mt t1' t2'
  -- := sorry

  -- lemma erase_forces_lam_mf : erase x f = lam mf t1 t2 ->
  --   ∃ t1' t2', erase x t1' = t1 ∧ erase x t2' = t2 ∧ f = lam mf t1' t2'
  -- := sorry

  -- lemma erase_no_eqind : erase x f ≠ J @τ t1 @τ t2 @0 t3 @0 t4 @ω t5 := sorry

  -- lemma erase_free_invariant :
  --   x ∉ (fv ∘ erase) ({_|-> x}t) ->
  --   (y : Name) -> y ∉ fv t ->
  --   erase x ({_|-> x}t) = erase x ({_|-> y}t)
  -- := sorry

  -- lemma erase_ctt_eq : erase x t = erase x ctt -> t = lam mf kindu (lam mf kindu (bound 0)) := sorry
  -- lemma erase_cff_eq : erase x t = erase x cff -> t = lam mf kindu (lam mf kindu (bound 1)) := sorry

end Cedille
