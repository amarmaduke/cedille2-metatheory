
import Common
import Cedille.Def
import Cedille.Lemma.Refold
import Cedille.Lemma.Inversion
import Cedille.Lemma.Syntax
import Cedille.Lemma.PseObj

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

--  lemma erase_weaken {m} {t : Term m} : (erase x t)ʷ = erase x tʷ := by sorry

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
        case eqind => rw [ih _ u3 s3]
      }
    })
    (size t)
    n
    t
    (by simp)

  -- lemma erase_open_fv_notin_shrink {t : Term (n + 1)} {x y z : Name}
  --   : x ∉ fv (erase z ({_|-> y}t)) -> x ∉ fv (erase z t)
  -- := by sorry

  -- lemma erase_open_fv_notin_grow {t : Term (n + 1)} {x y z : Name}
  --   : x ≠ y -> x ∉ fv (erase z t) -> x ∉ fv (erase z ({_|-> y}t))
  -- := by sorry

  lemma erase_size {n} (t : Term n) (x : Name) : size (erase x t) ≤ size t := @Nat.rec
    (λ s => ∀ {n} {t: Term n}, size t ≤ s -> size (erase x t) ≤ size t)
    (by {
      intros n t sh
      cases t <;> simp at *
    })
    (by {
      intro s ih n t sh
      cases t
      case free => apply ih (by simp)
      case bound => apply ih (by simp)
      case const => apply ih (by simp)
      case bind k u1 u2 => {
        simp at sh
        have sh1 : size u1 ≤ s := by linarith
        have sh2 : size u2 ≤ s := by linarith
        have sh2' : size ({_|-> x}u2) ≤ s := by simp; exact sh2
        have sh3 : size (erase x u1) ≤ size u1 := by apply ih sh1
        have sh4 : size (erase x u2) ≤ size u2 := by apply ih sh2
        cases k <;> simp
        case lam md => {
          cases md <;> simp
          case type => linarith
          case free => linarith
          case erased => {
            have sh := ih sh2'
            simp at sh; linarith
          }
        }
        case pi md => linarith
        case inter => linarith
      }
      case ctor k u1 u2 u3 => {
        simp at sh
        have sh1 : size u1 ≤ s := by linarith
        have sh2 : size u2 ≤ s := by linarith
        have sh3 : size u3 ≤ s := by linarith
        have sh4 : size (erase x u1) ≤ size u1 := by apply ih sh1
        have sh5 : size (erase x u2) ≤ size u2 := by apply ih sh2
        have sh6 : size (erase x u3) ≤ size u3 := by apply ih sh3
        cases k <;> (try simp; linarith)
        case app md => cases md <;> (simp; linarith)
        case refl => simp
        case j0 => simp
      }
    })
    (size t)
    n
    t
    (by simp)

  lemma erase_open_commute_same {n} {t : Term (n + 1)}
    : ∀ x, erase x ({_|-> x}t) = {_|-> x}erase x t
  := @Nat.rec
    (λ s => ∀ {n:Nat} {t:Term (n + 1)}, size t ≤ s ->
      ∀ x, erase x ({_|-> x}t) = {_|-> x}erase x t)
    (by {
      intro n t sh x
      cases t <;> simp at *
      case bound j => {
        unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
        unfold Syntax.opn_head; unfold bound; simp
        split <;> simp
      }
    })
    (by {
      intro s ih n t sh x
      cases t
      case bound j => apply ih (by simp)
      case free x => apply ih (by simp)
      case const k => apply ih (by simp)
      case bind k u1 u2 => {
        simp at sh
        have sh1 : size u1 ≤ s := by linarith
        have sh2 : size u2 ≤ s := by linarith
        cases k
        case lam md => {
          cases md <;> simp at *
          case free => rw [ih sh2]
          case type => rw [ih sh1 x, ih sh2 x]
          case erased => {
            have sh3 : size ({_|-> x}u2) ≤ s := by simp [*]
            rw [ih sh3]
          }
        }
        case pi md => simp at *; rw [ih sh1 x, ih sh2 x]
        case inter => simp at *; rw [ih sh1 x, ih sh2 x]
      }
      case ctor k u1 u2 u3 => {
        simp at sh
        have sh1 : size u1 ≤ s := by linarith
        have sh2 : size u2 ≤ s := by linarith
        have sh3 : size u3 ≤ s := by linarith
        cases k <;> simp at *
        case app md => {
          cases md <;> simp at *
          case type => rw [ih sh1, ih sh2]
          case free => rw [ih sh1, ih sh2]
          case erased => rw [ih sh1]
        }
        case pair => rw [ih sh1]
        case fst => rw [ih sh1]
        case snd => rw [ih sh1]
        case eq => rw [ih sh1, ih sh2, ih sh3]
        case eqind => rw [ih sh3]
        case jω => rw [ih sh1, ih sh2]
        case promote => rw [ih sh1]
        case delta => rw [ih sh1]
        case phi => rw [ih sh1]
      }
    })
    (size t)
    n
    t
    (by simp)

  lemma erase_fv (y : Name) : x ∈ fv (erase y t) -> x ∈ fv t := by sorry

  lemma erase_open_commute {t : Term 1} (x y : Name)
    : PseObj ({_|-> y}t) -> erase x ({_|-> y}t) = {_|-> y}erase x t
  := by sorry

  -- lemma erase_pseobj_open : PseObj (erase y ({_|-> x}t)) -> PseObj ({_|-> x}(erase y t))
  -- := λ h => @Nat.rec
  --   (λ s => ∀ t, size t ≤ s ->
  --     PseObj (erase y ({_|-> x}t)) ->
  --     PseObj ({_|-> x}(erase y t)))
  --   sorry
  --   (by {
  --     intro s ih t sh h
  --     cases t
  --     case bound => sorry
  --     case free => sorry
  --     case const => sorry
  --     case bind k u1 u2 => {
  --       simp at sh
  --       have sh1 : size u1 ≤ s := by linarith
  --       have sh2 : size u2 ≤ s := by linarith
  --       cases k
  --       case lam md => sorry
  --       case pi md => sorry
  --       case inter => {
  --         simp at *
  --         cases h; case _ S _ p1 p2 =>
  --         sorry
  --       }
  --     }
  --     case ctor k u1 u2 u3 => sorry
  --   })
  --   (size t)
  --   t
  --   (by simp)
  --   h

  -- lemma erase_pseobj (x : Name) (t : Term 0) : PseObj (erase x t) := @Nat.rec
  --   (λ s => ∀ {t}, size t ≤ s -> PseObj (erase x t))
  --   (by {
  --     intro t sh
  --     cases t <;> simp at *
  --     case bound j => cases j; linarith
  --     case free => constructor
  --     case const => constructor
  --   })
  --   (by {
  --     intro s ih t sh
  --     cases t
  --     case bound => apply ih (by simp)
  --     case free => apply ih (by simp)
  --     case const => apply ih (by simp)
  --     case bind k u1 u2 => {
  --       simp at sh
  --       have sh1 : size u1 ≤ s := by linarith
  --       have sh2 : size u2 ≤ s := by linarith
  --       cases k <;> simp
  --       case lam md => {
  --         cases md <;> simp
  --         case free => {
  --           constructor; simp; constructor
  --           swap; exact []; intro y _
  --           have sh2' : size ({_|-> y}u2) ≤ s := by simp; exact sh2
  --           have p := ih sh2'
  --           apply erase_pseobj_open p
  --         }
  --         case type => {
  --           constructor; simp; apply ih sh1
  --           swap; exact []; intro y _
  --           have sh2' : size ({_|-> y}u2) ≤ s := by simp; exact sh2
  --           have p := ih sh2'
  --           apply erase_pseobj_open p
  --         }
  --         case erased => {
  --           have sh2' : size ({_|-> x}u2) ≤ s := by simp; exact sh2
  --           apply ih sh2'
  --         }
  --       }
  --       case pi md => {
  --         constructor; simp; apply ih sh1
  --         swap; exact []; intro y _
  --         have sh2' : size ({_|-> y}u2) ≤ s := by simp; exact sh2
  --         have p := ih sh2'
  --         apply erase_pseobj_open p
  --       }
  --       case inter => {
  --         constructor; simp; apply ih sh1
  --         swap; exact []; intro y _
  --         have sh2' : size ({_|-> y}u2) ≤ s := by simp; exact sh2
  --         have p := ih sh2'
  --         apply erase_pseobj_open p
  --       }
  --     }
  --     case ctor k u1 u2 u3 => {
  --       simp at sh
  --       have sh1 : size u1 ≤ s := by linarith
  --       have sh2 : size u2 ≤ s := by linarith
  --       have sh3 : size u3 ≤ s := by linarith
  --       cases k <;> simp at *
  --       case app md => {
  --         cases md <;> simp
  --         case free => {
  --           constructor; simp
  --           apply ih sh1; apply ih sh2; constructor
  --         }
  --         case type => {
  --           constructor; simp
  --           apply ih sh1; apply ih sh2; constructor
  --         }
  --         case erased => apply ih sh1
  --       }
  --       case pair => apply ih sh1
  --       case fst => apply ih sh1
  --       case snd => apply ih sh1
  --       case eq => {
  --         constructor; simp
  --         apply ih sh1; apply ih sh2; apply ih sh3
  --       }
  --       case refl => {
  --         constructor; simp
  --         constructor; swap; exact []
  --         intro x _; constructor
  --       }
  --       case eqind => apply ih sh3
  --       case j0 => constructor
  --       case jω => {
  --         constructor; simp
  --         apply ih sh1; apply ih sh2; constructor
  --       }
  --       case promote => apply ih sh1
  --       case delta => apply ih sh1
  --       case phi => apply ih sh1
  --     }
  --   })
  --   (size t)
  --   t
  --   (by simp)

  -- lemma erase_pseobj_erase_swap (x y : Name) : PseObj t -> erase x t = erase y t := by {
  --   intro h
  --   induction h
  --   case ax => simp
  --   case var => simp
  --   case bind k _ _ _ _ _ _ _ _ => {
  --     cases k
  --     any_goals simp [*]
  --     case lam md => sorry
  --     case pi md => sorry
  --     case inter => sorry
  --   }
  --   case lam => sorry
  --   case pair ih1 ih2 ih3 => simp [*]
  --   case ctor k _ _ _ _ _ _ _ _ _ _ => {
  --     cases k
  --     any_goals simp [*]
  --     case app md _ => cases md <;> simp [*]
  --   }
  -- }

  -- lemma erase_pseobj_open_erase_swap (x y z : Name)
  --   : PseObj ({_|-> z}t) -> erase x t = erase y t
  -- := by sorry

  -- lemma erase_pseobj_lam_m0
  --   : PseObj (lam m0 t1 t2) -> ∀ y, erase x (lam m0 t1 t2) = {_|-> y}erase x t2
  -- := by {
  --   intro obj y
  --   cases obj
  --   case _ n _ _ => exfalso; apply n (by simp)
  --   case _ S p1 p2 h => {
  --     have p := PseObj.lam p1 p2 h
  --     have zfresh := @Name.fresh_is_fresh S
  --     generalize _zdef : @Name.fresh S = z at *
  --     rw [erase_pseobj_erase_swap x y p]; simp
  --     have lem := p2 z zfresh
  --     rw [erase_pseobj_open_erase_swap x y z lem]
  --     rw [erase_open_commute y]
  --   }
  -- }

end Cedille
