import Common
import Erased.Term
import Cedille2.Term
import Cedille2.Term.Classify

namespace Cedille2.Term
  @[simp]
  def erase : Term -> Erased.Term
  | .var K x => .var K x
  | .const K => .const K
  | .app mt f a => .appt (erase f) (erase a)
  | .app mf f a => .app (erase f) (erase a)
  | .app m0 f _ => erase f
  | .lam mt A t => .lamt (erase A) (erase t)
  | .lam mf _ t => .lam (erase t)
  | .lam m0 _ t => erase (t β[□])
  | .all m A B => .all m (erase A) (erase B)
  | .inter _ _ _ t _ => erase t
  | .fst t => erase t
  | .snd t => erase t
  | .inter_ty A B => .inter_ty (erase A) (erase B)
  | .refl _ _ _ _ => .lam (.var .type 0)
  | .eq a b => .eq (erase a) (erase b)
  | .subst _ _ t => erase t
  | .phi a _ _ => erase a
  | .conv _ _ _ t => erase t
end Cedille2.Term

namespace Erased.Term
  @[simp]
  def embed : Term -> Cedille2.Term
  | var K x => .var K x
  | const K => .const K
  | appt f a => .app mt (embed f) (embed a)
  | app f a => .app mf (embed f) (embed a)
  | lamt A t => .lam mt (embed A) (embed t)
  | lam t => .lam mf □ (embed t)
  | all m A B => .all m (embed A) (embed B)
  | inter_ty A B => .inter_ty (embed A) (embed B)
  | eq a b => .eq (embed a) (embed b)
end Erased.Term

namespace Cedille2

  theorem erase_rename_with_const_lemma {r : Ren} :
    (∀ {n t}, σ n = .su t -> ∃ K, t = .const K) ->
    Subst.map Term.erase (r.to ⊙ σ) = Subst.map Term.erase r.to ⊙ Subst.map Term.erase σ
  := by
  intro h
  funext; case _ x =>
    unfold Subst.compose; simp
    generalize zdef : σ x = z at *
    cases z <;> simp at *
    case _ t =>
      replace h := h zdef
      cases h; case _ k h =>
        subst h; simp

  theorem subst_is_const_lift σ :
    (∀ {n t}, σ n = .su t -> ∃ K, t = .const K) ->
    (∀ {n t}, ^σ n = .su t -> ∃ K, t = Term.const K)
  := by
  intro h1 n t h2; simp at *
  cases n <;> simp at *
  case _ n =>
    unfold Subst.compose at h2; simp at h2
    generalize zdef : σ n = z at h2
    cases z
    case _ k => simp at h2
    case _ t' =>
      simp at h2
      replace h1 := h1 zdef
      cases h1; case _ K h1 =>
        subst h2; subst h1; simp

  theorem erase_rename_with_const :
    (∀ {n t}, σ n = .su t -> ∃ K, t = .const K) ->
    Term.erase ([σ]t) = [Subst.map Term.erase σ](Term.erase t)
  := by
  intro h
  induction t generalizing σ <;> simp
  case _ K x =>
    generalize zdef : σ x = z at *
    cases z <;> simp at *
  case _ m f a ih1 ih2 =>
    cases m <;> simp at *
    case _ => rw [ih1 h, ih2 h]; simp
    case _ => rw [ih1 h]
    case _ => rw [ih1 h, ih2 h]; simp
  case _ m A t ih1 ih2 =>
    cases m
    case _ =>
      have lem1 := @ih2 (^σ) (subst_is_const_lift σ h); simp at *
      rw [lem1, <-to_S, erase_rename_with_const_lemma h, to_S]
      simp
    case _ =>
      have lem1 := @ih2 (.su □ :: I)
      have lem2 := @ih2 (.su □ :: σ)
      simp at *
      rw [lem1, lem2]; simp
      case _ =>
        intro n t h2
        cases n <;> simp at *
        case _ => subst t; simp
        case _ n => apply h h2
      case _ =>
        intro n t h2
        cases n <;> simp at *
        case _ => subst t; simp
    case _ =>
      have lem1 := @ih2 (^σ) (subst_is_const_lift σ h); simp at *
      rw [lem1, <-to_S, erase_rename_with_const_lemma h, to_S]
      simp; apply ih1 h
  case _ ih1 ih2 =>
    have lem1 := @ih2 (^σ) (subst_is_const_lift σ h); simp at *
    rw [lem1, <-to_S, erase_rename_with_const_lemma h, to_S]
    simp; apply ih1 h
  case _ ih _ => apply ih h
  case _ ih => apply ih h
  case _ ih => apply ih h
  case _ ih1 ih2 =>
    have lem1 := @ih2 (^σ) (subst_is_const_lift σ h); simp at *
    rw [lem1, <-to_S, erase_rename_with_const_lemma h, to_S]
    simp; apply ih1 h
  case _ ih1 ih2 => apply And.intro (ih1 h) (ih2 h)
  case _ ih => apply ih h
  case _ ih _ _ => apply ih h
  case _ ih => apply ih h

  theorem erase_rename_commute {r : Ren}
    : ∀ t, Term.erase ([r.to]t) = [r.to](Term.erase t)
  := by
  intro t
  induction t generalizing r <;> simp
  case _ => unfold Ren.to; simp
  case _ m f a ih1 ih2 =>
    cases m <;> simp at *
    case _ => rw [ih1, ih2]; simp
    case _ => rw [ih1]
    case _ => rw [ih1, ih2]; simp
  case _ m A t ih1 ih2 =>
    cases m <;> simp at *
    case _ =>
      have lem := @ih2 (Ren.lift r); rw [Subst.lift_lemma] at lem; simp at lem
      rw [lem, Subst.lift_lemma]; simp
    case _ =>
      rw [erase_rename_with_const, erase_rename_with_const]; simp
      case _ =>
        intro n t h
        cases n <;> simp at *
        subst h; exists .kind
      case _ =>
        intro n t h
        cases n <;> simp at *
        case _ => subst h; exists .kind
        case _ =>
          unfold Ren.to at h; simp at h
    case _ =>
      rw [ih1]; apply And.intro rfl
      have lem := @ih2 (Ren.lift r); rw [Subst.lift_lemma] at lem; simp at lem
      rw [lem, Subst.lift_lemma]; simp
  case _ ih1 ih2 =>
    rw [ih1]; apply And.intro rfl
    have lem := @ih2 (Ren.lift r); rw [Subst.lift_lemma] at lem; simp at lem
    rw [lem, Subst.lift_lemma]; simp
  case _ ih _ => apply ih
  case _ ih => apply ih
  case _ ih => apply ih
  case _ ih1 ih2 =>
    rw [ih1]; apply And.intro rfl
    have lem := @ih2 (Ren.lift r); rw [Subst.lift_lemma] at lem; simp at lem
    rw [lem, Subst.lift_lemma]; simp
  case _ ih1 ih2 => apply And.intro ih1 ih2
  case _ ih => apply ih
  case _ ih _ _ => apply ih
  case _ ih => apply ih

  theorem erase_subst {t : Term} : ([σ]t).erase = [Subst.map Term.erase σ]t.erase := by
  have lem : ∀ {T}, S = @Ren.to T (λ x => x + 1) := by
    unfold S; unfold Ren.to; simp
  induction t generalizing σ <;> simp
  case _ K x =>
    generalize zdef : σ x = z at *
    cases z <;> simp at *
  case _ m f a ih1 ih2 =>
    cases m <;> simp
    case _ =>
      rw [ih1, ih2]; apply And.intro rfl rfl
    case _ => apply ih1
    case _ =>
      rw [ih1, ih2]; apply And.intro rfl rfl
  case _ m A t ih1 ih2 =>
    cases m <;> simp
    case _ =>
      have lem2 := @ih2 (^σ); simp at lem2
      rw [lem2, lem, lem, Subst.map_rename_compose_left erase_rename_commute]
    case _ =>
      rw [@erase_rename_with_const (.su □ :: I)]; simp
      have lem2 := @ih2 (.su □ :: σ); simp at lem2
      rw [lem2]
      case _ =>
        intro n t h
        cases n <;> simp at *
        subst h; exists .kind
    case _ =>
      have lem2 := @ih2 (^σ); simp at lem2
      rw [lem2, lem, lem, Subst.map_rename_compose_left erase_rename_commute]
      apply And.intro ih1; rfl
  case _ ih1 ih2 =>
    have lem2 := @ih2 (^σ); simp at lem2
    rw [lem2, lem, lem, Subst.map_rename_compose_left erase_rename_commute]
    apply And.intro ih1; rfl
  case _ ih _ => apply ih
  case _ ih => apply ih
  case _ ih => apply ih
  case _ ih1 ih2 =>
    have lem2 := @ih2 (^σ); simp at lem2
    rw [lem2, lem, lem, Subst.map_rename_compose_left erase_rename_commute]
    apply And.intro ih1; rfl
  case _ ih1 ih2 => apply And.intro ih1 ih2
  case _ ih => apply ih
  case _ ih _ _ => apply ih
  case _ ih => apply ih

  theorem erase_beta {b t : Term} : (b β[t]).erase = b.erase β[t.erase] := by
  have lem := @erase_subst (.su t :: I) b; simp at lem
  apply lem

end Cedille2
