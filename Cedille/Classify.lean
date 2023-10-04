
import Cedille.Def

namespace Cedille

  inductive Class where
  | kind : Class
  | type : Class
  | term : Class

  namespace Class
    def demote (c : Class) : Class :=
      match c with
      | kind => type
      | type => term
      | term => term

    @[simp] lemma demote_kind : demote kind = type := by congr
    @[simp] lemma demote_type : demote type = term := by congr
    @[simp] lemma demote_term : demote term = term := by congr
  end Class

  def classify_inner (t : Term 0) (Γ : Map! Class) : Class :=
    match t with
    | Syntax.bound _i => Class.kind
    | Syntax.free x =>
      if h : Map.mem Γ x
      then Class.demote (Map.lookup Γ x h)
      else Class.kind
    | Syntax.const (Constant.typeU) => Class.kind
    | Syntax.const (Constant.kindU) => Class.kind
    | Syntax.bind (Binder.lam m) _ _ =>
      match m with
      | Mode.free => Class.term
      | Mode.type => Class.type
      | Mode.erased => Class.term
    | Syntax.bind (Binder.pi m) _ _ =>
      match m with
      | Mode.free => Class.type
      | Mode.type => Class.kind
      | Mode.erased => Class.type
    | Syntax.bind Binder.inter _t1 _t2 => Class.type
    | Syntax.ctor (Constructor.app m) _ _ _ =>
      match m with
      | Mode.free => Class.term
      | Mode.type => Class.type
      | Mode.erased => Class.term
    | Syntax.ctor Constructor.pair _ _ _ => Class.term
    | Syntax.ctor Constructor.fst _ _ _ => Class.term
    | Syntax.ctor Constructor.snd _ _ _ => Class.term
    | Syntax.ctor Constructor.eq _ _ _ => Class.type
    | Syntax.ctor Constructor.refl _ _ _ => Class.term
    | Syntax.ctor Constructor.eqind _ _ _ => Class.term
    | Syntax.ctor Constructor.promote _ _ _=> Class.term
    | Syntax.ctor Constructor.delta _ _ _ => Class.term
    | Syntax.ctor Constructor.phi _ _ _ => Class.term

  def classify_map (m : Map! (Term 0)) : Map! Class :=
    List.foldl (λ acc (x, t) =>
      let t' := classify_inner t acc
      (x, t') :: acc)
      List.nil m

  def classify (t : Term 0) (m : Map! (Term 0)) : Class :=
    let m := classify_map m
    classify_inner t m

  -- @[simp] lemma classify_free : classify (free x) Γ = k
  --   -> (if h : Map.mem (classify_map Γ) x = true
  --     then Class.demote (Map.lookup (classify_map Γ) x h)
  --     else Class.kind)
  --     = k
  -- := by
  --   intro h
  --   unfold classify at h
  --   unfold classify' at h
  --   unfold free at h
  --   simp at h
  --   exact h

  -- @[simp] lemma classify_typeu : classify typeu Γ = Class.kind := by congr
  -- @[simp] lemma classify_lam : classify (lam t1 t2) Γ = Class.term := by congr
  -- @[simp] lemma classify_tlam : classify (tlam t1 t2) Γ = Class.type := by congr
  -- @[simp] lemma classify_elam : classify (elam t1 t2) Γ = Class.term := by congr
  -- @[simp] lemma classify_epi : classify (epi t1 t2) Γ = Class.type := by congr
  -- @[simp] lemma classify_inter : classify (inter t1 t2) Γ = Class.type := by congr
  -- @[simp] lemma classify_app : classify (t1 ⬝ t2) Γ = k -> classify t1 Γ = k := by intro h; congr
  -- @[simp] lemma classify_eapp : classify (eapp t1 t2) Γ = Class.term := by congr
  -- @[simp] lemma classify_pair : classify (pair t1 t2) Γ = Class.term := by congr
  -- @[simp] lemma classify_fst : classify (fst t1 t2 t3) Γ = Class.term := by congr
  -- @[simp] lemma classify_snd : classify (snd t1 t2 t3) Γ = Class.term := by congr
  -- @[simp] lemma classify_eq : classify (eq t1 t2 t3) Γ = Class.type := by congr
  -- @[simp] lemma classify_refl : classify (refl t1 t2) Γ = Class.term := by congr
  -- @[simp] lemma classify_eqind : classify (J t1 t2 t3 t4 t5 t6) Γ = Class.term := by congr
  -- @[simp] lemma classify_promote : classify (promote t1 t2 t3 t4 t5) Γ = Class.term := by congr
  -- @[simp] lemma classify_deltatop : classify (deltatop t1 t2 t3) Γ = Class.term := by congr
  -- @[simp] lemma classify_deltabot : classify (deltabot t1) Γ = Class.term := by congr
  -- @[simp] lemma classify_phi : classify (phi t1 t2 t3 t4 t5) Γ = Class.term := by congr

  -- lemma classify_map_preserves_fv : Map.mem Γ x = true -> Map.mem (classify_map Γ) x = true := by
  --   sorry

  -- lemma classify_map_classified : (⊢ Γ)
  --   -> (h : Map.mem (classify_map Γ) x = true)
  --   -> (Map.lookup (classify_map Γ) x h = Class.type) ∨ (Map.lookup (classify_map Γ) x h = Class.kind)
  -- := by sorry

  theorem classify_kind : Γ ⊢ t : A -> classify t Γ = Class.kind -> A = kindu := by sorry
  --   intro wf jd cl
  --   induction jd <;> try (simp <;> simp at cl <;> simp [*] <;> contradiction)
  --   case var Γ1 x A' h1 h2 => {
  --     have cl' := classify_free cl
  --     have h' := classify_map_preserves_fv h1
  --     simp [*] at cl'
  --     have h3 := classify_map_classified wf h'
  --     cases h3
  --     case inr h4 => {
  --       simp [*] at cl'
  --     }
  --     case inl h4 => {
  --       simp [*] at cl'
  --     }
  --   }
  --   case conv j1 j2 j3 ih1 ih2 => {
  --     have lem1 := ih1 wf cl
  --     subst lem1
  --     sorry
  --   }
  --   case pi j1 j2 ih1 ih2 => {
  --     sorry
  --   }
  --   case app j1 j2 ih1 ih2 => {
  --     have lem1 := classify_app cl
  --     have lem2 := ih1 wf lem1
  --     contradiction
  --   }

  theorem classify_type : Γ ⊢ t : A -> classify t Γ = Class.type -> Γ ⊢ A >: kindu := by sorry
  --   intro wf jd cl
  --   induction jd <;> try (simp; simp at cl <;> simp [*] <;> contradiction)
  --   case var => sorry
  --   case conv j1 j2 j3 ih1 ih2 => {
  --     have lem1 := ih1 wf cl
  --     sorry
  --   }
  --   case pi => sorry
  --   case tpi => sorry
  --   case epi => sorry
  --   case app => sorry
  --   case inter => sorry
  --   case eq => sorry

  theorem classify_term : Γ ⊢ t : A -> classify t Γ = Class.term -> Γ ⊢ A >: typeu := sorry


end Cedille