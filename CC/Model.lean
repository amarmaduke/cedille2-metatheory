
import SetTheory

def BinaryFnSetoidExt {X : Sort u} {Y : Sort v} {Z : Sort w}
  (R1 : X -> X -> Prop) (R2 : Y -> Y -> Prop) (R3 : Z -> Z -> Prop)
  (f : X -> Y -> Z)
:= ∀ {x1 x2 y1 y2}, R1 x1 x2 -> R2 y1 y2 -> R3 (f x1 y1) (f x2 y2)

def BinderInnerSetoidExt {X : Sort u} (x : X) (R1 : X -> X -> Prop) (R2 : X -> X -> Prop) (f1 f2 : X -> X) :=
  ∀ {y1 y2}, R1 y1 x -> R2 y1 y2 -> R2 (f1 y1) (f2 y2)

def BinderFnSetoidExt {X : Sort u} (R1 : X -> X -> Prop) (R2 : X -> X -> Prop) (b : X -> (X -> X) -> X) :=
  ∀ {x1 x2 f1 f2}, x1 = x2 -> BinderInnerSetoidExt x1 R1 R2 f1 f2  -> b x1 f1 = b x2 f2

-- class CCModel where
--   X : Type u
--   inX : X -> X -> Prop

class CCModel where
  X : Type u
  inX : X -> X -> Prop
  props : X
  app : X -> X -> X
  lam : X -> (X -> X) -> X
  prod : X -> (X -> X) -> X
  prod_intro : ∀ dom f F,
    (∀ x, inX x dom -> inX (f x) (F x)) ->
    inX (lam dom f) (prod dom F)
  prod_elim : ∀ dom f x F,
    inX f (prod dom F) ->
    inX x dom ->
    inX (app f x) (F x)
  impredicative_prod : ∀ dom F,
    (∀ x, inX x dom -> inX (F x) props) ->
    inX (prod dom F) props
  beta_eq : ∀ dom F x,
    inX x dom ->
    app (lam dom F) x = F x

-- infix:40 "`∈" => CCModelBase.inX _

-- structure CCModel extends CCModelBase where
--   props : X
--   app : X -> X -> X
--   lam : X -> (X -> X) -> X
--   prod : X -> (X -> X) -> X

--   -- lam_ext : BinderFnSetoidExt inX eqX lam
--   -- prod_ext : BinderFnSetoidExt inX eqX prod

--   prod_intro : ∀ dom f F,
--     -- BinderInnerSetoidExt dom inX eqX f f ->
--     -- BinderInnerSetoidExt dom inX eqX F F ->
--     (∀ x, x `∈ dom -> f x `∈ F x) ->
--     lam dom f `∈ prod dom F

--   prod_elim : ∀ dom f x F,
--     -- BinderInnerSetoidExt dom inX eqX F F ->
--     f `∈ prod dom F ->
--     x `∈ dom ->
--     app f x `∈ F x

--   impredicative_prod : ∀ dom F,
--     -- BinderInnerSetoidExt dom inX eqX F F ->
--     (∀ x, x `∈ dom -> F x `∈ props) ->
--     prod dom F `∈ props

--   beta_eq : ∀ dom F x,
--     -- BinderInnerSetoidExt dom inX eqX F F ->
--     x `∈ dom ->
--     app (lam dom F) x = F x

-- theorem cc_eqX_equiv : @Equivalence ZFSet (·=·) := by sorry

-- theorem cc_in_ext : @BinaryFnSetoidExt ZFSet ZFSet Prop (·=·) (·=·) (·=·) (·∈·) := by sorry

-- def cc_props : ZFSet := ZFSet.powerset {∅}

-- noncomputable def cc_lam (A : ZFSet) (f : ZFSet -> ZFSet) :=
--   ZFSet.sUnion (Classical.image (λ A' => Classical.image (λ f' => ZFSet.pair A' f') (f A')) A)

-- theorem cc_impredicative_lam {dom : ZFSet} {F : ZFSet -> ZFSet} : (∀ x, x ∈ dom -> F x = ∅) -> cc_lam dom F = ∅ := by sorry

-- def cc_app (x y : ZFSet) := ZFSet.Rel.image (ZFSet.sep (λ p => ZFSet.fst p = y) x)

-- theorem cc_beta_eq {x dom : ZFSet} : x ∈ dom -> cc_app (cc_lam dom F) x = F x := by sorry

-- noncomputable def cc_prod (A : ZFSet) (B : ZFSet -> ZFSet) :=
--   Classical.image (λ f => cc_lam A (λ x' => ZFSet.app f x')) (ZFSet.dep_func A B)

-- theorem cc_prod_intro {dom : ZFSet} {f F : ZFSet -> ZFSet} :
--   (∀ x, x ∈ dom -> f x ∈ F x) -> cc_lam dom f ∈ cc_prod dom F
-- := by sorry

-- theorem cc_prod_elim : f ∈ cc_prod dom F -> x ∈ dom -> cc_app f x ∈ F x := by sorry

-- theorem cc_eta_eq : f ∈ cc_prod dom F -> f = cc_lam dom (λ x => cc_app f x) := by sorry

-- theorem cc_impredicative_prod {dom : ZFSet} {F : ZFSet -> ZFSet} :
--   (∀ x, x ∈ dom -> F x ∈ cc_props) -> cc_prod dom F ∈ cc_props
-- := by sorry

-- theorem cc_consistent : cc_prod cc_props (λ x => x) = ∅ := by
-- apply ZFSet.ext; intro z; simp; intro h
-- have lem1 : ∅ ∈ cc_props := by unfold cc_props; simp
-- have lem2 := cc_prod_elim h lem1
-- simp at lem2

-- def zf_cc_model_base : CCModelBase := {
--   X := ZFSet
--   inX := (·∈·)
--   eqX := (·=·)
-- }

-- noncomputable def zf_cc_model : CCModel := {
--   X := ZFSet
--   inX := (·∈·)
--   eqX := (·=·)
--   eqX_equiv := cc_eqX_equiv
--   in_ext := cc_in_ext
--   props := cc_props
--   app := cc_app
--   lam := cc_lam
--   prod := cc_prod
--   app_ext := by {
--     simp; unfold BinaryFnSetoidExt; simp
--     intro _ _ _ h; subst h; rfl
--   }
--   lam_ext := by {
--     simp; unfold BinderFnSetoidExt
--     intro _ _ _ _ h1 h2
--     unfold BinderInnerSetoidExt at h2; simp at h2
--     subst h1; unfold cc_lam; apply ZFSet.ext
--     intro z; simp; sorry
--   }
--   prod_ext := by sorry
--   prod_intro := by {
--     simp; intro dom f F h1 h2 h3
--     apply cc_prod_intro h3
--   }
--   prod_elim := by {
--     simp; intro dom f x F h1 h2 h3
--     apply cc_prod_elim h2 h3
--   }
--   impredicative_prod := by {
--     simp; intro dom F h1 h2
--     apply cc_impredicative_prod h2
--   }
--   beta_eq := by {
--     simp; intro dom F x h1 h2
--     apply cc_beta_eq h2
--   }
-- }
