-- import Untyped.Subst

-- inductive ValueVariant : Type where
-- | term | spine

-- inductive Value : ValueVariant -> Type where
-- | nil : Value .spine
-- | cons : Value .term -> Value .spine -> Value .spine
-- | var : Nat -> Value .spine -> Value .term
-- | lam : Value .term -> Value .spine -> Value .term
-- deriving Repr

-- namespace Value
--   @[simp]
--   def concat : Value .spine -> Value .spine -> Value .spine
--   | .nil, sp => sp
--   | .cons hd tl, sp => .cons hd (concat tl sp)

--   @[simp]
--   def add_spine : Value .term -> Value .spine -> Value .term
--   | .var x s1, s2 => .var x (concat s1 s2)
--   | .lam t s1, s2 => .lam t (concat s1 s2)

--   @[simp]
--   def smap (lf : Subst.Lift (∀ {v}, Value v)) (f : Nat -> Subst.Action (∀ {v}, Value v)) : ∀ {v}, Value v -> Value v
--   | _, nil => sorry
--   | _, cons hd tl => sorry
--   | _, var x sp =>
--     let sp := smap lf f sp
--     match f x with
--     | .re y => var y sp
--     | .su t => t.add_spine sp
--   | _, lam t sp => lam (smap lf (lf f) t) (smap lf f sp)
-- end Value

-- @[simp]
-- instance substType_Value : SubstitutionType Value where
--   smap := Value.smap

-- namespace Value

--   @[simp] -- 0[s.σ ] = s
--   theorem subst_var_replace
--     : [.su s :: σ]var 0 sp = s.add_spine sp
--   := by sorry

--   @[simp] -- 0[s.σ ] = s
--   theorem subst_var_rename
--     : [.re k :: σ]var 0 sp = var k (List.map (Subst.apply (.re k :: σ)) sp)
--   := by sorry

--   @[simp]
--   theorem subst_lam : [σ](lam t sp) = lam ([^σ]t) (List.map (Subst.apply σ) sp)  := by sorry

--   theorem apply_id {t : Value} : [I]t = t := by
--   have lem : ^I = @I Value := by
--     funext; case _ x =>
--     cases x; all_goals (unfold Subst.lift; unfold I; simp)
--   induction t
--   all_goals (simp at * <;> try simp [*])
--   unfold Subst.apply; unfold I; simp

--   theorem apply_stable {r : Ren} {σ : Subst Value} : r.to = σ -> r.apply = σ.apply := by sorry
--   -- intro h; funext; case _ x =>
--   --   unfold Ren.apply; simp at *
--   --   unfold Ren.to; simp
--   --   induction x generalizing r σ <;> simp at *
--   --   case _ x => unfold Subst.apply; simp; rw [<-h]; unfold Ren.to; simp
--   --   case _ => simp [*]
--   --   case _ =>
--   --     simp [*]; rw [Subst.lift_lemma, <-h]
--   --     unfold Ren.fro; simp

--   theorem apply_compose {s : Value} {σ τ : Subst Value} : [τ][σ]s = [τ ⊙ σ]s := by
--     solve_compose Value, apply_stable, s, σ, τ

-- end Value

-- instance substTypeLaws_Value : SubstitutionTypeLaws Value where
--   apply_id := Value.apply_id
--   apply_compose := Value.apply_compose
--   apply_stable := Value.apply_stable
