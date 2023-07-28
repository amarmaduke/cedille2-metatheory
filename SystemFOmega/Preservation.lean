
-- import Cedille2Lean.SystemFOmega.Def

-- namespace SystemFOmega

--   -- #check SystemFOmega.Infer.rec

--   theorem preservation_type : Γ ⊢ t >: A -> A -β> A' -> Γ ⊢ t >: A' :=
--     λ j1 j2 => @SystemFOmega.ConInfer.rec
--       (λ Γ t A j => True)
--       (λ Γ t A j => A -β> A' -> ConInfer Γ t A')
--       (λ Γ t A j => True)
--       (λ Γ wf => True)
--       (by simp)
--       (by simp)
--       (by simp)
--       (by simp)
--       (by simp)
--       (by simp)
--       (by {
--         simp
--         intros Γ t A B ih1 ih2 ih3
--         have lem1 : A -β>* A' := sorry -- by transitivity
--         apply (ConInfer.infer ih1 lem1)
--       })
--       (by simp)
--       (by simp)
--       (by simp)
--       (Γ)
--       (t)
--       (A)
--       (j1)
--       (j2)

--   theorem preservation : Γ ⊢ t =: A -> t -β> t' -> Γ ⊢ t' =: A := by {
--     intros j1 j2
--     induction j2
--     case beta t1 t2 t3 => {
--       sorry
--     }
--     case bind1 t1 t2 k t3 step ih => {

--     }
--   }


-- end SystemFOmega



