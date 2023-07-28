
import Common.Name

class HasSubst (α : Sort _) (β : Sort _) where
  subst : Name -> α -> β -> β
notation:200 "[" v:200 " := " w:200 "]" t:200 => HasSubst.subst v w t

class HasHSubst (α : Nat -> Sort _) (β : Nat -> Sort _) where
  hsubst : α n -> β (n + 1) -> β n
notation:200 "[_:= " w:200 "]" t:200 => HasHSubst.hsubst w t

class HasOpen (α : Nat -> Sort _) where
  opn : Fin n -> Name -> α n -> α n
notation:200 "{" i:200 " |-> " v:200 "}" t:200 => HasOpen.opn i v t

class HasHOpen (α : Nat -> Sort _) where
  hopn : Name -> α (n + 1) -> α n
notation:200 "{_|-> " v:200 "}" t:200 => HasHOpen.hopn v t

class HasClose (α : Nat -> Sort _) where
  cls : Fin n -> Name -> α n -> α n
notation:200 "{" i:200 " <-| " v:200 "}" t:200 => HasClose.cls i v t

class HasHClose (α : Nat -> Sort _) where
  hcls : Name -> α n -> α (n + 1)
notation:200 "{_<-| " v:200 "}" t:200 => HasHClose.hcls v t

-- class HasStep (α : Sort _) where
--   Step : α -> α -> Prop
-- notation:150 t1:150 " -β> " t2:150 => HasStep.Step t1 t2

-- class HasMStep (α : Sort _) where
--   MStep : α -> α -> Prop
-- notation:150 t1:150 " -β>* " t2:150 => HasMStep.MStep t1 t2

-- class HasConv (α : Sort _) where
--   Conv : α -> α -> Prop
-- notation:150 t1:150 " =β= " t2:150 => HasConv.Conv t1 t2
