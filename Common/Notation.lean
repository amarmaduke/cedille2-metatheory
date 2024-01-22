
import Common.Name

class HasSubst (α : Sort _) (β : Sort _) where
  subst : Name -> α -> β -> β
notation:200 "[" v:200 " := " w:200 "]" t:200 => HasSubst.subst v w t

class HasOpen (α : Sort _) where
  opn : Nat -> α -> α -> α
notation:200 "{" i:200 " |-> " v:200 "}" t:200 => HasOpen.opn i v t

class HasClose (α : Sort _) where
  cls : α -> Name -> α -> α
notation:200 "{" i:200 " <-| " v:200 "}" t:200 => HasClose.cls i v t
