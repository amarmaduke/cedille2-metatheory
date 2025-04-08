
import Common
import CC.Model
import Realizer

namespace CC

  structure Interp (X : Type) where
    i : VarMap X -> X
    tm : VarMap Realizer.Term -> Realizer.Term


  structure MakeObject (cc : CCModel) where
    ty := cc.X
    V := VarMap ty
    vnil := VarMap.nil cc.props
    term := Option (Interp ty)





end CC
