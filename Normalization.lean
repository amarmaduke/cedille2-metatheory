
import Common
import Cedille
import SystemFOmega

def interpret {n} (t : Term n) : ωTerm n :=
  match t with
  | Syntax.bound i => Syntax.bound i
  | Syntax.free x => Syntax.free x -- todo fix
  | Syntax.const (Cedille.Constant.typeU) => Syntax.const (SystemFOmega.Constant.typeU)
  | Syntax.const (Cedille.Constant.kindU) => Syntax.const (SystemFOmega.Constant.typeU)
  | Syntax.bind (Cedille.Binder.lam m) t1 t2 =>
    Syntax.bind (SystemFOmega.Binder.lam) (interpret t1) (interpret t2)
  | Syntax.bind (Cedille.Binder.pi m) _ _ =>
    match m with
    | Cedille.Mode.free => sorry
    | Cedille.Mode.type => sorry
    | Cedille.Mode.erased => sorry
  | Syntax.bind Cedille.Binder.inter _t1 _t2 => sorry
  | Syntax.ctor (Cedille.Constructor.app m) t1 t2 _ =>
    match m with
    | Cedille.Mode.free => interpret t1
    | Cedille.Mode.type => Syntax.ctor
      (SystemFOmega.Constructor.app)
      (interpret t1) (interpret t2) (Syntax.const (SystemFOmega.Constant.kindU))
    | Cedille.Mode.erased => interpret t1
  | Syntax.ctor Cedille.Constructor.pair _ _ _ => sorry
  | Syntax.ctor Cedille.Constructor.fst _ _ _ => sorry
  | Syntax.ctor Cedille.Constructor.snd _ _ _ => sorry
  | Syntax.ctor Cedille.Constructor.eq _ _ _ => sorry
  | Syntax.ctor Cedille.Constructor.refl _ _ _ => sorry
  | Syntax.ctor Cedille.Constructor.eqind _ _ _ => sorry
  | Syntax.ctor Cedille.Constructor.j0 _ _ _ => sorry
  | Syntax.ctor Cedille.Constructor.jω _ _ _ => sorry
  | Syntax.ctor Cedille.Constructor.promote _ _ _=> sorry
  | Syntax.ctor Cedille.Constructor.delta _ _ _ => sorry
  | Syntax.ctor Cedille.Constructor.phi _ b _ => interpret b

notation:4000 "⟦" t:4000 "⟧" => interpret t

