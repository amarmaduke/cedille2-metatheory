import Cedille.Def
import Cedille.Lemma.Basic
import Cedille.Lemma.Refold
import Cedille.Lemma.Erasure
import Cedille.Lemma.Inversion
import Cedille.Lemma.Syntax

namespace Cedille

  lemma subst_hsubst_commute {t1 t2 : Term n} {t3 : Term (n + 1)} :
    [x := t1][_:= t2]t3 = [_:= [x := t1]t2][x := t1ʷ]t3
  := by sorry

  lemma sanity_subst {S : FvSet!} :
    Sane a ->
    (∀ x, x ∉ S -> Sane ({_|-> x}f)) ->
    Sane ([_:= a]f)
  := by sorry

end Cedille
