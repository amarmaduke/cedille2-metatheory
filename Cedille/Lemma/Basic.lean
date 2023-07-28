
import Cedille.Def

namespace Cedille

  @[simp] def open_bound_0 : {_|-> x}(@bound 1 0) = free x := by {
      unfold HasHOpen.hopn; unfold Syntax.instHasHOpenSyntax; simp
      unfold Syntax.opn_head; simp; unfold bound; simp; unfold free; simp
  }

end Cedille
