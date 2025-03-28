import Mathlib.SetTheory.ZFC.Basic

namespace Classical

  noncomputable def image B := @ZFSet.image B (Classical.allZFSetDefinable _)

end Classical
