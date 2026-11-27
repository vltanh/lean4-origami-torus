module

public import OrigamiTorus.EightVertex.Type7.WideData
import Mathlib.Tactic

/-! Kernel replay of the disjoint edge–face tests for Type 7 height cell 1. -/

public section

namespace OrigamiTorus.Type7

set_option maxHeartbeats 0 in
check_wide_chunks widerPairs1 for 29 using stripPairChunk with (widerPairCheck 1)

end OrigamiTorus.Type7
