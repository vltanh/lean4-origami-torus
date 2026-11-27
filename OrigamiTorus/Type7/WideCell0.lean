module

public import OrigamiTorus.Type7.WideData
import Mathlib.Tactic

/-! Kernel replay of the disjoint edge–face tests for Type 7 height cell 0. -/

public section

namespace OrigamiTorus.Type7

set_option maxHeartbeats 0 in
check_wide_chunks widerPairs0 for 29 using stripPairChunk with (widerPairCheck 0)

end OrigamiTorus.Type7
