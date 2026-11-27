module

public import OrigamiTorus.Type7.WideData
import Mathlib.Tactic

/-! Kernel replay of the disjoint edge–face tests for Type 7 height cell 3. -/

public section

namespace OrigamiTorus.Type7

set_option maxHeartbeats 0 in
check_wide_chunks widerPairs3 for 29 using stripPairChunk with (widerPairCheck 3)

end OrigamiTorus.Type7
