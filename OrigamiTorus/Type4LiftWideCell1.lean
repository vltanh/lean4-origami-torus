module

public import OrigamiTorus.Type4LiftWideData
import Mathlib.Tactic

/-! Kernel replay of the Type 4 height cell indexed by 1. -/

public section

namespace OrigamiTorus.Type4.StripLift

set_option maxHeartbeats 0 in
check_wide_chunks widePairChunks1 for 28 using pairChunk with (pairCheckWide 1)
set_option maxHeartbeats 0 in
check_wide_chunks wideAreaChunks1 for 14 using tetrahedronChunk with (areaCheckWide 1)

end OrigamiTorus.Type4.StripLift
