module

public import OrigamiTorus.Type4.LiftWideData
import Mathlib.Tactic

/-! Kernel replay of the Type 4 height cell indexed by 4. -/

public section

namespace OrigamiTorus.Type4.StripLift

set_option maxHeartbeats 0 in
check_wide_chunks widePairChunks4 for 28 using pairChunk with (pairCheckWide 4)
set_option maxHeartbeats 0 in
check_wide_chunks wideAreaChunks4 for 14 using tetrahedronChunk with (areaCheckWide 4)

end OrigamiTorus.Type4.StripLift
