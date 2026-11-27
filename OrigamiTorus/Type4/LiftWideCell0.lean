module

public import OrigamiTorus.Type4.LiftWideData
import Mathlib.Tactic

/-! Kernel replay of the Type 4 height cell indexed by 0. -/

public section

namespace OrigamiTorus.Type4.StripLift

set_option maxHeartbeats 0 in
check_wide_chunks widePairChunks0 for 28 using pairChunk with (pairCheckWide 0)
set_option maxHeartbeats 0 in
check_wide_chunks wideAreaChunks0 for 14 using tetrahedronChunk with (areaCheckWide 0)

end OrigamiTorus.Type4.StripLift
