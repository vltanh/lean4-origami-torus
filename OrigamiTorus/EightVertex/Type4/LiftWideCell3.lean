module

public import OrigamiTorus.EightVertex.Type4.LiftWideData
import Mathlib.Tactic

/-! Kernel replay of the Type 4 height cell indexed by 3. -/

public section

namespace OrigamiTorus.Type4.StripLift

set_option maxHeartbeats 0 in
check_wide_chunks widePairChunks3 for 28 using pairChunk with (pairCheckWide 3)
set_option maxHeartbeats 0 in
check_wide_chunks wideAreaChunks3 for 14 using tetrahedronChunk with (areaCheckWide 3)

end OrigamiTorus.Type4.StripLift
