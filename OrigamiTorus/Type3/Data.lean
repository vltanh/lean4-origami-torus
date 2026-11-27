module

public import OrigamiTorus.Type6.Data

/-! The edge table and disjoint edge–face tests for the published Type 3 triangulation. -/

@[expose] public section

namespace OrigamiTorus.Type3

/-- The published diagonal is 12, in the slot occupied by 05 after the flip. -/
def edgeTable (e : EdgeIndex) : Edge × Period :=
  if e = 4 then ((1,2),0) else edgePeriod e

def disjointPairs : List (Edge × Triangle) :=
  (type3Faces.flatMap faceEdges).eraseDups.flatMap fun e =>
    (type3Faces.filter fun f =>
      !(triangleVertices f).contains e.1 && !(triangleVertices f).contains e.2).map (e, ·)

theorem disjointPairs_count : disjointPairs.length = 138 := by decide +kernel

end OrigamiTorus.Type3
