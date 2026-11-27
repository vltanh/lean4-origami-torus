module

public import OrigamiTorus.SevenVertex.Nonexistence

public section

namespace OrigamiTorusSevenVertexChallenge

open OrigamiTorus

/-- Every embedded seven-vertex torus triangulation has a vertex with nonzero angle defect. -/
theorem seven_vertex_nonexistence (fs : SevenVertex.Faces)
    (hf : SevenVertex.IsTorusTriangulation fs) (q : SevenVertex.Label → Point3)
    (he : Function.Injective (SevenVertex.evaluate fs q)) :
    ¬ ∀ v, SevenVertex.angleSum fs q v = 2 * Real.pi :=
  SevenVertex.nonexistence fs hf q he

end OrigamiTorusSevenVertexChallenge
