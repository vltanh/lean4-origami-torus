module

public import OrigamiTorus.EightVertex.Type1.Nonexistence

public section

namespace OrigamiTorusType1Challenge

open OrigamiTorus

/-- Every embedded Lutz Type 1 realization has a vertex with nonzero angle defect. -/
theorem type1_nonexistence (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles Type1.faces q)) :
    ¬ ∀ v, coneAngles Type1.faces (Type2.euclideanPoint ∘ q) v = 2 * Real.pi :=
  Type1.nonexistence q h

end OrigamiTorusType1Challenge
