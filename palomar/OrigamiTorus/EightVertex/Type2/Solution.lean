module

public import OrigamiTorus.EightVertex.Type2.Nonexistence
import OrigamiTorus.EightVertex.Type2.Certificate

public section

namespace OrigamiTorusType2Challenge

open OrigamiTorus

/-- Every embedded Lutz Type 2 realization has a vertex with nonzero angle defect. -/
theorem type2_nonexistence (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles Type2.geometricFaces q)) :
    ¬ ∀ v, ((Type2.incidentCorners v).map (Type2.cornerAngle q v)).sum = 2 * Real.pi := by
  intro hflat
  apply Type2.type2_nonexistence q h
  intro v
  rw [Type2.linkPerimeter_eq_coneAngle]
  exact hflat v

/-- No assignment satisfies the Type 2 determinant-sign formula. -/
theorem type2_sign_obstruction (a : Nat → Bool) :
    ¬ ∀ c ∈ OrigamiTorus.Type2.signClauses, ∃ l ∈ c, a l.1 = l.2 :=
  OrigamiTorus.Type2.type2_signsImpossible a

end OrigamiTorusType2Challenge
