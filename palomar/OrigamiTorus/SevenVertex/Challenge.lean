module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Tactic

/-! Nonexistence of a paper torus with seven vertices. -/

@[expose] public section

namespace OrigamiTorus

abbrev Point3 := ℝ × ℝ × ℝ

namespace Type2

def euclideanPoint : Point3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun p := WithLp.toLp _ ![p.1,p.2.1,p.2.2]
  map_add' p q := by ext i; fin_cases i <;> rfl
  map_smul' r p := by ext i; fin_cases i <;> rfl

end Type2

namespace SevenVertex

open InnerProductGeometry

abbrev Label := Fin 7
abbrev Faces := Finset (Finset Label)

/-- The number of faces containing the edge `e`. -/
def incidence (fs : Faces) (e : Finset Label) : ℕ :=
  (fs.filter (e ⊆ ·)).card

/-- Combinatorial conditions satisfied by a simplicial triangulation of the
torus on seven vertices. Each triangle is recorded by its set of labels.
The face count comes from Euler characteristic zero and two faces per edge. -/
def IsTorusTriangulation (fs : Faces) : Prop :=
  (∀ f ∈ fs, f.card = 3) ∧ fs.card = 14 ∧
    ∀ e : Finset Label, e.card = 2 → incidence fs e = 0 ∨ incidence fs e = 2

/-- The union of the barycentric simplices of the triangulation. -/
def weightSpace (fs : Faces) : Set (Label → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ ∃ f ∈ fs, ∀ i ∉ f, w i = 0}

/-- The piecewise-affine realization with the given vertex positions. -/
noncomputable def evaluate (fs : Faces) (q : Label → Point3)
    (w : weightSpace fs) : Point3 :=
  ∑ i, w.val i • q i

/-- The cone angle at a vertex. Each incident triangle contributes the angle
between its other two vertices. The inner sum counts both orders. -/
noncomputable def angleSum (fs : Faces) (q : Label → Point3) (v : Label) : ℝ :=
  let p := Type2.euclideanPoint ∘ q
  ∑ f ∈ fs, if v ∈ f then
    (∑ a ∈ f.erase v, ∑ b ∈ (f.erase v).erase a, angle (p a - p v) (p b - p v)) / (↑(2 : ℕ) : ℝ)
  else 0

end SevenVertex

end OrigamiTorus

namespace OrigamiTorusSevenVertexChallenge

open OrigamiTorus

/-- Every embedded seven-vertex torus triangulation has a vertex with nonzero angle defect. -/
theorem seven_vertex_nonexistence (fs : SevenVertex.Faces)
    (hf : SevenVertex.IsTorusTriangulation fs) (q : SevenVertex.Label → Point3)
    (he : Function.Injective (SevenVertex.evaluate fs q)) :
    ¬ ∀ v, SevenVertex.angleSum fs q v = 2 * Real.pi := by
  sorry

end OrigamiTorusSevenVertexChallenge
