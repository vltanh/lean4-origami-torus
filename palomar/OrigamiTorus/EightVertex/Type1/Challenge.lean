module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions.SumProd
import Mathlib.Tactic

/-!
# Type 1 origami tori

A flat embedded realization of the Type 1 face list is impossible.
The valence-three vertex has label 0.
-/

@[expose] public section

namespace OrigamiTorus

abbrev Vertex := Fin 8
abbrev Triangle := Vertex × Vertex × Vertex
abbrev Edge := Vertex × Vertex

def triangleVertices (f : Triangle) : List Vertex := [f.1, f.2.1, f.2.2]

abbrev Point3 := ℝ × ℝ × ℝ

def triangleVertexSet (f : Triangle) : Finset Vertex := (triangleVertices f).toFinset

def faceWeights (s : Finset Vertex) : Set (Vertex → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ ∀ i ∉ s, w i = 0}

def triangleWeightSpace (fs : List Triangle) : Set (Vertex → ℝ) :=
  {w | ∃ f ∈ fs, w ∈ faceWeights (triangleVertexSet f)}

noncomputable def evaluateWeights (q : Vertex → Point3) (w : Vertex → ℝ) : Point3 :=
  ∑ i, w i • q i

noncomputable def evaluateTriangles (fs : List Triangle) (q : Vertex → Point3)
    (w : triangleWeightSpace fs) : Point3 := evaluateWeights q w.val

namespace Type2

def euclideanPoint : Point3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun p := WithLp.toLp _ ![p.1,p.2.1,p.2.2]
  map_add' p q := by ext i; fin_cases i <;> rfl
  map_smul' r p := by ext i; fin_cases i <;> rfl

end Type2

open InnerProductGeometry

/-- The two rays at a face corner in cyclic face order. -/
def cornerRays (v : Vertex) (f : Triangle) : Option Edge :=
  let (a,b,c) := f
  if v = a then some (b,c) else if v = b then some (c,a) else if v = c then some (a,b) else none

/-- Sum the Euclidean face angles at a labeled vertex of a spatial or planar placement. -/
noncomputable def coneAngles {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (fs : List Triangle) (q : Vertex → E) (v : Vertex) : ℝ :=
  (fs.map fun f => match cornerRays v f with
    | none => 0
    | some (a,b) => angle (q a-q v) (q b-q v)).sum

namespace Type1

theorem vertexCount_neZero : NeZero 8 := @Nat.instNeZeroSucc 7

/-- The Lutz Type 1 face list, with the valence-three vertex labeled 0. -/
def faces : List Triangle :=
  letI : NeZero 8 := vertexCount_neZero
  [(0,1,2),(0,3,1),(0,2,3),(1,4,2),(1,3,5),(1,6,4),(1,5,7),(1,7,6),
   (2,6,3),(2,4,7),(2,5,6),(2,7,5),(3,4,5),(3,7,4),(3,6,7),(4,6,5)]

end Type1

end OrigamiTorus

namespace OrigamiTorusType1Challenge

open OrigamiTorus

/-- Every embedded Lutz Type 1 realization has a vertex with nonzero angle defect. -/
theorem type1_nonexistence (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles Type1.faces q)) :
    ¬ ∀ v, coneAngles Type1.faces (Type2.euclideanPoint ∘ q) v = 2 * Real.pi := by
  sorry

end OrigamiTorusType1Challenge
