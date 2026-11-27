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
# Type 6 origami tori

The Type 6 face complex admits a piecewise-isometric embedding of every
rank-two lattice torus. The marked-modulus and seven-angle map has rank
nine at the same spatial placement.
-/

@[expose] public section

namespace OrigamiTorus

abbrev Vertex := Fin 8
abbrev Triangle := Vertex × Vertex × Vertex
abbrev Edge := Vertex × Vertex

def type3Faces : List Triangle :=
  [(0,1,2), (0,3,1), (0,2,4), (0,4,3), (1,5,2), (1,3,6), (1,4,5), (1,7,4),
   (1,6,7), (2,6,4), (2,5,7), (2,7,6), (3,4,7), (3,5,6), (3,7,5), (4,6,5)]

def type6FlippedFaces : List Triangle :=
  type3Faces.filter (fun f => f != (0,1,2) && f != (1,5,2)) ++ [(0,1,5), (0,5,2)]

abbrev Period := ℤ × ℤ
abbrev EdgeIndex := Fin 24

/-- The second endpoint uses this translate relative to the first, in the basis
`(1,0),(x,y)`. Edges are sorted in the flipped Type 3 labeling. -/
def edgePeriod : EdgeIndex → Edge × Period :=
  letI : NeZero 8 := @Nat.instNeZeroSucc 7
  ![((0,1),(0,0)), ((0,2),(0,0)), ((0,3),(0,0)), ((0,4),(0,-1)), ((0,5),(0,0)),
    ((1,3),(0,0)), ((1,4),(0,0)), ((1,5),(0,0)), ((1,6),(0,0)), ((1,7),(0,0)),
    ((2,4),(0,-1)), ((2,5),(0,0)), ((2,6),(-1,0)), ((2,7),(-1,0)),
    ((3,4),(0,-1)), ((3,5),(1,-1)), ((3,6),(0,0)), ((3,7),(0,-1)),
    ((4,5),(0,0)), ((4,6),(-1,1)), ((4,7),(0,0)),
    ((5,6),(-1,1)), ((5,7),(-1,0)), ((6,7),(0,0))]

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

def complexLattice (u v : ℂ) : Set ℂ :=
  {p | ∃ m n : ℤ, (m : ℂ)*u+(n : ℂ)*v=p}

def complexPeriodSubgroup (u v : ℂ) : AddSubgroup ℂ where
  carrier := complexLattice u v
  zero_mem' := ⟨0,0,by simp⟩
  add_mem' := by
    rintro _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    exact ⟨a+c,b+d,by push_cast; ring⟩
  neg_mem' := by
    rintro _ ⟨a,b,rfl⟩
    exact ⟨-a,-b,by push_cast; ring⟩

abbrev ComplexTorus (u v : ℂ) := ℂ ⧸ complexPeriodSubgroup u v

def complexTorusProjection (u v : ℂ) (p : ℂ) : ComplexTorus u v := p

namespace Type5

abbrev Plane (R : Type*) := R × R
abbrev Space (R : Type*) := R × R × R

def dot {R : Type*} [Ring R] (u v : Plane R) : R := u.1*v.1 + u.2*v.2
def horizontal {R : Type*} (p : Space R) : Plane R := (p.1,p.2.1)
def squared2 {R : Type*} [Ring R] (p : Plane R) : R := dot p p
def squared3 {R : Type*} [Ring R] (p : Space R) : R := squared2 (horizontal p) + p.2.2^2

end Type5

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

/-- Keep the cone angles at vertices 1 through 7. -/
noncomputable def sevenConeAngles {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (fs : List Triangle) (q : Vertex → E) (v : Fin 7) : ℝ :=
  coneAngles fs q v.succ

theorem developedTwo : Nat.AtLeastTwo 2 := ⟨by decide⟩

/-- The horizontal coordinate of a triangle corner in the chart taking its first
two corners to 0 and 1. The arguments are the squared lengths AB, AC, and BC. -/
noncomputable def developedRe (ab ac bc : ℝ) : ℝ :=
  letI : Nat.AtLeastTwo 2 := developedTwo
  (ab+ac-bc)/(2*ab)

/-- The squared height of the third triangle corner in the same chart. -/
noncomputable def developedHeightSq (ab ac bc : ℝ) : ℝ := ac/ab-(developedRe ab ac bc)^2

/-- The third vertex in the chart taking the first two vertices to 0 and 1.
The side tag chooses which half-plane contains that vertex. -/
noncomputable def developedCorner (positive : Bool) (ab ac bc : ℝ) : ℂ :=
  (developedRe ab ac bc : ℂ) +
    ((if positive then 1 else -1) * Real.sqrt (developedHeightSq ab ac bc) : ℝ) * Complex.I

namespace Type7

noncomputable def triangleCorner (s : Vertex → Vertex → ℝ) (positive : Bool)
    (a b c : Vertex) : ℂ := developedCorner positive (s a b) (s a c) (s b c)

/-- Squared edge lengths for a spatial placement. -/
def spatialEdgeSq (q : Vertex → Point3) (a b : Vertex) : ℝ :=
  Type5.squared3 (q b-q a)

end Type7

open Type7 (triangleCorner) in
noncomputable def attachMetricCorner (s : Vertex → Vertex → ℝ) (a b c : Vertex) (A B : ℂ) : ℂ :=
  A+(B-A)*triangleCorner s true a b c

theorem type6VertexCount_neZero : NeZero 8 := @Nat.instNeZeroSucc 7

open Type7 (triangleCorner) in
/-- The two marked displacements in the chart taking vertex 1 to 0 and
vertex 7 to 1. The first strip crosses the flipped diagonal 05. -/
noncomputable def type6MetricDisplacements (s : Vertex → Vertex → ℝ) : ℂ × ℂ :=
  letI : NeZero 8 := type6VertexCount_neZero
  let z6 := triangleCorner s false 1 7 6
  let z2 := attachMetricCorner s 7 6 2 1 z6
  let z5 := attachMetricCorner s 7 2 5 1 z2
  let z0 := attachMetricCorner s 5 2 0 z5 z2
  let u := attachMetricCorner s 5 0 1 z5 z0
  let z3 := attachMetricCorner s 7 5 3 1 z5
  let z6' := attachMetricCorner s 3 5 6 z3 z5
  let v := attachMetricCorner s 3 6 1 z3 z6'
  (u,v)

/-- The marked period ratio, also defined on nearby nonflat metrics. -/
noncomputable def type6MetricShape (s : Vertex → Vertex → ℝ) : ℂ :=
  (type6MetricDisplacements s).2/(type6MetricDisplacements s).1

/-- Index the table by an unordered edge, leaving nonedges undefined. -/
def type6EdgeSlot (a b : Vertex) : Option EdgeIndex :=
  (List.finRange 24).find? fun e =>
    ((edgePeriod e).1 == (a,b)) || ((edgePeriod e).1 == (b,a))

/-- Squared distances on the labeled Type 6 spatial edges. -/
noncomputable def type6SpatialLengths (q : Vertex → Point3) (e : EdgeIndex) : ℝ :=
  Type7.spatialEdgeSq q (edgePeriod e).1.1 (edgePeriod e).1.2

noncomputable def type6SpatialLengthData (q : Vertex → Point3) (a b : Vertex) : ℝ :=
  ((type6EdgeSlot a b).map (type6SpatialLengths q)).getD 0

/-- Seven Euclidean cone angles and the marked modulus of a spatial placement. -/
noncomputable def type6SpatialAngleShape (q : Vertex → Point3) : (Fin 7 → ℝ) × ℂ :=
  (sevenConeAngles type6FlippedFaces (Type2.euclideanPoint ∘ q),
    type6MetricShape (type6SpatialLengthData q))

/-- The spatial angle and marked modulus map is locally smooth and has rank nine. -/
def Type6SpatiallyRegular (q : Vertex → Point3) : Prop :=
  ContDiffAt ℝ 1 type6SpatialAngleShape q ∧
    Function.Surjective (fderiv ℝ type6SpatialAngleShape q)

end OrigamiTorus

namespace OrigamiTorusType6Challenge

open OrigamiTorus

/-- A Type 6 realization for every flat lattice torus, regular for the joint angle and marked modulus map. -/
theorem type6_regular_universal (a b : ℂ) (ha : a ≠ 0) (hb : (b/a).im ≠ 0) :
    ∃ (H : triangleWeightSpace type6FlippedFaces ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Type6SpatiallyRegular Q ∧ Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type6FlippedFaces Q u) ∧
      (∀ f ∈ type6FlippedFaces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ type6FlippedFaces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  sorry

end OrigamiTorusType6Challenge
