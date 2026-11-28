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
# Type 4 origami tori

The Type 4 face complex admits a piecewise-isometric embedding throughout
the reduced strip with real part strictly below one half. The spatial angle
and marked modulus map has rank nine at the embedding.
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

def faces : List Triangle :=
  [(3,5,6), (3,2,5), (3,6,4), (3,0,2), (3,4,1), (3,1,0), (5,0,6), (5,2,4),
    (5,4,7), (5,7,0), (6,7,4), (6,0,1), (6,1,7), (2,1,4), (2,0,7), (2,7,1)]

def flippedFaces : List Triangle :=
  faces.filter (fun f => f != (3,5,6) && f != (3,2,5)) ++ [(6,3,2), (6,2,5)]

end Type7

namespace Type4

open Type7 (triangleCorner)

-- The face list and the marking are developed in separate library modules.
-- Name the marking's instance proof explicitly for the standalone comparison.
theorem flippedMarkingDisplacements._proof_1 : type_of% (@Nat.instNeZeroSucc 7) := @Nat.instNeZeroSucc 7

/-- Period displacements developed across the flipped diagonal in the chart at 26. -/
noncomputable def flippedMarkingDisplacements (s : Vertex → Vertex → ℝ) : ℂ × ℂ :=
  letI : NeZero 8 := flippedMarkingDisplacements._proof_1
  let z₃ := triangleCorner s true 2 6 3
  let z₅ := triangleCorner s false 2 6 5
  let z₄ := z₅-z₅*triangleCorner s true 5 2 4
  let z₀ := z₃*triangleCorner s true 2 3 0
  let z₄' := z₃+(1-z₃)*triangleCorner s true 3 6 4
  let z₀' := 1+(z₅-1)*triangleCorner s true 6 5 0
  (z₄'-z₄,z₀-z₀')

noncomputable def flippedMarkedShape (s : Vertex → Vertex → ℝ) : ℂ :=
  (flippedMarkingDisplacements s).2/(flippedMarkingDisplacements s).1

/-- Seven cone angles and the complex marked modulus as functions of the
eight spatial vertex positions. -/
noncomputable def spatialAngleShape (q : Vertex → Point3) : (Fin 7 → ℝ) × ℂ :=
  (sevenConeAngles Type7.flippedFaces (Type2.euclideanPoint ∘ q),
    flippedMarkedShape (Type7.spatialEdgeSq q))

/-- The spatial angle and modulus map is locally smooth and has rank nine. -/
def SpatiallyRegular (q : Vertex → Point3) : Prop :=
  ContDiffAt ℝ 1 spatialAngleShape q ∧ Function.Surjective (fderiv ℝ spatialAngleShape q)

end Type4

end OrigamiTorus

namespace OrigamiTorusType4Challenge

open OrigamiTorus

/-- On the reduced strip, the seven cone angles and complex marked modulus
have surjective joint spatial derivative at the vertices of the Type 4 embedding. -/
theorem type4_regular_open_strip (x w : ℝ) (hx : 0 ≤ x) (hx' : x < 1/2) (hw : 1-x^2 ≤ w) :
    let a : ℂ := 1
    let b : ℂ := x+Real.sqrt w*Complex.I
    let fs := Type7.flippedFaces
    ∃ (H : triangleWeightSpace fs ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Type4.SpatiallyRegular Q ∧ Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles fs Q u) ∧
      (∀ f ∈ fs, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ fs, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  sorry

/-- Type 4 admits a piecewise-isometric embedding for every normalized modulus
in the open strip. The labels are those of the flipped Type 7 chart. -/
theorem type4_open_strip (x w : ℝ) (hx : 0 ≤ x) (hx' : x < 1/2) (hw : 1-x^2 ≤ w) :
    let a : ℂ := 1
    let b : ℂ := x+Real.sqrt w*Complex.I
    let fs : List Triangle :=
      [(3,6,4), (3,0,2), (3,4,1), (3,1,0), (5,0,6), (5,2,4), (5,4,7), (5,7,0),
        (6,7,4), (6,0,1), (6,1,7), (2,1,4), (2,0,7), (2,7,1), (6,3,2), (6,2,5)]
    ∃ (H : triangleWeightSpace fs ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles fs Q u) ∧
      (∀ f ∈ fs, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ fs, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  obtain ⟨H,F,Q,P,_,h⟩ := type4_regular_open_strip x w hx hx' hw
  exact ⟨H,F,Q,P,h⟩

end OrigamiTorusType4Challenge
