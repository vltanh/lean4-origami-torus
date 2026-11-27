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
# Eight-vertex origami torus proofs

For Lutz Types 1 and 2, no embedded realization has cone angle `2π` at every
vertex. The sign formula records the finite obstruction used in the Type 2 proof.

For the flip from Type 3 to Type 6, the two charts cover the half modular domain.
The four signed areas certify the planar diagonal flip. The second Type 6 theorem
supplies an inflated lift in general position with strict separation of
disjoint edges and faces. Its squared edge lengths match those of the
corrected intrinsic triangles with the two periods held fixed.

Two further theorems verify generic perturbation of embedded triangles
and the spatial embedding of the Type 6 lift. The existence theorems give
piecewise-isometric embeddings for every rank-two plane lattice in Types 3 and 6
and every rectangular lattice in Type 7. The strengthened Type 6 result
also verifies rank nine for the seven cone angles and two real coordinates
of the marked modulus at the same spatial placement. Two further statements
give the Type 4 embeddings on the reduced open strip and the Type 5
embedding of the unit square lattice torus.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS
namespace OrigamiTorus.Type2

def faces : List (List Nat) :=
  [[0,4,6], [0,4,7], [0,5,6], [0,5,7], [1,3,5], [1,3,6], [1,4,5], [1,4,7],
    [1,6,7], [2,3,4], [2,3,7], [2,4,5], [2,5,6], [2,6,7], [3,4,6], [3,5,7]]

def vertices : List Nat := List.range 8

/-- Increasing sublists, in lexicographic order on increasing input. -/
def choose {α : Type u} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (choose k xs).map (x :: ·) ++ choose (k + 1) xs

def quadruples : List (List Nat) := choose 4 vertices

def isEdge (u v : Nat) : Bool :=
  (u != v) && faces.any (fun f => f.contains u && f.contains v)

abbrev Sign := Nat × Bool
abbrev SignClause := List Sign

def negate (l : Sign) : Sign := (l.1, !l.2)

def inversionParity : List Nat → Bool
  | [] => false
  | a :: xs => ((xs.countP (· < a)) % 2 == 1) ^^ inversionParity xs

def insertVertex (v : Nat) : List Nat → List Nat
  | [] => [v]
  | w :: ws => if v ≤ w then v :: w :: ws else w :: insertVertex v ws

def sortVertices : List Nat → List Nat
  | [] => []
  | v :: vs => insertVertex v (sortVertices vs)

/-- Positive orientation of the listed tuple, with parity handled on unsorted input. -/
def bracket (q : List Nat) : Sign :=
  (quadruples.idxOf (sortVertices q), !inversionParity q)

def circuit (q : List Nat) : List Sign :=
  (List.range 5).map (fun i =>
    let s := bracket (q.eraseIdx i)
    if i % 2 == 0 then s else negate s)

def truthVectors : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (truthVectors n).map (false :: ·) ++ (truthVectors n).map (true :: ·)

def forbid (l : SignClause) : List SignClause := [l, l.map negate]

/-- Exclude assignments where the three nonzero terms of a Plücker relation have one sign. -/
def pluckerAt (s q : List Nat) : List SignClause :=
      match q with
      | [a,b,c,d] =>
        let l := [bracket (s ++ [a,b]), bracket (s ++ [c,d]), negate (bracket (s ++ [a,c])),
          bracket (s ++ [b,d]), bracket (s ++ [a,d]), bracket (s ++ [b,c])]
        let sameProductSign
          | [a,b,c,d,e,f] => ((a == b) == (c == d)) && ((c == d) == (e == f))
          | _ => false
        ((truthVectors 6).filter sameProductSign).map fun pat =>
          List.zipWith (fun l b => if b then negate l else l) l pat
      | _ => []

def pluckerClauses : List SignClause :=
  (choose 2 vertices).flatMap fun s =>
    (choose 4 (vertices.filter fun v => !s.contains v)).flatMap (pluckerAt s)

/-- Circuits have coefficients of both signs. Additional patterns are ruled out by
disjointness of edges and faces and strict support at each vertex among its neighbors. -/
def circuitAt (q : List Nat) : List SignClause :=
    let signs := circuit q
    let forbidPartition (side : List Nat) :=
      forbid (List.zipWith (fun l v => if side.contains v then l else negate l) signs q)
    forbid signs ++
      ((choose 2 q).filter fun e =>
        match e with
        | [a,b] => isEdge a b && faces.contains (q.filter fun v => !e.contains v)
        | _ => false).flatMap forbidPartition ++
      (q.filter fun v => (q.filter (· != v)).all (isEdge v)).flatMap
        (fun v => forbidPartition [v])

def circuitClauses : List SignClause := (choose 5 vertices).flatMap circuitAt

def markedFaces : List (Nat × List Nat) :=
  [0,1,2].flatMap fun v => (faces.filter (·.contains v)).map (v, ·)

def mixedAt (v : Nat) : List SignClause :=
    let localFaces := faces.filter (·.contains v)
    let chooseFace (f : List Nat) : Sign := (70 + markedFaces.idxOf (v,f), true)
    let witnessClauses := localFaces.flatMap fun f =>
      let selected := negate (chooseFace f)
      let signs := (vertices.filter fun w => isEdge v w && !f.contains w).map
        (fun w => bracket (f ++ [w]))
      [selected :: signs, selected :: signs.map negate]
    witnessClauses ++ [localFaces.map chooseFace]

def mixedClauses : List SignClause := [0,1,2].flatMap mixedAt

/-- The normalization chooses the orientation for which `0123` is positive. -/
def signClauses : List SignClause := [[(0, true)]] ++ pluckerClauses ++ circuitClauses ++ mixedClauses

end OrigamiTorus.Type2

namespace OrigamiTorus

abbrev Vertex := Fin 8
abbrev Triangle := Vertex × Vertex × Vertex
abbrev Edge := Vertex × Vertex
abbrev Tetrahedron := Vertex × Vertex × Vertex × Vertex

def type3Faces : List Triangle :=
  [(0,1,2), (0,3,1), (0,2,4), (0,4,3), (1,5,2), (1,3,6), (1,4,5), (1,7,4),
   (1,6,7), (2,6,4), (2,5,7), (2,7,6), (3,4,7), (3,5,6), (3,7,5), (4,6,5)]

def type6FlippedFaces : List Triangle :=
  type3Faces.filter (fun f => f != (0,1,2) && f != (1,5,2)) ++ [(0,1,5), (0,5,2)]

def triangleVertices (f : Triangle) : List Vertex := [f.1, f.2.1, f.2.2]

def orderedEdge (a b : Vertex) : Edge := (min a b, max a b)

def faceEdges (f : Triangle) : List Edge :=
  [orderedEdge f.1 f.2.1, orderedEdge f.2.1 f.2.2, orderedEdge f.2.2 f.1]

def type6DisjointPairs : List (Edge × Triangle) :=
  (type6FlippedFaces.flatMap faceEdges).eraseDups.flatMap fun e =>
    (type6FlippedFaces.filter fun f =>
      !((triangleVertices f).contains e.1 || (triangleVertices f).contains e.2)).map (e, ·)

/-- The Boolean charts index the first and second published planar families.
Here `w = y²`, where `x + iy` is the modulus. -/
def chartDomain (second : Bool) (x w : ℝ) : Prop :=
  (if second then 1 / 6 else 0) ≤ x ∧ x ≤ (if second then 1 / 2 else 1 / 6) ∧
    1 - x ^ 2 ≤ w

/-- The coordinates are `(p₁, y * p₂)`. The positive scale factor in the second coordinate
preserves orientation and all convex incidence relations. -/
def stripPoint {R : Type*} [Field R] (second : Bool) (x w : R) : Vertex → R × R :=
  let u := if second then x / 2 - 1 / 2048 else 3 / 128
  let k : R := if second then 1 / 16 else 11 / 32
  let l : R := if second then 1 / 2 else 13 / 32
  let b := 1 - x - 2 * k
  ![(0, 0), (u, u * (b + 2 * k / l)), (u - 1 / 2, (1 - 2 * u) * x / 2),
    (-k - b * l, (l * (w - b * b) - 2 * b * k) / 2),
    (x + k - 1 / 2, (w + b * x) / 2),
    (u - 1 / 2, (w + b * (b + 2 * u - 1)) / 2),
    (u - k, b * (u - k)),
    (u, (w + b * b + 2 * b * u) / 2 - (2 * u - 2 * x - 2 * k + 1) / (2 * (1 - l)))]

def area {R : Type*} [Ring R] (p : Vertex → R × R) (a b c : Vertex) : R :=
  (p b).1 * ((p c).2 - (p a).2) +
  (p c).1 * ((p a).2 - (p b).2) +
  (p a).1 * ((p b).2 - (p c).2)

/-- Affine determinant with rows `(1, p₁, y * p₂, z)`. -/
def volume {R : Type*} [Ring R] (p : Vertex → R × R) (z : Vertex → R) (a b c d : Vertex) : R :=
  -(z a) * area p b c d + z b * area p a c d - z c * area p a b d + z d * area p a b c

/-- The relevant complementary minors of the ordered tuple `a,b,c,d,e`. -/
def separates {R : Type*} [Zero R] [Mul R] [LT R] (v₀ v₁ v₂ v₃ v₄ : R) : Prop :=
  0 < v₀ * v₁ ∨ 0 < v₂ * v₃ ∨ 0 < v₃ * v₄ ∨ v₂ * v₄ < 0

def isSeparated (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (pair : Edge × Triangle) : Prop :=
  let ((a,b), (c,d,e)) := pair
  separates (volume p z b c d e) (volume p z a c d e) (volume p z a b d e)
    (volume p z a b c e) (volume p z a b c d)

/-- Distinct increasing quadruples suffice for general position by alternation. -/
def GenericLift (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) : Prop :=
  ∀ a b c d : Vertex, a < b → b < c → c < d → volume p z a b c d ≠ 0

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

/-- Unfolded coordinates on the plane before taking its lattice quotient, with the second
coordinate multiplied by `y` as in `stripPoint`. -/
def intrinsicPoint {R : Type*} [Field R] (second : Bool) (x w : R) (v : Vertex) : R × R :=
  let n (a : Nat) : R := a
  let u := if second then x / n 2 - 1 / n 2048 else n 3 / n 128
  let k := if second then 1 / n 16 else n 11 / n 32
  let l := if second then 1 / n 2 else n 13 / n 32
  let b := 1 - x - n 2 * k
  if v.val = 3 then (k, -(n 2 * b * k + l * (b*b + w)) / n 2)
  else if v.val = 6 then (u+k, b*(u-k))
  else stripPoint second x w v

def translatePoint {R : Type*} [Ring R] (x w : R) (period : Period) (p : R × R) : R × R :=
  (p.1 + period.1 + period.2 * x, p.2 + period.2 * w)

/-- The scaled distance is `w` times the actual squared planar distance when `w = y² > 0`. -/
def scaledSquaredDistance {R : Type*} [Ring R] (w : R) (p q : R × R) : R :=
  w * (q.1 - p.1)^2 + (q.2 - p.2)^2

def intrinsicEdgeSquared {R : Type*} [Field R] (second : Bool) (x w : R) (e : EdgeIndex) : R :=
  let ((a,b), d) := edgePeriod e
  let p := intrinsicPoint second x w
  scaledSquaredDistance w (p a) (translatePoint x w d (p b))

def foldedEdgeSquared {R : Type*} [Field R] (second : Bool) (x w : R) (e : EdgeIndex) : R :=
  let ((a,b), _) := edgePeriod e
  let p := stripPoint second x w
  scaledSquaredDistance w (p a) (p b)

/-- These twenty-four coordinates are allowed to move when the two lattice periods are fixed. -/
def FoldedMotion (m : Fin 24 → ℝ) : Vertex → ℝ × ℝ :=
  letI : NeZero 24 := @Nat.instNeZeroSucc 23
  ![(m 0,m 1), (m 2,m 3), (m 4,m 5), (m 6,m 7), (m 8,m 9), (m 10,m 11), (m 12,0), (0,0)]

def IntrinsicMotion (m : Fin 24 → ℝ) : Vertex → ℝ × ℝ :=
  letI : NeZero 24 := @Nat.instNeZeroSucc 23
  ![(m 13,m 14), (m 15,m 16), (m 17,m 18), (m 19,m 20), (m 21,0), (m 22,m 23), (0,0), (0,0)]

abbrev SheetMotion := Fin 24 → ℝ

noncomputable def lengthResidual (second : Bool) (x w : ℝ) (z : Vertex → ℝ)
    (s : ℝ × SheetMotion) (e : EdgeIndex) : ℝ :=
  let a := (edgePeriod e).1.1
  let b := (edgePeriod e).1.2
  let d := (edgePeriod e).2
  let p v := stripPoint second x w v + FoldedMotion s.2 v
  let q v := intrinsicPoint second x w v + IntrinsicMotion s.2 v
  scaledSquaredDistance w (p a) (p b) + w * s.1^2 * (z b - z a)^2 -
    scaledSquaredDistance w (q a) (translatePoint x w d (q b))

noncomputable def movedFoldedPoint (second : Bool) (x w : ℝ) (m : SheetMotion) (v : Vertex) :
    ℝ × ℝ :=
  stripPoint second x w v + FoldedMotion m v

end OrigamiTorus
-- END SHARED DEFINITIONS

namespace OrigamiTorus

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

theorem vertexCount_neZero : NeZero 8 := @Nat.instNeZeroSucc 7

def geometricFaces : List Triangle :=
  let v := @Fin.ofNat 8 vertexCount_neZero
  [(v 0,v 4,v 6), (v 0,v 4,v 7), (v 0,v 5,v 6), (v 0,v 5,v 7),
   (v 1,v 3,v 5), (v 1,v 3,v 6), (v 1,v 4,v 5), (v 1,v 4,v 7),
   (v 1,v 6,v 7), (v 2,v 3,v 4), (v 2,v 3,v 7), (v 2,v 4,v 5),
   (v 2,v 5,v 6), (v 2,v 6,v 7), (v 3,v 4,v 6), (v 3,v 5,v 7)]

def incidentCorners (v : Vertex) : List Edge :=
  geometricFaces.filterMap fun f =>
    let a := f.1
    let b := f.2.1
    let c := f.2.2
    if v = a then some (b,c) else if v = b then some (a,c) else
      if v = c then some (a,b) else none

def euclideanPoint : Point3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun p := WithLp.toLp _ ![p.1,p.2.1,p.2.2]
  map_add' p q := by ext i; fin_cases i <;> rfl
  map_smul' r p := by ext i; fin_cases i <;> rfl

def linkDirection (q : Vertex → Point3) (v w : Vertex) : EuclideanSpace ℝ (Fin 3) :=
  euclideanPoint (q w - q v)

noncomputable def cornerAngle (q : Vertex → Point3) (v : Vertex) (e : Edge) : ℝ :=
  InnerProductGeometry.angle (linkDirection q v e.1) (linkDirection q v e.2)

end Type2

noncomputable def physicalFoldedVertex (second : Bool) (x y : ℝ) (m : SheetMotion)
    (z : Vertex → ℝ) (t : ℝ) (i : Vertex) : Point3 :=
  let p := movedFoldedPoint second x (y^2) m i
  (p.1, p.2/y, t*z i)

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

namespace Type1

theorem vertexCount_neZero : NeZero 8 := @Nat.instNeZeroSucc 7

/-- The Lutz Type 1 face list, with the valence-three vertex labeled 0. -/
def faces : List Triangle :=
  letI : NeZero 8 := vertexCount_neZero
  [(0,1,2),(0,3,1),(0,2,3),(1,4,2),(1,3,5),(1,6,4),(1,5,7),(1,7,6),
   (2,6,3),(2,4,7),(2,5,6),(2,7,5),(3,4,5),(3,7,4),(3,6,7),(4,6,5)]

end Type1

end OrigamiTorus

namespace OrigamiTorusChallenge

open OrigamiTorus

/-- Every embedded Lutz Type 1 realization has a vertex with nonzero angle defect. -/
theorem type1_nonexistence (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles Type1.faces q)) :
    ¬ ∀ v, coneAngles Type1.faces (Type2.euclideanPoint ∘ q) v = 2 * Real.pi := by
  sorry

/-- No assignment satisfies the Type 2 determinant-sign formula. -/
theorem type2_sign_obstruction (a : Nat → Bool) :
    ¬ ∀ c ∈ OrigamiTorus.Type2.signClauses, ∃ l ∈ c, a l.1 = l.2 := by
  sorry

/-- Every embedded Lutz Type 2 realization has a vertex with nonzero angle defect. -/
theorem type2_nonexistence (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles Type2.geometricFaces q)) :
    ¬ ∀ v, ((Type2.incidentCorners v).map (Type2.cornerAngle q v)).sum = 2 * Real.pi := by
  sorry

/-- Every flat lattice torus has a piecewise-isometric Type 3 embedding. -/
theorem type3_universal (a b : ℂ) (ha : a ≠ 0) (hb : (b/a).im ≠ 0) :
    ∃ (H : triangleWeightSpace type3Faces ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type3Faces Q u) ∧
      (∀ f ∈ type3Faces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ type3Faces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  sorry

/-- Both diagonals separate the respective opposite vertices on the entire chart. -/
theorem type6_diagonal_signs (second : Bool) (x w : ℝ) (hd : chartDomain second x w) :
    let p := stripPoint second x w
    0 < area p 1 2 0 ∧ area p 1 2 5 < 0 ∧ area p 0 5 1 < 0 ∧ 0 < area p 0 5 2 := by
  sorry

/-- An inflated generic lift matches all twenty-four intrinsic squared edge lengths
while the lattice periods stay fixed. -/
theorem type6_length_matched_lift (x w : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) (hw : 1 - x^2 ≤ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (second : Bool) (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion),
      chartDomain second x w ∧ 0 < t ∧ (∀ i, |m i| < ε) ∧
      lengthResidual second x w z (t,m) = 0 ∧
      GenericLift (movedFoldedPoint second x w m) (fun v => t * z v) ∧
      ∀ pair ∈ type6DisjointPairs,
        isSeparated (movedFoldedPoint second x w m) (fun v => t * z v) pair := by
  sorry

/-- An embedding can be perturbed to general position inside any open set of placements. -/
theorem generic_embedded_perturbation (fs : List Triangle) (q : Vertex → Point3)
    {U : Set (Vertex → Point3)} (hU : IsOpen U) (hq : q ∈ U)
    (h : Function.Injective (evaluateTriangles fs q)) :
    ∃ v ∈ U, Function.Injective (evaluateTriangles fs v) ∧
      GenericLift (fun i => ((v i).1,(v i).2.1)) (fun i => (v i).2.2) := by
  sorry

/-- The length-matched Type 6 configuration embeds the labeled triangles in Euclidean space. -/
theorem type6_spatial_embedding_lift (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hy : 0 < y) (hw : 1-x^2 ≤ y^2) {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (second : Bool) (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion),
      chartDomain second x (y^2) ∧ 0 < t ∧ m ∈ U ∧ lengthResidual second x (y^2) z (t,m) = 0 ∧
      Topology.IsClosedEmbedding (evaluateTriangles type6FlippedFaces (physicalFoldedVertex second x y m z t)) := by
  sorry

/-- Every flat lattice torus has a piecewise-isometric Type 6 embedding. -/
theorem type6_universal (a b : ℂ) (ha : a ≠ 0) (hb : (b/a).im ≠ 0) :
    ∃ (H : triangleWeightSpace type6FlippedFaces ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type6FlippedFaces Q u) ∧
      (∀ f ∈ type6FlippedFaces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ type6FlippedFaces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  sorry

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
  sorry

/-- The unit square lattice torus has a piecewise-isometric Type 5 embedding. -/
theorem type5_square :
    let a : ℂ := 1
    let b : ℂ := Complex.I
    let fs : List Triangle :=
      [(0,1,2), (0,3,1), (0,2,4), (0,5,3), (0,4,5), (1,5,2), (1,3,6), (1,6,4),
        (1,4,7), (1,7,5), (2,6,3), (2,3,7), (2,7,4), (2,5,6), (3,5,7), (4,6,5)]
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
  sorry

/-- Every rectangular flat torus has a piecewise-isometric Type 7 embedding. -/
theorem type7_rectangular (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (ho : (b/a).re = 0) :
    let fs : List Triangle :=
      [(3,5,6), (3,2,5), (3,6,4), (3,0,2), (3,4,1), (3,1,0), (5,0,6), (5,2,4),
        (5,4,7), (5,7,0), (6,7,4), (6,0,1), (6,1,7), (2,1,4), (2,0,7), (2,7,1)]
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
  sorry

end OrigamiTorusChallenge
