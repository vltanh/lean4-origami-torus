module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation

/-! The definitions shared word for word with the Palomar Challenge. -/

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
