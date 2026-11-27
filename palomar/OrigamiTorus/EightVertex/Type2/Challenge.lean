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
# Type 2 origami tori

A flat embedded realization of the Type 2 face list is impossible.
The finite determinant-sign statement gives the obstruction used in the proof.
-/

@[expose] public section

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

end OrigamiTorus

namespace OrigamiTorusType2Challenge

open OrigamiTorus

/-- Every embedded Lutz Type 2 realization has a vertex with nonzero angle defect. -/
theorem type2_nonexistence (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles Type2.geometricFaces q)) :
    ¬ ∀ v, ((Type2.incidentCorners v).map (Type2.cornerAngle q v)).sum = 2 * Real.pi := by
  sorry

/-- No assignment satisfies the Type 2 determinant-sign formula. -/
theorem type2_sign_obstruction (a : Nat → Bool) :
    ¬ ∀ c ∈ OrigamiTorus.Type2.signClauses, ∃ l ∈ c, a l.1 = l.2 := by
  sorry

end OrigamiTorusType2Challenge
