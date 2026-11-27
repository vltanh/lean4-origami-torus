module

public import OrigamiTorus.WindingOrbits
import Mathlib.Tactic

/-! Exact intrinsic coordinates for the seven sharp-ray representatives at
the hexagonal endpoint. -/

@[expose] public section

namespace OrigamiTorus.Winding.Hexagonal

abbrev RationalPoint := ℚ × ℚ

def rationalPeriod (p : Period) : RationalPoint := (p.1,p.2)

def mapPeriodRat (M : PeriodMatrix) (u : RationalPoint) : RationalPoint :=
  (u.1*M.1.1+u.2*M.2.1,u.1*M.1.2+u.2*M.2.2)

def shiftSum (k : Triangulation) (v : Vertex) : RationalPoint :=
  ∑ w : Vertex, rationalPeriod (k.dualCocycle v w)

/-- The inverse of the two-vertex block with diagonal 7 and off-diagonal 1. -/
def pairSolution (s : Vertex → RationalPoint) (v w : Vertex) : RationalPoint :=
  (1/48 : ℚ) • ((7 : ℚ) • s v-s w)

/-- Solve the planar equilibrium equations using the complement of the
one-skeleton. Each connected component has at most four vertices. -/
def centeredPlacement (k : Triangulation) (v : Vertex) : RationalPoint :=
  let s := shiftSum k
  match k with
  | .type4 =>
    let c₀ := (7 : ℚ) • s 0-s 6
    let c₇ := (7 : ℚ) • s 7-s 1
    let q₀ := (1/1632 : ℚ) • ((41 : ℚ) • c₀-(7 : ℚ) • c₇)
    let q₇ := (1/1632 : ℚ) • ((41 : ℚ) • c₇-(7 : ℚ) • c₀)
    ![q₀,(1/7 : ℚ) • (s 1-q₇),pairSolution s 2 3,pairSolution s 3 2,
      (1/8 : ℚ) • s 4,(1/8 : ℚ) • s 5,(1/7 : ℚ) • (s 6-q₀),q₇] v
  | .type5 =>
    let c := (1/8 : ℚ) • (s 0+s 6+s 7)
    ![(1/5 : ℚ) • (s 0-c),(1/8 : ℚ) • s 1,(1/8 : ℚ) • s 2,
      pairSolution s 3 4,pairSolution s 4 3,(1/8 : ℚ) • s 5,
      (1/5 : ℚ) • (s 6-c),(1/5 : ℚ) • (s 7-c)] v
  | .type7 => pairSolution s v (v+4)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
/-- The explicit formula solves the rational equilibrium equations on the
one-skeleton with mean zero. -/
theorem centeredPlacement_harmonic (k : Triangulation) :
    (∑ v : Vertex, centeredPlacement k v) = 0 ∧
    ∀ v : Vertex, (((List.finRange 8).filter fun w => k.edges.contains (orderedEdge v w)).map fun w =>
      (centeredPlacement k w-centeredPlacement k v)+rationalPeriod (k.dualCocycle v w)).sum = 0 := by
  cases k <;> decide +kernel

/-- Translate vertex 0 to the origin and express the coordinates in the
given winding matrix. -/
def placement (k : Triangulation) (M : PeriodMatrix) (v : Vertex) : RationalPoint :=
  mapPeriodRat M (centeredPlacement k v-centeredPlacement k 0)

def markedShift (k : Triangulation) (M : PeriodMatrix) (a b : Vertex) : Period :=
  mapPeriod M (k.dualCocycle a b)

theorem markedShift_recovers_matrix (k : Triangulation) (M : PeriodMatrix) :
    (cyclePeriod (markedShift k M) k.basisCycles.1,cyclePeriod (markedShift k M) k.basisCycles.2) = M := by
  change (cyclePeriod (fun a b => mapPeriod M (k.dualCocycle a b)) k.basisCycles.1,
    cyclePeriod (fun a b => mapPeriod M (k.dualCocycle a b)) k.basisCycles.2) = M
  simp only [cyclePeriod_mapPeriod,(k.dualCocycle_basis).1,(k.dualCocycle_basis).2]
  exact Prod.ext (by simp [mapPeriod]) (by simp [mapPeriod])

def markedDisplacement (k : Triangulation) (M : PeriodMatrix) (a b : Vertex) : RationalPoint :=
  placement k M b-placement k M a+rationalPeriod (markedShift k M a b)

def faceDoubleArea (k : Triangulation) (M : PeriodMatrix) (f : Triangle) : ℚ :=
  let u := markedDisplacement k M f.1 f.2.1
  let v := markedDisplacement k M f.1 f.2.2
  u.1*v.2-u.2*v.1

def dot (u v : RationalPoint) : ℚ :=
  u.1*v.1+(u.1*v.2+u.2*v.1)/2+u.2*v.2

def nearestDirections : List Period := [(1,0),(0,1),(-1,1)]

def rayCases : List (Triangulation × PeriodMatrix) :=
  [Triangulation.type4,.type5,.type7].flatMap fun k => (k.representatives .ray).map (k,·)

theorem rayCases_length : rayCases.length = 7 := by decide +kernel

def rayCase (j : Fin 7) : Triangulation × PeriodMatrix :=
  rayCases.get (Fin.cast rayCases_length.symm j)

def areaSign (k : Triangulation) (M : PeriodMatrix) : ℚ :=
  if 0 < faceDoubleArea k M (k.faces.headD (0,0,0)) then 1 else -1

/-- Exact area and three nearest-direction inequalities for a representative. -/
def CoordinateCertificate (k : Triangulation) (M : PeriodMatrix) : Prop :=
  let s := areaSign k M
  (∀ f ∈ k.faces, 0 < s*faceDoubleArea k M f) ∧
  (k.faces.map fun f => s*faceDoubleArea k M f).sum = 2 ∧
  ∀ e ∈ k.edges, ∀ v ∈ nearestDirections,
    2*|dot (markedDisplacement k M e.1 e.2) (rationalPeriod v)| < 1

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
/-- The harmonic coordinates satisfy all of the recorded intrinsic checks
using rational arithmetic in the Lean kernel. -/
theorem coordinate_certificate (j : Fin 7) : CoordinateCertificate (rayCase j).1 (rayCase j).2 := by
  unfold CoordinateCertificate
  revert j
  decide +kernel

theorem all_sharp_representatives (k : Triangulation) (M : PeriodMatrix)
    (hM : M ∈ k.representatives .ray) : CoordinateCertificate k M := by
  have h : (k,M) ∈ rayCases := List.mem_flatMap.mpr ⟨k,by cases k <;> simp,
    List.mem_map.mpr ⟨M,hM,rfl⟩⟩
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem h
  have hi₇ := rayCases_length ▸ hi
  let j : Fin 7 := ⟨i,hi₇⟩
  have hcase : rayCase j = (k,M) := he
  simpa only [hcase] using coordinate_certificate j

end OrigamiTorus.Winding.Hexagonal
