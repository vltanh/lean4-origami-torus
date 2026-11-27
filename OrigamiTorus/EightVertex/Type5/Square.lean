module

public import OrigamiTorus.EightVertex.Type5.Reconstruction
public import OrigamiTorus.Geometry.EdgeFaceSeparation
public import OrigamiTorus.Geometry.TriangleMetric
public meta import OrigamiTorus.Certificates.RadicalIntervals
import OrigamiTorus.Certificates.RadicalIntervals
import Mathlib.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-! The exact radical Type 5 square witness, in its gauge with vertex 1 at the origin. -/

@[expose] public section

namespace OrigamiTorus.Type5

def positiveShift (a b : Vertex) : ℤ × ℤ :=
  match a.val,b.val with
  | 0,4 => (1,-1)
  | 0,5 => (1,0)
  | 2,3 => (0,-1)
  | 2,4 => (1,-1)
  | 2,6 => (0,-1)
  | 2,7 => (1,-1)
  | 3,5 => (1,0)
  | 3,7 => (1,0)
  | 4,5 => (0,1)
  | 5,6 => (0,-1)
  | _,_ => (0,0)

def squareShift (a b : Vertex) : ℤ × ℤ :=
  if a < b then positiveShift a b else -(positiveShift b a)

def shiftPoint {R : Type*} [Ring R] (a b : Vertex) : Plane R :=
  ((squareShift a b).1, (squareShift a b).2)

theorem squareShift_cocycle :
    (∀ a : Vertex, squareShift 1 a = 0) ∧
      (∀ f ∈ faces, squareShift f.1 f.2.1 + squareShift f.2.1 f.2.2 +
        squareShift f.2.2 f.1 = 0) := by
  decide +kernel

/-- The four exact rational coordinates in the core, and the origin at vertex 1. -/
def squareCore {R : Type*} [Field R] : Vertex → Plane R :=
  ![(0,0), (0,0), (444720882667740 / 10^15,-499972918103549 / 10^15),
    (499999999999045 / 10^15,87262616850970 / 10^15),
    (-81664706988789 / 10^15,418104802964447 / 10^15),
    (-39101278348661 / 10^15,-213154941393696 / 10^15), (0,0), (0,0)]

def offsetCore {R : Type*} [Field R] (a b : Vertex) : Plane R :=
  squareCore a - shiftPoint a b

def coreXY {R : Type*} [Field R] (j : Vertex) : Plane R :=
  projection (squareCore 2) (squareCore 5) (offsetCore 2 j) (offsetCore 5 j) (squareCore j)

def coreRadicand {R : Type*} [Field R] (j : Vertex) : R :=
  squared2 (squareCore j) - squared2 (coreXY j)

noncomputable def firstHeight : ℝ := Real.sqrt (coreRadicand 3)
noncomputable def secondHeight : ℝ := -Real.sqrt (coreRadicand 4)

def leafSystem {R : Type*} [Field R] (j : Vertex) (z₃ z₄ : R) : LeafData R :=
  let f := projection (squareCore 2) (squareCore 5) (offsetCore 2 j) (offsetCore 5 j)
  let p₀ := f (0,0)
  let colX := f (1,0) - p₀
  let colY := f (0,1) - p₀
  let coeff k :=
    let s := offsetCore k j
    let q := coreXY k
    (s.1 - dot q colX, s.2 - dot q colY)
  let rhs k height :=
    let s := offsetCore k j
    let q := coreXY k
    (squared3 (atHeight q height) - squared2 s)/2 - dot q p₀
  ⟨p₀,colX,colY,coeff 3,coeff 4,rhs 3 z₃,rhs 4 z₄,z₃,z₄⟩

noncomputable def squareLeaf (j : Vertex) : LeafData ℝ := leafSystem j firstHeight secondHeight

noncomputable def leafParameter (j : Vertex) : ℝ :=
  let q := (squareLeaf j).quadratic
  quadraticRoot q.1 q.2.1 q.2.2 (j != 6)

noncomputable def squareIntrinsic (j : Vertex) : Plane ℝ :=
  if j = 0 ∨ j = 6 ∨ j = 7 then (squareLeaf j).intrinsicAt (leafParameter j)
  else squareCore j

noncomputable def squareExtrinsic (j : Vertex) : Space ℝ :=
  if j = 0 ∨ j = 6 ∨ j = 7 then (squareLeaf j).extrinsicAt (leafParameter j)
  else if j = 3 then atHeight (coreXY 3) firstHeight
  else if j = 4 then atHeight (coreXY 4) secondHeight
  else atHeight (squareCore j) 0

private theorem anchor_nondegenerate : cross (squareCore 2) (squareCore 5) ≠ (0 : ℝ) := by
  norm_num [squareCore, cross]

private theorem root3_positive : (0 : ℝ) < coreRadicand 3 := by
  norm_num [coreRadicand, coreXY, squared2, projection, linearSolve, anchorRhs, dot, cross,
    squareCore, offsetCore, shiftPoint, squareShift, positiveShift]

private theorem root4_positive : (0 : ℝ) < coreRadicand 4 := by
  norm_num [coreRadicand, coreXY, squared2, projection, linearSolve, anchorRhs, dot, cross,
    squareCore, offsetCore, shiftPoint, squareShift, positiveShift]

theorem square_root3_edges :
    squared3 (squareExtrinsic 3) = squared2 (squareIntrinsic 3) ∧
    squared3 (squareExtrinsic 3 - squareExtrinsic 2) =
      squared2 (squareIntrinsic 3 - offsetCore 2 3) ∧
    squared3 (squareExtrinsic 3 - squareExtrinsic 5) =
      squared2 (squareIntrinsic 3 - offsetCore 5 3) := by
  have h := makeRoot_edges (squareCore 2) (squareCore 5) (offsetCore 2 3) (offsetCore 5 3)
    (squareCore 3) true anchor_nondegenerate root3_positive.le
  change _ ∧ _ ∧ _ at h
  norm_num [squareIntrinsic, squareExtrinsic]
  exact h

theorem square_root4_edges :
    squared3 (squareExtrinsic 4) = squared2 (squareIntrinsic 4) ∧
    squared3 (squareExtrinsic 4 - squareExtrinsic 2) =
      squared2 (squareIntrinsic 4 - offsetCore 2 4) ∧
    squared3 (squareExtrinsic 4 - squareExtrinsic 5) =
      squared2 (squareIntrinsic 4 - offsetCore 5 4) := by
  have h := makeRoot_edges (squareCore 2) (squareCore 5) (offsetCore 2 4) (offsetCore 5 4)
    (squareCore 4) false anchor_nondegenerate root4_positive.le
  change _ ∧ _ ∧ _ at h
  norm_num [squareIntrinsic, squareExtrinsic]
  exact h


private theorem firstHeight_ne : firstHeight ≠ 0 := (Real.sqrt_pos.2 root3_positive).ne'

macro "square_bounds" p:ident : tactic => `(tactic|
  (norm_num [squareIntrinsic, squareExtrinsic, leafParameter, quadraticRoot, signedRoot,
    squareLeaf, leafSystem, LeafData.intrinsicAt, LeafData.extrinsicAt, LeafData.quadratic, LeafData.intrinsicBase,
    LeafData.intrinsicDirection, LeafData.extrinsicBase, LeafData.extrinsicDirection,
    LeafData.lineNormal, LeafData.lineOffset, LeafData.planarLin, discriminant,
    firstHeight, secondHeight, coreRadicand, coreXY, squared2, squared3, dot, dot3, horizontal,
    atHeight, smul2, smul3, projection, linearSolve, anchorRhs, cross, squareCore,
    offsetCore, shiftPoint, squareShift, positiveShift]
   <;> dyadic_interval +kernel [$p := 120]))

set_option maxHeartbeats 0 in
private theorem squareLeaf_good {j : Vertex} (hj : j ∈ leaves) :
    squared2 (squareLeaf j).lineNormal ≠ 0 ∧ (squareLeaf j).quadratic.1 ≠ 0 ∧
      0 ≤ discriminant (squareLeaf j).quadratic.1 (squareLeaf j).quadratic.2.1
        (squareLeaf j).quadratic.2.2 := by
  fin_cases j <;> simp [leaves] at hj
  all_goals
    refine ⟨ne_of_gt ?_,?_ ,?_⟩
    · square_bounds prec
    · exact ne_of_gt (by square_bounds prec)
    · square_bounds prec

theorem square_leaf_system {j : Vertex} (hj : j ∈ leaves) :
    let u := (squareLeaf j).intrinsicAt (leafParameter j)
    let v := (squareLeaf j).extrinsicAt (leafParameter j)
    squared3 v = squared2 u ∧ horizontal v = (squareLeaf j).planarLin u + (squareLeaf j).base ∧
      firstHeight*v.2.2 = dot (squareLeaf j).a₃ u + (squareLeaf j).b₃ ∧
      secondHeight*v.2.2 = dot (squareLeaf j).a₄ u + (squareLeaf j).b₄ := by
  obtain ⟨hn,ha,hd⟩ := squareLeaf_good hj
  exact (squareLeaf j).branch_sound (j != 6) firstHeight_ne hn ha hd


private theorem projection_affine (p₂ p₅ s₂ s₅ u : Plane ℝ) :
    let f := projection p₂ p₅ s₂ s₅
    let b := f (0,0)
    f u = smul2 u.1 (f (1,0)-b) + smul2 u.2 (f (0,1)-b) + b := by
  apply Prod.ext <;>
    simp [projection, linearSolve, anchorRhs, dot, smul2, div_eq_mul_inv] <;> ring

private theorem leaf_root_distance (u s q base colX colY : Plane ℝ) (v : Space ℝ) (z : ℝ)
    (h0 : squared3 v = squared2 u)
    (hxy : horizontal v = smul2 u.1 colX + smul2 u.2 colY + base)
    (hroot : z*v.2.2 =
      dot (s.1-dot q colX,s.2-dot q colY) u +
        ((squared3 (atHeight q z)-squared2 s)/2-dot q base)) :
    squared3 (v-atHeight q z) = squared2 (u-s) := by
  apply (edgeEquation_iff _ _ _ _ h0).mpr
  simp only [dot3, horizontal, atHeight] at hroot ⊢
  have hp : (v.1,v.2.1) = smul2 u.1 colX + smul2 u.2 colY + base := hxy
  rw [hp]
  simp [dot,smul2] at hroot ⊢
  linear_combination hroot

/-- All five edges incident to an exact radical leaf have the required lengths. -/
theorem square_leaf_edges {j : Vertex} (hj : j ∈ leaves) :
    let u := (squareLeaf j).intrinsicAt (leafParameter j)
    let v := (squareLeaf j).extrinsicAt (leafParameter j)
    squared3 v = squared2 u ∧
      squared3 (v-atHeight (squareCore 2) 0) = squared2 (u-offsetCore 2 j) ∧
      squared3 (v-atHeight (squareCore 5) 0) = squared2 (u-offsetCore 5 j) ∧
      squared3 (v-atHeight (coreXY 3) firstHeight) = squared2 (u-offsetCore 3 j) ∧
      squared3 (v-atHeight (coreXY 4) secondHeight) = squared2 (u-offsetCore 4 j) := by
  let u := (squareLeaf j).intrinsicAt (leafParameter j)
  let v := (squareLeaf j).extrinsicAt (leafParameter j)
  let f := projection (squareCore (R := ℝ) 2) (squareCore 5) (offsetCore 2 j) (offsetCore 5 j)
  let B := f (0,0)
  let X := f (1,0) - B
  let Y := f (0,1) - B
  obtain ⟨h0,hxy,h3,h4⟩ := square_leaf_system hj
  have hp : horizontal v = smul2 u.1 X + smul2 u.2 Y + B := hxy
  have hxy' : horizontal v = f u := hp.trans (projection_affine _ _ _ _ _).symm
  have ⟨hA₂,hA₅⟩ := linearSolve_spec anchor_nondegenerate
    (anchorRhs (squareCore 2) (offsetCore 2 j) u) (anchorRhs (squareCore 5) (offsetCore 5 j) u)
  refine ⟨h0,(edgeEquation_iff _ _ _ _ h0).mpr ?_,(edgeEquation_iff _ _ _ _ h0).mpr ?_,?_,?_⟩
  · change dot (squareCore 2) (horizontal v) + 0*v.2.2 - dot (offsetCore 2 j) u =
      (squared2 (squareCore 2) + (0 : ℝ)^2 - squared2 (offsetCore 2 j))/2
    rw [hxy']
    change dot (squareCore 2) (f u) = _ at hA₂
    unfold anchorRhs at hA₂
    linarith only [hA₂]
  · change dot (squareCore 5) (horizontal v) + 0*v.2.2 - dot (offsetCore 5 j) u =
      (squared2 (squareCore 5) + (0 : ℝ)^2 - squared2 (offsetCore 5 j))/2
    rw [hxy']
    change dot (squareCore 5) (f u) = _ at hA₅
    unfold anchorRhs at hA₅
    linarith only [hA₅]
  · exact leaf_root_distance u _ _ B X Y v firstHeight h0 hp h3
  · exact leaf_root_distance u _ _ B X Y v secondHeight h0 hp h4


def orientedEdges : List Edge :=
  [(1,2), (1,5), (2,5), (1,3), (2,3), (5,3), (1,4), (2,4), (5,4)] ++
  leaves.flatMap fun j => ([1,2,5,3,4] : List Vertex).map (·,j)

theorem oriented_edges_cover (e : Edge) (he : e ∈ edgeList) :
    ∃ ab ∈ orientedEdges, orderedEdge ab.1 ab.2 = e := by
  obtain ⟨a,b⟩ := e
  have hh : ∀ a b : Vertex, (a,b) ∈ edgeList →
      ∃ ab ∈ orientedEdges, orderedEdge ab.1 ab.2 = (a,b) := by
    decide +kernel
  exact hh a b he

noncomputable def edgeMatch (a b : Vertex) : Prop :=
  squared3 (squareExtrinsic b - squareExtrinsic a) =
    squared2 (squareIntrinsic b - squareIntrinsic a + shiftPoint a b)

private theorem shiftPoint_swap (a b : Vertex) :
    shiftPoint (R := ℝ) b a = -shiftPoint a b := by
  have h : ∀ a b : Vertex, squareShift b a = -squareShift a b := by decide +kernel
  obtain ⟨hx, hy⟩ := Prod.mk_inj.mp (h a b)
  apply Prod.ext
  · simp only [shiftPoint, Prod.fst_neg]
    exact_mod_cast hx
  · simp only [shiftPoint, Prod.snd_neg]
    exact_mod_cast hy

private theorem edgeMatch_swap {a b : Vertex} (h : edgeMatch a b) : edgeMatch b a := by
  unfold edgeMatch at h ⊢
  rw [shiftPoint_swap a b]
  simp [squared2, squared3, dot, horizontal] at h ⊢
  linear_combination h

private theorem edgeMatch_origin (b : Vertex)
    (h : squared3 (squareExtrinsic b) = squared2 (squareIntrinsic b)) : edgeMatch 1 b := by
  have hs : shiftPoint (R := ℝ) 1 b = 0 := by
    simp [shiftPoint, squareShift_cocycle.1 b]
  have hi : squareIntrinsic 1 = 0 := by norm_num [squareIntrinsic,squareCore]
  have he : squareExtrinsic 1 = 0 := by norm_num [squareExtrinsic,squareCore,atHeight]
  simpa [edgeMatch, hs, hi, he] using h

private theorem sub_offset (a b k : Plane ℝ) : a - (b - k) = a - b + k := by abel

private theorem oriented_edge_matches {e : Edge} (he : e ∈ orientedEdges) :
    edgeMatch e.1 e.2 := by
  obtain ⟨a,b⟩ := e
  simp only [orientedEdges, List.mem_append, List.mem_flatMap, List.mem_map] at he
  rcases he with he | ⟨j,hj,k,hk,he⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he | he | he | he | he | he | he | he <;>
      rcases Prod.mk_inj.mp he with ⟨rfl,rfl⟩
    · norm_num [edgeMatch, squareExtrinsic, squareIntrinsic, shiftPoint, squareShift, positiveShift,
        squared3, horizontal, atHeight, squared2, dot]
    · norm_num [edgeMatch, squareExtrinsic, squareIntrinsic, shiftPoint, squareShift, positiveShift,
        squared3, horizontal, atHeight, squared2, dot]
    · norm_num [edgeMatch, squareExtrinsic, squareIntrinsic, shiftPoint, squareShift, positiveShift,
        squared3, horizontal, atHeight, squared2, dot]
    · exact edgeMatch_origin 3 square_root3_edges.1
    · simpa [edgeMatch, offsetCore, squareExtrinsic, squareIntrinsic, sub_offset]
        using square_root3_edges.2.1
    · simpa [edgeMatch, offsetCore, squareExtrinsic, squareIntrinsic, sub_offset]
        using square_root3_edges.2.2
    · exact edgeMatch_origin 4 square_root4_edges.1
    · simpa [edgeMatch, offsetCore, squareExtrinsic, squareIntrinsic, sub_offset]
        using square_root4_edges.2.1
    · simpa [edgeMatch, offsetCore, squareExtrinsic, squareIntrinsic, sub_offset]
        using square_root4_edges.2.2
  · rcases Prod.mk_inj.mp he with ⟨rfl,rfl⟩
    obtain ⟨h1,h2,h5,h3,h4⟩ := square_leaf_edges hj
    have hj' : j = 0 ∨ j = 6 ∨ j = 7 := by simpa [leaves] using hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · apply edgeMatch_origin
      simpa [squareExtrinsic, squareIntrinsic, hj'] using h1
    · simpa [edgeMatch, squareExtrinsic, squareIntrinsic, hj', offsetCore, sub_offset] using h2
    · simpa [edgeMatch, squareExtrinsic, squareIntrinsic, hj', offsetCore, sub_offset] using h5
    · simpa [edgeMatch, squareExtrinsic, squareIntrinsic, hj', offsetCore, sub_offset] using h3
    · simpa [edgeMatch, squareExtrinsic, squareIntrinsic, hj', offsetCore, sub_offset] using h4

/-- The exact radical configuration matches all 24 squared edge lengths of the
intrinsic square-lattice marking. -/
theorem square_all_edge_lengths (e : Edge) (he : e ∈ edgeList) :
    edgeMatch e.1 e.2 := by
  obtain ⟨⟨a,b⟩,hm,rfl⟩ := oriented_edges_cover e he
  have hh := oriented_edge_matches hm
  by_cases h : a ≤ b
  · simpa [orderedEdge, min_eq_left h, max_eq_right h] using hh
  · have h' : b ≤ a := le_of_not_ge h
    simpa [orderedEdge,min_eq_right h',max_eq_left h'] using edgeMatch_swap hh

private theorem edgeMatch_of_mem {a b : Vertex} (he : orderedEdge a b ∈ edgeList) : edgeMatch a b := by
  have h := square_all_edge_lengths (orderedEdge a b) he
  by_cases hab : a ≤ b
  · simpa [orderedEdge,min_eq_left hab,max_eq_right hab] using h
  · have hba : b ≤ a := le_of_not_ge hab
    exact edgeMatch_swap (by simpa [orderedEdge,min_eq_right hba,max_eq_left hba] using h)

private theorem squareShift_add {a b c : Vertex} (hf : (a,b,c) ∈ faces) :
    shiftPoint (R := ℝ) a c = shiftPoint a b + shiftPoint b c := by
  have hz := squareShift_cocycle.2 (a,b,c) hf
  have hsum : shiftPoint (R := ℝ) a b + shiftPoint b c + shiftPoint c a = 0 := by
    have hx := congrArg Prod.fst hz
    have hy := congrArg Prod.snd hz
    simp only [Prod.fst_add,Prod.snd_add,Prod.fst_zero,Prod.snd_zero] at hx hy
    apply Prod.ext
    · simp only [shiftPoint,Prod.fst_add,Prod.fst_zero]
      exact_mod_cast hx
    · simp only [shiftPoint,Prod.snd_add,Prod.snd_zero]
      exact_mod_cast hy
  rw [shiftPoint_swap a c] at hsum
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hsum)).symm

/-- The affine metric on every intrinsic square face agrees exactly with its spatial face. -/
theorem square_face_metric (a b c : Vertex) (hf : (a,b,c) ∈ faces) (s t : ℝ) :
    let u := squareIntrinsic b + shiftPoint a b - squareIntrinsic a
    let v := squareIntrinsic c + shiftPoint a c - squareIntrinsic a
    squared3 (smul3 s (squareExtrinsic b-squareExtrinsic a) +
      smul3 t (squareExtrinsic c-squareExtrinsic a)) = squared2 (smul2 s u+smul2 t v) := by
  have hedges {e : Edge} (he : e ∈ faceEdges (a,b,c)) : e ∈ edgeList := by
    simp only [edgeList,List.mem_eraseDups,List.mem_flatMap]
    exact ⟨(a,b,c),hf,he⟩
  have hab := edgeMatch_of_mem (hedges (e := orderedEdge a b) (by simp [faceEdges]))
  have hbc := edgeMatch_of_mem (hedges (e := orderedEdge b c) (by simp [faceEdges]))
  have hca := edgeMatch_of_mem (hedges (e := orderedEdge c a) (by simp [faceEdges]))
  have hac := edgeMatch_swap hca
  have hab' : squareIntrinsic b+shiftPoint a b-squareIntrinsic a =
      squareIntrinsic b-squareIntrinsic a+shiftPoint a b := by abel
  have hac' : squareIntrinsic c+shiftPoint a c-squareIntrinsic a =
      squareIntrinsic c-squareIntrinsic a+shiftPoint a c := by abel
  have hbc' : squareIntrinsic c+shiftPoint a c-(squareIntrinsic b+shiftPoint a b) =
      squareIntrinsic c-squareIntrinsic b+shiftPoint b c := by
    rw [squareShift_add hf]
    abel
  exact triangle_squared_metric (squareIntrinsic a) (squareIntrinsic b+shiftPoint a b)
    (squareIntrinsic c+shiftPoint a c) (squareExtrinsic a) (squareExtrinsic b) (squareExtrinsic c)
    (by simpa [edgeMatch,hab'] using hab) (by simpa [edgeMatch,hac'] using hac)
    (by simpa [edgeMatch,hbc'] using hbc) s t

def orientedArea {R : Type*} [Field R] (u : Vertex → Plane R) (f : Triangle) : R :=
  let (a,b,c) := f
  cross (u b - u a + shiftPoint a b) (u c - u a + shiftPoint a c)

set_option maxHeartbeats 3000000 in
theorem square_total_area (u : Vertex → Plane ℝ) : (faces.map (orientedArea u)).sum = 2 := by
  norm_num [faces, orientedArea, cross, shiftPoint, squareShift, positiveShift]
  ring

private def coordinateFloors : Vertex → Fin 5 → ℤ :=
  ![![49911999,-39249564,33199625,-54115052,1040164],
    ![0,0,0,0,0],
    ![44472088,-49997292,44472088,-49997292,0],
    ![49999999,8726261,49164893,-9464610,8329591],
    ![-8166471,41810480,17294615,-24439617,-30305263],
    ![-3910128,-21315495,-3910128,-21315495,0],
    ![30334901,49856051,30695977,-49534863,-3144280],
    ![-43934815,8495072,43492663,-7542680,7343730]]

private noncomputable def coordinate (j : Vertex) : Fin 5 → ℝ :=
  ![(squareIntrinsic j).1,(squareIntrinsic j).2,
    (squareExtrinsic j).1,(squareExtrinsic j).2.1,(squareExtrinsic j).2.2]

set_option maxHeartbeats 0 in
private theorem coordinate_bounds (j : Vertex) (i : Fin 5) :
    (((coordinateFloors j i : ℚ)-1)/100000000 : ℚ) ≤ coordinate j i ∧
      coordinate j i ≤ (((coordinateFloors j i : ℚ)+2)/100000000 : ℚ) := by
  fin_cases j <;> fin_cases i <;> constructor <;>
    norm_num [coordinate,coordinateFloors] <;> square_bounds prec

open Inclusion IntervalDyadicReal

private def box (j : Vertex) (i : Fin 5) : Interval Dyadic :=
  let n := (coordinateFloors j i : ℚ)
  Interval.Icc (rat ((n-1)/100000000) 48).lb (rat ((n+2)/100000000) 48).ub

private theorem coordinate_mem (j : Vertex) (i : Fin 5) : coordinate j i ∈ box j i := by
  rw [mem_iff_mem_map]
  exact Interval.mem_Icc_of_le (ratCast_mem _ _) (coordinate_bounds j i).1
    (coordinate_bounds j i).2 (ratCast_mem _ _)

private def areaBox (a b c : Vertex) (i j : Fin 5) : Interval Dyadic :=
  ((box b i).mul ((box c j).sub (box a j))).add
    (((box c i).mul ((box a j).sub (box b j))).add
      ((box a i).mul ((box b j).sub (box c j))))

private theorem area_mem (a b c : Vertex) :
    area (fun j => horizontal (squareExtrinsic j)) a b c ∈ areaBox a b c 2 3 := by
  simp only [area,areaBox,add_assoc]
  exact add_mem (mul_mem (coordinate_mem b 2) (sub_mem (coordinate_mem c 3) (coordinate_mem a 3)))
    (add_mem (mul_mem (coordinate_mem c 2) (sub_mem (coordinate_mem a 3) (coordinate_mem b 3)))
      (mul_mem (coordinate_mem a 2) (sub_mem (coordinate_mem b 3) (coordinate_mem c 3))))

private def volumeBox (a b c d : Vertex) : Interval Dyadic :=
  (((box a 4).neg.mul (areaBox b c d 2 3)).add ((box b 4).mul (areaBox a c d 2 3))).sub
      ((box c 4).mul (areaBox a b d 2 3)) |>.add ((box d 4).mul (areaBox a b c 2 3))

private def intrinsicAreaBox (f : Triangle) : Interval Dyadic :=
  let ((a,b,c)) := f
  let ux := ((box b 0).sub (box a 0)).add (Interval.singleton (squareShift a b).1)
  let uy := ((box b 1).sub (box a 1)).add (Interval.singleton (squareShift a b).2)
  let vx := ((box c 0).sub (box a 0)).add (Interval.singleton (squareShift a c).1)
  let vy := ((box c 1).sub (box a 1)).add (Interval.singleton (squareShift a c).2)
  (ux.mul vy).sub (uy.mul vx)

private theorem intrinsic_area_mem (f : Triangle) :
    orientedArea squareIntrinsic f ∈ intrinsicAreaBox f := by
  rcases f with ⟨a,b,c⟩
  exact sub_mem
    (mul_mem (add_mem (sub_mem (coordinate_mem b 0) (coordinate_mem a 0)) (intCast_mem _))
      (add_mem (sub_mem (coordinate_mem c 1) (coordinate_mem a 1)) (intCast_mem _)))
    (mul_mem (add_mem (sub_mem (coordinate_mem b 1) (coordinate_mem a 1)) (intCast_mem _))
      (add_mem (sub_mem (coordinate_mem c 0) (coordinate_mem a 0)) (intCast_mem _)))

private theorem volume_mem (a b c d : Vertex) :
    volume (fun j => horizontal (squareExtrinsic j)) (fun j => (squareExtrinsic j).2.2)
      a b c d ∈ volumeBox a b c d := by
  exact add_mem
    (sub_mem
      (add_mem (mul_mem (neg_mem (coordinate_mem a 4)) (area_mem b c d))
        (mul_mem (coordinate_mem b 4) (area_mem a c d)))
      (mul_mem (coordinate_mem c 4) (area_mem a b d)))
    (mul_mem (coordinate_mem d 4) (area_mem a b c))

private def signCert (I : Interval Dyadic) : ℤ :=
  if I.lb.any fun l => 0 < l then 1 else if I.ub.any fun r => r < 0 then -1 else 0

private theorem signCert_pos {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I)
    (h : 0 < signCert I) : 0 < x := by
  rw [mem_iff_mem_map,Interval.mem_map_iff] at hx
  rcases I with ⟨_ | a,b⟩
  · simp [signCert] at h
    split at h <;> omega
  · have ha : 0 < a := by
      simp only [signCert,Option.any_some,decide_eq_true_eq] at h
      split at h
      · assumption
      · split at h <;> omega
    have hz : 0 < Dyadic.toReal a := by simpa [Dyadic.toReal] using Dyadic.toReal_lt_toReal.mpr ha
    exact hz.trans_le (hx.1 a rfl)

noncomputable def squareDisplacement (e : Edge) : Plane ℝ :=
  squareIntrinsic e.2-squareIntrinsic e.1+shiftPoint e.1 e.2

private noncomputable def squareComponent (e : Edge) (second : Bool) : ℝ :=
  if second then (squareDisplacement e).2 else (squareDisplacement e).1

private def squareComponentBox (e : Edge) (second : Bool) : Interval Dyadic :=
  let i : Fin 5 := if second then 1 else 0
  let d := squareShift e.1 e.2
  ((box e.2 i).sub (box e.1 i)).add (Interval.singleton ((if second then d.2 else d.1) : Dyadic))

private theorem square_component_mem (e : Edge) (second : Bool) :
    squareComponent e second ∈ squareComponentBox e second := by
  cases second
  · exact add_mem (sub_mem (coordinate_mem e.2 0) (coordinate_mem e.1 0)) (intCast_mem _)
  · exact add_mem (sub_mem (coordinate_mem e.2 1) (coordinate_mem e.1 1)) (intCast_mem _)

private def squareComponentCheck (e : Edge) (second : Bool) : Bool :=
  if e = (1,3) ∧ second = false then true else
    let u := (Interval.singleton (2 : Dyadic)).mul (squareComponentBox e second)
    let N := Interval.singleton (1 : Dyadic)
    decide (0 < signCert (N.sub u) ∧ 0 < signCert (N.add u))

private theorem square_component_slack_at {e : Edge} (he : e ∈ edgeList) (second : Bool) :
    |2*squareComponent e second| < 1 := by
  by_cases ht : e = (1,3) ∧ second = false
  · obtain ⟨rfl,rfl⟩ := ht
    norm_num [squareComponent,squareDisplacement,squareIntrinsic,squareCore,leaves,shiftPoint,
      squareShift,positiveShift]
  have checked : edgeList.all (fun e => [false,true].all (squareComponentCheck e)) = true := by
    decide +kernel
  have hm : second ∈ [false,true] := by cases second <;> simp
  have hc := List.all_eq_true.mp (List.all_eq_true.mp checked e he) second hm
  simp only [squareComponentCheck,ite_eq_right ht,decide_eq_true_eq] at hc
  have h₂ : (2 : ℝ) ∈ Interval.singleton (2 : Dyadic) := by exact_mod_cast intCast_mem (2 : ℤ)
  have h₁ : (1 : ℝ) ∈ Interval.singleton (1 : Dyadic) := by simpa using intCast_mem (1 : ℤ)
  have hu := mul_mem h₂ (square_component_mem e second)
  have hpos := signCert_pos (sub_mem h₁ hu) hc.1
  have hneg := signCert_pos (add_mem h₁ hu) hc.2
  exact abs_lt.mpr ⟨by linarith only [hneg],by linarith only [hpos]⟩

/-- Both coordinate comparisons are strict for each lifted square edge. -/
theorem square_edge_slack {e : Edge} (he : e ∈ edgeList) :
    |2*(squareDisplacement e).1| < 1 ∧ |2*(squareDisplacement e).2| < 1 :=
  ⟨square_component_slack_at he false,square_component_slack_at he true⟩

private theorem signCert_neg {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I)
    (h : signCert I < 0) : x < 0 := by
  rw [mem_iff_mem_map,Interval.mem_map_iff] at hx
  rcases I with ⟨a,_ | b⟩
  · simp [signCert] at h
    split at h <;> omega
  · have hb : b < 0 := by
      simp only [signCert,Option.any_some,decide_eq_true_eq] at h
      split at h
      · omega
      · split at h
        · assumption
        · omega
    exact (hx.2 b rfl).trans_lt (by simpa [Dyadic.toReal] using Dyadic.toReal_lt_toReal.mpr hb)

private theorem signCert_mul_pos {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J)
    (h : 0 < signCert I * signCert J) : 0 < x*y := by
  rcases mul_pos_iff.mp h with ⟨a,b⟩ | ⟨a,b⟩
  · exact mul_pos (signCert_pos hx a) (signCert_pos hy b)
  · exact mul_pos_of_neg_of_neg (signCert_neg hx a) (signCert_neg hy b)

private theorem signCert_mul_neg {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J)
    (h : signCert I * signCert J < 0) : x*y < 0 := by
  rcases mul_neg_iff.mp h with ⟨a,b⟩ | ⟨a,b⟩
  · exact mul_neg_of_pos_of_neg (signCert_pos hx a) (signCert_neg hy b)
  · exact mul_neg_of_neg_of_pos (signCert_neg hx a) (signCert_pos hy b)

set_option maxRecDepth 10000 in
theorem square_intrinsic_positive (f : Triangle) (hf : f ∈ faces) :
    0 < orientedArea squareIntrinsic f := by
  have checked : faces.all (fun f => decide (0 < signCert (intrinsicAreaBox f))) = true := by
    decide +kernel
  exact signCert_pos (intrinsic_area_mem f) (of_decide_eq_true ((List.all_eq_true.mp checked) f hf))

private def vols (a b c d : Vertex) : ℤ := signCert (volumeBox a b c d)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem volume_checks : ∀ a b c d : Vertex, a < b → b < c → c < d →
    vols a b c d ≠ 0 := by decide +kernel

theorem square_generic :
    ∀ a b c d : Vertex, a < b → b < c → c < d →
      volume (fun j => horizontal (squareExtrinsic j)) (fun j => (squareExtrinsic j).2.2) a b c d ≠ 0 := by
  intro a b c d hab hbc hcd
  rcases lt_or_gt_of_ne (volume_checks a b c d hab hbc hcd) with hn | hp
  · exact (signCert_neg (volume_mem a b c d) hn).ne
  · exact (signCert_pos (volume_mem a b c d) hp).ne'

def squareDisjointPairs : List (Edge × Triangle) :=
  edgeList.flatMap fun e =>
    (faces.filter fun f => !(triangleVertices f).contains e.1 && !(triangleVertices f).contains e.2)
      |>.map (e, ·)

private def separationCheck (p : Edge × Triangle) : Bool :=
  let ((a,b),c,d,e) := p
  @decide (separates (vols b c d e) (vols a c d e) (vols a b d e) (vols a b c e) (vols a b c d))
    (by unfold separates; infer_instance)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem separation_checks : squareDisjointPairs.all separationCheck = true := by decide +kernel

theorem square_separation (p : Edge × Triangle) (hp : p ∈ squareDisjointPairs) :
    isSeparated (fun j => horizontal (squareExtrinsic j)) (fun j => (squareExtrinsic j).2.2) p := by
  obtain ⟨⟨a,b⟩,c,d,e⟩ := p
  have hc := (List.all_eq_true.mp separation_checks) _ hp
  simp only [separationCheck,decide_eq_true_eq,separates] at hc
  simp only [isSeparated,separates]
  rcases hc with h | h | h | h
  · exact Or.inl (signCert_mul_pos (volume_mem b c d e) (volume_mem a c d e) h)
  · exact Or.inr (Or.inl (signCert_mul_pos (volume_mem a b d e) (volume_mem a b c e) h))
  · exact Or.inr (Or.inr (Or.inl (signCert_mul_pos (volume_mem a b c e) (volume_mem a b c d) h)))
  · exact Or.inr (Or.inr (Or.inr (signCert_mul_neg (volume_mem a b d e) (volume_mem a b c d) h)))

theorem square_pair_count : squareDisjointPairs.length = 138 := by decide +kernel

/-- The exact spatial square witness has no intersections of disjoint edges and faces. -/
theorem square_disjoint_edge_face (a b c d e : Vertex) (h : ((a,b),(c,d,e)) ∈ squareDisjointPairs) :
    Disjoint (segment ℝ (squareExtrinsic a) (squareExtrinsic b))
      (convexHull ℝ (Set.range (![squareExtrinsic c,squareExtrinsic d,squareExtrinsic e] : Fin 3 → Point3))) := by
  have hc : squareDisjointPairs.all (fun ((a,b),c,d,e) =>
      decide ([a,b,c,d,e].Pairwise (· ≠ ·))) = true := by decide +kernel
  have hh := of_decide_eq_true ((List.all_eq_true.mp hc) _ h)
  exact separated_segment_disjoint_triangle (fun j => horizontal (squareExtrinsic j))
    (fun j => (squareExtrinsic j).2.2) a b c d e square_generic hh (square_separation _ h)

end OrigamiTorus.Type5
