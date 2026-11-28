module

public import OrigamiTorus.EightVertex.Type5.ContinuationTorus
public import OrigamiTorus.EightVertex.Type5.DistanceRigidity
import Mathlib.Tactic

/-! A self-intersecting, facewise-isometric Type 5 map at the hexagonal modulus. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type5.HexagonalFold

open Inclusion IntervalDyadicReal BoxArithmetic

def grid : Vertex → Plane ℚ :=
  ![(0,0),(0,0),(56/1024,-252/1024),(494/1024,130/1024),(-185/1024,307/1024),(-409/1024,-284/1024),(0,0),(0,0)]

/-- Both roots take the positive height. Leaf 0 takes the negative quadratic branch. -/
def chart : RadicalChart where
  x := ((1/2 : ℚ) : ℝ)
  y := Real.sqrt 3 / 2
  core j := ((grid j).1,(grid j).2)
  origin := by norm_num [grid]
  rootSign _ := true
  leafSign j := j != 0

private def coreBound (j : Vertex) : PlaneBounds (chart.core j) :=
  (rational (grid j).1,rational (grid j).2)

private def xBound : Bound chart.x := rational (1/2)
private def yBound : Bound chart.y := divide (sqrt (integer 3)) two

private def shiftBound (i j : Vertex) : PlaneBounds (Continuation.shift chart.x chart.y i j) :=
  Continuation.shiftBounds xBound yBound (squareShift i j)

private def offsetBound (i j : Vertex) : PlaneBounds (chart.offset i j) :=
  planeMinus (coreBound i) (shiftBound i j)

private def rootProj (j : Vertex) :=
  project (coreBound 2) (coreBound 5) (offsetBound 2 j) (offsetBound 5 j) (coreBound j)

private def radicandBound (j : Vertex) :
    Bound (rootRadicand (chart.core 2) (chart.core 5) (chart.offset 2 j) (chart.offset 5 j) (chart.core j)) :=
  minus (squaredPlane (coreBound j)) (squaredPlane (rootProj j))

private def rootBound (j : Vertex) : SpaceBounds (chart.rootPoint j) :=
  BoxArithmetic.root (coreBound 2) (coreBound 5) (offsetBound 2 j) (offsetBound 5 j) (coreBound j) true

private def leafBound (j : Vertex) : LeafBounds (chart.leaf j) :=
  BoxArithmetic.leaf (coreBound 2) (coreBound 5) (rootBound 3) (rootBound 4)
    (offsetBound 2 j) (offsetBound 5 j) (offsetBound 3 j) (offsetBound 4 j)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem good : chart.Good := by
  refine ⟨?_,?_,?_⟩
  · norm_num [chart,grid,cross]
  · intro j hj
    have checked : roots.all (fun k => positive (radicandBound k).range) = true := by decide +kernel
    exact positive_of_check (radicandBound j) (List.all_eq_true.mp checked j hj)
  · intro j hj
    let D := leafBound j
    have checked : leaves.all (fun k =>
        let B := leafBound k
        positive (squaredPlane B.normal).range &&
          (positive B.quadratic.1.range || positive (neg B.quadratic.1).range) &&
          positive B.discriminant.range) = true := by decide +kernel
    have hh := List.all_eq_true.mp checked j hj
    change (_ && (_ || _) && _) = true at hh
    simp only [Bool.and_eq_true,Bool.or_eq_true] at hh
    refine ⟨(positive_of_check (squaredPlane D.normal) hh.1.1).ne',?_,
      (positive_of_check D.discriminant hh.2).le⟩
    rcases hh.1.2 with h | h
    · exact (positive_of_check D.quadratic.1 h).ne'
    · exact (neg_pos.mp (positive_of_check (neg D.quadratic.1) h)).ne

theorem edge_lengths {a b : Vertex} (h : orderedEdge a b ∈ edgeList) :
    squared3 (chart.extrinsic b - chart.extrinsic a) =
      squared2 (chart.intrinsic b - chart.intrinsic a + Continuation.shift chart.x chart.y a b) :=
  RadicalChart.all_edge_lengths good h

private def intrinsicBound (j : Vertex) : PlaneBounds (chart.intrinsic j) :=
  if h : j ∈ leaves then by
    simp only [RadicalChart.intrinsic,ite_eq_left h]
    exact (leafBound j).intrinsicAt ((leafBound j).parameter (j != 0))
  else by
    simpa only [RadicalChart.intrinsic,ite_eq_right h] using coreBound j

private def areaBound (f : Triangle) :
    Bound (markedFaceCross (Continuation.shift chart.x chart.y) chart.intrinsic f) :=
  let difference (j : Vertex) := planeMinus (planePlus (intrinsicBound j) (shiftBound f.1 j)) (intrinsicBound f.1)
  crossBounds (difference f.2.1) (difference f.2.2)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem face_positive {f : Triangle} (hf : f ∈ faces) :
    0 < markedFaceCross (Continuation.shift chart.x chart.y) chart.intrinsic f := by
  have checked : faces.all (fun g => positive (areaBound g).range) = true := by decide +kernel
  exact positive_of_check (areaBound f) (List.all_eq_true.mp checked f hf)

/-- The sixteen intrinsic faces develop to the hexagonal lattice quotient. -/
def intrinsicHomeomorph : triangleWeightSpace faces ≃ₜ MarkedTorus :=
  Continuation.markedIntrinsicHomeomorph (x := chart.x) (y := chart.y) (by dsimp [chart]; positivity)
    chart.intrinsic (fun _ hf => face_positive hf)

/-- Every affine face of the spatial map preserves the full intrinsic metric. -/
theorem face_metric (a b c : Vertex) (hf : (a,b,c) ∈ faces) (s t : ℝ) :
    let u := chart.intrinsic b + Continuation.shift chart.x chart.y a b - chart.intrinsic a
    let v := chart.intrinsic c + Continuation.shift chart.x chart.y a c - chart.intrinsic a
    squared3 (smul3 s (chart.extrinsic b - chart.extrinsic a) + smul3 t (chart.extrinsic c - chart.extrinsic a)) =
      squared2 (smul2 s u + smul2 t v) :=
  Continuation.marked_face_metric edge_lengths a b c hf s t

private def spatialBound (j : Vertex) : SpaceBounds (chart.extrinsic j) :=
  if h : j ∈ leaves then by
    simp only [RadicalChart.extrinsic,ite_eq_left h]
    exact (leafBound j).extrinsicAt ((leafBound j).parameter (j != 0))
  else if k : j ∈ roots then by
    simpa only [RadicalChart.extrinsic,ite_eq_right h,ite_eq_left k] using rootBound j
  else by
    simpa only [RadicalChart.extrinsic,ite_eq_right h,ite_eq_right k] using height (coreBound j) zero

private def component (p : Point3) : Fin 3 → ℝ := ![p.1,p.2.1,p.2.2]

private def componentBound (j : Vertex) (k : Fin 3) : Bound (component (chart.extrinsic j) k) :=
  match k with
  | ⟨0,_⟩ => (spatialBound j).1
  | ⟨1,_⟩ => (spatialBound j).2.1
  | ⟨2,_⟩ => (spatialBound j).2.2

/-- Centers of the rational coordinate boxes, in units of 2⁻³⁰. Each radius is one unit. -/
private def centers : Vertex → Fin 3 → ℚ :=
  ![![-310192055,-404568215,104466947], ![0,0,0], ![58720256,-264241152,0],
    ![-274328353,-200911072,413860921], ![-210937320,-76446457,301529506], ![-428867584,-297795584,0],
    ![-301057980,-442683456,39920047], ![-156804411,44446725,313568942]]

private def lower (j : Vertex) (k : Fin 3) : ℚ := (centers j k - 1)/2^30
private def upper (j : Vertex) (k : Fin 3) : ℚ := (centers j k + 1)/2^30

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem endpoints : ∀ j k, positive (minus (componentBound j k) (rational (lower j k))).range = true ∧
    positive (minus (rational (upper j k)) (componentBound j k)).range = true := by decide +kernel

private def coordinateBox (j : Vertex) (k : Fin 3) : Bound (component (chart.extrinsic j) k) :=
  ⟨Continuation.enclosure (lower j k) (upper j k),by
    rw [mem_iff_mem_map]
    exact Interval.mem_Icc_of_le (ratCast_mem _ _)
      (sub_pos.mp (positive_of_check _ (endpoints j k).1)).le
      (sub_pos.mp (positive_of_check _ (endpoints j k).2)).le (ratCast_mem _ _)⟩

private def spatialBox (j : Vertex) : SpaceBounds (chart.extrinsic j) :=
  (coordinateBox j 0, coordinateBox j 1, coordinateBox j 2)

private abbrev bracket (a b c d : Vertex) :=
  affineBracket (chart.extrinsic a) (chart.extrinsic b) (chart.extrinsic c) (chart.extrinsic d)

private def bracketBound (a b c d : Vertex) : Bound (bracket a b c d) :=
  let diff (i : Vertex) : SpaceBounds (chart.extrinsic i - chart.extrinsic a) :=
    let A := spatialBox a
    let B := spatialBox i
    (minus B.1 A.1, minus B.2.1 A.2.1, minus B.2.2 A.2.2)
  let B := diff b
  let C := diff c
  let D := diff d
  plus (minus (times B.1 (minus (times C.2.1 D.2.2) (times C.2.2 D.2.1)))
    (times B.2.1 (minus (times C.1 D.2.2) (times C.2.2 D.1))))
    (times B.2.2 (minus (times C.1 D.2.1) (times C.2.1 D.1)))

private theorem crossing_of_signs (a b c d e : Vertex)
    (h₀ : bracket b c d e < 0) (h₁ : 0 < bracket a c d e) (h₂ : 0 < bracket a b d e)
    (h₃ : bracket a b c e < 0) (h₄ : 0 < bracket a b c d) :
    (vertexHull chart.extrinsic {a,b} ∩ vertexHull chart.extrinsic {c,d,e}).Nonempty := by
  classical
  let v : Fin 5 → Vertex := ![a,b,c,d,e]
  let w : Fin 5 → ℝ := ![bracket b c d e,-bracket a c d e,bracket a b d e,-bracket a b c e,bracket a b c d]
  have hn : w ≠ 0 := fun h => h₀.ne (congrFun h 0)
  have hs : ∑ i, w i = 0 := by
    simpa [w,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc] using
      affineBracket_circuitSum (chart.extrinsic a) (chart.extrinsic b) (chart.extrinsic c)
        (chart.extrinsic d) (chart.extrinsic e)
  have hv : ∑ i, w i • (chart.extrinsic ∘ v) i = 0 := by
    simpa [w,v,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc,neg_smul] using
      affineBracket_circuitVector (chart.extrinsic a) (chart.extrinsic b) (chart.extrinsic c)
        (chart.extrinsic d) (chart.extrinsic e)
  obtain ⟨u,hp,hm⟩ := vertexHull_inter_of_signed_relation (chart.extrinsic ∘ v) w hn hs hv
  have mono {S : Finset (Fin 5)} {T : Finset Vertex} (h : ∀ i ∈ S, v i ∈ T) :
      vertexHull (chart.extrinsic ∘ v) S ⊆ vertexHull chart.extrinsic T := by
    apply convexHull_mono
    rintro _ ⟨i,hi,rfl⟩
    exact ⟨v i,h i hi,rfl⟩
  refine ⟨u,mono ?_ hm,mono ?_ hp⟩
  · intro i hi
    have h := (Finset.mem_filter.mp hi).2
    fin_cases i <;> simp [v,w] at h ⊢ <;> exfalso <;> linarith only [h,h₂,h₃,h₄]
  · intro i hi
    have h := (Finset.mem_filter.mp hi).2
    fin_cases i <;> simp [v,w] at h ⊢ <;> exfalso <;> linarith only [h,h₀,h₁]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Two disjoint edge–face pairs meet at this hexagonal fold. -/
theorem crossings :
    (vertexHull chart.extrinsic {1,3} ∩ vertexHull chart.extrinsic {0,2,4}).Nonempty ∧
    (vertexHull chart.extrinsic {0,2} ∩ vertexHull chart.extrinsic {1,3,6}).Nonempty := by
  constructor <;> apply crossing_of_signs
  all_goals first
    | exact positive_of_check (bracketBound _ _ _ _) (by decide +kernel)
    | exact neg_pos.mp (positive_of_check (neg (bracketBound _ _ _ _)) (by decide +kernel))

private abbrev xy (j : Vertex) := horizontal (chart.extrinsic j)
private abbrev z (j : Vertex) := (chart.extrinsic j).2.2

private theorem volume_mem (a b c d : Vertex) :
    volume xy z a b c d ∈ (bracketBound a b c d).range := by
  rw [volume_eq_affineBracket]
  exact (bracketBound a b c d).mem

private def volSign (a b c d : Vertex) : ℤ :=
  Continuation.strictSign (bracketBound a b c d).range

private def otherPairs : List (Edge × Triangle) :=
  squareDisjointPairs.filter fun p => p != ((0,2),(1,3,6)) && p != ((1,3),(0,2,4))

private def separated (p : Edge × Triangle) : Bool :=
  let ((a,b),c,d,e) := p
  @decide (separates (volSign b c d e) (volSign a c d e) (volSign a b d e) (volSign a b c e)
    (volSign a b c d)) (by unfold separates; infer_instance)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem generic : GenericLift xy z := by
  have checked : ∀ a b c d : Vertex, a < b → b < c → c < d → volSign a b c d ≠ 0 := by decide +kernel
  intro a b c d hab hbc hcd
  rcases lt_or_gt_of_ne (checked a b c d hab hbc hcd) with h | h
  · exact (Continuation.sign_neg (volume_mem a b c d) h).ne
  · exact (Continuation.sign_pos (volume_mem a b c d) h).ne'

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem separation_checked : otherPairs.all separated = true := by decide +kernel

set_option maxHeartbeats 1000000 in
/-- The other 136 disjoint edge–face pairs have disjoint closed convex hulls. -/
theorem remaining_pairs_disjoint {a b c d e : Vertex} (hm : ((a,b),(c,d,e)) ∈ squareDisjointPairs)
    (h₁ : ((a,b),(c,d,e)) ≠ ((0,2),(1,3,6))) (h₂ : ((a,b),(c,d,e)) ≠ ((1,3),(0,2,4))) :
    Disjoint (vertexHull chart.extrinsic {a,b}) (vertexHull chart.extrinsic (triangleVertexSet (c,d,e))) := by
  have hp : ((a,b),(c,d,e)) ∈ otherPairs := List.mem_filter.mpr ⟨hm,by simp [h₁,h₂]⟩
  have hs := List.all_eq_true.mp separation_checked _ hp
  simp only [separated,decide_eq_true_eq,separates] at hs
  have hsep : isSeparated xy z ((a,b),(c,d,e)) := by
    simp only [isSeparated,separates]
    rcases hs with h | h | h | h
    · exact Or.inl (Continuation.sign_mul_pos (volume_mem _ _ _ _) (volume_mem _ _ _ _) h)
    · exact Or.inr (Or.inl (Continuation.sign_mul_pos (volume_mem _ _ _ _) (volume_mem _ _ _ _) h))
    · exact Or.inr (Or.inr (Or.inl (Continuation.sign_mul_pos (volume_mem _ _ _ _) (volume_mem _ _ _ _) h)))
    · exact Or.inr (Or.inr (Or.inr (Continuation.sign_mul_neg (volume_mem _ _ _ _) (volume_mem _ _ _ _) h)))
  have checked : squareDisjointPairs.all (fun ((i,j),k,l,m) =>
      decide ([i,j,k,l,m].Pairwise (· ≠ ·))) = true := by decide +kernel
  have hd := of_decide_eq_true (List.all_eq_true.mp checked _ hm)
  rw [vertexHull_pair,vertexHull_triangle]
  exact separated_segment_disjoint_triangle xy z _ _ _ _ _ generic hd hsep

theorem not_injective : ¬ Function.Injective (evaluateTriangles faces chart.extrinsic) := by
  intro h
  have edge : ({1,3} : Finset Vertex) ∈ (triangleComplex faces).faces :=
    ⟨by decide,(1,3,6),by decide,by decide⟩
  have face : ({0,2,4} : Finset Vertex) ∈ (triangleComplex faces).faces :=
    ⟨by decide,(0,2,4),by decide,by decide⟩
  obtain ⟨u,ha,hb⟩ := crossings.1
  exact Set.disjoint_left.mp (disjoint_vertexHull_of_injective_evaluateTriangles faces chart.extrinsic h
    _ _ edge face (by decide)) ha hb

/-- Moving the spatial vertices while retaining these determining lengths cannot remove
the crossings and give a flat embedding. A hexagonal embedding must change the intrinsic data. -/
theorem no_embedding_with_these_lengths (q : Vertex → Point3) (hf : ∀ v, FlatAt q v)
    (h : ∀ a b, determiningEdge a b = true →
      dist (Type2.euclideanPoint (q a)) (Type2.euclideanPoint (q b)) =
        dist (Type2.euclideanPoint (chart.extrinsic a)) (Type2.euclideanPoint (chart.extrinsic b))) :
    ¬ Function.Injective (evaluateTriangles faces q) :=
  fun he => not_injective (injective_of_determining_lengths q chart.extrinsic he hf h)

/-- A facewise isometry from the hexagonal torus with the Type 5 triangulation.
The spatial map identifies points of the disjoint edge 13 and triangle 024. -/
theorem hexagonal_map_by_faces :
    let τ : ℂ := ((1/2 : ℝ) : ℂ) + (Real.sqrt 3 / 2 : ℝ) * Complex.I
    ∃ (H : triangleWeightSpace faces ≃ₜ ComplexTorus 1 τ)
      (F : ComplexTorus 1 τ → Point3) (P : Triangle → Vertex → ℂ),
      Continuous F ∧ ¬ Function.Injective F ∧
      (∀ u, F (H u) = evaluateTriangles faces chart.extrinsic u) ∧
      (∀ f ∈ faces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection 1 τ (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ faces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        squared3 (F (H u)-F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  have hy : 0 < chart.y := by dsimp [chart]; positivity
  obtain ⟨H,F,P,hcont,hF,hP,hm⟩ := Continuation.marked_map_by_faces edge_lengths hy (fun _ hf => face_positive hf)
  have hx : chart.x = 1/2 := by norm_num [chart]
  change ∃ _ _ _, _
  rw [← hx]
  refine ⟨H,F,P,hcont,?_,hF,hP,hm⟩
  intro hinj
  apply not_injective
  intro a b he
  exact H.injective (hinj (by simpa only [hF] using he))

end OrigamiTorus.Type5.HexagonalFold
