module

public import OrigamiTorus.EightVertex.Type5.ChartBounds
public import OrigamiTorus.EightVertex.Type5.ContinuationTorus
public import OrigamiTorus.EightVertex.Type5.OffRaySeparation
import Mathlib.Tactic

/-! An embedded oblique modulus box containing the base point (d,U) = (1/4,1/2)
of the off-ray continuation. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type5.OffRayBase

open Inclusion IntervalDyadicReal BoxArithmetic

/-- Store each intrinsic core coordinate as (horizontal, y times vertical). -/
def grid : Vertex → Plane ℚ :=
  ![(0,0), (0,0), (1903/8192, -72710356991/68719476736),
    (1073741823/2147483648, 28632416275/163208757248),
    (-3/32, 133347454740336344998423771343888576536231/450883210163767894319335326818189031768064),
    (-137/512, -1687/2048), (0,0), (0,0)]

def chart (x v : ℝ) : RadicalChart where
  x := x
  y := Real.sqrt v
  core i := ((grid i).1, (grid i).2 / Real.sqrt v)
  origin := by norm_num [grid]
  rootSign i := i == 3
  leafSign i := i != 6

def radius : ℚ := 1 / 2^80

/-- The variables are x and v = y². -/
def Box (x v : ℝ) : Prop :=
  x ∈ Set.Icc (((1/4 - radius : ℚ) : ℝ)) (((1/4 + radius : ℚ) : ℝ)) ∧
  v ∈ Set.Icc (((31/16 - radius : ℚ) : ℝ)) (((31/16 + radius : ℚ) : ℝ))

private def enclose {v : ℝ} (a b : ℚ) (h : v ∈ Set.Icc (a : ℝ) (b : ℝ)) : Bound v :=
  ⟨Continuation.enclosure a b, by
    rw [mem_iff_mem_map]
    exact Interval.mem_Icc_of_le (ratCast_mem _ _) h.1 h.2 (ratCast_mem _ _)⟩

private def bounds {x v : ℝ} (h : Box x v) : (chart x v).Bounds :=
  let Y := sqrt (enclose (31/16 - radius) (31/16 + radius) h.2)
  ⟨enclose (1/4 - radius) (1/4 + radius) h.1, Y,
    fun i => (rational (grid i).1, divide (rational (grid i).2) Y)⟩

-- Every computed interval depends only on the rational box. Its membership
-- proof can refer to x and v, so the Boolean checks have open real indices.
-- The kernel checks reflexivity after reducing the Boolean to true.
local macro "check_interval" : tactic => `(tactic|
  run_tac (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.mkEqRefl (Lean.mkConst ``Bool.true)))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem good {x v : ℝ} (h : Box x v) : (chart x v).Good := by
  apply (bounds h).good_of_regular
  check_interval

private def coordinate (c : RadicalChart) (i : Vertex) : Fin 5 → ℝ :=
  ![(c.intrinsic i).1, (c.intrinsic i).2, (c.extrinsic i).1, (c.extrinsic i).2.1,
    (c.extrinsic i).2.2]

private def boundAt {x v : ℝ} (h : Box x v) (i : Vertex) (j : Fin 5) :
    Bound (coordinate (chart x v) i j) :=
  match j with
  | ⟨0,_⟩ => ((bounds h).intrinsic i).1
  | ⟨1,_⟩ => ((bounds h).intrinsic i).2
  | ⟨2,_⟩ => ((bounds h).spatial i).1
  | ⟨3,_⟩ => ((bounds h).spatial i).2.1
  | ⟨4,_⟩ => ((bounds h).spatial i).2.2

/-- Centers in units of 2⁻³⁰, with radius one unit. -/
private def centers : Vertex → Fin 5 → ℚ :=
  ![![536869725, -610604172, -103832497, -806402734, 1476],
    ![0, 0, 0, 0, 0],
    ![249430016, -816197852, 249430016, -816197852, 0],
    ![536870912, 135329836, 456214557, -313697683, 2565591],
    ![-100663296, 228139078, 158583508, -184710882, -53978692],
    ![-287309824, -635424776, -287309824, -635424776, 0],
    ![254581575, 725656030, -13841047, -768891230, -1775918],
    ![-49358580, 30428902, 55447943, -16959782, 280973]]

private def lower (i : Vertex) (j : Fin 5) : ℚ := (centers i j - 1) / 2^30
private def upper (i : Vertex) (j : Fin 5) : ℚ := (centers i j + 1) / 2^30

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem endpoints {x v : ℝ} (h : Box x v) :
    (List.finRange 8).all (fun i => (List.finRange 5).all fun j =>
      positive (minus (boundAt h i j) (rational (lower i j))).range &&
      positive (minus (rational (upper i j)) (boundAt h i j)).range) = true := by
  check_interval

private def small {x v : ℝ} (h : Box x v) (i : Vertex) (j : Fin 5) :
    Bound (coordinate (chart x v) i j) := by
  have row := List.all_eq_true.mp (endpoints h) i (List.mem_finRange i)
  have ends := List.all_eq_true.mp row j (List.mem_finRange j)
  simp only [Bool.and_eq_true] at ends
  exact enclose (lower i j) (upper i j)
    ⟨(sub_pos.mp (positive_of_check _ ends.1)).le, (sub_pos.mp (positive_of_check _ ends.2)).le⟩

private def intrinsicSmall {x v : ℝ} (h : Box x v) (i : Vertex) : PlaneBounds ((chart x v).intrinsic i) :=
  (small h i 0, small h i 1)

private def spatialSmall {x v : ℝ} (h : Box x v) (i : Vertex) : SpaceBounds ((chart x v).extrinsic i) :=
  (small h i 2, small h i 3, small h i 4)

private def area {x v : ℝ} (h : Box x v) (f : Triangle) :
    Bound (markedFaceCross (Continuation.shift x (Real.sqrt v)) (chart x v).intrinsic f) :=
  let d (i : Vertex) :=
    planeMinus (planePlus (intrinsicSmall h i) ((bounds h).shift f.1 i)) (intrinsicSmall h f.1)
  crossBounds (d f.2.1) (d f.2.2)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem positive_faces {x v : ℝ} (h : Box x v) {f : Triangle} (hf : f ∈ faces) :
    0 < markedFaceCross (Continuation.shift x (Real.sqrt v)) (chart x v).intrinsic f := by
  have check : faces.all (fun g => positive (area h g).range) = true := by check_interval
  exact positive_of_check (area h f) (List.all_eq_true.mp check f hf)

private def vol {x v : ℝ} (h : Box x v) (a b c d : Vertex) :=
  RadicalChart.bracketBound (spatialSmall h) a b c d

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem signs {x v : ℝ} (h : Box x v) : OffRay.Signs (chart x v).extrinsic := by
  constructor
  · exact neg_pos.mp (positive_of_check (neg (vol h 1 2 3 4)) (by check_interval))
  · exact positive_of_check (vol h 1 2 3 5) (by check_interval)
  · exact neg_pos.mp (positive_of_check (neg (vol h 1 2 4 5)) (by check_interval))
  · exact neg_pos.mp (positive_of_check (neg (vol h 1 3 4 5)) (by check_interval))
  · exact positive_of_check (vol h 2 3 4 5) (by check_interval)
  · exact positive_of_check (vol h 0 1 2 5) (by check_interval)
  · exact neg_pos.mp (positive_of_check (neg (vol h 0 1 3 5)) (by check_interval))
  · exact neg_pos.mp (positive_of_check (neg (vol h 0 2 3 4)) (by check_interval))
  · exact positive_of_check (vol h 0 2 4 5) (by check_interval)
  · exact neg_pos.mp (positive_of_check (neg (vol h 1 2 3 6)) (by check_interval))
  · exact positive_of_check (vol h 1 2 4 7) (by check_interval)
  · exact neg_pos.mp (positive_of_check (neg (vol h 1 3 5 7)) (by check_interval))
  · exact neg_pos.mp (positive_of_check (neg (vol h 2 3 5 7)) (by check_interval))
  · exact neg_pos.mp (positive_of_check (neg (vol h 2 4 5 6)) (by check_interval))
  · exact positive_of_check (vol h 0 2 4 6) (by check_interval)
  · exact positive_of_check (vol h 0 4 5 6) (by check_interval)
  · exact neg_pos.mp (positive_of_check (neg (vol h 2 3 6 7)) (by check_interval))

/-- Every upper half-plane modulus in the oblique box gives an embedded flat torus. -/
theorem torus_by_faces {x y : ℝ} (hy : 0 < y) (h : Box x (y^2)) :
    let τ : ℂ := x+y*Complex.I
    ∃ (H : triangleWeightSpace faces ≃ₜ ComplexTorus 1 τ)
      (F : ComplexTorus 1 τ → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles faces (chart x (y^2)).extrinsic u) ∧
      (∀ f ∈ faces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection 1 τ (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ faces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        squared3 (F (H u)-F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  have sqrt_y : Real.sqrt (y^2) = y := Real.sqrt_sq hy.le
  exact Continuation.marked_embedding_by_faces
    (p := (chart x (y^2)).intrinsic)
    (fun he => by simpa only [RadicalChart.EdgeMatch, chart, sqrt_y] using
      RadicalChart.all_edge_lengths (good h) he)
    hy (fun _ hf => by simpa only [sqrt_y] using positive_faces h hf)
    (OffRay.spatial_embedding (signs h))

end OrigamiTorus.Type5.OffRayBase
