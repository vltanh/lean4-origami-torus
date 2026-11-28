module

public import OrigamiTorus.EightVertex.Type5.RadicalChart
public import OrigamiTorus.EightVertex.Type5.BoxArithmetic
public meta import OrigamiTorus.Certificates.RadicalIntervals
import OrigamiTorus.Certificates.RadicalIntervals
import Mathlib.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-! The exact Type 5 radical family on the near-square modulus box. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type5.Continuation

open Inclusion IntervalDyadicReal BoxArithmetic

/-- The near-square modulus box certified by direct interval evaluation. -/
def ModulusBox (x y : ℝ) : Prop :=
  x ∈ Set.Icc 0 ((1 / 512)^4) ∧ y ∈ Set.Icc 1 (1 + (1 / 512)^4)

theorem modulus_bounds {x y : ℝ} (h : ModulusBox x y) :
    0 ≤ x ∧ x ≤ 1/2 ∧ 0 < y ∧ 1 ≤ x^2+y^2 := by
  obtain ⟨⟨hx, hx'⟩, ⟨hy, _⟩⟩ := h
  refine ⟨hx, hx'.trans (by norm_num), zero_lt_one.trans_le hy, ?_⟩
  nlinarith [sq_nonneg x, sq_nonneg (y - 1)]

/-- The dyadic-grid core for the periods `(1,0)` and `(x,y)` at `s = 1/512`. -/
def core (x y : ℝ) : Vertex → Plane ℝ :=
  let X : ℝ := ((29 / 64 : ℚ) : ℝ)
  let half : ℝ := ((1 / 2 : ℚ) : ℝ)
  let displacement : ℝ := ((1 / 512 : ℚ) : ℝ)^2
  ![(0,0), (0,0), (X, ((displacement - half) * (x^2 + y^2) - x * X) / y),
    (half - displacement, ((5 / 64 : ℚ) : ℝ) * y),
    (((-4 / 64 : ℚ) : ℝ), ((27 / 64 : ℚ) : ℝ) * y),
    (((-2 / 64 : ℚ) : ℝ), ((-12 / 64 : ℚ) : ℝ) * y), (0,0), (0,0)]

theorem core_at_square (j : Vertex) : core (0 : ℝ) 1 j = squareCore j := by
  fin_cases j <;> norm_num [core, squareCore]

def offset (x y : ℝ) (a b : Vertex) : Plane ℝ :=
  core x y a-shift x y a b

def rootPoint (x y : ℝ) (j : Vertex) : Point3 :=
  makeRoot (core x y 2) (core x y 5) (offset x y 2 j) (offset x y 5 j) (core x y j) (j == 3)

def leaf (x y : ℝ) (j : Vertex) : LeafData ℝ :=
  normalizedLeafData (core x y 2) (core x y 5) (rootPoint x y 3) (rootPoint x y 4)
    (offset x y 2 j) (offset x y 5 j) (offset x y 3 j) (offset x y 4 j)

def leafParameter (x y : ℝ) (j : Vertex) : ℝ :=
  let q := (leaf x y j).quadratic
  quadraticRoot q.1 q.2.1 q.2.2 (j != 6)

def intrinsic (x y : ℝ) (j : Vertex) : Plane ℝ :=
  if j ∈ leaves then (leaf x y j).intrinsicAt (leafParameter x y j) else core x y j

def extrinsic (x y : ℝ) (j : Vertex) : Point3 :=
  if j ∈ leaves then (leaf x y j).extrinsicAt (leafParameter x y j)
  else if j ∈ roots then rootPoint x y j else atHeight (core x y j) 0

theorem anchors_nondegenerate {x y : ℝ} (h : ModulusBox x y) :
    cross (core x y 2) (core x y 5) ≠ 0 := by
  obtain ⟨hx, hy⟩ := h
  apply ne_of_lt
  norm_num [cross, core]
  dyadic_interval +kernel [prec := 120]

macro "continuation_bounds" p:ident : tactic => `(tactic|
  (norm_num [extrinsic,intrinsic,leafParameter,quadraticRoot,signedRoot,makeRoot,leaf,
    normalizedLeafData,leafRootCoefficient,leafRootConstant,rootPoint,rootRadicand,projection,
    linearSolve,anchorRhs,LeafData.intrinsicAt,LeafData.extrinsicAt,LeafData.quadratic,
    LeafData.intrinsicBase,LeafData.intrinsicDirection,LeafData.extrinsicBase,LeafData.extrinsicDirection,
    LeafData.lineNormal,LeafData.lineOffset,LeafData.planarLin,discriminant,squared2,squared3,
    dot,dot3,horizontal,atHeight,smul2,smul3,cross,core,offset,shift,translatePoint,
    squareShift,positiveShift,leaves,roots]
    <;> dyadic_interval +kernel [$p := 200]))

set_option maxHeartbeats 0 in
theorem root_positive {x y : ℝ} (h : ModulusBox x y) (j : Vertex) (hj : j ∈ roots) :
    0 < rootRadicand (core x y 2) (core x y 5) (offset x y 2 j) (offset x y 5 j) (core x y j) := by
  obtain ⟨hx,hy⟩ := h
  fin_cases j <;> simp [roots] at hj
  all_goals continuation_bounds prec

theorem root_pivot_ne {x y : ℝ} (h : ModulusBox x y) : (rootPoint x y 3).2.2 ≠ 0 := by
  have hp := root_positive h 3 (by decide)
  exact (Real.sqrt_pos.mpr hp).ne'

def enclosure (a b : ℚ) : Interval Dyadic := Interval.Icc (rat a precision).lb (rat b precision).ub

private theorem enclosure_mem {a b : ℚ} {v : ℝ} (ha : (a : ℝ) ≤ v) (hb : v ≤ (b : ℝ)) :
    v ∈ enclosure a b := by
  rw [mem_iff_mem_map]
  exact Interval.mem_Icc_of_le (ratCast_mem _ _) ha hb (ratCast_mem _ _)

def xInterval : Interval Dyadic := enclosure 0 ((1 / 512)^4)
def yInterval : Interval Dyadic := enclosure 1 (1 + (1 / 512)^4)

def xBound {x y : ℝ} (h : ModulusBox x y) : Bound x := ⟨xInterval,by
  apply enclosure_mem <;> push_cast
  exact h.1.1
  exact h.1.2⟩

def yBound {x y : ℝ} (h : ModulusBox x y) : Bound y := ⟨yInterval,by
  apply enclosure_mem <;> push_cast
  exact h.2.1
  exact h.2.2⟩

def coreBounds {x y : ℝ} (X : Bound x) (Y : Bound y) (j : Vertex) :
    PlaneBounds (core x y j) :=
  let horizontal2 := rational (29 / 64)
  let displacement := sq (rational (1 / 512))
  let half := rational (1 / 2)
  let vertical2 := divide
    (minus (times (minus displacement half) (plus (sq X) (sq Y))) (times X horizontal2)) Y
  match j with
  | ⟨0, _⟩ => planeZero
  | ⟨1, _⟩ => planeZero
  | ⟨2, _⟩ => (horizontal2, vertical2)
  | ⟨3, _⟩ => (minus half displacement, times (rational (5 / 64)) Y)
  | ⟨4, _⟩ => (rational (-4 / 64), times (rational (27 / 64)) Y)
  | ⟨5, _⟩ => (rational (-2 / 64), times (rational (-12 / 64)) Y)
  | ⟨6, _⟩ => planeZero
  | ⟨7, _⟩ => planeZero
  | ⟨n + 8, h⟩ => by omega

def shiftBounds {x y : ℝ} (X : Bound x) (Y : Bound y) (d : Period) :
    PlaneBounds (translatePoint x y d (0,0)) :=
  (plus (plus zero (integer d.1)) (times (integer d.2) X),plus zero (times (integer d.2) Y))

def offsetBounds {x y : ℝ} (X : Bound x) (Y : Bound y) (a b : Vertex) : PlaneBounds (offset x y a b) :=
  planeMinus (coreBounds X Y a) (shiftBounds X Y (squareShift a b))

def rootBounds {x y : ℝ} (X : Bound x) (Y : Bound y) (j : Vertex) : SpaceBounds (rootPoint x y j) :=
  BoxArithmetic.root (coreBounds X Y 2) (coreBounds X Y 5) (offsetBounds X Y 2 j) (offsetBounds X Y 5 j)
    (coreBounds X Y j) (j == 3)

def leafBounds {x y : ℝ} (X : Bound x) (Y : Bound y) (j : Vertex) : LeafBounds (leaf x y j) :=
  BoxArithmetic.leaf (coreBounds X Y 2) (coreBounds X Y 5) (rootBounds X Y 3) (rootBounds X Y 4)
    (offsetBounds X Y 2 j) (offsetBounds X Y 5 j) (offsetBounds X Y 3 j) (offsetBounds X Y 4 j)

theorem box_ne : ModulusBox 0 1 := by
  norm_num [ModulusBox,Set.mem_Icc]

open Lean.Parser.Tactic in
macro "compute_box_ranges" loc:(location)? : tactic => `(tactic|
  dsimp only [leafBounds,BoxArithmetic.leaf,rootBounds,BoxArithmetic.root,offsetBounds,shiftBounds,
    LeafBounds.normal,LeafBounds.discriminant,LeafBounds.quadratic,LeafBounds.vBase,
    LeafBounds.vDirection,LeafBounds.uBase,LeafBounds.uDirection,LeafBounds.linear,LeafBounds.intercept,
    LeafBounds.intrinsicAt,LeafBounds.extrinsicAt,LeafBounds.parameter,coreBounds,
    BoxArithmetic.coefficient,BoxArithmetic.constant,project,solve,rhs,planeMinus,planePlus,
    planeScale,spacePlus,spaceScale,height,plane,signedSqrt,sqrt,squaredSpace,squaredPlane,
    dotBounds,dotSpace,crossBounds,plus,minus,neg,times,divide,BoxArithmetic.sq,xBound,yBound] $[$loc]?)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem leaf_checked : leaves.all (fun j =>
    let D := leafBounds (xBound box_ne) (yBound box_ne) j
    positive (squaredPlane D.normal).range && positive D.quadratic.1.range && positive D.discriminant.range) = true := by
  decide +kernel

set_option maxHeartbeats 1500000 in
theorem leaf_good {x y : ℝ} (h : ModulusBox x y) (j : Vertex) (hj : j ∈ leaves) :
    0 < squared2 (leaf x y j).lineNormal ∧ 0 < (leaf x y j).quadratic.1 ∧
      0 < discriminant (leaf x y j).quadratic.1 (leaf x y j).quadratic.2.1 (leaf x y j).quadratic.2.2 := by
  let D := leafBounds (xBound h) (yBound h) j
  have hcheck := List.all_eq_true.mp leaf_checked j hj
  have hc : (positive (squaredPlane D.normal).range && positive D.quadratic.1.range &&
      positive D.discriminant.range) = true := by
    fin_cases j <;> (dsimp only [D]; compute_box_ranges at hcheck ⊢; exact hcheck)
  simp only [Bool.and_eq_true] at hc
  exact ⟨positive_of_check (squaredPlane D.normal) hc.1.1,positive_of_check D.quadratic.1 hc.1.2,
    positive_of_check D.discriminant hc.2⟩

private def boxChart (x y : ℝ) : RadicalChart :=
  ⟨x,y,core x y,by norm_num [core],(· == 3),(· != 6)⟩

private theorem boxChart_good {x y : ℝ} (h : ModulusBox x y) : (boxChart x y).Good := by
  refine ⟨anchors_nondegenerate h,root_positive h,fun j hj => ?_⟩
  obtain ⟨hn,ha,hd⟩ := leaf_good h j hj
  exact ⟨hn.ne',ha.ne',hd.le⟩

theorem root_distances {x y : ℝ} (h : ModulusBox x y) {j : Vertex} (hj : j ∈ roots) :
    let r := rootPoint x y j
    squared3 r = squared2 (core x y j) ∧
    squared3 (r-atHeight (core x y 2) 0) = squared2 (core x y j-offset x y 2 j) ∧
    squared3 (r-atHeight (core x y 5) 0) = squared2 (core x y j-offset x y 5 j) :=
  RadicalChart.root_distances (boxChart_good h) hj

theorem leaf_distances {x y : ℝ} (h : ModulusBox x y) {j : Vertex} (hj : j ∈ leaves) :
    let p := leaf x y j
    let u := p.intrinsicAt (leafParameter x y j)
    let v := p.extrinsicAt (leafParameter x y j)
    squared3 v = squared2 u ∧
    squared3 (v-atHeight (core x y 2) 0) = squared2 (u-offset x y 2 j) ∧
    squared3 (v-atHeight (core x y 5) 0) = squared2 (u-offset x y 5 j) ∧
    squared3 (v-rootPoint x y 3) = squared2 (u-offset x y 3 j) ∧
    squared3 (v-rootPoint x y 4) = squared2 (u-offset x y 4 j) :=
  RadicalChart.leaf_distances (boxChart_good h) hj

def EdgeMatch (x y : ℝ) (a b : Vertex) : Prop :=
  squared3 (extrinsic x y b-extrinsic x y a) = squared2 (intrinsic x y b-intrinsic x y a+shift x y a b)

/-- All marked edge lengths agree identically throughout the modulus box. -/
theorem all_edge_lengths {x y : ℝ} (h : ModulusBox x y) {a b : Vertex} (he : orderedEdge a b ∈ edgeList) :
    EdgeMatch x y a b :=
  RadicalChart.all_edge_lengths (boxChart_good h) he

def coordinate (x y : ℝ) (j : Vertex) : Fin 5 → ℝ :=
  ![(intrinsic x y j).1,(intrinsic x y j).2,
    (extrinsic x y j).1,(extrinsic x y j).2.1,(extrinsic x y j).2.2]

def coordinateIntervals {x y : ℝ} (h : ModulusBox x y) (j : Vertex) : Fin 5 → Interval Dyadic :=
  if j ∈ leaves then
    let D := leafBounds (xBound h) (yBound h) j
    let t := D.parameter (j != 6)
    let p := D.intrinsicAt t
    let q := D.extrinsicAt t
    ![p.1.range,p.2.range,q.1.range,q.2.1.range,q.2.2.range]
  else
    let p := coreBounds (xBound h) (yBound h) j
    if j ∈ roots then
      let q := rootBounds (xBound h) (yBound h) j
      ![p.1.range,p.2.range,q.1.range,q.2.1.range,q.2.2.range]
    else ![p.1.range,p.2.range,p.1.range,p.2.range,BoxArithmetic.zero.range]

def coordinateBox (j : Vertex) : Fin 5 → Interval Dyadic := coordinateIntervals box_ne j

set_option maxHeartbeats 1500000 in
theorem coordinate_mem {x y : ℝ} (h : ModulusBox x y) (j : Vertex) (i : Fin 5) :
    coordinate x y j i ∈ coordinateBox j i := by
  have he : coordinateIntervals h j = coordinateBox j := by
    unfold coordinateBox coordinateIntervals
    split
    · fin_cases j <;> compute_box_ranges
    · split <;> fin_cases j <;> compute_box_ranges
  rw [← he]
  unfold coordinate coordinateIntervals intrinsic extrinsic
  split
  ·
    let D := leafBounds (xBound h) (yBound h) j
    let t := D.parameter (j != 6)
    exact Fin.cases (D.intrinsicAt t).1.mem (Fin.cases (D.intrinsicAt t).2.mem
      (Fin.cases (D.extrinsicAt t).1.mem (Fin.cases (D.extrinsicAt t).2.1.mem
        (Fin.cases (D.extrinsicAt t).2.2.mem (fun k => k.elim0))))) i
  · split
    ·
      let p := coreBounds (xBound h) (yBound h) j
      let q := rootBounds (xBound h) (yBound h) j
      exact Fin.cases p.1.mem (Fin.cases p.2.mem (Fin.cases q.1.mem (Fin.cases q.2.1.mem
        (Fin.cases q.2.2.mem (fun k => k.elim0))))) i
    ·
      let p := coreBounds (xBound h) (yBound h) j
      exact Fin.cases p.1.mem (Fin.cases p.2.mem (Fin.cases p.1.mem (Fin.cases p.2.mem
        (Fin.cases BoxArithmetic.zero.mem (fun k => k.elim0))))) i

end OrigamiTorus.Type5.Continuation
