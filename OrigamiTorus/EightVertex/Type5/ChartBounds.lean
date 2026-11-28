module

public import OrigamiTorus.EightVertex.Type5.Continuation

/-! Enclosures for the metric reconstruction, the oriented faces and the spatial brackets
of a Type 5 radical chart. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type5.RadicalChart

open Inclusion IntervalDyadicReal BoxArithmetic

/-- Bounds on the input coordinates. All derived quantities use the radical chart's
own root and leaf choices. -/
structure Bounds (c : RadicalChart) where
  x : Bound c.x
  y : Bound c.y
  core : ∀ j, PlaneBounds (c.core j)

namespace Bounds

variable {c : RadicalChart} (B : Bounds c)

def shift (i j : Vertex) : PlaneBounds (Continuation.shift c.x c.y i j) :=
  Continuation.shiftBounds B.x B.y (squareShift i j)

def offset (i j : Vertex) : PlaneBounds (c.offset i j) :=
  planeMinus (B.core i) (B.shift i j)

def rootRad (j : Vertex) :
    Bound (rootRadicand (c.core 2) (c.core 5) (c.offset 2 j) (c.offset 5 j) (c.core j)) :=
  let h := project (B.core 2) (B.core 5) (B.offset 2 j) (B.offset 5 j) (B.core j)
  minus (squaredPlane (B.core j)) (squaredPlane h)

def root (j : Vertex) : SpaceBounds (c.rootPoint j) :=
  BoxArithmetic.root (B.core 2) (B.core 5) (B.offset 2 j) (B.offset 5 j) (B.core j) (c.rootSign j)

def leaf (j : Vertex) : LeafBounds (c.leaf j) :=
  BoxArithmetic.leaf (B.core 2) (B.core 5) (B.root 3) (B.root 4)
    (B.offset 2 j) (B.offset 5 j) (B.offset 3 j) (B.offset 4 j)

def regular : Bool :=
  positive (crossBounds (B.core 5) (B.core 2)).range &&
    roots.all (fun i => positive (B.rootRad i).range) &&
    leaves.all (fun i =>
      let L := B.leaf i
      positive (squaredPlane L.normal).range &&
        (positive L.quadratic.1.range || positive (neg L.quadratic.1).range) &&
        positive L.discriminant.range)

theorem good_of_regular (h : B.regular = true) : c.Good := by
  simp only [regular, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨ha, hr⟩, hl⟩ := h
  refine ⟨?_, fun i hi => (positive_of_check (B.rootRad i) (hr i hi)), ?_⟩
  · have hcross := positive_of_check (crossBounds (B.core 5) (B.core 2)) ha
    unfold cross at hcross ⊢
    linarith
  · intro i hi
    obtain ⟨⟨hn, hq⟩, hd⟩ := hl i hi
    let L := B.leaf i
    refine ⟨(positive_of_check (squaredPlane L.normal) hn).ne', ?_,
      (positive_of_check L.discriminant hd).le⟩
    rcases hq with hp | hm
    · exact (positive_of_check L.quadratic.1 hp).ne'
    · exact (neg_pos.mp (positive_of_check (neg L.quadratic.1) hm)).ne

def intrinsic (i : Vertex) : PlaneBounds (c.intrinsic i) :=
  if h : i ∈ leaves then by
    simp only [RadicalChart.intrinsic, ite_eq_left h]
    exact (B.leaf i).intrinsicAt ((B.leaf i).parameter (c.leafSign i))
  else by simpa only [RadicalChart.intrinsic, ite_eq_right h] using B.core i

def spatial (i : Vertex) : SpaceBounds (c.extrinsic i) :=
  if h : i ∈ leaves then by
    simp only [RadicalChart.extrinsic, ite_eq_left h]
    exact (B.leaf i).extrinsicAt ((B.leaf i).parameter (c.leafSign i))
  else if k : i ∈ roots then by
    simpa only [RadicalChart.extrinsic, ite_eq_right h, ite_eq_left k] using B.root i
  else by
    simpa only [RadicalChart.extrinsic, ite_eq_right h, ite_eq_right k] using height (B.core i) zero

end Bounds

/-- Enclose a signed tetrahedron determinant from four coordinate boxes. -/
def bracketBound {r : Vertex → Point3} (R : ∀ i, SpaceBounds (r i)) (a b c d : Vertex) :
    Bound (affineBracket (r a) (r b) (r c) (r d)) :=
  let diff (i : Vertex) : SpaceBounds (r i - r a) :=
    (minus (R i).1 (R a).1, minus (R i).2.1 (R a).2.1, minus (R i).2.2 (R a).2.2)
  let u := diff b
  let v := diff c
  let w := diff d
  plus (minus (times u.1 (minus (times v.2.1 w.2.2) (times v.2.2 w.2.1)))
    (times u.2.1 (minus (times v.1 w.2.2) (times v.2.2 w.1))))
    (times u.2.2 (minus (times v.1 w.2.1) (times v.2.1 w.1)))

end OrigamiTorus.Type5.RadicalChart
