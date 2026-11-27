module

public import OrigamiTorus.Type6Data
import Mathlib.Tactic

/-! Squared edge length equations for the Type 6 planar construction. -/

@[expose] public section

namespace OrigamiTorus

set_option maxHeartbeats 6000000 in
/-- The folded and intrinsic planar families have the same length on all twenty-four edges. -/
theorem type6_samePlanarLengths (second : Bool) (x w : ℝ) (e : EdgeIndex) :
    foldedEdgeSquared second x w e = intrinsicEdgeSquared second x w e := by
  cases second <;> fin_cases e
  all_goals
    norm_num [foldedEdgeSquared, intrinsicEdgeSquared, intrinsicPoint, stripPoint,
      edgePeriod, translatePoint, scaledSquaredDistance]
  all_goals ring_nf
  all_goals exact Or.inl trivial

theorem type6_edgePeriodCovers :
    let edgeList := (List.finRange 24).map (fun e => (edgePeriod e).1)
    let flipEdges := type6FlippedFaces.flatMap faceEdges
    edgeList.Nodup ∧ edgeList.all flipEdges.contains = true ∧
      flipEdges.all edgeList.contains = true := by
  decide +kernel


def halfLengthDerivative (w : ℝ) (p q dp dq : ℝ × ℝ) : ℝ :=
  w * (q.1 - p.1) * (dq.1 - dp.1) + (q.2 - p.2) * (dq.2 - dp.2)

/-- Half the horizontal derivative of the squared-edge-length matching equations. -/
noncomputable def edgeDerivative (second : Bool) (x w : ℝ) (m : Fin 24 → ℝ) (e : EdgeIndex) : ℝ :=
  let ((a,b), d) := edgePeriod e
  let p := stripPoint second x w
  let q := intrinsicPoint second x w
  halfLengthDerivative w (p a) (p b) (FoldedMotion m a) (FoldedMotion m b) -
    halfLengthDerivative w (q a) (translatePoint x w d (q b))
      (IntrinsicMotion m a) (IntrinsicMotion m b)

end OrigamiTorus
