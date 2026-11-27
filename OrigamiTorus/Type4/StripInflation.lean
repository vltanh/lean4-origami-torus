module

public import OrigamiTorus.Type4.StripRank
public import OrigamiTorus.Type7.Tiling
import Mathlib.Tactic

/-! Inflation and intrinsic realization at a strip point with a strict lift. -/

@[expose] public section

namespace OrigamiTorus.Type4

private theorem spatialAngleShape_smul (q : Vertex → Point3) {r : ℝ} (hr : r ≠ 0) :
    spatialAngleShape (r • q) = spatialAngleShape q := by
  apply Prod.ext
  · funext i
    change coneAngles Type7.flippedFaces (Type2.euclideanPoint ∘ (r • q)) i.succ = _
    have he : Type2.euclideanPoint ∘ (r • q) = fun v => r • Type2.euclideanPoint (q v) := by
      funext v
      exact Type2.euclideanPoint.map_smul r (q v)
    rw [he,coneAngles_smul _ _ hr]
    rfl
  · change flippedMarkedShape (Type7.spatialEdgeSq (r • q)) =
      flippedMarkedShape (Type7.spatialEdgeSq q)
    have he : Type7.spatialEdgeSq (r • q) = fun a b => r^2*Type7.spatialEdgeSq q a b := by
      funext a b
      simp only [Type7.spatialEdgeSq, Pi.smul_apply, ← smul_sub, squared3_smul]
    rw [he]
    simp only [flippedMarkedShape, flippedMarkingDisplacements, Type7.triangleCorner,
      developedCorner_scale _ _ _ _ _ (pow_ne_zero _ hr)]

/-- Changing the common length scale preserves the spatial rank. -/
theorem SpatiallyRegular.smul {q : Vertex → Point3} (hq : SpatiallyRegular q)
    {r : ℝ} (hr : r ≠ 0) : SpatiallyRegular (r • q) := by
  let L : (Vertex → Point3) →L[ℝ] (Vertex → Point3) := r⁻¹ • ContinuousLinearMap.id ℝ _
  have he : L (r • q) = q := by simp [L,smul_smul,hr]
  have hs : Function.Surjective L := fun p => ⟨r • p,by simp [L,smul_smul,hr]⟩
  have heq : spatialAngleShape ∘ L = spatialAngleShape :=
    funext fun p => spatialAngleShape_smul p (inv_ne_zero hr)
  have hC : ContDiffAt ℝ 1 spatialAngleShape (L (r • q)) := by rw [he]; exact hq.1
  have h₁ := hC.comp (r • q) L.contDiff.contDiffAt
  have h₂ := (hC.differentiableAt (by decide)).hasFDerivAt.comp
    (r • q) L.hasFDerivAt
  rw [heq] at h₁ h₂
  refine ⟨h₁,?_⟩
  rw [h₂.fderiv]
  exact (he.symm ▸ hq.2).comp hs

/-- An embedded height lift at a strip point gives a regular piecewise-isometric
Type 4 realization at that modulus and the requested lattice scale. -/
theorem strip_regular_realizes_of_lift {second : Bool} {x w : ℝ} (hd : domain second x w)
    (h : Vertex → ℝ) (hemb : Function.Injective
      (evaluateTriangles Type7.flippedFaces (angleLift (stripBase second x w) h 1)))
    (a b D : ℂ) (refl : Bool) (hD : D ≠ 0)
    (hL : complexSimilarity D refl '' complexLattice 1 (x+Real.sqrt w*Complex.I) = complexLattice a b) :
    Type7.ChartRealizesWith true a b SpatiallyRegular := by
  let z := stripBase second x w
  let y := Real.sqrt w
  have hy : 0 < y := Real.sqrt_pos.mpr (domain_bounds hd).2.2
  have ha (v : Vertex) : coneAngles Type7.flippedFaces z v = 2*Real.pi := by
    rw [coneAngles_eq_chart_list]
    exact flipped_euclidean_cone_angle hd v
  obtain ⟨q,he,hflat,hm,hreg⟩ := regular_embedded_flat_markedShape_of_planar z h ⟨x,y⟩ hy
    (strip_markingChartValid hd) (trapezoid_flippedMarkedShape hd) hemb ha
    (strip_flipped_corners_nondegenerate hd) (strip_flippedAngleShape_derivative_surjective hd)
  refine Type7.realizes_of_markedShape_with true q he hflat x y hy ?_ a b D refl hD hL
    (fun r hr => hreg.smul hr.ne')
  change flippedMarkedShape (Type7.spatialEdgeSq q) = _
  rw [hm]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]

/-- An embedded height lift at a strip point gives a Type 4 realization. -/
theorem strip_realizes_of_lift {second : Bool} {x w : ℝ} (hd : domain second x w)
    (h : Vertex → ℝ) (hemb : Function.Injective
      (evaluateTriangles Type7.flippedFaces (angleLift (stripBase second x w) h 1)))
    (a b D : ℂ) (refl : Bool) (hD : D ≠ 0)
    (hL : complexSimilarity D refl '' complexLattice 1 (x+Real.sqrt w*Complex.I) = complexLattice a b) :
    Type7.ChartRealizes true a b :=
  (strip_regular_realizes_of_lift hd h hemb a b D refl hD hL).realizes

end OrigamiTorus.Type4
