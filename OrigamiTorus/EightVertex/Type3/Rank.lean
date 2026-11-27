module

public import OrigamiTorus.EightVertex.Type3.Data
public import OrigamiTorus.EightVertex.Type6.Inflation
import OrigamiTorus.EightVertex.Type6.Rank
import OrigamiTorus.EightVertex.Type6.Signs
import Mathlib.Tactic

/-! The fixed-period length Jacobian for the original diagonal. -/

public section

namespace OrigamiTorus.Type3

theorem planarLengthsMatch (second : Bool) (x w : ℝ) :
    PlanarLengthsMatch edgeTable second x w := by
  intro e
  by_cases h : e = 4
  · subst e
    norm_num [edgeTable, intrinsicPoint, translatePoint]
  · simpa only [edgeTable, ite_eq_right h, foldedEdgeSquared, intrinsicEdgeSquared] using type6_samePlanarLengths second x w e

private theorem weightedPairIdentity (a b c d x y z u X Y Z U : ℝ) :
    a*b*(y-x)*(Y-X) + a*c*(z-x)*(Z-X) + a*d*(u-x)*(U-X) +
      b*c*(z-y)*(Z-Y) + b*d*(u-y)*(U-Y) + c*d*(u-z)*(U-Z) =
    (a+b+c+d)*(a*x*X+b*y*Y+c*z*Z+d*u*U) -
      (a*x+b*y+c*z+d*u)*(a*X+b*Y+c*Z+d*U) := by ring

/-- The planar affine dependence gives a linear dependence of the six
squared length derivatives on the quadrilateral. -/
private theorem diagonal_relation (w : ℝ) (p v : Vertex → ℝ × ℝ)
    (h01 : halfLengthDerivative w (p 0) (p 1) (v 0) (v 1) = 0)
    (h02 : halfLengthDerivative w (p 0) (p 2) (v 0) (v 2) = 0)
    (h12 : halfLengthDerivative w (p 1) (p 2) (v 1) (v 2) = 0)
    (h15 : halfLengthDerivative w (p 1) (p 5) (v 1) (v 5) = 0)
    (h25 : halfLengthDerivative w (p 2) (p 5) (v 2) (v 5) = 0)
    (ha : area p 1 2 5 ≠ 0) (hd : area p 1 2 0 ≠ 0) :
    halfLengthDerivative w (p 0) (p 5) (v 0) (v 5) = 0 := by
  let a := area p 1 2 5
  let b := -area p 0 2 5
  let c := area p 0 1 5
  let d := -area p 0 1 2
  have hm : a+b+c+d = 0 := by dsimp [a,b,c,d,area]; ring
  have hx : a*(p 0).1+b*(p 1).1+c*(p 2).1+d*(p 5).1 = 0 := by
    dsimp [a,b,c,d,area]
    ring
  have hy : a*(p 0).2+b*(p 1).2+c*(p 2).2+d*(p 5).2 = 0 := by
    dsimp [a,b,c,d,area]
    ring
  have hd' : d ≠ 0 := by
    have he : area p 0 1 2 = area p 1 2 0 := by unfold area; ring
    simpa [d,he] using hd
  have Hx := weightedPairIdentity a b c d (p 0).1 (p 1).1 (p 2).1 (p 5).1
    (v 0).1 (v 1).1 (v 2).1 (v 5).1
  have Hy := weightedPairIdentity a b c d (p 0).2 (p 1).2 (p 2).2 (p 5).2
    (v 0).2 (v 1).2 (v 2).2 (v 5).2
  simp only [hm,hx,hy,zero_mul,sub_zero] at Hx Hy
  apply (mul_eq_zero.mp (show a*d*halfLengthDerivative w (p 0) (p 5) (v 0) (v 5) = 0 by
    unfold halfLengthDerivative at *
    linear_combination w*Hx + Hy - a*b*h01 - a*c*h02 - b*c*h12 - b*d*h15 - c*d*h25)).resolve_left
  exact mul_ne_zero ha hd'

/-- Restoring the paper's diagonal preserves the nonsingular length-matching
Jacobian, because the two intrinsic and folded planar quadrilaterals coincide. -/
theorem edgeDerivative_injective (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    (m : SheetMotion) (he : ∀ e, fixedPeriodDerivative edgeTable second x w m e = 0) : m = 0 := by
  let p := stripPoint second x w
  let v : Vertex → ℝ × ℝ := fun i => FoldedMotion m i - IntrinsicMotion m i
  have h01 := he 0
  have h02 := he 1
  have h12 := he 4
  have h15 := he 7
  have h25 := he 11
  have h (i : EdgeIndex) (hi : i ≠ 4) :
      fixedPeriodDerivative edgeTable second x w m i = edgeDerivative second x w m i := by
    simp only [fixedPeriodDerivative,edgeTable,ite_eq_right hi,edgeDerivative]
  have hs := type6_flipSigns second x w hd
  apply type6_edgeDerivative_injective second x w hd m
  intro e
  by_cases h₄ : e = 4
  · subst e
    have hdg : halfLengthDerivative w (p 0) (p 5) (v 0) (v 5) = 0 := by
      apply diagonal_relation w p v _ _ _ _ _ hs.2.1.ne hs.1.ne'
      all_goals
        norm_num [p,v,halfLengthDerivative,Prod.fst_sub,Prod.snd_sub]
        first
        | rw [h 0 (by decide)] at h01
          norm_num [edgeDerivative,edgePeriod,intrinsicPoint,translatePoint,halfLengthDerivative] at h01
          linear_combination h01
        | rw [h 1 (by decide)] at h02
          norm_num [edgeDerivative,edgePeriod,intrinsicPoint,translatePoint,halfLengthDerivative] at h02
          linear_combination h02
        | norm_num [fixedPeriodDerivative,edgeTable,intrinsicPoint,translatePoint,halfLengthDerivative] at h12
          linear_combination h12
        | rw [h 7 (by decide)] at h15
          norm_num [edgeDerivative,edgePeriod,intrinsicPoint,translatePoint,halfLengthDerivative] at h15
          linear_combination h15
        | rw [h 11 (by decide)] at h25
          norm_num [edgeDerivative,edgePeriod,intrinsicPoint,translatePoint,halfLengthDerivative] at h25
          linear_combination h25
    norm_num [edgeDerivative,edgePeriod,intrinsicPoint,translatePoint,halfLengthDerivative]
    norm_num [p,v,halfLengthDerivative,Prod.fst_sub,Prod.snd_sub] at hdg
    linear_combination hdg
  · exact h e h₄ ▸ he e

end OrigamiTorus.Type3
