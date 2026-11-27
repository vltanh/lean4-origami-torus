module

public import OrigamiTorus.Type4Angles
public import OrigamiTorus.ConvexFlip
public import OrigamiTorus.AngleDerivative
import Mathlib.Tactic

/-! The convex diagonal exchange preserves the Euclidean angle sums. -/

@[expose] public section

open Filter InnerProductGeometry
open scoped Topology

namespace OrigamiTorus.Type4

open Type7 (physicalComplex)
open Type5 (Plane)

private theorem physical_interpolate (w s : ℝ) (a b : Plane ℝ) :
    physicalComplex w ((1-s) • a+s • b) = (1-s) • physicalComplex w a+s • physicalComplex w b := by
  apply Complex.ext <;> simp [physicalComplex] <;> ring

private theorem physical_ne_of_ne (w : ℝ) (hw : 0 < w) {a b : Plane ℝ}
    (hn : a ≠ b) : physicalComplex w a ≠ physicalComplex w b := by
  intro he
  apply hn
  have h1 := congrArg Complex.re he
  have h2 := congrArg Complex.im he
  change Real.sqrt w*a.2 = Real.sqrt w*b.2 at h2
  exact Prod.ext h1 (mul_left_cancel₀ (Real.sqrt_pos.mpr hw).ne' h2)

theorem flip_angle_sum (p : Vertex → Plane ℝ) (w : ℝ) (hw : 0 < w)
    (h356 : 0 < area p 3 5 6) (h352 : area p 3 5 2 < 0)
    (h623 : area p 6 2 3 < 0) (h625 : 0 < area p 6 2 5) (v : Vertex) :
    let q := physicalComplex w ∘ p
    (Type7.flippedFaces.map (chartEuclideanCorner q v)).sum =
      (Type7.faces.map (chartEuclideanCorner q v)).sum := by
  obtain ⟨s,t,hs,hs',ht,ht',he⟩ := diagonal_intersection p 3 5 6 2 h356 h352 h623 h625
  let q := physicalComplex w ∘ p
  have hp : (1-s) • q 3+s • q 5 = (1-t) • q 6+t • q 2 := by
    change (1-s) • physicalComplex w (p 3)+s • physicalComplex w (p 5) =
      (1-t) • physicalComplex w (p 6)+t • physicalComplex w (p 2)
    rw [← physical_interpolate,← physical_interpolate,he]
  have h35 : q 3 ≠ q 5 := by
    apply physical_ne_of_ne w hw
    intro h
    have hz : area p 3 5 6 = 0 := by simp only [area,h]; ring
    exact h356.ne' hz
  have h62 : q 6 ≠ q 2 := by
    apply physical_ne_of_ne w hw
    intro h
    have hz : area p 6 2 5 = 0 := by simp only [area,h]; ring
    exact h625.ne' hz
  have h1 := angle_split_at_diagonal (q 3) (q 5) (q 6) (q 2) s t hs ht.le ht'.le h35.symm hp
  have h2 := angle_split_at_diagonal (q 5) (q 3) (q 6) (q 2) (1-s) t (sub_pos.mpr hs') ht.le
    ht'.le h35 (by linear_combination (norm := module) hp)
  have h3 := angle_split_at_diagonal (q 6) (q 2) (q 3) (q 5) t s ht hs.le hs'.le h62.symm hp.symm
  have h4 := angle_split_at_diagonal (q 2) (q 6) (q 5) (q 3) (1-t) (1-s) (sub_pos.mpr ht')
    (sub_nonneg.mpr hs'.le) (by linarith) h62 (by linear_combination (norm := module) -hp)
  rw [angle_comm (q 6-q 3) (q 2-q 3), angle_comm (q 6-q 3) (q 5-q 3),
    angle_comm (q 5-q 3) (q 2-q 3)] at h1
  change (Type7.flippedFaces.map (chartEuclideanCorner q v)).sum =
    (Type7.faces.map (chartEuclideanCorner q v)).sum
  fin_cases v <;>
    norm_num [Type7.flippedFaces,Type7.faces,chartEuclideanCorner] <;>
    linarith only [h1,h2,h3,h4]

/-- Strict diagonal crossing makes the two angle maps coincide on a neighborhood
of the physical planar placement. -/
theorem sevenConeAngles_flip_eventuallyEq (p : Vertex → Plane ℝ) (w : ℝ) (hw : 0 < w)
    (h356 : 0 < area p 3 5 6) (h352 : area p 3 5 2 < 0)
    (h623 : area p 6 2 3 < 0) (h625 : 0 < area p 6 2 5) :
    (sevenConeAngles Type7.flippedFaces : (Vertex → ℂ) → Fin 7 → ℝ)
      =ᶠ[𝓝 (physicalComplex w ∘ p)] sevenConeAngles Type7.faces := by
  let z := physicalComplex w ∘ p
  let planar (q : Vertex → ℂ) (i : Vertex) := ((q i).re,(q i).im)
  let S (a b c : Vertex) (q : Vertex → ℂ) := area (planar q) a b c
  have hc (a b c : Vertex) : Continuous (S a b c) := by
    unfold S planar area
    fun_prop
  have hval (a b c : Vertex) : S a b c z = Real.sqrt w * area p a b c := by
    simp only [S,planar,z,Function.comp_apply,area,physicalComplex]
    ring
  have hpos (a b c : Vertex) (h : 0 < area p a b c) :
      ∀ᶠ q in 𝓝 z, 0 < S a b c q :=
    continuousAt_const.eventually_lt (hc a b c).continuousAt
      (by rw [hval]; exact mul_pos (Real.sqrt_pos.mpr hw) h)
  have hneg (a b c : Vertex) (h : area p a b c < 0) :
      ∀ᶠ q in 𝓝 z, S a b c q < 0 :=
    (hc a b c).continuousAt.eventually_lt continuousAt_const
      (by rw [hval]; exact mul_neg_of_pos_of_neg (Real.sqrt_pos.mpr hw) h)
  filter_upwards [hpos 3 5 6 h356,hneg 3 5 2 h352,hneg 6 2 3 h623,hpos 6 2 5 h625]
    with q h1 h2 h3 h4
  funext i
  have he : physicalComplex 1 ∘ planar q = q := by
    funext j
    apply Complex.ext <;> simp [planar,physicalComplex]
  have hf := flip_angle_sum (planar q) 1 one_pos h1 h2 h3 h4 i.succ
  dsimp only at hf
  rw [he] at hf
  change coneAngles Type7.flippedFaces q i.succ = coneAngles Type7.faces q i.succ
  rwa [coneAngles_eq_chart_list,coneAngles_eq_chart_list]

/-- Both diagonals cross in their interiors on the polynomially scaled chart. -/
theorem poly_chart_flipSigns {nearEndpoint : Bool} {x w : ℝ} (hd : domain nearEndpoint x w) :
    let p := polynomialPoints x w (if nearEndpoint then 2/3 else 1/3) (trapezoidHeight nearEndpoint x) 1
    0 < area p 3 5 6 ∧ area p 3 5 2 < 0 ∧ area p 6 2 3 < 0 ∧ 0 < area p 6 2 5 := by
  let c : ℝ := if nearEndpoint then 2/3 else 1/3
  let H := trapezoidHeight nearEndpoint x
  let p := polynomialPoints x w c H 1
  let D := H-1+H*x
  let Q := D^2+H^2*w
  obtain ⟨hx,_,hw⟩ := domain_bounds hd
  have hH : 1 < H := height_gt_one hd
  have hH₀ : 0 < H := by linarith
  have hD : 0 < D := add_pos_of_pos_of_nonneg (sub_pos.mpr hH) (mul_nonneg hH₀.le hx)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hc : 1-c ≠ 0 := by cases nearEndpoint <;> norm_num [c]
  have hp (v : Vertex) : p v =
      (Q*(planarPoint nearEndpoint x w v).1,Q*(planarPoint nearEndpoint x w v).2) := by
    simpa only [p,div_one,one_mul,planarPoint,trapezoidCut,neg_mul,D,Q] using
      polynomial_rescale x w c H 1 one_ne_zero hH₀.ne' hc hD.ne' hQ.ne' v
  have h (i j k : Vertex) : area p i j k = Q^2*area (planarPoint nearEndpoint x w) i j k := by
    simp only [area,hp]
    ring
  obtain ⟨h1,h2,h3,h4⟩ := planar_flipSigns hd
  change 0 < area p 3 5 6 ∧ area p 3 5 2 < 0 ∧ area p 6 2 3 < 0 ∧ 0 < area p 6 2 5
  simp only [h]
  exact ⟨mul_pos (sq_pos_of_pos hQ) h1,mul_neg_of_pos_of_neg (sq_pos_of_pos hQ) h2,
    mul_neg_of_pos_of_neg (sq_pos_of_pos hQ) h3,mul_pos (sq_pos_of_pos hQ) h4⟩

/-- The Euclidean angle sums on the Type 4 face list are exactly a full turn on both charts. -/
theorem flipped_euclidean_cone_angle {nearEndpoint : Bool} {x w : ℝ}
    (hd : domain nearEndpoint x w) (v : Vertex) :
    let p := polynomialPoints x w (if nearEndpoint then 2/3 else 1/3) (trapezoidHeight nearEndpoint x) 1
    let q := physicalComplex w ∘ p
    (Type7.flippedFaces.map (chartEuclideanCorner q v)).sum = 2*Real.pi := by
  let p := polynomialPoints x w (if nearEndpoint then 2/3 else 1/3) (trapezoidHeight nearEndpoint x) 1
  obtain ⟨h1,h2,h3,h4⟩ := poly_chart_flipSigns hd
  have hb := flip_angle_sum p w (domain_bounds hd).2.2 h1 h2 h3 h4 v
  dsimp only at hb
  change (Type7.flippedFaces.map (chartEuclideanCorner (physicalComplex w ∘ p) v)).sum = 2*Real.pi
  rw [hb]
  exact trapezoid_euclidean_cone_angle hd v

end OrigamiTorus.Type4
