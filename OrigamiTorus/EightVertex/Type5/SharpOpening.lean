module

public import OrigamiTorus.EightVertex.Type5.Square
import Mathlib.Tactic

/-! The projected area of triangle 015 in a first-order opening at the sharp ray.
The second planar component is multiplied by the positive factor √L. -/

public section

noncomputable section

namespace OrigamiTorus.Type5.SharpOpening

def inner (L : ℝ) (a b : Plane ℝ) : ℝ := L*a.1*b.1 + a.2*b.2

/-- Intrinsic positions of the planar configuration. -/
def intrinsic (L : ℝ) : Vertex → Plane ℝ :=
  ![(1/10,-2/25),(0,0),(0,-(L+2)/8),(9/20,(L+1)/4-9/20),
    (-9/20,(L+1)/4-9/20),(-1/2,-2/5),(0,(L+1)/4),
    (-1/2,(25*L^2-44*L+16)/(4*(25*L-18)))]

def planar (L : ℝ) (i : Vertex) : Plane ℝ :=
  if i = 0 then (-1/10,-2/25)
  else if i = 3 ∨ i = 4 then (-1/20,(1-L)/4-9/20)
  else if i = 6 then (-1/2,(1-L)/4)
  else if i = 7 then
    (-(5*L-2)/(2*(25*L-18)), -(25*L^2+4*L-16)/(4*(25*L-18)))
  else intrinsic L i

def shift (L : ℝ) (i j : Vertex) : Plane ℝ :=
  let (m,n) := squareShift i j
  ((m : ℝ)+(n : ℝ)/2,(n : ℝ)*L/2)

set_option maxHeartbeats 0 in
/-- The planar boundary configuration realizes all 24 marked lengths.
Both sides are squared physical lengths multiplied by L. -/
theorem planar_edge_lengths {L : ℝ} (hL : 3 ≤ L) (a b : Vertex) (he : (a,b) ∈ edgeList) :
    let s := planar L b - planar L a
    let d := intrinsic L b - intrinsic L a + shift L a b
    inner L s s = inner L d d := by
  have hden : 25*L-18 ≠ 0 := by linarith
  have hn : -18 + L*25 ≠ 0 := by linarith
  have hs : 324 - L*900 + L^2*625 ≠ 0 := by nlinarith [sq_pos_of_ne_zero hden]
  fin_cases a <;> fin_cases b <;> try (exfalso; revert he; decide)
  all_goals norm_num [planar, intrinsic, inner, shift, squareShift, positiveShift]
  all_goals field_simp [hden]
  all_goals ring_nf
  all_goals field_simp [hn, hs]
  all_goals ring

set_option maxHeartbeats 0 in
/-- The marked triangles in the planar construction all have positive intrinsic area. -/
theorem intrinsic_face_positive {L : ℝ} (hL : 3 ≤ L) {f : Triangle} (hf : f ∈ faces) :
    let d (i : Vertex) := intrinsic L i - intrinsic L f.1 + shift L f.1 i
    0 < cross (d f.2.1) (d f.2.2) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ L = t+3 := ⟨L-3, by linarith, by ring⟩
  have hd : 0 < 25*(t+3)-18 := by linarith
  have hi : 0 < (57+t*25)⁻¹ := by positivity
  simp only [faces, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [intrinsic, shift, cross, squareShift, positiveShift]
  all_goals field_simp
  all_goals ring_nf
  all_goals first | positivity | nlinarith [mul_nonneg ht hi.le, mul_nonneg (sq_nonneg t) hi.le]

/-- Coefficient of t in the scaled squared-length residual, for spatial
height √t times h and horizontal velocities u and v. -/
def residual (L : ℝ) (u v : Vertex → Plane ℝ) (h : Vertex → ℝ) (i j : Vertex) : ℝ :=
  2*inner L (planar L j-planar L i) (v j-v i) -
  2*inner L (intrinsic L j-intrinsic L i+shift L i j) (u j-u i) + L*(h j-h i)^2

/-- First-order change of the projected signed double area of triangle 015,
computed with vertex 1 fixed at the origin. -/
def areaVelocity (L : ℝ) (v : Vertex → Plane ℝ) : ℝ :=
  cross (v 5) (planar L 0) + cross (planar L 5) (v 0)

/-- A squared-length defect D at edge 01 and the leading height of vertex 4
determine the motion across the projected line 15. -/
theorem area_identity {L D : ℝ} (hL : 0 < L) (u v : Vertex → Plane ℝ) (h : Vertex → ℝ)
    (u1 : u 1 = 0) (v1 : v 1 = 0) (v2 : v 2 = u 2) (v5 : v 5 = u 5)
    (h0 : h 0 = 0) (h1 : h 1 = 0) (h2 : h 2 = 0) (h5 : h 5 = 0)
    (he : ∀ e ∈ ([(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,4),(3,5),(4,5)] : List Edge),
      residual L u v h e.1 e.2 = if e = (0,1) then L*D else 0) :
    5*(75*L+14)*areaVelocity L v + 9*(75*L+14)*D + 100*(L+2)*(h 4)^2 = 0 := by
  have e01 := he (0,1) (by decide)
  have e02 := he (0,2) (by decide)
  have e03 := he (0,3) (by decide)
  have e04 := he (0,4) (by decide)
  have e05 := he (0,5) (by decide)
  have e13 := he (1,3) (by decide)
  have e24 := he (2,4) (by decide)
  have e35 := he (3,5) (by decide)
  have e45 := he (4,5) (by decide)
  norm_num [residual, inner, intrinsic, planar, shift, areaVelocity, cross, squareShift,
    positiveShift, u1,v1,v2,v5,h0,h1,h2,h5] at e01 e02 e03 e04 e05 e13 e24 e35 e45 ⊢
  apply (mul_eq_zero_iff_left (a := 8*L) (by positivity)).mp
  linear_combination -72*(75*L+14)*e01 - 32*(25*L+16)*e02 - 20*(75*L+14)*e03
    - 20*(55*L-26)*e04 - 5*(75*L+14)*e05 + 16*(75*L+14)*e13
    + 64*(25*L+16)*e24 + 4*(75*L+14)*e35 + 4*(75*L+14)*e45

/-- Two signed tetrahedra determine on which side of line 15 vertex 0 projects. -/
theorem volume_area_relation (r : Vertex → Plane ℝ) (z : Vertex → ℝ)
    (r1 : r 1 = 0) (z1 : z 1 = 0) (z2 : z 2 = 0) (z5 : z 5 = 0) :
    -(cross (r 5) (r 7)) * volume r z 0 1 2 5 +
      cross (r 2) (r 5) * volume r z 0 1 5 7 =
    cross (r 2) (r 5) * (z 7 * cross (r 5) (r 0)) := by
  simp [volume, area, cross, r1, z1, z2, z5]
  ring

/-- Exact edge lengths force strictly negative area velocity when vertex 4 rises. -/
theorem exact_area_velocity_neg {L : ℝ} (hL : 0 < L) (u v : Vertex → Plane ℝ)
    (h : Vertex → ℝ) (u1 : u 1 = 0) (v1 : v 1 = 0) (v2 : v 2 = u 2) (v5 : v 5 = u 5)
    (h0 : h 0 = 0) (h1 : h 1 = 0) (h2 : h 2 = 0) (h5 : h 5 = 0) (h4 : h 4 ≠ 0)
    (he : ∀ e ∈ ([(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,4),(3,5),(4,5)] : List Edge),
      residual L u v h e.1 e.2 = 0) : areaVelocity L v < 0 := by
  have eqn := area_identity (D := 0) hL u v h u1 v1 v2 v5 h0 h1 h2 h5
    (fun e hem ↦ by simp [he e hem])
  have hp : 0 < 100*(L+2)*(h 4)^2 := by positivity
  have hc : 0 < 5*(75*L+14) := by positivity
  by_contra! hn
  linarith [mul_nonneg hc.le hn]

end OrigamiTorus.Type5.SharpOpening
