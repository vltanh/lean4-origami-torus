module

public import OrigamiTorus.EightVertex.Type5.ContinuationTorus
import Mathlib.Tactic

/-! An explicit planar Type 5 folding on every nonrectangular reduced modulus.
The two coordinates used in the table are dot products with the period vectors. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type5.PlanarFold

open Continuation

/-- Coordinates in the dual basis to the periods, with T the squared length of the second period. -/
def dual (x T : ℝ) : Vertex → Plane ℝ :=
  ![(3/8, -T/2+1/4+3*x/4), (0,0), (3/8-3*x/4, -T/2+1/4),
    (3/8,1/4), (-1/8+x/4,1/4), (-1/8,-T/2+1/4), (1/8,1/4), (-1/8,1/4-x/4)]

def physical (x y : ℝ) (v : Vertex) : Plane ℝ :=
  let q := dual x (x^2+y^2) v
  (q.1, (q.2-x*q.1)/y)

def spatial (x y : ℝ) (v : Vertex) : Point3 := atHeight (physical x y v) 0

private def dualShift (x T : ℝ) (a b : Vertex) : Plane ℝ :=
  let k := squareShift a b
  (k.1+k.2*x, k.1*x+k.2*T)

set_option maxHeartbeats 0 in
private theorem dual_lengths (x T : ℝ) (a b : Vertex) :
    let k := squareShift a b
    let v := dual x T b-dual x T a
    2*k.1*v.1+2*k.2*v.2+(k.1:ℝ)^2+2*k.1*k.2*x+(k.2:ℝ)^2*T = 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [squareShift,positiveShift,dual] <;> ring

theorem edge_lengths {x y : ℝ} (hy : y ≠ 0) (a b : Vertex) :
    squared3 (spatial x y b-spatial x y a) =
      squared2 (physical x y b-physical x y a+shift x y a b) := by
  have h := dual_lengths x (x^2+y^2) a b
  dsimp only [Prod.fst_sub,Prod.snd_sub] at h
  simp only [spatial,atHeight,squared3,horizontal,squared2,dot,physical,shift,translatePoint,
    Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,
    sub_self,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,add_zero,zero_add]
  field_simp [hy]
  linear_combination -y^2 * h

private def dualArea (x T : ℝ) (f : Triangle) : ℝ :=
  cross (dual x T f.2.1 + dualShift x T f.1 f.2.1 - dual x T f.1)
        (dual x T f.2.2 + dualShift x T f.1 f.2.2 - dual x T f.1)

private theorem area_scale {x y : ℝ} (hy : y ≠ 0) (f : Triangle) :
    y * markedFaceCross (shift x y) (physical x y) f = dualArea x (x^2+y^2) f := by
  rcases f with ⟨a,b,c⟩
  simp only [markedFaceCross,physical,dualArea,dualShift,cross,shift,translatePoint,
    Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add]
  field_simp [hy]
  ring

/-- Signed double areas in dual coordinates, in the order of the sixteen faces. -/
private def areas (x T : ℝ) : Fin 16 → ℝ :=
  ![3*x*(4*T-6*x+1)/32, 3*(2*T-3*x)/32, 3*x*(T-2*x+1)/8, (2*T-3*x)/8,
    (4*T-3*x^2)/16, (2*T-1)*(2-3*x)/16, 1/16, (1-x)/16,
    x*(3-2*x)/32, (2*T-x)/32, T/8, (4*T-3*x^2)/16,
    x*(T-2*x+1)/8, T*(2-3*x)/8, (2*T-x)/8, T*(1-x)/8]

set_option maxHeartbeats 0 in
private theorem dual_area_table (x T : ℝ) (i : Fin 16) :
    dualArea x T (faces.get (Fin.cast (by decide : 16 = faces.length) i)) = areas x T i := by
  fin_cases i <;> norm_num [areas,dualArea,dualShift,dual,cross,faces,squareShift,positiveShift] <;> ring

theorem face_positive {x y : ℝ} (hx : 0 < x) (hs : x ≤ 1/2) (hy : 0 < y)
    (ht : 1 ≤ x^2+y^2) (f : Triangle) (hf : f ∈ faces) :
    0 < markedFaceCross (shift x y) (physical x y) f := by
  let T := x^2+y^2
  change 1 ≤ T at ht
  have hT : 0 < T := by linarith
  have h₁ : 0 < 4*T-6*x+1 := by linarith
  have h₂ : 0 < 2*T-3*x := by linarith
  have h₃ : 0 < T-2*x+1 := by linarith
  have h₄ : 0 < 4*T-3*x^2 := by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hs)]
  have h₅ : 0 < 2*T-1 := by linarith
  have h₆ : 0 < 2-3*x := by linarith
  have h₇ : 0 < 1-x := by linarith
  have h₈ : 0 < 3-2*x := by linarith
  have h₉ : 0 < 2*T-x := by linarith
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hf
  let i := Fin.cast (by decide : faces.length = 16) j
  have iden := dual_area_table x T i
  have hpos (k : Fin 16) : 0 < areas x T k := by
    fin_cases k <;> dsimp [areas] <;> positivity
  have hk : 0 < dualArea x T f := by
    rw [← hj]
    exact iden.symm ▸ hpos i
  rw [← area_scale hy.ne' f] at hk
  exact pos_of_mul_pos_right hk hy.le

/-- The actual oblique flat torus admits this continuous, planar, facewise-isometric map. -/
theorem torus_by_faces {x y : ℝ} (hx : 0 < x) (hs : x ≤ 1/2) (hy : 0 < y)
    (ht : 1 ≤ x^2+y^2) :
    let τ : ℂ := x+y*Complex.I
    ∃ (H : triangleWeightSpace faces ≃ₜ ComplexTorus 1 τ)
      (F : ComplexTorus 1 τ → Point3) (P : Triangle → Vertex → ℂ),
      Continuous F ∧
      (∀ u, F (H u) = evaluateTriangles faces (spatial x y) u) ∧
      (∀ f ∈ faces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection 1 τ (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ faces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        squared3 (F (H u)-F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 :=
  marked_map_by_faces (fun {a b} _ => edge_lengths hy.ne' a b) hy (face_positive hx hs hy ht)

end OrigamiTorus.Type5.PlanarFold
