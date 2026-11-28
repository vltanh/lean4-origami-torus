module

public import OrigamiTorus.EightVertex.Type5.RadicalChart
import Mathlib.Tactic

/-! Linear reconstruction of both root vertices from the two faces on edge 16. -/

@[expose] public section

namespace OrigamiTorus.Type5.HingeChart

/-- Both anchor-to-hinge shifts coincide. The two coherent copies used for
either root give three distinct shifts at the anchor triangle. -/
theorem marked_shifts :
    squareShift 2 6 = (0,-1) ∧ squareShift 5 6 = (0,-1) ∧
    squareShift 2 5 = 0 ∧ squareShift 3 6 = 0 ∧ squareShift 4 6 = 0 ∧
    ∀ i ∈ roots, squareShift 2 i ≠ 0 ∧ squareShift 5 i ≠ 0 ∧
      squareShift 2 i ≠ squareShift 5 i := by decide +kernel

/-- The two coherent anchors lie on the same line in the base plane. -/
theorem anchor_line (B p a : Plane ℝ) (r : Space ℝ)
    (h : squared3 r = squared2 p) :
    squared3 (r-atHeight a 0) = squared2 (p-a-B) ↔
    dot a (B+horizontal r-p) = dot B p-squared2 B/2 := by
  simp only [squared3,squared2,dot,horizontal,atHeight,Prod.fst_sub,Prod.snd_sub,
    Prod.fst_add,Prod.snd_add] at h ⊢
  constructor <;> intro he <;> nlinarith only [h,he]

theorem anchor_line_normal_ne (B p : Plane ℝ) (r : Space ℝ)
    (h : squared3 r = squared2 p) (hlt : squared2 p < squared2 (p-B)) :
    B+horizontal r-p ≠ 0 := by
  intro hn
  have hh : horizontal r = p-B := by
    rw [sub_eq_zero] at hn
    rw [← hn]
    abel
  rw [squared3, hh] at h
  linarith only [h, hlt, sq_nonneg r.2.2]

/-- Coordinates of a spatial vector on the two axes of a face plane. -/
def pull (w n v : Space ℝ) : Plane ℝ := (dot3 w v, dot3 n v)

/-- Spatial isometry of a face with intrinsic coordinates in an orthonormal basis. -/
def lift (w n : Space ℝ) (p : Plane ℝ) : Space ℝ := p.1 • w + p.2 • n

structure Frame (w n : Space ℝ) : Prop where
  first : squared3 w = 1
  second : squared3 n = 1
  perp : dot3 w n = 0

theorem lift_norm {w n} (h : Frame w n) (p : Plane ℝ) :
    squared3 (lift w n p) = squared2 p := by
  obtain ⟨hw,hn,ho⟩ := h
  simp only [lift, squared3, squared2, dot3, dot, horizontal, Prod.fst_add,
    Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
  linear_combination p.1^2*hw + p.2^2*hn + 2*p.1*p.2*ho

theorem adjoint (w n v : Space ℝ) (p : Plane ℝ) :
    dot (pull w n v) p = dot3 v (lift w n p) := by
  simp only [pull,lift,dot,dot3,horizontal,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

private theorem pull_le {w n} (h : Frame w n) (v : Space ℝ) :
    squared2 (pull w n v) ≤ squared3 v := by
  let s := lift w n (pull w n v)
  have he : squared3 s = squared2 (pull w n v) := lift_norm h _
  have hd : dot3 v s = squared2 (pull w n v) := (adjoint w n v _).symm
  have hz : 0 ≤ squared3 (v-s) := by
    simp only [squared3,squared2,dot,horizontal,← sq]
    positivity
  have hexp : squared3 (v-s) = squared3 v+squared3 s-2*dot3 v s := by
    simp only [squared3,squared2,dot,dot3,horizontal,Prod.fst_sub,Prod.snd_sub]
    ring
  linarith only [hz,hexp,he,hd]

/-- When the three spatial anchor distances are strictly shorter than the
three coherent intrinsic anchor distances, the two linear equations of a
root in a fixed face plane are independent at every solution. -/
theorem nonsingular {w n : Space ℝ} (hw : Frame w n) (a b : Space ℝ) (s t p : Plane ℝ)
    (hs : squared3 a < squared2 s) (ht : squared3 b < squared2 t)
    (hab : squared3 (a-b) < squared2 (s-t))
    (ha : dot (pull w n a-s) p = (squared3 a-squared2 s)/2)
    (hb : dot (pull w n b-t) p = (squared3 b-squared2 t)/2) :
    cross (pull w n a-s) (pull w n b-t) ≠ 0 := by
  let h := (squared3 a-squared2 s)/2
  let k := (squared3 b-squared2 t)/2
  have hh : h < 0 := by dsimp [h]; linarith only [hs]
  have hk : k < 0 := by dsimp [k]; linarith only [ht]
  have hid : squared2 (k • s-h • t) - squared3 (k • a-h • b) =
      h*k*(squared2 (s-t)-squared3 (a-b)) := by
    have dh : 2*h = squared3 a-squared2 s := by dsimp [h]; ring
    have dk : 2*k = squared3 b-squared2 t := by dsimp [k]; ring
    simp only [squared3,squared2,dot,horizontal,Prod.fst_sub,Prod.snd_sub,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul] at dh dk ⊢
    linear_combination (k^2-h*k)*dh + (h^2-h*k)*dk
  intro hz
  let A := pull w n a-s
  let B := pull w n b-t
  have he : k • A - h • B = 0 := by
    rw [show k = dot B p from hb.symm, show h = dot A p from ha.symm]
    change cross A B = 0 at hz
    ext <;> simp only [cross,dot,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,
      Prod.smul_snd,smul_eq_mul,Prod.fst_zero,Prod.snd_zero] at hz ⊢
    · linear_combination p.2*hz
    · linear_combination -p.1*hz
  have hp : pull w n (k • a-h • b) = k • s-h • t := by
    have eqv : k • pull w n a - h • pull w n b = k • s - h • t := by
      dsimp [A,B] at he
      rw [smul_sub, smul_sub] at he
      abel_nf at he ⊢
      linear_combination he
    rw [← eqv]
    ext <;> simp only [pull,dot3,horizontal,dot,Prod.fst_sub,Prod.snd_sub,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring
  have hle := pull_le hw (k • a-h • b)
  rw [hp] at hle
  linarith only [hid, hle, mul_pos (mul_pos_of_neg_of_neg hh hk) (sub_pos.mpr hab)]

/-- Solving the two linear equations recovers the distances to the origin
and the two other anchors. -/
theorem solve_edges {w n : Space ℝ} (hw : Frame w n) (a b : Space ℝ) (s t : Plane ℝ)
    (hdet : cross (pull w n a-s) (pull w n b-t) ≠ 0) :
    let p := linearSolve (pull w n a-s) (pull w n b-t)
      ((squared3 a-squared2 s)/2) ((squared3 b-squared2 t)/2)
    squared3 (lift w n p) = squared2 p ∧
    squared3 (lift w n p-a) = squared2 (p-s) ∧
    squared3 (lift w n p-b) = squared2 (p-t) := by
  intro p
  have he := linearSolve_spec hdet ((squared3 a-squared2 s)/2) ((squared3 b-squared2 t)/2)
  have one (v : Space ℝ) (u : Plane ℝ)
      (h : dot (pull w n v-u) p = (squared3 v-squared2 u)/2) :
      squared3 (lift w n p-v) = squared2 (p-u) := by
    apply (edgeEquation_iff p u _ v (lift_norm hw p)).2
    rw [← adjoint]
    convert h using 1
    simp only [dot,Prod.fst_sub,Prod.snd_sub]
    ring
  exact ⟨lift_norm hw _,one a s he.1,one b t he.2⟩

end OrigamiTorus.Type5.HingeChart
