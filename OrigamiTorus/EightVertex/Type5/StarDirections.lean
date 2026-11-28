module

public import OrigamiTorus.EightVertex.Type5.Square
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! Recovering the radii in the star of vertex 2 from its intrinsic and spatial rays. -/

@[expose] public section

namespace OrigamiTorus.Type5.StarDirections

/-- Period on a chord when all seven neighbor lifts are based at vertex 2. -/
def winding (i j : Vertex) : ℤ × ℤ :=
  squareShift 2 i + squareShift i j - squareShift 2 j

/-- Two disjoint triangular cycles and an edge to the last neighbor. -/
def determining : List Edge := [(0,3),(3,5),(0,5),(1,4),(4,6),(1,6),(1,7)]

theorem chord_table :
    (edgeList.filter (fun e => winding e.1 e.2 != 0)).toFinset =
      {(0,3),(0,5),(1,3),(1,4),(1,6),(1,7),(3,5),(4,5),(4,6),(5,7)} ∧
    ∀ e ∈ determining, e ∈ edgeList ∧ winding e.1 e.2 ≠ 0 := by decide +kernel

/-- Physical period associated to a marked chord. -/
def period (A B : Plane ℝ) (i j : Vertex) : Plane ℝ :=
  ((winding i j).1 : ℝ) • A + ((winding i j).2 : ℝ) • B

/-- A marked displacement from vertex 2 to one of its neighbors. -/
def based (A B : Plane ℝ) (p : Vertex → Plane ℝ) (i : Vertex) : Plane ℝ :=
  p i - p 2 + ((squareShift 2 i).1 : ℝ) • A + ((squareShift 2 i).2 : ℝ) • B

theorem based_chord (A B : Plane ℝ) (p : Vertex → Plane ℝ) (i j : Vertex) :
    based A B p j - based A B p i + period A B i j =
      p j - p i + ((squareShift i j).1 : ℝ) • A + ((squareShift i j).2 : ℝ) • B := by
  simp only [based, period, winding, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Int.cast_add, Int.cast_sub, add_smul, sub_smul]
  abel

/-- The length equation for two rays with prescribed directions.
The endpoint inequalities compare each radial segment with its alternate lift. -/
structure Chord (d f : Plane ℝ) (v w : Space ℝ) (H : Plane ℝ) (l k : ℝ) : Prop where
  left_pos : 0 < l
  right_pos : 0 < k
  length : squared3 (k • w - l • v) = squared2 (k • f - l • d + H)
  left_short : squared2 (l • d) < squared2 (l • d - H)
  right_short : squared2 (k • f) < squared2 (k • f + H)

private theorem left_margin {d H : Plane ℝ} {l : ℝ} (hl : 0 < l)
    (hs : squared2 (l • d) < squared2 (l • d - H)) :
    0 < squared2 H / l - 2 * dot H d := by
  apply sub_pos.mpr ((lt_div_iff₀ hl).2 ?_)
  simp only [squared2, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_sub, Prod.snd_sub] at hs ⊢
  nlinarith only [hs]

private theorem right_margin {f H : Plane ℝ} {k : ℝ} (hk : 0 < k)
    (hs : squared2 (k • f) < squared2 (k • f + H)) :
    0 < squared2 H / k + 2 * dot H f := by
  have hg : -(2 * dot H f) < squared2 H / k := by
    apply (lt_div_iff₀ hk).2
    simp only [squared2, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_add, Prod.snd_add] at hs ⊢
    nlinarith only [hs]
  linarith only [hg]

private theorem inverse_equation {d f v w H l k} (h : Chord d f v w H l k)
    (hd : squared3 v = squared2 d) (hf : squared3 w = squared2 f) :
    squared2 H * l⁻¹ * k⁻¹ - 2 * dot H d * k⁻¹ + 2 * dot H f * l⁻¹ =
      2 * (dot d f - dot3 v w) := by
  have g := h.length
  field_simp [h.left_pos.ne', h.right_pos.ne']
  simp only [squared3, squared2, dot3, horizontal, dot, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at g hd hf ⊢
  linear_combination -g + l^2 * hd + k^2 * hf

/-- Inverse radii obey a product identity whose two factors are strictly positive. -/
theorem product_identity {d f v w H l k} (h : Chord d f v w H l k)
    (hd : squared3 v = squared2 d) (hf : squared3 w = squared2 f) :
    (squared2 H / l - 2 * dot H d) * (squared2 H / k + 2 * dot H f) =
      2 * squared2 H * (dot d f - dot3 v w) - 4 * dot H d * dot H f ∧
    0 < squared2 H / l - 2 * dot H d ∧ 0 < squared2 H / k + 2 * dot H f := by
  refine ⟨?_, left_margin h.left_pos h.left_short, right_margin h.right_pos h.right_short⟩
  simp only [div_eq_mul_inv]
  linear_combination squared2 H * inverse_equation h hd hf

/-- Two other periods of the same length sharpen the reflected-angle bound
when they give tighter projections on the respective radial directions. -/
theorem comparison_of_equal_periods {d f v w H l k} (h : Chord d f v w H l k)
    (hd : squared3 v = squared2 d) (hf : squared3 w = squared2 f) (P Q : Plane ℝ)
    (hP : squared2 P = squared2 H) (hQ : squared2 Q = squared2 H)
    (hsP : squared2 (l • d) < squared2 (l • d - P))
    (hsQ : squared2 (k • f) < squared2 (k • f + Q))
    (hp : dot H d ≤ dot P d) :
    (2 * dot P d - 2 * dot H d) * (2 * dot H f - 2 * dot Q f) <
      2 * squared2 H * (dot d f - dot3 v w) - 4 * dot H d * dot H f := by
  obtain ⟨he, _, hright⟩ := product_identity h hd hf
  rw [← he]
  have ha := left_margin h.left_pos hsP
  have hb := right_margin h.right_pos hsQ
  rw [hP] at ha
  rw [hQ] at hb
  calc
    _ ≤ (2 * dot P d - 2 * dot H d) * (squared2 H / k + 2 * dot H f) :=
      mul_le_mul_of_nonneg_left (by linarith only [hb]) (by linarith only [hp])
    _ < _ := mul_lt_mul_of_pos_right (by linarith only [ha]) hright

private theorem angle_lt_of_cos_lt {u α : ℝ} (hu : 0 ≤ u) (huπ : u ≤ Real.pi)
    (hα : 0 ≤ α) (hαπ : α ≤ Real.pi) (h : Real.cos α < Real.cos u) : u < α := by
  by_contra! h'
  exact (not_lt_of_ge (Real.strictAntiOn_cos.antitoneOn ⟨hα,hαπ⟩ ⟨hu,huπ⟩ h')) h

private theorem directed_hex_bound {i j α x y : ℝ}
    (hi : |i| < Real.pi/2) (hj : |j| < Real.pi/2) (hα : 0 ≤ α) (hαπ : α ≤ Real.pi)
    (hfirst : |i+j| < α) (hx : Real.sin (i-Real.pi/6) < x)
    (hy : Real.sin (-j-Real.pi/6) < y)
    (he : Real.cos α = Real.cos (i+j) - 2*x*y) : i-j-Real.pi/3 < α := by
  by_cases ha : i ≤ Real.pi/6
  · linarith only [ha, neg_le_abs (i+j), hfirst]
  by_cases hb : -(Real.pi/6) ≤ j
  · linarith only [hb, le_abs_self (i+j), hfirst]
  obtain ⟨hiLo,hiHi⟩ := abs_lt.mp hi
  obtain ⟨hjLo,hjHi⟩ := abs_lt.mp hj
  have hp := Real.pi_pos
  have h₁ : 0 < Real.sin (i-Real.pi/6) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h₂ : 0 < Real.sin (-j-Real.pi/6) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hprod : Real.sin (i-Real.pi/6)*Real.sin (-j-Real.pi/6) < x*y :=
    (mul_lt_mul_of_pos_right hx h₂).trans (mul_lt_mul_of_pos_left hy (h₁.trans hx))
  have hc : Real.cos (i-j-Real.pi/3) =
      Real.cos (i+j) - 2*Real.sin (i-Real.pi/6)*Real.sin (-j-Real.pi/6) := by
    rw [show i-j-Real.pi/3 = (i-Real.pi/6)-(j+Real.pi/6) by ring,
      show i+j = (i-Real.pi/6)+(j+Real.pi/6) by ring,
      show -j-Real.pi/6 = -(j+Real.pi/6) by ring, Real.cos_sub (i-Real.pi/6) (j+Real.pi/6),
      Real.cos_add (i-Real.pi/6) (j+Real.pi/6), Real.sin_neg]
    ring
  apply angle_lt_of_cos_lt (by linarith) (by linarith) hα hαπ
  rw [he,hc]
  linarith only [hprod]

/-- In radians, the two strict linear angle bounds at a corner of a winding
triangle. The four sine bounds are the projections onto its neighboring unit
periods at angles ±π/3, after subtracting the projection onto the winding. -/
private theorem hex_angle_bounds_of_margins {i j α x y : ℝ} (hi : |i| < Real.pi/2) (hj : |j| < Real.pi/2)
    (hα : 0 ≤ α) (hαπ : α ≤ Real.pi) (hx : 0 < x) (hy : 0 < y)
    (hxHi : Real.sin (i-Real.pi/6) < x) (hxLo : Real.sin (-i-Real.pi/6) < x)
    (hyHi : Real.sin (j-Real.pi/6) < y) (hyLo : Real.sin (-j-Real.pi/6) < y)
    (he : Real.cos α = Real.cos (i+j) - 2*x*y) :
    |i+j| < α ∧ |i-j| - Real.pi/3 < α := by
  have hh : |i+j| < α := by
    apply angle_lt_of_cos_lt (abs_nonneg _) ((abs_add_le i j).trans (by linarith)) hα hαπ
    rw [Real.cos_abs, he]
    linarith only [mul_pos hx hy]
  refine ⟨hh,?_⟩
  rcases le_total j i with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact directed_hex_bound hi hj hα hαπ hh hxHi hyLo he
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    exact directed_hex_bound hj hi hα hαπ (by simpa [add_comm] using hh) hyHi hxLo
      (by rw [he,add_comm j i]; ring)

/-- Strict nearest-lift comparisons with the three unit periods in the
hexagonal lattice imply both angular inequalities. Here `u,v` are half the
reciprocal edge lengths, and `i,j` are measured from the cycle period. -/
theorem hex_angle_bounds {i j α u v : ℝ} (hi : |i| < Real.pi/2) (hj : |j| < Real.pi/2)
    (hα : 0 ≤ α) (hαπ : α ≤ Real.pi)
    (hu : Real.cos i < u ∧ Real.cos (i-Real.pi/3) < u ∧ Real.cos (i+Real.pi/3) < u)
    (hv : Real.cos j < v ∧ Real.cos (j-Real.pi/3) < v ∧ Real.cos (j+Real.pi/3) < v)
    (he : Real.cos α = Real.cos (i+j) - 2*(u-Real.cos i)*(v-Real.cos j)) :
    |i+j| < α ∧ |i-j| - Real.pi/3 < α := by
  have positive (t : ℝ) : Real.sin (t-Real.pi/6) = Real.cos (t-Real.pi/3) - Real.cos t := by
    rw [Real.sin_sub, Real.cos_sub, Real.sin_pi_div_six, Real.cos_pi_div_six,
      Real.sin_pi_div_three, Real.cos_pi_div_three]
    ring
  have negative (t : ℝ) : Real.sin (-t-Real.pi/6) = Real.cos (t+Real.pi/3) - Real.cos t := by
    rw [positive, show -t-Real.pi/3 = -(t+Real.pi/3) by ring, Real.cos_neg, Real.cos_neg]
  apply hex_angle_bounds_of_margins hi hj hα hαπ (sub_pos.mpr hu.1) (sub_pos.mpr hv.1)
  · rw [positive]; exact sub_lt_sub_right hu.2.1 _
  · rw [negative]; exact sub_lt_sub_right hu.2.2 _
  · rw [positive]; exact sub_lt_sub_right hv.2.1 _
  · rw [negative]; exact sub_lt_sub_right hv.2.2 _
  · exact he

private theorem opposite {d f v w H l k l' k'} (h : Chord d f v w H l k)
    (h' : Chord d f v w H l' k') (hd : squared3 v = squared2 d) (hf : squared3 w = squared2 f) :
    (l⁻¹ < l'⁻¹ ↔ k'⁻¹ < k⁻¹) ∧ (l'⁻¹ < l⁻¹ ↔ k⁻¹ < k'⁻¹) := by
  have balance : (l'⁻¹-l⁻¹) * (squared2 H / k + 2 * dot H f) =
      (k⁻¹-k'⁻¹) * (squared2 H / l' - 2 * dot H d) := by
    simp only [div_eq_mul_inv]
    linear_combination inverse_equation h' hd hf - inverse_equation h hd hf
  have hpos := congrArg (fun x : ℝ => 0 < x) balance
  have hn : (l⁻¹-l'⁻¹) * (squared2 H / k + 2 * dot H f) =
      (k'⁻¹-k⁻¹) * (squared2 H / l' - 2 * dot H d) := by linear_combination -balance
  have hneg := congrArg (fun x : ℝ => 0 < x) hn
  simpa only [mul_pos_iff_of_pos_right (right_margin h.right_pos h.right_short), mul_pos_iff_of_pos_right (left_margin h'.left_pos h'.left_short),
    sub_pos, eq_iff_iff] using And.intro hpos hneg

private def Flips (x y : Vertex → ℝ) (i j : Vertex) : Prop :=
  (x i < y i ↔ y j < x j) ∧ (y i < x i ↔ x j < y j)

private theorem along {x y i j} (h : Flips x y i j) (hi : x i = y i) : x j = y j := by
  apply le_antisymm <;> apply le_of_not_gt
  · intro hs
    exact (ne_of_lt (h.1.mpr hs)) hi
  · intro hs
    exact (ne_of_lt (h.2.mpr hs)) hi.symm

private theorem triangle {x y i j k} (hij : Flips x y i j) (hjk : Flips x y j k)
    (hik : Flips x y i k) : x i = y i := by
  rcases lt_trichotomy (x i) (y i) with h | h | h
  · exact (lt_asymm (hik.1.mp h) (hjk.2.mp (hij.1.mp h))).elim
  · exact h
  · exact (lt_asymm (hik.2.mp h) (hjk.1.mp (hij.2.mp h))).elim

/-- At fixed periods and fixed intrinsic and spatial directions, the seven
chords in `determining` determine all seven radii of the star. -/
theorem radii_unique (A B : Plane ℝ) (d : Vertex → Plane ℝ) (v : Vertex → Space ℝ)
    (l k : Vertex → ℝ) (hn : ∀ i ≠ 2, squared3 (v i) = squared2 (d i))
    (hl : ∀ e ∈ determining, Chord (d e.1) (d e.2) (v e.1) (v e.2)
      (period A B e.1 e.2) (l e.1) (l e.2))
    (hk : ∀ e ∈ determining, Chord (d e.1) (d e.2) (v e.1) (v e.2)
      (period A B e.1 e.2) (k e.1) (k e.2)) :
    ∀ i ≠ 2, l i = k i := by
  let x := fun i => (l i)⁻¹
  let y := fun i => (k i)⁻¹
  have edge (i j : Vertex) (he : (i,j) ∈ determining) : Flips x y i j := by
    have ne : ∀ e ∈ determining, e.1 ≠ 2 ∧ e.2 ≠ 2 := by decide +kernel
    exact opposite (hl _ he) (hk _ he) (hn i (ne _ he).1) (hn j (ne _ he).2)
  have h03 := edge 0 3 (by decide +kernel)
  have h35 := edge 3 5 (by decide +kernel)
  have h05 := edge 0 5 (by decide +kernel)
  have h14 := edge 1 4 (by decide +kernel)
  have h46 := edge 4 6 (by decide +kernel)
  have h16 := edge 1 6 (by decide +kernel)
  have h17 := edge 1 7 (by decide +kernel)
  have h0 := triangle h03 h35 h05
  have h1 := triangle h14 h46 h16
  intro i hi
  apply inv_injective
  change x i = y i
  fin_cases i
  · exact h0
  · exact h1
  · exact (hi rfl).elim
  · exact along h03 h0
  · exact along h14 h1
  · exact along h05 h0
  · exact along h16 h1
  · exact along h17 h1

end OrigamiTorus.Type5.StarDirections
