module

public import OrigamiTorus.EightVertex.Type5.Reconstruction
public import OrigamiTorus.Geometry.AffineDeterminants
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Limiting planar areas and hinge equations for the off-ray hand construction. -/

@[expose] public section

namespace OrigamiTorus.Type5.OffRayOpening

open scoped ComplexConjugate

/-- The vertex 0 obtained from the two planar reflections lies on the
period bisector and on the direct-isometry branch of the 025 hinge. -/
theorem reflected_leaf0 (P R A : ℂ)
    (hP : P ≠ 0) (hR : R ≠ 0) (hN : P*conj R-conj P*R ≠ 0)
    (hgap : (P-R)*conj A+(conj P-conj R)*A = A*conj A) :
    let N := P*conj R-conj P*R
    let q := P*conj R*A/N
    let r := -P*R*conj A/N
    r = P*conj q/conj P ∧
      r = R*conj (q-A)/conj R ∧
      q*conj A + conj q*A = A*conj A ∧
      (q-P)*(P-R) = (r-P)*(P-R-A) := by
  intro N q r
  have hconj : conj N = -N := by dsimp [N]; simp
  have hq : conj q = -conj P*R*conj A/N := by
    dsimp only [q]
    rw [map_div₀, map_mul, map_mul, RingHomCompTriple.comp_apply, hconj]
    simp [div_neg, neg_div]
  have hPN : conj P ≠ 0 := by simpa using hP
  have hRN : conj R ≠ 0 := by simpa using hR
  have hn : N ≠ 0 := hN
  refine ⟨?_,?_,?_,?_⟩
  · rw [hq]
    dsimp only [r]
    field_simp
  · rw [map_sub, hq]
    dsimp only [r]
    field_simp
    dsimp [N]
    ring
  · rw [hq]
    dsimp only [q]
    field_simp
    dsimp [N]
    ring
  · dsimp only [q,r]
    field_simp
    dsimp [N]
    linear_combination R*hgap

/-- The two images of vertex 3 by conjugation and the shifted reflection
agree. Its intrinsic position lies on the period bisector. -/
theorem reflected_root3 (B R : ℂ) (k : ℝ) (hB : B ≠ 0) (hR : R ≠ 0)
    (hk : k ≠ 0) (hIm : R-conj R = k*(B-conj B)) :
    let A := (conj B-B)/B
    let r := R/(k*conj B)
    let q := conj r
    r = R*conj (q-A)/conj R ∧ q*conj A+conj q*A = A*conj A := by
  intro A r q
  have hBc : conj B ≠ 0 := by simpa using hB
  have hRc : conj R ≠ 0 := by simpa using hR
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hq : q = conj R/(k*B) := by
    dsimp [q,r]
    simp
  have hqc : conj q = r := by dsimp [q]; simp
  have hAc : conj A = (B-conj B)/conj B := by dsimp [A]; simp
  constructor
  · rw [map_sub, hqc, hAc]
    dsimp only [r]
    field_simp
    linear_combination -hIm
  · rw [hqc,hq,hAc]
    dsimp only [A,r]
    field_simp
    linear_combination (conj B-B)*hIm

/-- The collision r₀=P on the rectangular boundary separates linearly
in λ. Here B=iy, k=1−2d/T and the displayed denominator is nonzero
in a neighborhood of (k,λ)=(1,0). -/
theorem rectangular_leaf0_difference (y k l : ℝ) (hy : y ≠ 0)
    (hden : k+2*l*(1-k) ≠ 0) :
    let B : ℂ := y*Complex.I
    let P : ℂ := -1+2*l+B
    let R : ℂ := 2*l+k*B
    let s : ℝ := (conj P*R).im
    let r : ℂ := y*P*R/(s*conj B)
    r-P = -2*l*P*((1-k)+Complex.I/y)/(k+2*l*(1-k)) := by
  intro B P R s r
  have hs : s = -y*(k+2*l*(1-k)) := by
    simp [s,P,R,B,Complex.mul_im,Complex.mul_re]
    ring
  have hB : conj B = -B := by simp [B]
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hdc : (k : ℂ)+2*l*(1-k) ≠ 0 := by exact_mod_cast hden
  dsimp only [r]
  rw [hs,hB]
  push_cast
  dsimp only [P,R,B]
  field_simp [Complex.I_ne_zero]
  linear_combination (norm := ring) (2*l*((-1+2*l)+y*Complex.I)) * Complex.I_sq

/-- The normalized rectangular displacement has the claimed joint limit
when the tie and d approach zero. -/
theorem rectangular_leaf0_limit (y : ℝ) (hy : y ≠ 0) :
    Filter.Tendsto (fun kl : ℝ × ℝ =>
      -(-1+2*(kl.2 : ℂ)+y*Complex.I)*((1-(kl.1 : ℂ))+Complex.I/y) /
        ((kl.1 : ℂ)+2*kl.2*(1-kl.1)))
      (nhds (1,0)) (nhds (1+Complex.I/y)) := by
  let f := fun kl : ℝ × ℝ =>
    -(-1+2*(kl.2 : ℂ)+y*Complex.I)*((1-(kl.1 : ℂ))+Complex.I/y) /
      ((kl.1 : ℂ)+2*kl.2*(1-kl.1))
  have hc : ContinuousAt f (1,0) := by
    dsimp only [f]
    fun_prop (disch := norm_num)
  have hval : f (1,0) = 1+Complex.I/y := by
    simp [f]
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy
    field_simp
    linear_combination -↑y*Complex.I_sq
  exact hval ▸ hc.tendsto

/-- Limiting bisector equations for vertex 4. The two derivatives
Re(Ba) and Re(q−r) are strictly positive for y>0. -/
theorem bisector_model (x y : ℝ) (hy : 0 < y) :
    let B : ℂ := ⟨x,y⟩
    let p := B-1
    let T := x^2+y^2
    let S := B/conj B
    let a := 4*Complex.I*y*(1-B)/B^2
    let q := 2*(Complex.normSq p : ℂ)/B
    let r := 2*p^2/B
    (B*a).re = 4*y^2/T ∧
    2*(conj a*q).re = Complex.normSq a ∧ S*(q-a) = r ∧
    (q-r).re = 4*y^2/T := by
  intro B p T S a q r
  have hT : x^2+y^2 ≠ 0 := ne_of_gt (by positivity)
  have hB : B ≠ 0 := fun h => (ne_of_gt hy) (congrArg Complex.im h)
  have ha : B^2 ≠ 0 := pow_ne_zero _ hB
  have hN : Complex.normSq B = x^2+y^2 := by simp [Complex.normSq_apply,B]; ring
  have hNN : Complex.normSq (B^2) = (x^2+y^2)^2 := by rw [map_pow,hN]
  have hp : Complex.normSq p = (x-1)^2+y^2 := by simp [p,B,Complex.normSq_apply];ring
  have hB' : conj B ≠ 0 := by simpa using hB
  have hB₂ : (B^2).re = x^2-y^2 ∧ (B^2).im = 2*x*y := by
    simp [B,pow_two,Complex.mul_re,Complex.mul_im]
    ring
  have hA : a.re = (4*y^2*(x^2-y^2)+8*x*y^2*(1-x))/(x^2+y^2)^2 ∧
      a.im = (4*y*(1-x)*(x^2-y^2)-8*x*y^3)/(x^2+y^2)^2 := by
    simp only [a, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,hB₂.1,hB₂.2,hNN]
    simp [B]
    constructor <;> ring
  have hQ : q.re = 2*((x-1)^2+y^2)*x/(x^2+y^2) ∧
      q.im = -2*((x-1)^2+y^2)*y/(x^2+y^2) := by
    have coeff : (2 : ℂ)*(Complex.normSq p : ℂ) = ((2*Complex.normSq p : ℝ) : ℂ) := by push_cast; rfl
    simp only [q,coeff,Complex.div_re,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im]
    simp [hp,hN,B,neg_div]
  have hR : r.re = 2*((x-1)^2-y^2)*x/(x^2+y^2)+4*(x-1)*y^2/(x^2+y^2) := by
    simp [r,Complex.div_re,Complex.mul_re,pow_two,Complex.mul_im,p,B,Complex.normSq_apply]
    ring
  refine ⟨?_,?_,?_,?_⟩
  · rw [Complex.mul_re,hA.1,hA.2]
    dsimp [B,T]
    field_simp
    ring
  · rw [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.normSq_apply,hA.1,hA.2,hQ.1,hQ.2]
    field_simp
    ring
  · change (B/conj B)*(2*(Complex.normSq p : ℂ)/B - 4*Complex.I*(y : ℂ)*(1-B)/B^2) = 2*p^2/B
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp [p]
    field_simp
    have hdiff : B-conj B = 2*Complex.I*y := by
      apply Complex.ext <;> simp [B]
      ring
    simp only [map_sub, map_one]
    linear_combination -2*(B-1) * hdiff
  · rw [Complex.sub_re,hQ.1,hR]
    dsimp [T]
    field_simp
    ring

/-- Complex multiplication in the plane coordinates used by the reconstruction. -/
def mul (a b : Plane ℝ) : Plane ℝ := (a.1*b.1-a.2*b.2, a.1*b.2+a.2*b.1)

/-- The five limiting core/leaf locations, uniformly multiplied by the positive
modulus norm squared. The other three vertices collide with 1 or 2. -/
def limitPoints (x y : ℝ) : Fin 8 → Plane ℝ :=
  let T := x^2 + y^2
  let B := (x,y)
  let p := (x-1,y)
  let s := mul B B
  ![-mul p s, 0, T • p, s, 0, T • B, T • p, 0]

/-- Oriented projected double area of a labeled triangle. -/
def area (q : Fin 8 → Plane ℝ) (i j k : Fin 8) : ℝ := cross (q j-q i) (q k-q i)

/-- Ten limiting area identities, including the three which vanish
on the rectangular boundary. The common scale factor for the areas is T². -/
theorem limit_area_table (x y : ℝ) :
    let T := x^2+y^2
    let ρ := T-2*x
    let q := limitPoints x y
    area q 1 2 3 = T*y*ρ ∧ area q 2 3 5 = T*y*ρ ∧
    area q 1 2 5 = -T^2*y ∧ area q 1 3 5 = -T^2*y ∧ area q 0 1 3 = -T^2*y ∧
    area q 0 1 2 = -2*T*x*y*((x-1)^2+y^2) ∧
    area q 0 1 5 = T^2*y*(1-2*x) ∧ area q 0 3 5 = T^2*y*(1-2*x) ∧
    area q 0 2 5 = 2*T*x*y*(1-2*x) ∧ area q 0 2 3 = 2*T*x*y*ρ := by
  dsimp [limitPoints, area, cross, mul]
  repeat' apply And.intro
  all_goals ring

/-- The limiting directions of vertices 4 and 7 have the signs needed for
the projected faces 164, 147, 127, 137 and 175. Here p=B−1 and S=B/conj B.
The factors T in the direction vectors clear denominators. -/
theorem direction_area_table (x y : ℝ) :
    let T := x^2+y^2
    let B := (x,y)
    let p := (x-1,y)
    let d₄ := mul (mul p p) (x,-y)
    let d₇ := mul p B
    let s := mul B B
    cross p d₄ = ((x-1)^2+y^2)*y ∧
    cross d₄ d₇ = ((x-1)^2+y^2)*y*(T-2*x) ∧
    cross p d₇ = ((x-1)^2+y^2)*y ∧ cross s d₇ = T*y ∧
    cross d₇ B = -T*y := by
  dsimp [mul, cross]
  repeat' apply And.intro
  all_goals ring

/-- At the last planar leaf the rows U and W/d have independent limits.
Both rows below are multiplied by T², where T=x²+y². The null row annihilates
pB and the nonzero row gives the factor in the solution r₇/λ. -/
theorem leaf7_limiting_rows (x y : ℝ) (hy : 0 < y) (hρ : 2*x < x^2+y^2) :
    let T := x^2+y^2
    let ρ := T-2*x
    let B := (x,y)
    let p := (x-1,y)
    let s := mul B B
    let jump := mul p B
    let rot := fun a : Plane ℝ => (-a.2,a.1)
    let u := (2*y*ρ) • rot s
    let w := (-4*y*ρ) • rot jump
    (mul p (mul (x,-y) (x,-y))).2 = -y*ρ ∧
      dot u jump = 2*y^2*ρ*T ∧ dot w jump = 0 ∧
      cross u w = -8*y^3*ρ^2*T ∧ cross u w < 0 := by
  intro T ρ B p s jump rot u w
  have hT : 0 < T := by dsimp [T]; positivity
  have hpos : 0 < ρ := sub_pos.mpr hρ
  have hd : cross u w = -8*y^3*ρ^2*T := by
    dsimp [u,w,rot,s,jump,B,p,ρ,T,mul,cross]
    ring
  refine ⟨?_,?_,?_,hd,?_⟩
  · dsimp [T,ρ,B,p,mul]; ring
  · dsimp [u,s,jump,rot,T,ρ,p,B,mul,dot]; ring
  · dsimp [w,jump,rot,ρ,T,p,B,mul,dot]; ring
  · rw [hd]
    linarith only [show 0 < 8*y^3*ρ^2*T by positivity]

/-- The rectangular slice has r₀−r₂ parallel to 1+i/y to first order in
2λ. Multiplication by y clears its only denominator. -/
theorem rectangular_area_coefficients (y : ℝ) :
    let v := (y,1)
    let p := (-1,y)
    cross v p = y^2+1 ∧ cross v (1,0) = -1 ∧ cross v (0,y) = y^2 := by
  dsimp [cross]
  repeat' apply And.intro
  all_goals ring

/-- The three marked squared-distance gaps used to open the hinges. A, B
denote the original marked periods; the final common similarity multiplies
the three gaps by the same positive factor. -/
theorem coherent_gaps (A B p₂ p₃ p₅ : Plane ℝ) (g t : ℝ)
    (h₂₅ : dot (p₂-p₅) A = squared2 A/2-g)
    (h₁₂ : dot p₂ B = -squared2 B/2+t^2)
    (h₁₃ : dot p₃ A = squared2 A/2-t^2) :
    squared2 (p₂-p₅-A) - squared2 (p₂-p₅) = 2*g ∧
    squared2 (p₂+B) - squared2 p₂ = 2*t^2 ∧
    squared2 (p₃-A) - squared2 p₃ = 2*t^2 := by
  simp only [squared2, dot, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at *
  exact ⟨by linear_combination -2*h₂₅, by linear_combination 2*h₁₂,
    by linear_combination -2*h₁₃⟩

/-- A zero-height root meets the height equation transversely if its
horizontal velocity differs from the flat one by a nonzero normal to P,
and the flat root q is not on P. -/
theorem root_height_transverse {P q w n : Plane ℝ} (hP : dot P n = 0)
    (hn : squared2 n ≠ 0) (hq : cross P q ≠ 0) :
    -2*dot q n ≠ 0 ∧ ∀ t : ℝ,
    squared2 (q+t • w) - squared2 (q+t • (w+n)) =
      (-2*dot q n)*t-(2*dot w n+squared2 n)*t^2 := by
  have hid : dot P n * cross n q + dot q n * cross P n = squared2 n * cross P q := by
    simp only [dot, cross, squared2]
    ring
  refine ⟨?_, ?_⟩
  · intro h
    have hh : dot q n = 0 := by linarith only [h]
    rw [hP, hh] at hid
    exact (mul_ne_zero hn hq) (by linarith only [hid])
  · intro t
    simp only [squared2, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- A homogeneous row and a row with nonzero right-hand side are independent
at their common solution if the homogeneous row is nonzero. This gives the
two-by-two solve for vertex 0 at the first fold. -/
theorem leaf0_nonsingular {u v p : Plane ℝ} (hu : squared2 u ≠ 0)
    (hup : dot u p = 0) (hvp : dot v p ≠ 0) : cross u v ≠ 0 := by
  have hid : squared2 u*dot v p = dot u v*dot u p + cross u v*cross u p := by
    simp only [squared2, dot, cross]
    ring
  intro hc
  rw [hc, hup] at hid
  exact (mul_ne_zero hu hvp) (by linarith only [hid])

/-- Rotating a pair of triangles away from the unfolded position shortens
the opposite squared distance by 2uv(1−cos θ). Coordinates are relative
to the hinge, with perpendicular altitudes u,v and axial separation a. -/
theorem hinge_shortening (a u v c s : ℝ) (h : c^2+s^2 = 1) :
    a^2+(u+v)^2 - (a^2+(u+v*c)^2+(v*s)^2) = 2*u*v*(1-c) := by
  linear_combination -v^2*h

/-- Both signed hinge branches at a positive shortening have positive
radicand and give the same change in the opposite squared length. -/
theorem hinge_branches {u v gap : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hg : 0 < gap) (hsmall : gap < 2*u*v) :
    let c := 1-gap/(u*v)
    let s := Real.sqrt (1-c^2)
    0 < s ∧ c^2+s^2 = 1 ∧ c^2+(-s)^2 = 1 ∧ 2*u*v*(1-c) = 2*gap := by
  intro c s
  have hprod : 0 < u*v := mul_pos hu hv
  have hlo : 0 < gap/(u*v) := div_pos hg hprod
  have hhi : gap/(u*v) < 2 := (div_lt_iff₀ hprod).2 (by linarith only [hsmall])
  have hleft : 0 < 1-c := by dsimp [c]; linarith
  have hright : 0 < 1+c := by dsimp [c]; linarith
  have hrad : 0 < 1-c^2 := by nlinarith only [mul_pos hleft hright]
  have hs : s^2 = 1-c^2 := Real.sq_sqrt hrad.le
  refine ⟨Real.sqrt_pos.2 hrad, by linarith only [hs], by nlinarith only [hs], ?_⟩
  dsimp [c]
  field_simp
  ring

/-- The signed sine for a fold that changes the opposite squared distance by
a multiple of t². The positive factor b is the multiple divided by 2uv. -/
noncomputable def hingeSine (t b : ℝ) : ℝ := t * Real.sqrt (2*b - b^2*t^2)

/-- The formula for the signed sine remains smooth at the unfolded
configuration jointly in t and the varying altitude factor. -/
theorem hingeSine_smooth {b : ℝ} (hb : 0 < b) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × ℝ => hingeSine q.1 q.2) (0,b) := by
  unfold hingeSine
  fun_prop (disch := simp [ne_of_gt hb])

/-- The two smooth branches have opposite nonzero signs after the tie is
released, and give the same cosine. -/
theorem hingeSine_spec {t b : ℝ} (ht : 0 < t) (hb : 0 < b) (hsmall : b*t^2 < 2) :
    0 < hingeSine t b ∧ (1-b*t^2)^2 + (hingeSine t b)^2 = 1 ∧
    (1-b*t^2)^2 + (-hingeSine t b)^2 = 1 := by
  have h : 0 < 2*b-b^2*t^2 := by nlinarith only [mul_pos hb (sub_pos.mpr hsmall)]
  have hs := Real.sq_sqrt h.le
  have hcircle : (1-b*t^2)^2 + (hingeSine t b)^2 = 1 := by
    dsimp [hingeSine]
    linear_combination t^2*hs
  exact ⟨mul_pos ht (Real.sqrt_pos.2 h), hcircle, by simpa only [neg_sq] using hcircle⟩

/-- Expansion of a spatial bracket in the heights of its four vertices. -/
theorem height_expansion (p : Fin 8 → Plane ℝ) (z : Fin 8 → ℝ) (i j k l : Fin 8) :
    affineBracket (atHeight (p i) (z i)) (atHeight (p j) (z j))
      (atHeight (p k) (z k)) (atHeight (p l) (z l)) =
    -(z i)*area p j k l + (z j)*area p i k l -
      (z k)*area p i j l + (z l)*area p i j k := by
  simp only [affineBracket, determinant3, atHeight, area, cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-- In the two tied planes 1236 and 1357, the remaining two-leaf volume
has a sign fixed by four projected areas and the height of 3. -/
theorem two_leaf_volume (p : Fin 8 → Plane ℝ) (z : Fin 8 → ℝ)
    (z₁ : z 1 = 0) (z₂ : z 2 = 0) (z₅ : z 5 = 0) :
    let r := fun i => atHeight (p i) (z i)
    affineBracket (r 1) (r 2) (r 3) (r 6) = 0 →
    affineBracket (r 1) (r 3) (r 5) (r 7) = 0 →
    affineBracket (r 2) (r 3) (r 6) (r 7) * area p 1 2 3 * area p 1 3 5 =
      -(z 3)*area p 1 2 5 * area p 1 3 7 * area p 2 3 6 := by
  intro r h₆ h₇
  have hp : area p 2 6 7 * area p 1 2 3 - area p 1 2 6 * area p 2 3 7 =
      -area p 2 3 6 * area p 1 2 7 := by
    simp only [area, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  have hq : area p 1 5 7 * area p 1 2 3 + area p 1 2 7 * area p 1 3 5 =
      area p 1 2 5 * area p 1 3 7 := by
    simp only [area, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  dsimp only [r] at h₆ h₇ ⊢
  rw [height_expansion p z 1 2 3 6] at h₆
  rw [height_expansion p z 1 3 5 7] at h₇
  rw [height_expansion p z 2 3 6 7]
  simp only [z₁, z₂, z₅, neg_zero, zero_mul, zero_add, sub_zero] at h₆ h₇ ⊢
  linear_combination -area p 2 3 7 * area p 1 3 5 * h₆ +
    area p 2 3 6 * area p 1 2 3 * h₇ + z 3 * area p 1 3 5 * hp - z 3 * area p 2 3 6 * hq

end OrigamiTorus.Type5.OffRayOpening
