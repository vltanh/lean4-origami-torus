module

public import OrigamiTorus.Type7.Rectangular
import Mathlib.Tactic

/-! The two rational Type 4 families and their domains in the half modular region. -/

@[expose] public section

namespace OrigamiTorus.Type4

def domain (nearEndpoint : Bool) (x w : ℝ) : Prop :=
  (if nearEndpoint then 9/20 else 0) ≤ x ∧
    (if nearEndpoint then x < 1/2 else x ≤ 9/20) ∧ 1-x^2 ≤ w

def trapezoidHeight {R : Type*} [Field R] (nearEndpoint : Bool) (x : R) : R :=
  if nearEndpoint then 1 + (3/2)*(1-2*x)^2 else 33/(20+26*x)

def trapezoidSpan {R : Type*} [Field R] (H x : R) : R := H - 1 + H*x

def trapezoidCut {R : Type*} [Field R] (nearEndpoint : Bool) (H x : R) : R :=
  -(if nearEndpoint then 2/3 else 1/3) * trapezoidSpan H x

/-- These are the planar positions from the PR. Their physical coordinates are `(X,y*Y)`. -/
def trapezoidPoint {R : Type*} [Field R] (x w H r : R) : Vertex → R × R :=
  let a := H*x
  let D := trapezoidSpan H x
  let q := H/D
  let t₅ := ((a^2-a+H^2*w)*q/H-1)/(1+q^2*w)
  let t₃ := -(-a^2*q+2*a*H+a*q+H^2*q*w+H*q^2*r*w+H*r-H)/((H+q*r)*(q^2*w+1))
  ![(0,0), (1-a-r,H+q*r), (1/2,0), (a+t₃,H+q*t₃), (1,0), (1+t₅,q*t₅), (a,H), (1-a,H)]

def planarPoint {R : Type*} [Field R] (nearEndpoint : Bool) (x w : R) : Vertex → R × R :=
  let H := trapezoidHeight nearEndpoint x
  trapezoidPoint x w H (trapezoidCut nearEndpoint H x)

theorem domain_covers (x w : ℝ) (hx : 0 ≤ x) (hx' : x < 1/2) (hw : 1-x^2 ≤ w) :
    ∃ nearEndpoint, domain nearEndpoint x w := by
  by_cases h : x ≤ 9/20
  · exact ⟨false,hx,h,hw⟩
  · exact ⟨true,le_of_lt (lt_of_not_ge h),hx',hw⟩

theorem domain_bounds {nearEndpoint : Bool} {x w : ℝ} (hd : domain nearEndpoint x w) :
    0 ≤ x ∧ x < 1/2 ∧ 0 < w := by
  have hx : 0 ≤ x := by
    cases nearEndpoint
    · exact hd.1
    · have h : (9 / 20 : ℝ) ≤ x := hd.1
      linarith
  have hx' : x < 1/2 := by
    cases nearEndpoint
    · have h : x ≤ (9 / 20 : ℝ) := hd.2.1
      linarith
    · exact hd.2.1
  have hl := mul_nonneg (sub_nonneg.mpr (le_of_lt hx')) (add_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hx)
  have hw : 1-x^2 ≤ w := hd.2.2
  exact ⟨hx,hx', by nlinarith only [hl,hw]⟩

theorem height_gt_one {nearEndpoint : Bool} {x w : ℝ} (hd : domain nearEndpoint x w) :
    1 < trapezoidHeight nearEndpoint x := by
  obtain ⟨hx,hx',_⟩ := domain_bounds hd
  cases nearEndpoint
  · have hd' : x ≤ (9 / 20 : ℝ) := hd.2.1
    simp [trapezoidHeight]
    apply (lt_div_iff₀ (by linarith)).mpr
    linarith
  · have hs : 0 < (1-2*x)^2 := sq_pos_of_pos (by linarith)
    simp [trapezoidHeight]
    linarith

/-- The coordinate formulas are defined throughout the claimed strips, including the cusp. -/
theorem denominator_signs {nearEndpoint : Bool} {x w : ℝ} (hd : domain nearEndpoint x w) :
    let H := trapezoidHeight nearEndpoint x
    let D := trapezoidSpan H x
    let q := H/D
    let r := trapezoidCut nearEndpoint H x
    0 < H ∧ 0 < D ∧ 0 < (H+q*r) ∧ 0 < (1+q^2*w) := by
  obtain ⟨hx,_,hw⟩ := domain_bounds hd
  let H := trapezoidHeight nearEndpoint x
  let D := trapezoidSpan H x
  have hH' : 1 < H := height_gt_one hd
  have hH : 0 < H := by linarith
  have hD : 0 < D := by
    change 0 < H-1+H*x
    linarith only [hH',mul_nonneg hH.le hx]
  change 0 < H ∧ 0 < D ∧ 0 < H + H/D * trapezoidCut nearEndpoint H x ∧ 0 < 1+(H/D)^2*w
  refine ⟨hH,hD,?_,by positivity⟩
  cases nearEndpoint
  · have he : H+H/D*trapezoidCut false H x = 2*H/3 := by
      change H+H/D*(-(1/3)*D) = 2*H/3
      field_simp [hD.ne']
      ring
    rw [he]
    positivity
  · have he : H+H/D*trapezoidCut true H x = H/3 := by
      change H+H/D*(-(2/3)*D) = H/3
      field_simp [hD.ne']
      ring
    rw [he]
    positivity

/-- All eight points, with the same positive denominator cleared. The arguments
are the numerator and denominator of the trapezoid height and the fixed cut ratio. -/
def polynomialPoints {R : Type*} [Field R] (x w c H J : R) : Vertex → R × R :=
  let A := H*x
  let D := H-J+A
  let Q := D^2+H^2*w
  let S := (A^2-A*J-(1-c)*H^2*w-D*(2*A-c*D-J))/(1-c)
  let T := A^2-A*J+H^2*w-D*J
  ![(0,0), ((J-A+c*D)*Q,(1-c)*H*Q), (J*Q/2,0), (A*Q+D*S,H*Q+H*S),
    (J*Q,0), (J*Q+D*T,H*T), (A*Q,H*Q), ((J-A)*Q,H*Q)]

theorem polynomial_rescale (x w c H J : ℝ)
    (hJ : J ≠ 0) (hH : H ≠ 0) (hc : 1-c ≠ 0) (hD : H-J+H*x ≠ 0)
    (hQ : (H-J+H*x)^2+H^2*w ≠ 0) (v : Vertex) :
    let Q := (H-J+H*x)^2+H^2*w
    let P := trapezoidPoint x w (H/J) (-c*trapezoidSpan (H/J) x) v
    polynomialPoints x w c H J v = (J*Q*P.1,J*Q*P.2) := by
  have hspan : trapezoidSpan (H/J) x = (H-J+H*x)/J := by
    unfold trapezoidSpan
    field_simp
  have hquot : H/J/((H-J+H*x)/J) = H/(H-J+H*x) := by field_simp
  have hsum : H/J+H/(H-J+H*x)*(-c*((H-J+H*x)/J)) = ((1-c)*H)/J := by
    field_simp
    ring
  simp only [neg_mul,mul_neg] at hsum
  have hsq : 1+(H/(H-J+H*x))^2*w = ((H-J+H*x)^2+H^2*w)/(H-J+H*x)^2 := by
    field_simp
  have hsq' : (H/(H-J+H*x))^2*w+1 = ((H-J+H*x)^2+H^2*w)/(H-J+H*x)^2 := by
    rw [add_comm,hsq]
  fin_cases v <;> apply Prod.ext <;>
    simp [polynomialPoints,trapezoidPoint,hspan,hquot,hsum,hsq,hsq'] <;>
    field_simp [hJ,hH,hc,hD,hQ] <;> ring

def heightNumerator {R : Type*} [Field R] (nearEndpoint : Bool) (x : R) : R :=
  if nearEndpoint then 1+(3/2)*(1-2*x)^2 else 33

def heightDenominator {R : Type*} [Field R] (nearEndpoint : Bool) (x : R) : R :=
  if nearEndpoint then 1 else 20+26*x

theorem polynomial_planarPoint {nearEndpoint : Bool} {x w : ℝ} (hd : domain nearEndpoint x w) :
    let H := heightNumerator nearEndpoint x
    let J := heightDenominator nearEndpoint x
    let c : ℝ := if nearEndpoint then 2/3 else 1/3
    let Q := (H-J+H*x)^2+H^2*w
    0 < J*Q ∧ ∀ v, polynomialPoints x w c H J v =
      (J*Q*(planarPoint nearEndpoint x w v).1,J*Q*(planarPoint nearEndpoint x w v).2) := by
  let H := heightNumerator nearEndpoint x
  let J := heightDenominator nearEndpoint x
  let c : ℝ := if nearEndpoint then 2/3 else 1/3
  obtain ⟨hx,_,hw⟩ := domain_bounds hd
  have hJ : 0 < J := by cases nearEndpoint <;> simp [J,heightDenominator] <;> positivity
  have hh : H/J = trapezoidHeight nearEndpoint x := by
    cases nearEndpoint <;> simp [H,J,heightNumerator,heightDenominator,trapezoidHeight]
  have h1 : J < H := (one_lt_div hJ).1 (hh ▸ height_gt_one hd)
  have hH : 0 < H := hJ.trans h1
  have hD : 0 < H-J+H*x := add_pos_of_pos_of_nonneg (sub_pos.mpr h1) (mul_nonneg hH.le hx)
  have hc : 1-c ≠ 0 := by cases nearEndpoint <;> norm_num [c]
  have hQ : 0 < (H-J+H*x)^2+H^2*w := by positivity
  refine ⟨mul_pos hJ hQ,?_⟩
  intro v
  simpa only [hh, planarPoint, trapezoidCut, neg_mul] using
    polynomial_rescale x w c H J hJ.ne' hH.ne' hc hD.ne' hQ.ne' v

private theorem polynomial_faceSigns (x w c H : ℝ)
    (hx : 0 ≤ x) (hx' : x < 1/2) (hw : 1-x^2 ≤ w) (hw' : 0 < w) (hH : 1 < H)
    (hHmax : H < 2) (haMax : H*x < 1/2) (hc : c = 1/3 ∨ c = 2/3 ∧ H ≤ 6/5) :
    let p := polynomialPoints x w c H 1
    (0 < area p 3 5 6 ∧ area p 3 5 2 < 0 ∧ area p 6 2 3 < 0 ∧ 0 < area p 6 2 5) ∧
    ∀ (f : Triangle) (pos : Bool), (f,pos) ∈ Type7.orientedFaces →
      if pos then 0 < area p f.1 f.2.1 f.2.2 else area p f.1 f.2.1 f.2.2 < 0 := by
  let a := H*x
  let D := H-1+a
  let Q := D^2+H^2*w
  let S := (a^2-a-(1-c)*H^2*w-D*(2*a-c*D-1))/(1-c)
  let T := a^2-a+H^2*w-D
  let K := Q+S
  have hH₀ : 0 < H := by linarith
  have ha : 0 ≤ a := mul_nonneg hH₀.le hx
  have hD : 0 < D := add_pos_of_pos_of_nonneg (sub_pos.mpr hH) ha
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hc₀ : 0 < 1-c := by rcases hc with rfl | ⟨rfl,_⟩ <;> norm_num
  have hc' : 0 < c := by rcases hc with rfl | ⟨rfl,_⟩ <;> norm_num
  have ha' : a < 1/2 := haMax
  have hbase : 0 ≤ a^2+H^2*w-H^2 := by
    dsimp [a]
    nlinarith only [mul_nonneg (sq_nonneg H) (sub_nonneg.mpr hw)]
  have hT : 0 < T := by
    have h := mul_pos hH₀ (sub_pos.mpr hx')
    dsimp [T,D,a] at *
    nlinarith only [hbase,h,sq_nonneg (H-1)]
  have hS_eq : S*(1-c) = a^2-a-(1-c)*H^2*w-D*(2*a-c*D-1) :=
    div_mul_cancel₀ _ hc₀.ne'
  have hS : S < 0 := by
    have hN : S*(1-c) ≤ (H-1)+c*(H-1)^2-(1-c)*H^2 := by
      have hcross := mul_nonneg (mul_nonneg hc₀.le (sub_nonneg.mpr hH.le)) ha
      dsimp only [D] at hS_eq
      nlinarith only [hS_eq,mul_nonneg hc₀.le hbase,hcross]
    have hneg : (H-1)+c*(H-1)^2-(1-c)*H^2 < 0 := by
      rcases hc with rfl | ⟨rfl,hH'⟩
      · nlinarith only [mul_pos hH₀ (sub_pos.mpr hH)]
      · nlinarith only [mul_nonneg (sub_nonneg.mpr hH') (sub_nonneg.mpr hH.le),hH']
    exact neg_of_mul_neg_left (lt_of_le_of_lt hN hneg) hc₀.le
  have hsum : 0 < Q+(2*H-1)*T+S := by
    have he : (1-c)*(Q+(2*H-1)*T+S) = (1-c)*(2*H-1)*T+H*(H-1) := by
      dsimp only [D,Q] at hS_eq ⊢
      linear_combination hS_eq
    apply (mul_pos_iff_of_pos_left hc₀).mp
    rw [he]
    have h₁ : 0 < 2*H-1 := by linarith
    have h₂ : 0 < H-1 := sub_pos.mpr hH
    positivity
  have hK : (1-c)*K = H*(H-1) := by
    dsimp only [K,Q,D] at hS_eq ⊢
    linear_combination hS_eq
  have hKpos : 0 < K := (mul_pos_iff_of_pos_left hc₀).mp (hK ▸ mul_pos hH₀ (sub_pos.mpr hH))
  have hQT : Q-T = H*(D+a) := by
    dsimp [Q,T,D]
    ring
  have hHQ : 0 < H-1 := sub_pos.mpr hH
  have hR : (1-2*c)*D+a-1 < 0 := by
    rcases hc with hc | ⟨hc,_⟩
    · rw [hc]
      dsimp only [D]
      linarith only [ha',hHmax]
    · rw [hc]
      linarith only [ha',hD]
  have hF : 0 < (1-c)*H*Q+((2*c-1)*D-a)*K := by
    apply (mul_pos_iff_of_pos_left hc₀).mp
    have he : (1-c)*((1-c)*H*Q+((2*c-1)*D-a)*K) =
        H*((c*(H-1)-(1-c)*a)^2+(1-c)^2*H^2*w) := by
      dsimp only [Q,D] at *
      linear_combination ((2*c-1)*(H-1+a)-a)*hK
    rw [he]
    positivity
  let p := polynomialPoints x w c H 1
  have h₁ : 0 < H-1/2 := by linarith
  have h₂ : 0 < 2*H-1 := by linarith
  have h356 : area p 3 5 6 = -S*H^2*Q := by
    norm_num [p,area,polynomialPoints,a,D,Q,S,T]
    ring
  have h352 : area p 3 5 2 = -H*Q*(Q+(2*H-1)*T+S)/2 := by
    norm_num [p,area,polynomialPoints,a,D,Q,S,T]
    ring
  have h623 : area p 6 2 3 = S*H*Q*(H-1/2) := by
    norm_num [p,area,polynomialPoints,a,D,Q,S]
    ring
  have h625 : area p 6 2 5 = H*Q*(Q+(2*H-1)*T)/2 := by
    norm_num [p,area,polynomialPoints,a,D,Q,T]
    ring
  have hflip : 0 < area p 3 5 6 ∧ area p 3 5 2 < 0 ∧ area p 6 2 3 < 0 ∧ 0 < area p 6 2 5 := by
    rw [h356,h352,h623,h625]
    refine ⟨mul_pos (mul_pos (neg_pos.mpr hS) (sq_pos_of_pos hH₀)) hQ,?_,?_,by positivity⟩
    · exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hH₀) hQ) hsum)
        (by norm_num)
    · exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hS hH₀) hQ) h₁
  refine ⟨hflip,?_⟩
  intro f pos hf
  simp [Type7.orientedFaces,Type7.faces] at hf
  rcases hf with hf | hf | hf | hf | hf | hf | hf | hf | hf | hf | hf | hf | hf | hf | hf | hf
  all_goals
    rcases hf with ⟨rfl,rfl⟩
    simp only [ite_true,Bool.false_eq_true,ite_false]
  · exact hflip.1
  · have he : area p 3 2 5 = -area p 3 5 2 := by unfold area; ring
    rw [he]
    exact neg_pos.mpr hflip.2.1
  · have he : area p 3 6 4 = S*H^2*Q := by
      norm_num [p,area,polynomialPoints,a,D,Q,S]; ring
    rw [he]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hS (sq_pos_of_pos hH₀)) hQ
  · have he : area p 3 0 2 = H*Q*K/2 := by
      norm_num [p,area,polynomialPoints,a,D,Q,S,K]; ring
    rw [he]
    positivity
  · have he : area p 3 4 1 = H*Q*((1-c)*H*Q+((2*c-1)*D-a)*K) := by
      norm_num [p,area,polynomialPoints,a,D,Q,S,K]; ring
    rw [he]
    positivity
  · have he : area p 3 1 0 = H*Q*(-((1-c)*(H-1)*Q)+((1-2*c)*D+a-1)*K) := by
      norm_num [p,area,polynomialPoints,a,D,Q,S,K]; ring
    rw [he]
    exact mul_neg_of_pos_of_neg (mul_pos hH₀ hQ)
      (add_neg (neg_neg_of_pos (mul_pos (mul_pos hc₀ hHQ) hQ)) (mul_neg_of_neg_of_pos hR hKpos))
  · have he : area p 5 0 6 = -(H*Q*(Q+(H-1)*T)) := by
      norm_num [p,area,polynomialPoints,a,D,Q,T]; ring
    rw [he,neg_lt_zero]
    positivity
  · have he : area p 5 2 4 = H*Q*T/2 := by
      norm_num [p,area,polynomialPoints,a,D,Q,T]; ring
    rw [he]
    positivity
  · have he : area p 5 4 7 = -(T*H*Q*(D+a)) := by
      norm_num [p,area,polynomialPoints,a,D,Q,T]; ring
    rw [he,neg_lt_zero]
    positivity
  · have he : area p 5 7 0 = H*Q*(H*(D+a)+(H-1+2*a)*T) := by
      have h := hQT
      dsimp [p,area,polynomialPoints,a,D,Q,T] at h ⊢
      norm_num at h ⊢
      ring
    rw [he]
    positivity
  · have he : area p 6 7 4 = -((1-2*a)*H*Q^2) := by
      norm_num [p,area,polynomialPoints,a,D,Q]; ring
    have hh : 0 < 1-2*a := by linarith
    rw [he,neg_lt_zero]
    positivity
  · have he : area p 6 0 1 = H*Q^2*(1-2*a+c*(D+a)) := by
      norm_num [p,area,polynomialPoints,a,D,Q]; ring
    have hh : 0 < 1-2*a := by linarith
    rw [he]
    positivity
  · have he : area p 6 1 7 = c*H*Q^2*(1-2*a) := by
      norm_num [p,area,polynomialPoints,a,D,Q]; ring
    have hh : 0 < 1-2*a := by linarith
    rw [he]
    positivity
  · have he : area p 2 1 4 = -((1-c)*H*Q^2/2) := by
      norm_num [p,area,polynomialPoints,a,D,Q]; ring
    rw [he,neg_lt_zero]
    positivity
  · have he : area p 2 0 7 = -(H*Q^2/2) := by
      norm_num [p,area,polynomialPoints,a,D,Q]; ring
    rw [he,neg_lt_zero]
    positivity
  · have he : area p 2 7 1 = -(c*H*Q^2*(H-1/2)) := by
      norm_num [p,area,polynomialPoints,a,D,Q]; ring
    rw [he,neg_lt_zero]
    positivity

theorem height_mul_lt_half {nearEndpoint : Bool} {x w : ℝ}
    (hd : domain nearEndpoint x w) : trapezoidHeight nearEndpoint x * x < 1/2 := by
  obtain ⟨hx,hx',_⟩ := domain_bounds hd
  cases nearEndpoint
  · simp [trapezoidHeight]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith)).2
    linarith
  · have hlo : (9/20 : ℝ) ≤ x := hd.1
    have hh : 0 ≤ 1-2*x := by linarith
    have hm : 0 ≤ x*(1-2*x) := mul_nonneg hx hh
    have ht : 0 < 1/2-(3/2)*x*(1-2*x) := by
      nlinarith only [mul_nonneg (show 0 ≤ x by exact hx)
        (show 0 ≤ 1/10-(1-2*x) by linarith), hx']
    have hp := mul_pos ht (sub_pos.mpr (show 2*x < 1 by linarith))
    simp [trapezoidHeight]
    nlinarith only [hp]

/-- The four flip signs and all sixteen original face orientations hold throughout both strips. -/
theorem planar_faceSigns {nearEndpoint : Bool} {x w : ℝ} (hd : domain nearEndpoint x w) :
    let p := planarPoint nearEndpoint x w
    (0 < area p 3 5 6 ∧ area p 3 5 2 < 0 ∧ area p 6 2 3 < 0 ∧ 0 < area p 6 2 5) ∧
    ∀ (f : Triangle) (pos : Bool), (f,pos) ∈ Type7.orientedFaces →
      if pos then 0 < area p f.1 f.2.1 f.2.2 else area p f.1 f.2.1 f.2.2 < 0 := by
  obtain ⟨hx,hx',hw⟩ := domain_bounds hd
  let H := trapezoidHeight nearEndpoint x
  let c : ℝ := if nearEndpoint then 2/3 else 1/3
  have hH : 1 < H := height_gt_one hd
  have hc : c = 1/3 ∨ c = 2/3 ∧ H ≤ 6/5 := by
    cases nearEndpoint
    · exact Or.inl rfl
    · refine Or.inr ⟨rfl,?_⟩
      have h0 : (9/20 : ℝ) ≤ x := hd.1
      have hh := mul_nonneg (show (0 : ℝ) ≤ 2*x-9/10 by linarith)
        (show (0 : ℝ) ≤ 11/10-2*x by linarith)
      norm_num [H,trapezoidHeight]
      nlinarith only [hh]
  have hH₀ : 0 < H := by linarith
  have hD : 0 < H-1+H*x := add_pos_of_pos_of_nonneg (sub_pos.mpr hH) (mul_nonneg hH₀.le hx)
  let Q := (H-1+H*x)^2+H^2*w
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hc₀ : 1-c ≠ 0 := by rcases hc with h | ⟨h,_⟩ <;> norm_num [h]
  have hp (v : Vertex) : polynomialPoints x w c H 1 v =
      (Q*(planarPoint nearEndpoint x w v).1,Q*(planarPoint nearEndpoint x w v).2) := by
    simpa only [div_one,one_mul,planarPoint,trapezoidCut,neg_mul] using
      polynomial_rescale x w c H 1 one_ne_zero hH₀.ne' hc₀ hD.ne' hQ.ne' v
  have h (i j k : Vertex) : area (polynomialPoints x w c H 1) i j k =
      Q^2*area (planarPoint nearEndpoint x w) i j k := by
    simp only [area,hp]
    ring
  have hHmax : H < 2 := by
    cases nearEndpoint
    · simp [H,trapezoidHeight]
      apply (div_lt_iff₀ (by linarith)).2
      linarith
    · rcases hc with h | ⟨_,h⟩
      · norm_num [c] at h
      · linarith
  have haMax : H*x < 1/2 := height_mul_lt_half hd
  obtain ⟨hs,hf⟩ := polynomial_faceSigns x w c H hx hx' hd.2.2 hw hH hHmax haMax hc
  simp only [h] at hs
  have hQ₂ : 0 < Q^2 := sq_pos_of_pos hQ
  refine ⟨⟨(mul_pos_iff_of_pos_left hQ₂).mp hs.1, neg_of_mul_neg_right hs.2.1 hQ₂.le,
    neg_of_mul_neg_right hs.2.2.1 hQ₂.le, (mul_pos_iff_of_pos_left hQ₂).mp hs.2.2.2⟩,?_⟩
  intro f pos hm
  have hz := hf f pos hm
  simp only [h] at hz
  cases pos
  · exact neg_of_mul_neg_right hz hQ₂.le
  · exact (mul_pos_iff_of_pos_left hQ₂).mp hz

theorem planar_flipSigns {nearEndpoint : Bool} {x w : ℝ} (hd : domain nearEndpoint x w) :
    let p := planarPoint nearEndpoint x w
    0 < area p 3 5 6 ∧ area p 3 5 2 < 0 ∧ area p 6 2 3 < 0 ∧ 0 < area p 6 2 5 :=
  (planar_faceSigns hd).1

end OrigamiTorus.Type4
