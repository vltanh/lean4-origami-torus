module

public import OrigamiTorus.Type6.Data
public import OrigamiTorus.Type3.Data
import Mathlib.Tactic

/-! Exact signs over the two unbounded modulus strips. -/

@[expose] public section

namespace OrigamiTorus

private def lo (second : Bool) : ℚ := if second then 1 / 6 else 0
private def hi (second : Bool) : ℚ := if second then 1 / 2 else 1 / 6

-- These are coefficients in powers of two complementary nonnegative variables `1-t` and `t`.
private abbrev Linear := Fin 2 → ℚ
private abbrev Quadratic := Fin 3 → ℚ
private abbrev Cubic := Fin 4 → ℚ

private def evalLinear (c : Linear) (t : ℝ) : ℝ :=
  c 0 * (1 - t) + c 1 * t

private def evalQuadratic (c : Quadratic) (t : ℝ) : ℝ :=
  c 0 * (1 - t)^2 + c 1 * (1 - t) * t + c 2 * t^2

private def evalCubic (c : Cubic) (t : ℝ) : ℝ :=
  c 0 * (1 - t)^3 + c 1 * (1 - t)^2 * t + c 2 * (1 - t) * t^2 + c 3 * t^3

private def mulCoeffs (a : Linear) (b : Quadratic) : Cubic :=
  ![a 0 * b 0, a 0 * b 1 + a 1 * b 0, a 0 * b 2 + a 1 * b 1, a 1 * b 2]

private theorem eval_mulCoeffs (a : Linear) (b : Quadratic) (t : ℝ) :
    evalCubic (mulCoeffs a b) t = evalLinear a t * evalQuadratic b t := by
  simp [evalCubic, evalLinear, evalQuadratic, mulCoeffs]
  ring

private def xCoeffs (second : Bool) (v : Vertex) : Linear :=
  ![(stripPoint second (lo second) 0 v).1, (stripPoint second (hi second) 0 v).1]

private def boundaryY (second : Bool) (x : ℚ) (v : Vertex) : ℚ :=
  (stripPoint second x (1 - x^2) v).2

private def yCoeffs (second : Bool) (v : Vertex) : Quadratic :=
  let a := boundaryY second (lo second) v
  let b := boundaryY second ((lo second + hi second) / 2) v
  let c := boundaryY second (hi second) v
  ![a, 4 * b - a - c, c]

private def ySlope (second : Bool) (v : Vertex) : ℚ :=
  (stripPoint second 0 1 v).2 - (stripPoint second 0 0 v).2

private def paramX (second : Bool) (t : ℝ) : ℝ :=
  lo second * (1 - t) + hi second * t

private def paramW (second : Bool) (t h : ℝ) : ℝ :=
  1 - (paramX second t)^2 + h

set_option maxHeartbeats 2000000 in
private theorem point_coeffs (second : Bool) (v : Vertex) (t h : ℝ) :
    stripPoint second (paramX second t) (paramW second t h) v =
      (evalLinear (xCoeffs second v) t, evalQuadratic (yCoeffs second v) t + ySlope second v * h) := by
  cases second <;> fin_cases v <;> apply Prod.ext <;>
    norm_num [stripPoint, paramX, paramW, evalLinear, evalQuadratic,
      xCoeffs, yCoeffs, ySlope, boundaryY, lo, hi] <;> ring

private theorem domain_param {second : Bool} {x w : ℝ} (hd : chartDomain second x w) :
    ∃ t h : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ h ∧ x = paramX second t ∧ w = paramW second t h := by
  cases second
  · simp [chartDomain] at hd
    refine ⟨6*x, w - (1-x^2), by linarith [hd.1], by linarith [hd.2.1],
      by linarith [hd.2.2], ?_, ?_⟩ <;> norm_num [paramW, paramX, lo, hi] <;> ring
  · simp [chartDomain] at hd
    refine ⟨3*x-1/2, w - (1-x^2), by linarith [hd.1], by linarith [hd.2.1],
      by linarith [hd.2.2], ?_, ?_⟩ <;> norm_num [paramW, paramX, lo, hi] <;> ring

private structure StripPoly where
  base : Cubic
  slope : Linear

private def StripPoly.eval (p : StripPoly) (t h : ℝ) : ℝ :=
  evalCubic p.base t + evalLinear p.slope t * h

private def StripPoly.scale (r : ℚ) (p : StripPoly) : StripPoly :=
  ⟨fun i => r * p.base i, fun i => r * p.slope i⟩

private def StripPoly.add (p q : StripPoly) : StripPoly :=
  ⟨p.base + q.base, p.slope + q.slope⟩

private theorem StripPoly.eval_scale (r : ℚ) (p : StripPoly) (t h : ℝ) :
    (p.scale r).eval t h = r * p.eval t h := by
  simp [StripPoly.scale, StripPoly.eval, evalLinear, evalCubic]
  ring

private theorem StripPoly.eval_add (p q : StripPoly) (t h : ℝ) :
    (p.add q).eval t h = p.eval t h + q.eval t h := by
  simp [StripPoly.add, StripPoly.eval, evalLinear, evalCubic]
  ring

private def areaCoeffs (second : Bool) (a b c : Vertex) : StripPoly :=
  let term (i j k : Vertex) : StripPoly :=
    ⟨mulCoeffs (xCoeffs second i) (yCoeffs second j - yCoeffs second k),
     fun m => xCoeffs second i m * (ySlope second j - ySlope second k)⟩
  ((term b c a).add (term c a b)).add (term a b c)

private theorem area_eval (second : Bool) (a b c : Vertex) (t h : ℝ) :
    area (stripPoint second (paramX second t) (paramW second t h)) a b c =
      (areaCoeffs second a b c).eval t h := by
  simp only [areaCoeffs, StripPoly.eval_add, area, point_coeffs]
  simp only [StripPoly.eval, eval_mulCoeffs, evalLinear, evalQuadratic, Pi.sub_apply]
  push_cast
  ring

private def volumeCoeffs (second : Bool) (z : Vertex → ℚ) (a b c d : Vertex) : StripPoly :=
  let first := ((areaCoeffs second b c d).scale (-z a)).add ((areaCoeffs second a c d).scale (z b))
  (first.add ((areaCoeffs second a b d).scale (-z c))).add ((areaCoeffs second a b c).scale (z d))

private theorem volume_eval (second : Bool) (z : Vertex → ℚ) (a b c d : Vertex) (t h : ℝ) :
    volume (stripPoint second (paramX second t) (paramW second t h))
      (fun v => (z v : ℝ)) a b c d = (volumeCoeffs second z a b c d).eval t h := by
  simp only [volumeCoeffs, StripPoly.eval_add, StripPoly.eval_scale, volume, area_eval, Rat.cast_neg]
  ring

private def StripPoly.positive (p : StripPoly) : Bool :=
  decide (∀ i, 0 < p.base i) && decide (∀ i, 0 ≤ p.slope i)

private theorem StripPoly.positive_sound {p : StripPoly} (hp : p.positive = true) {t h : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hh : 0 ≤ h) : 0 < p.eval t h := by
  simp only [StripPoly.positive, Bool.and_eq_true, decide_eq_true_eq] at hp
  have base (i : Fin 4) : 0 < (p.base i : ℝ) := by exact_mod_cast hp.1 i
  have slope (i : Fin 2) : 0 ≤ (p.slope i : ℝ) := by exact_mod_cast hp.2 i
  have hs : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  have hl : 0 ≤ evalLinear p.slope t := by
    unfold evalLinear
    have := slope 0
    have := slope 1
    positivity
  apply add_pos_of_pos_of_nonneg _ (mul_nonneg hl hh)
  unfold evalCubic
  have := base 0
  have := base 1
  have := base 2
  have := base 3
  by_cases he : t = 1
  · simpa [he] using base 3
  · have hlt : 0 < 1 - t := by linarith [lt_of_le_of_ne ht₁ he]
    positivity

private def StripPoly.sign (p : StripPoly) : ℤ :=
  if p.positive then 1 else if (p.scale (-1)).positive then -1 else 0

private theorem StripPoly.sign_pos {p : StripPoly} (hp : 0 < p.sign) {t h : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hh : 0 ≤ h) : 0 < p.eval t h := by
  unfold StripPoly.sign at hp
  split at hp
  · exact positive_sound ‹_› ht₀ ht₁ hh
  · split at hp <;> omega

private theorem StripPoly.sign_neg {p : StripPoly} (hp : p.sign < 0) {t h : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hh : 0 ≤ h) : p.eval t h < 0 := by
  unfold StripPoly.sign at hp
  split at hp
  · omega
  · split at hp
    · have hn := positive_sound ‹(p.scale (-1)).positive = true› ht₀ ht₁ hh
      simpa [StripPoly.eval_scale] using hn
    · omega

private theorem StripPoly.sign_mul_pos {p q : StripPoly} (hp : 0 < p.sign * q.sign) {t h : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hh : 0 ≤ h) : 0 < p.eval t h * q.eval t h := by
  rcases mul_pos_iff.mp hp with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact mul_pos (p.sign_pos hp ht₀ ht₁ hh) (q.sign_pos hq ht₀ ht₁ hh)
  · exact mul_pos_of_neg_of_neg (p.sign_neg hp ht₀ ht₁ hh) (q.sign_neg hq ht₀ ht₁ hh)

private theorem StripPoly.sign_mul_neg {p q : StripPoly} (hp : p.sign * q.sign < 0) {t h : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hh : 0 ≤ h) : p.eval t h * q.eval t h < 0 := by
  rcases mul_neg_iff.mp hp with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact mul_neg_of_pos_of_neg (p.sign_pos hp ht₀ ht₁ hh) (q.sign_neg hq ht₀ ht₁ hh)
  · exact mul_neg_of_neg_of_pos (p.sign_neg hp ht₀ ht₁ hh) (q.sign_pos hq ht₀ ht₁ hh)

private theorem lift_cast (second : Bool) (v : Vertex) :
    ((lift second v : ℚ) : ℝ) = lift second v := by
  cases second <;> fin_cases v <;> norm_num [lift]

private theorem direction_cast (second : Bool) (v : Vertex) :
    ((generalPositionDirection second v : ℚ) : ℝ) = generalPositionDirection second v := by
  cases second <;> fin_cases v <;> norm_num [generalPositionDirection]

private def sepCheck (second : Bool) (z : Vertex → ℚ) (pair : Edge × Triangle) : Bool :=
  let ((a,b),(c,d,e)) := pair
  let v := fun a b c d => (volumeCoeffs second z a b c d).sign
  @decide (separates (v b c d e) (v a c d e) (v a b d e) (v a b c e) (v a b c d))
    (by unfold separates; infer_instance)

private theorem strictSeparation_of_check (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    (pairs : List (Edge × Triangle)) (z : Vertex → ℚ) (hc : pairs.all (sepCheck second z) = true) :
    ∀ pair ∈ pairs, isSeparated (stripPoint second x w) (fun v => (z v : ℝ)) pair := by
  obtain ⟨t, h, ht₀, ht₁, hh, rfl, rfl⟩ := domain_param hd
  rintro ⟨⟨a,b⟩,c,d,e⟩ hpair
  have hcheck := (List.all_eq_true.mp hc) _ hpair
  simp only [sepCheck, decide_eq_true_eq, separates] at hcheck
  have hv (a b c d : Vertex) := volume_eval second z a b c d t h
  simp only [isSeparated, separates, hv]
  rcases hcheck with hcheck | hcheck | hcheck | hcheck
  · exact Or.inl (StripPoly.sign_mul_pos hcheck ht₀ ht₁ hh)
  · exact Or.inr (Or.inl (StripPoly.sign_mul_pos hcheck ht₀ ht₁ hh))
  · exact Or.inr (Or.inr (Or.inl (StripPoly.sign_mul_pos hcheck ht₀ ht₁ hh)))
  · exact Or.inr (Or.inr (Or.inr (StripPoly.sign_mul_neg hcheck ht₀ ht₁ hh)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sepListCheck (second : Bool) : type6DisjointPairs.all (sepCheck second (lift second)) = true := by
  cases second <;> decide +kernel

theorem type6_strictSeparation (second : Bool) (x w : ℝ) (hd : chartDomain second x w) :
    ∀ pair ∈ type6DisjointPairs, isSeparated (stripPoint second x w) (lift second) pair := by
  simpa only [lift_cast] using
    strictSeparation_of_check second x w hd _ (lift second) (sepListCheck second)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem type3_sepListCheck (second : Bool) :
    Type3.disjointPairs.all (sepCheck second (generalPositionDirection second)) = true := by
  cases second <;> decide +kernel

/-- The published heights separate the 138 disjoint edge–face pairs of Type 3. -/
theorem type3_strictSeparation (second : Bool) (x w : ℝ) (hd : chartDomain second x w) :
    ∀ pair ∈ Type3.disjointPairs,
      isSeparated (stripPoint second x w) (generalPositionDirection second) pair := by
  simpa only [direction_cast] using
    strictSeparation_of_check second x w hd _ (generalPositionDirection second) (type3_sepListCheck second)

private def tetrahedra : List Tetrahedron :=
  (List.finRange 8).flatMap fun a =>
    (List.finRange 8).flatMap fun b =>
      (List.finRange 8).flatMap fun c =>
        ((List.finRange 8).filter fun d => decide (a < b ∧ b < c ∧ c < d)).map (a,b,c,·)

private theorem mem_tetrahedra {a b c d : Vertex} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    (a,b,c,d) ∈ tetrahedra := by
  simp [tetrahedra, hab, hbc, hcd]

private def directionCheck (second : Bool) (q : Tetrahedron) : Bool :=
  let (a,b,c,d) := q
  (volumeCoeffs second (generalPositionDirection second) a b c d).sign != 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem directionListCheck (second : Bool) : tetrahedra.all (directionCheck second) = true := by
  cases second <;> decide +kernel

theorem type6_nonzeroDirection (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    (a b c d : Vertex) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    volume (stripPoint second x w) (generalPositionDirection second) a b c d ≠ 0 := by
  obtain ⟨t, h, ht₀, ht₁, hh, rfl, rfl⟩ := domain_param hd
  have hcheck := (List.all_eq_true.mp (directionListCheck second)) _ (mem_tetrahedra hab hbc hcd)
  change ((volumeCoeffs second (generalPositionDirection second) a b c d).sign != 0) = true at hcheck
  have hcheck := bne_iff_ne.mp hcheck
  have hv := volume_eval second (generalPositionDirection second) a b c d t h
  simp only [direction_cast] at hv
  rw [hv]
  rcases lt_or_gt_of_ne hcheck with hn | hp
  · exact ne_of_lt (StripPoly.sign_neg hn ht₀ ht₁ hh)
  · exact ne_of_gt (StripPoly.sign_pos hp ht₀ ht₁ hh)

private theorem convexityCheck (second : Bool) :
    0 < (areaCoeffs second 1 2 0).sign ∧ (areaCoeffs second 1 2 5).sign < 0 ∧
    (areaCoeffs second 0 5 1).sign < 0 ∧ 0 < (areaCoeffs second 0 5 2).sign := by
  cases second <;> decide +kernel

theorem type6_flipSigns (second : Bool) (x w : ℝ) (hd : chartDomain second x w) :
    let p := stripPoint second x w
    0 < area p 1 2 0 ∧ area p 1 2 5 < 0 ∧ area p 0 5 1 < 0 ∧ 0 < area p 0 5 2 := by
  obtain ⟨t, h, ht₀, ht₁, hh, rfl, rfl⟩ := domain_param hd
  obtain ⟨ha, hb, hc, hd⟩ := convexityCheck second
  simp only [area_eval]
  exact ⟨StripPoly.sign_pos ha ht₀ ht₁ hh, StripPoly.sign_neg hb ht₀ ht₁ hh,
    StripPoly.sign_neg hc ht₀ ht₁ hh, StripPoly.sign_pos hd ht₀ ht₁ hh⟩

end OrigamiTorus
