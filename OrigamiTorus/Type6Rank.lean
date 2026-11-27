module

public import OrigamiTorus.Type6Metric
import Mathlib.Tactic

/-!
Invertibility of the fixed-period squared-edge-length Jacobian.

The two proofs use fraction-free elimination. Each row update is an explicit
linear combination, with every cancelled scalar proved nonzero on its strip.
-/

namespace OrigamiTorus

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 0 in
private theorem injective_false (x h : ℝ) (hl : 0 ≤ x)
    (hu : x ≤ (1 / 6)) (hh : 0 ≤ h) (m : Fin 24 → ℝ)
    (he : ∀ e, edgeDerivative false x (1 - x^2 + h) m e = 0) : m = 0 := by
  have hx : 0 ≤ x := by linarith only [hl]
  have hsq : x^2 ≤ (1 / 36) := by nlinarith only [hu, mul_nonneg (sub_nonneg.mpr hu) (add_nonneg hx (by norm_num : (0 : ℝ) ≤ (1 / 6)))]
  have f0 : (173472 * x + 63232 * h + 26119) ≠ 0 := ne_of_gt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f1 : (640 * x - 1024 * h - 819) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f2 : (128 * x + 41) ≠ 0 := ne_of_gt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f3 : (128 * x - 23) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f4 : (x^2 - h - 1) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f5 : (53376 * x + 19456 * h + 22329) ≠ 0 := ne_of_gt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f6 : (2080 * x - 3328 * h - 3389) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f7 : (16 * x - 5) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f8 : (208 * x - 417) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f9 : (2080 * x - 3328 * h - 9021) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f10 : (173152 * x - 198400 * h - 233135) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f11 : (416 * x - 89) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have e0 : (624 * x^2 - 624 * h - 624) * m 0 + (624 * x - 1251) * m 1 + (-624 * x^2 + 624 * h + 624) * m 2 + (-624 * x + 1251) * m 3 + (-624 * x^2 + 624 * h + 624) * m 13 + (-624 * x + 1251) * m 14 + (624 * x^2 - 624 * h - 624) * m 15 + (624 * x - 1251) * m 16 = 0 := by
    have he' := he 0
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 26624)) * ((624 * x^2 - 624 * h - 624) * m 0 + (624 * x - 1251) * m 1 + (-624 * x^2 + 624 * h + 624) * m 2 + (-624 * x + 1251) * m 3 + (-624 * x^2 + 624 * h + 624) * m 13 + (-624 * x + 1251) * m 14 + (624 * x^2 - 624 * h - 624) * m 15 + (624 * x - 1251) * m 16) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 26624) : ℝ) ≠ 0)
  have e1 : (-61 * x^2 + 61 * h + 61) * m 0 + (-61 * x) * m 1 + (61 * x^2 - 61 * h - 61) * m 4 + (61 * x) * m 5 + (61 * x^2 - 61 * h - 61) * m 13 + (61 * x) * m 14 + (-61 * x^2 + 61 * h + 61) * m 17 + (-61 * x) * m 18 = 0 := by
    have he' := he 1
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 128)) * ((-61 * x^2 + 61 * h + 61) * m 0 + (-61 * x) * m 1 + (61 * x^2 - 61 * h - 61) * m 4 + (61 * x) * m 5 + (61 * x^2 - 61 * h - 61) * m 13 + (61 * x) * m 14 + (-61 * x^2 + 61 * h + 61) * m 17 + (-61 * x) * m 18) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 128) : ℝ) ≠ 0)
  have e2 : (6656 * x^3 - 7712 * x^2 - 6656 * x * h - 6656 * x + 7712 * h + 7712) * m 0 + (6656 * x^2 - 7712 * x - 3328 * h - 1243) * m 1 + (-6656 * x^3 + 7712 * x^2 + 6656 * x * h + 6656 * x - 7712 * h - 7712) * m 6 + (-6656 * x^2 + 7712 * x + 3328 * h + 1243) * m 7 + (-5632 * x^2 + 5632 * h + 5632) * m 13 + (7712 * x - 3328 * h - 5413) * m 14 + (5632 * x^2 - 5632 * h - 5632) * m 19 + (-7712 * x + 3328 * h + 5413) * m 20 = 0 := by
    have he' := he 2
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((6656 * x^3 - 7712 * x^2 - 6656 * x * h - 6656 * x + 7712 * h + 7712) * m 0 + (6656 * x^2 - 7712 * x - 3328 * h - 1243) * m 1 + (-6656 * x^3 + 7712 * x^2 + 6656 * x * h + 6656 * x - 7712 * h - 7712) * m 6 + (-6656 * x^2 + 7712 * x + 3328 * h + 1243) * m 7 + (-5632 * x^2 + 5632 * h + 5632) * m 13 + (7712 * x - 3328 * h - 5413) * m 14 + (5632 * x^2 - 5632 * h - 5632) * m 19 + (-7712 * x + 3328 * h + 5413) * m 20) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e3 : (32 * x^3 - 5 * x^2 - 32 * x * h - 32 * x + 5 * h + 5) * m 0 + (32 * x^2 - 5 * x - 16 * h - 16) * m 1 + (-32 * x^3 + 5 * x^2 + 32 * x * h + 32 * x - 5 * h - 5) * m 8 + (-32 * x^2 + 5 * x + 16 * h + 16) * m 9 + (5 * x^2 - 5 * h - 5) * m 13 + (5 * x - 16 * h - 16) * m 14 + (-5 * x^2 + 5 * h + 5) * m 21 = 0 := by
    have he' := he 3
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 32)) * ((32 * x^3 - 5 * x^2 - 32 * x * h - 32 * x + 5 * h + 5) * m 0 + (32 * x^2 - 5 * x - 16 * h - 16) * m 1 + (-32 * x^3 + 5 * x^2 + 32 * x * h + 32 * x - 5 * h - 5) * m 8 + (-32 * x^2 + 5 * x + 16 * h + 16) * m 9 + (5 * x^2 - 5 * h - 5) * m 13 + (5 * x - 16 * h - 16) * m 14 + (-5 * x^2 + 5 * h + 5) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 32) : ℝ) ≠ 0)
  have e4 : (-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (976 * x^2 - 976 * h - 976) * m 10 + (336 * x + 1024 * h + 819) * m 11 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14 + (-976 * x^2 + 976 * h + 976) * m 22 + (-336 * x - 1024 * h - 819) * m 23 = 0 := by
    have he' := he 4
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 2048)) * ((-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (976 * x^2 - 976 * h - 976) * m 10 + (336 * x + 1024 * h + 819) * m 11 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14 + (-976 * x^2 + 976 * h + 976) * m 22 + (-336 * x - 1024 * h - 819) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 2048) : ℝ) ≠ 0)
  have e5 : (86528 * x^3 - 105248 * x^2 - 86528 * x * h - 86528 * x + 105248 * h + 105248) * m 2 + (86528 * x^2 - 105248 * x - 43264 * h - 6151) * m 3 + (-86528 * x^3 + 105248 * x^2 + 86528 * x * h + 86528 * x - 105248 * h - 105248) * m 6 + (-86528 * x^2 + 105248 * x + 43264 * h + 6151) * m 7 + (-68224 * x^2 + 68224 * h + 68224) * m 15 + (105248 * x - 43264 * h - 80377) * m 16 + (68224 * x^2 - 68224 * h - 68224) * m 19 + (-105248 * x + 43264 * h + 80377) * m 20 = 0 := by
    have he' := he 5
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 212992)) * ((86528 * x^3 - 105248 * x^2 - 86528 * x * h - 86528 * x + 105248 * h + 105248) * m 2 + (86528 * x^2 - 105248 * x - 43264 * h - 6151) * m 3 + (-86528 * x^3 + 105248 * x^2 + 86528 * x * h + 86528 * x - 105248 * h - 105248) * m 6 + (-86528 * x^2 + 105248 * x + 43264 * h + 6151) * m 7 + (-68224 * x^2 + 68224 * h + 68224) * m 15 + (105248 * x - 43264 * h - 80377) * m 16 + (68224 * x^2 - 68224 * h - 68224) * m 19 + (-105248 * x + 43264 * h + 80377) * m 20) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 212992) : ℝ) ≠ 0)
  have e6 : (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 2 + (26624 * x^2 - 4784 * x - 13312 * h - 12061) * m 3 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 8 + (-26624 * x^2 + 4784 * x + 13312 * h + 12061) * m 9 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 15 + (-26624 * x^2 + 4784 * x + 13312 * h + 12061) * m 16 + (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 21 = 0 := by
    have he' := he 6
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 26624)) * ((26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 2 + (26624 * x^2 - 4784 * x - 13312 * h - 12061) * m 3 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 8 + (-26624 * x^2 + 4784 * x + 13312 * h + 12061) * m 9 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 15 + (-26624 * x^2 + 4784 * x + 13312 * h + 12061) * m 16 + (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 26624) : ℝ) ≠ 0)
  have e7 : (-3328 * x^2 + 3328 * h + 3328) * m 2 + (-1248 * x - 3328 * h - 2349) * m 3 + (3328 * x^2 - 3328 * h - 3328) * m 10 + (1248 * x + 3328 * h + 2349) * m 11 + (3328 * x^2 - 3328 * h - 3328) * m 15 + (1248 * x + 3328 * h + 2349) * m 16 + (-3328 * x^2 + 3328 * h + 3328) * m 22 + (-1248 * x - 3328 * h - 2349) * m 23 = 0 := by
    have he' := he 7
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 6656)) * ((-3328 * x^2 + 3328 * h + 3328) * m 2 + (-1248 * x - 3328 * h - 2349) * m 3 + (3328 * x^2 - 3328 * h - 3328) * m 10 + (1248 * x + 3328 * h + 2349) * m 11 + (3328 * x^2 - 3328 * h - 3328) * m 15 + (1248 * x + 3328 * h + 2349) * m 16 + (-3328 * x^2 + 3328 * h + 3328) * m 22 + (-1248 * x - 3328 * h - 2349) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 6656) : ℝ) ≠ 0)
  have e8 : (-2288 * x^2 + 2288 * h + 2288) * m 2 + (-2288 * x + 979) * m 3 + (2288 * x^2 - 2288 * h - 2288) * m 12 + (-2288 * x^2 + 2288 * h + 2288) * m 15 + (2288 * x - 979) * m 16 = 0 := by
    have he' := he 8
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 6656)) * ((-2288 * x^2 + 2288 * h + 2288) * m 2 + (-2288 * x + 979) * m 3 + (2288 * x^2 - 2288 * h - 2288) * m 12 + (-2288 * x^2 + 2288 * h + 2288) * m 15 + (2288 * x - 979) * m 16) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 6656) : ℝ) ≠ 0)
  have e9 : (-417) * m 3 + (417) * m 16 = 0 := by
    have he' := he 9
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 52735488) * (173472 * x + 63232 * h + 26119)) * ((-417) * m 3 + (417) * m 16) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : ((1 / 52735488) : ℝ) ≠ 0) f0)
  have e10 : (128 * x^3 + 41 * x^2 - 128 * x * h - 128 * x - 41 * h - 41) * m 4 + (128 * x^2 + 41 * x - 64 * h - 64) * m 5 + (-128 * x^3 - 41 * x^2 + 128 * x * h + 128 * x + 41 * h + 41) * m 8 + (-128 * x^2 - 41 * x + 64 * h + 64) * m 9 + (-41 * x^2 + 41 * h + 41) * m 17 + (-41 * x - 64 * h - 64) * m 18 + (41 * x^2 - 41 * h - 41) * m 21 = 0 := by
    have he' := he 10
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 128)) * ((128 * x^3 + 41 * x^2 - 128 * x * h - 128 * x - 41 * h - 41) * m 4 + (128 * x^2 + 41 * x - 64 * h - 64) * m 5 + (-128 * x^3 - 41 * x^2 + 128 * x * h + 128 * x + 41 * h + 41) * m 8 + (-128 * x^2 - 41 * x + 64 * h + 64) * m 9 + (-41 * x^2 + 41 * h + 41) * m 17 + (-41 * x - 64 * h - 64) * m 18 + (41 * x^2 - 41 * h - 41) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 128) : ℝ) ≠ 0)
  have e11 : (5) * m 5 + (-5) * m 11 + (-5) * m 18 + (5) * m 23 = 0 := by
    have he' := he 11
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 10240) * (640 * x - 1024 * h - 819)) * ((5) * m 5 + (-5) * m 11 + (-5) * m 18 + (5) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : ((1 / 10240) : ℝ) ≠ 0) f1)
  have e12 : (320 * x^2 - 320 * h - 320) * m 4 + (320 * x + 205) * m 5 + (-320 * x^2 + 320 * h + 320) * m 12 + (320 * x^2 - 320 * h - 320) * m 17 + (-320 * x - 205) * m 18 = 0 := by
    have he' := he 12
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 2048)) * ((320 * x^2 - 320 * h - 320) * m 4 + (320 * x + 205) * m 5 + (-320 * x^2 + 320 * h + 320) * m 12 + (320 * x^2 - 320 * h - 320) * m 17 + (-320 * x - 205) * m 18) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 2048) : ℝ) ≠ 0)
  have e13 : (19456 * x^2 - 19456 * h - 19456) * m 4 + (-33920 * x - 19456 * h - 9865) * m 5 + (19456 * x^2 - 19456 * h - 19456) * m 17 + (33920 * x + 19456 * h + 9865) * m 18 = 0 := by
    have he' := he 13
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 38912)) * ((19456 * x^2 - 19456 * h - 19456) * m 4 + (-33920 * x - 19456 * h - 9865) * m 5 + (19456 * x^2 - 19456 * h - 19456) * m 17 + (33920 * x + 19456 * h + 9865) * m 18) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 38912) : ℝ) ≠ 0)
  have e14 : (9728 * x^3 + 5152 * x^2 - 9728 * x * h - 9728 * x - 5152 * h - 5152) * m 6 + (9728 * x^2 + 5152 * x - 4864 * h - 6949) * m 7 + (-9728 * x^3 - 5152 * x^2 + 9728 * x * h + 9728 * x + 5152 * h + 5152) * m 8 + (-9728 * x^2 - 5152 * x + 4864 * h + 6949) * m 9 + (8192 * x^2 - 8192 * h - 8192) * m 19 + (-5152 * x - 4864 * h - 2779) * m 20 + (-8192 * x^2 + 8192 * h + 8192) * m 21 = 0 := by
    have he' := he 14
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((9728 * x^3 + 5152 * x^2 - 9728 * x * h - 9728 * x - 5152 * h - 5152) * m 6 + (9728 * x^2 + 5152 * x - 4864 * h - 6949) * m 7 + (-9728 * x^3 - 5152 * x^2 + 9728 * x * h + 9728 * x + 5152 * h + 5152) * m 8 + (-9728 * x^2 - 5152 * x + 4864 * h + 6949) * m 9 + (8192 * x^2 - 8192 * h - 8192) * m 19 + (-5152 * x - 4864 * h - 2779) * m 20 + (-8192 * x^2 + 8192 * h + 8192) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e15 : (-6656 * x^3 - 96 * x^2 + 6656 * x * h + 6656 * x + 96 * h + 96) * m 6 + (-6656 * x^2 + 5024 * x - 4864 * h - 5309) * m 7 + (6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 10 + (6656 * x^2 - 5024 * x + 4864 * h + 5309) * m 11 + (16384 * x^3 - 2944 * x^2 - 16384 * x * h - 16384 * x + 2944 * h + 2944) * m 19 + (16384 * x^2 - 5024 * x - 4864 * h - 4419) * m 20 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 22 + (-16384 * x^2 + 5024 * x + 4864 * h + 4419) * m 23 = 0 := by
    have he' := he 15
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((-6656 * x^3 - 96 * x^2 + 6656 * x * h + 6656 * x + 96 * h + 96) * m 6 + (-6656 * x^2 + 5024 * x - 4864 * h - 5309) * m 7 + (6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 10 + (6656 * x^2 - 5024 * x + 4864 * h + 5309) * m 11 + (16384 * x^3 - 2944 * x^2 - 16384 * x * h - 16384 * x + 2944 * h + 2944) * m 19 + (16384 * x^2 - 5024 * x - 4864 * h - 4419) * m 20 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 22 + (-16384 * x^2 + 5024 * x + 4864 * h + 4419) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e16 : (-6656 * x^3 + 2464 * x^2 + 6656 * x * h + 6656 * x - 2464 * h - 2464) * m 6 + (-6656 * x^2 + 2464 * x + 3328 * h + 2883) * m 7 + (6656 * x^3 - 2464 * x^2 - 6656 * x * h - 6656 * x + 2464 * h + 2464) * m 12 + (-384 * x^2 + 384 * h + 384) * m 19 + (-2464 * x + 3328 * h + 3773) * m 20 = 0 := by
    have he' := he 16
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((-6656 * x^3 + 2464 * x^2 + 6656 * x * h + 6656 * x - 2464 * h - 2464) * m 6 + (-6656 * x^2 + 2464 * x + 3328 * h + 2883) * m 7 + (6656 * x^3 - 2464 * x^2 - 6656 * x * h - 6656 * x + 2464 * h + 2464) * m 12 + (-384 * x^2 + 384 * h + 384) * m 19 + (-2464 * x + 3328 * h + 3773) * m 20) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e17 : (-126464 * x^3 + 153824 * x^2 + 126464 * x * h + 126464 * x - 153824 * h - 153824) * m 6 + (-126464 * x^2 - 273184 * x - 92416 * h - 55303) * m 7 + (311296 * x^3 + 99712 * x^2 - 311296 * x * h - 311296 * x - 99712 * h - 99712) * m 19 + (311296 * x^2 + 273184 * x - 92416 * h - 129529) * m 20 = 0 := by
    have he' := he 17
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 311296)) * ((-126464 * x^3 + 153824 * x^2 + 126464 * x * h + 126464 * x - 153824 * h - 153824) * m 6 + (-126464 * x^2 - 273184 * x - 92416 * h - 55303) * m 7 + (311296 * x^3 + 99712 * x^2 - 311296 * x * h - 311296 * x - 99712 * h - 99712) * m 19 + (311296 * x^2 + 273184 * x - 92416 * h - 129529) * m 20) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 311296) : ℝ) ≠ 0)
  have e18 : (-16 * x^2 + 16 * h + 16) * m 8 + (-16 * x + 5) * m 9 + (16 * x^2 - 16 * h - 16) * m 10 + (16 * x - 5) * m 11 + (16 * x^2 - 16 * h - 16) * m 21 + (-16 * x^2 + 16 * h + 16) * m 22 + (-16 * x + 5) * m 23 = 0 := by
    have he' := he 18
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 2048) * (128 * x + 41)) * ((-16 * x^2 + 16 * h + 16) * m 8 + (-16 * x + 5) * m 9 + (16 * x^2 - 16 * h - 16) * m 10 + (16 * x - 5) * m 11 + (16 * x^2 - 16 * h - 16) * m 21 + (-16 * x^2 + 16 * h + 16) * m 22 + (-16 * x + 5) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : ((1 / 2048) : ℝ) ≠ 0) f2)
  have e19 : (-2048 * x^3 - 336 * x^2 + 2048 * x * h + 2048 * x + 336 * h + 336) * m 8 + (-2048 * x^2 - 336 * x + 1024 * h + 1229) * m 9 + (2048 * x^3 + 336 * x^2 - 2048 * x * h - 2048 * x - 336 * h - 336) * m 12 + (976 * x^2 - 976 * h - 976) * m 21 = 0 := by
    have he' := he 19
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 2048)) * ((-2048 * x^3 - 336 * x^2 + 2048 * x * h + 2048 * x + 336 * h + 336) * m 8 + (-2048 * x^2 - 336 * x + 1024 * h + 1229) * m 9 + (2048 * x^3 + 336 * x^2 - 2048 * x * h - 2048 * x - 336 * h - 336) * m 12 + (976 * x^2 - 976 * h - 976) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 2048) : ℝ) ≠ 0)
  have e20 : (-304 * x^2 + 304 * h + 304) * m 8 + (-304 * x - 417) * m 9 + (304 * x^2 - 304 * h - 304) * m 21 = 0 := by
    have he' := he 20
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 38912) * (128 * x - 23)) * ((-304 * x^2 + 304 * h + 304) * m 8 + (-304 * x - 417) * m 9 + (304 * x^2 - 304 * h - 304) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : ((1 / 38912) : ℝ) ≠ 0) f3)
  have e21 : (5 * x^2 - 5 * h - 5) * m 10 + (-5 * x + 16 * h + 16) * m 11 + (-5 * x^2 + 5 * h + 5) * m 12 + (-32 * x^3 + 5 * x^2 + 32 * x * h + 32 * x - 5 * h - 5) * m 22 + (-32 * x^2 + 5 * x + 16 * h + 16) * m 23 = 0 := by
    have he' := he 21
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 32)) * ((5 * x^2 - 5 * h - 5) * m 10 + (-5 * x + 16 * h + 16) * m 11 + (-5 * x^2 + 5 * h + 5) * m 12 + (-32 * x^3 + 5 * x^2 + 32 * x * h + 32 * x - 5 * h - 5) * m 22 + (-32 * x^2 + 5 * x + 16 * h + 16) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 32) : ℝ) ≠ 0)
  have e22 : (304 * x^2 - 304 * h - 304) * m 10 + (-720 * x + 89) * m 11 + (304 * x^2 - 304 * h - 304) * m 22 + (720 * x - 89) * m 23 = 0 := by
    have he' := he 22
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 608)) * ((304 * x^2 - 304 * h - 304) * m 10 + (-720 * x + 89) * m 11 + (304 * x^2 - 304 * h - 304) * m 22 + (720 * x - 89) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 608) : ℝ) ≠ 0)
  have e23 : (1) * m 12 = 0 := by
    have he' := he 23
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    simpa using he'.resolve_left (fun hz => f4 (by linarith only [hz]))
  have e8_0 : (-208 * x^2 + 208 * h + 208) * m 2 + (-208 * x + 89) * m 3 + (-208 * x^2 + 208 * h + 208) * m 15 + (208 * x - 89) * m 16 = 0 := by
    have hc : (11) * ((-208 * x^2 + 208 * h + 208) * m 2 + (-208 * x + 89) * m 3 + (-208 * x^2 + 208 * h + 208) * m 15 + (208 * x - 89) * m 16) = 0 := by
      linear_combination (1) * e8 - (2288 * x^2 - 2288 * h - 2288) * e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (11 : ℝ) ≠ 0)
  have e12_0 : (64 * x^2 - 64 * h - 64) * m 4 + (64 * x + 41) * m 5 + (64 * x^2 - 64 * h - 64) * m 17 + (-64 * x - 41) * m 18 = 0 := by
    have hc : (5) * ((64 * x^2 - 64 * h - 64) * m 4 + (64 * x + 41) * m 5 + (64 * x^2 - 64 * h - 64) * m 17 + (-64 * x - 41) * m 18) = 0 := by
      linear_combination (1) * e12 - (-320 * x^2 + 320 * h + 320) * e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (5 : ℝ) ≠ 0)
  have e16_0 : (-6656 * x^3 + 2464 * x^2 + 6656 * x * h + 6656 * x - 2464 * h - 2464) * m 6 + (-6656 * x^2 + 2464 * x + 3328 * h + 2883) * m 7 + (-384 * x^2 + 384 * h + 384) * m 19 + (-2464 * x + 3328 * h + 3773) * m 20 = 0 := by
    have hc : (1) * ((-6656 * x^3 + 2464 * x^2 + 6656 * x * h + 6656 * x - 2464 * h - 2464) * m 6 + (-6656 * x^2 + 2464 * x + 3328 * h + 2883) * m 7 + (-384 * x^2 + 384 * h + 384) * m 19 + (-2464 * x + 3328 * h + 3773) * m 20) = 0 := by
      linear_combination (1) * e16 - (6656 * x^3 - 2464 * x^2 - 6656 * x * h - 6656 * x + 2464 * h + 2464) * e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e19_0 : (-2048 * x^3 - 336 * x^2 + 2048 * x * h + 2048 * x + 336 * h + 336) * m 8 + (-2048 * x^2 - 336 * x + 1024 * h + 1229) * m 9 + (976 * x^2 - 976 * h - 976) * m 21 = 0 := by
    have hc : (1) * ((-2048 * x^3 - 336 * x^2 + 2048 * x * h + 2048 * x + 336 * h + 336) * m 8 + (-2048 * x^2 - 336 * x + 1024 * h + 1229) * m 9 + (976 * x^2 - 976 * h - 976) * m 21) = 0 := by
      linear_combination (1) * e19 - (2048 * x^3 + 336 * x^2 - 2048 * x * h - 2048 * x - 336 * h - 336) * e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e21_0 : (5 * x^2 - 5 * h - 5) * m 10 + (-5 * x + 16 * h + 16) * m 11 + (-32 * x^3 + 5 * x^2 + 32 * x * h + 32 * x - 5 * h - 5) * m 22 + (-32 * x^2 + 5 * x + 16 * h + 16) * m 23 = 0 := by
    have hc : (1) * ((5 * x^2 - 5 * h - 5) * m 10 + (-5 * x + 16 * h + 16) * m 11 + (-32 * x^3 + 5 * x^2 + 32 * x * h + 32 * x - 5 * h - 5) * m 22 + (-32 * x^2 + 5 * x + 16 * h + 16) * m 23) = 0 := by
      linear_combination (1) * e21 - (-5 * x^2 + 5 * h + 5) * e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e0_1 : (208 * x^2 - 208 * h - 208) * m 0 + (208 * x - 417) * m 1 + (-208 * x^2 + 208 * h + 208) * m 2 + (-208 * x^2 + 208 * h + 208) * m 13 + (-208 * x + 417) * m 14 + (208 * x^2 - 208 * h - 208) * m 15 = 0 := by
    have hc : (1251) * ((208 * x^2 - 208 * h - 208) * m 0 + (208 * x - 417) * m 1 + (-208 * x^2 + 208 * h + 208) * m 2 + (-208 * x^2 + 208 * h + 208) * m 13 + (-208 * x + 417) * m 14 + (208 * x^2 - 208 * h - 208) * m 15) = 0 := by
      linear_combination (417) * e0 - (624 * x - 1251) * e9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1251 : ℝ) ≠ 0)
  have e5_1 : (86528 * x^3 - 105248 * x^2 - 86528 * x * h - 86528 * x + 105248 * h + 105248) * m 2 + (86528 * x^2 - 86528 * h - 86528) * m 3 + (-86528 * x^3 + 105248 * x^2 + 86528 * x * h + 86528 * x - 105248 * h - 105248) * m 6 + (-86528 * x^2 + 105248 * x + 43264 * h + 6151) * m 7 + (-68224 * x^2 + 68224 * h + 68224) * m 15 + (68224 * x^2 - 68224 * h - 68224) * m 19 + (-105248 * x + 43264 * h + 80377) * m 20 = 0 := by
    have hc : (417) * ((86528 * x^3 - 105248 * x^2 - 86528 * x * h - 86528 * x + 105248 * h + 105248) * m 2 + (86528 * x^2 - 86528 * h - 86528) * m 3 + (-86528 * x^3 + 105248 * x^2 + 86528 * x * h + 86528 * x - 105248 * h - 105248) * m 6 + (-86528 * x^2 + 105248 * x + 43264 * h + 6151) * m 7 + (-68224 * x^2 + 68224 * h + 68224) * m 15 + (68224 * x^2 - 68224 * h - 68224) * m 19 + (-105248 * x + 43264 * h + 80377) * m 20) = 0 := by
      linear_combination (417) * e5 - (105248 * x - 43264 * h - 80377) * e9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (417 : ℝ) ≠ 0)
  have e6_1 : (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 2 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 8 + (-26624 * x^2 + 4784 * x + 13312 * h + 12061) * m 9 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 15 + (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 21 = 0 := by
    have hc : (417) * ((26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 2 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 8 + (-26624 * x^2 + 4784 * x + 13312 * h + 12061) * m 9 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 15 + (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 21) = 0 := by
      linear_combination (417) * e6 - (-26624 * x^2 + 4784 * x + 13312 * h + 12061) * e9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (417 : ℝ) ≠ 0)
  have e7_1 : (-3328 * x^2 + 3328 * h + 3328) * m 2 + (3328 * x^2 - 3328 * h - 3328) * m 10 + (1248 * x + 3328 * h + 2349) * m 11 + (3328 * x^2 - 3328 * h - 3328) * m 15 + (-3328 * x^2 + 3328 * h + 3328) * m 22 + (-1248 * x - 3328 * h - 2349) * m 23 = 0 := by
    have hc : (417) * ((-3328 * x^2 + 3328 * h + 3328) * m 2 + (3328 * x^2 - 3328 * h - 3328) * m 10 + (1248 * x + 3328 * h + 2349) * m 11 + (3328 * x^2 - 3328 * h - 3328) * m 15 + (-3328 * x^2 + 3328 * h + 3328) * m 22 + (-1248 * x - 3328 * h - 2349) * m 23) = 0 := by
      linear_combination (417) * e7 - (1248 * x + 3328 * h + 2349) * e9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (417 : ℝ) ≠ 0)
  have e8_1 : (-1) * m 2 + (-1) * m 15 = 0 := by
    have hc : (86736 * (x^2 - h - 1)) * ((-1) * m 2 + (-1) * m 15) = 0 := by
      linear_combination (417) * e8_0 - (208 * x - 89) * e9
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (86736 : ℝ) ≠ 0) f4)
  have e0_3 : (-208 * x^2 + 208 * h + 208) * m 0 + (-208 * x + 417) * m 1 + (208 * x^2 - 208 * h - 208) * m 13 + (208 * x - 417) * m 14 + (-416 * x^2 + 416 * h + 416) * m 15 = 0 := by
    have hc : (1) * ((-208 * x^2 + 208 * h + 208) * m 0 + (-208 * x + 417) * m 1 + (208 * x^2 - 208 * h - 208) * m 13 + (208 * x - 417) * m 14 + (-416 * x^2 + 416 * h + 416) * m 15) = 0 := by
      linear_combination (-1) * e0_1 - (-208 * x^2 + 208 * h + 208) * e8_1
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e6_3 : (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 8 + (26624 * x^2 - 4784 * x - 13312 * h - 12061) * m 9 + (53248 * x^3 - 9568 * x^2 - 53248 * x * h - 53248 * x + 9568 * h + 9568) * m 15 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 21 = 0 := by
    have hc : (1) * ((26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 8 + (26624 * x^2 - 4784 * x - 13312 * h - 12061) * m 9 + (53248 * x^3 - 9568 * x^2 - 53248 * x * h - 53248 * x + 9568 * h + 9568) * m 15 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 21) = 0 := by
      linear_combination (-1) * e6_1 - (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * e8_1
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e7_3 : (-3328 * x^2 + 3328 * h + 3328) * m 10 + (-1248 * x - 3328 * h - 2349) * m 11 + (-6656 * x^2 + 6656 * h + 6656) * m 15 + (3328 * x^2 - 3328 * h - 3328) * m 22 + (1248 * x + 3328 * h + 2349) * m 23 = 0 := by
    have hc : (1) * ((-3328 * x^2 + 3328 * h + 3328) * m 10 + (-1248 * x - 3328 * h - 2349) * m 11 + (-6656 * x^2 + 6656 * h + 6656) * m 15 + (3328 * x^2 - 3328 * h - 3328) * m 22 + (1248 * x + 3328 * h + 2349) * m 23) = 0 := by
      linear_combination (-1) * e7_1 - (-3328 * x^2 + 3328 * h + 3328) * e8_1
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e0_4 : (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 0 + (-26624 * x^2 + 58160 * x - 9591) * m 1 + (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 8 + (26624 * x^2 - 4784 * x - 13312 * h - 12061) * m 9 + (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 13 + (26624 * x^2 - 58160 * x + 9591) * m 14 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 21 = 0 := by
    have hc : (416 * (x^2 - h - 1)) * ((-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 0 + (-26624 * x^2 + 58160 * x - 9591) * m 1 + (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 8 + (26624 * x^2 - 4784 * x - 13312 * h - 12061) * m 9 + (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 13 + (26624 * x^2 - 58160 * x + 9591) * m 14 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 21) = 0 := by
      linear_combination (53248 * x^3 - 9568 * x^2 - 53248 * x * h - 53248 * x + 9568 * h + 9568) * e0_3 - (-416 * x^2 + 416 * h + 416) * e6_3
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (416 : ℝ) ≠ 0) f4)
  have e7_4 : (425984 * x^3 - 76544 * x^2 - 425984 * x * h - 425984 * x + 76544 * h + 76544) * m 8 + (425984 * x^2 - 76544 * x - 212992 * h - 192976) * m 9 + (-425984 * x^3 + 76544 * x^2 + 425984 * x * h + 425984 * x - 76544 * h - 76544) * m 10 + (-159744 * x^2 - 425984 * x * h - 271968 * x + 76544 * h + 54027) * m 11 + (-425984 * x^3 + 76544 * x^2 + 425984 * x * h + 425984 * x - 76544 * h - 76544) * m 21 + (425984 * x^3 - 76544 * x^2 - 425984 * x * h - 425984 * x + 76544 * h + 76544) * m 22 + (159744 * x^2 + 425984 * x * h + 271968 * x - 76544 * h - 54027) * m 23 = 0 := by
    have hc : (416 * (x^2 - h - 1)) * ((425984 * x^3 - 76544 * x^2 - 425984 * x * h - 425984 * x + 76544 * h + 76544) * m 8 + (425984 * x^2 - 76544 * x - 212992 * h - 192976) * m 9 + (-425984 * x^3 + 76544 * x^2 + 425984 * x * h + 425984 * x - 76544 * h - 76544) * m 10 + (-159744 * x^2 - 425984 * x * h - 271968 * x + 76544 * h + 54027) * m 11 + (-425984 * x^3 + 76544 * x^2 + 425984 * x * h + 425984 * x - 76544 * h - 76544) * m 21 + (425984 * x^3 - 76544 * x^2 - 425984 * x * h - 425984 * x + 76544 * h + 76544) * m 22 + (159744 * x^2 + 425984 * x * h + 271968 * x - 76544 * h - 54027) * m 23) = 0 := by
      linear_combination (53248 * x^3 - 9568 * x^2 - 53248 * x * h - 53248 * x + 9568 * h + 9568) * e7_3 - (-6656 * x^2 + 6656 * h + 6656) * e6_3
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (416 : ℝ) ≠ 0) f4)
  have e1_5 : (-19456 * x^2 + 19456 * h + 19456) * m 0 + (-19456 * x) * m 1 + (53376 * x + 19456 * h + 9865) * m 5 + (19456 * x^2 - 19456 * h - 19456) * m 13 + (19456 * x) * m 14 + (-38912 * x^2 + 38912 * h + 38912) * m 17 + (-53376 * x - 19456 * h - 9865) * m 18 = 0 := by
    have hc : (61 * (x^2 - h - 1)) * ((-19456 * x^2 + 19456 * h + 19456) * m 0 + (-19456 * x) * m 1 + (53376 * x + 19456 * h + 9865) * m 5 + (19456 * x^2 - 19456 * h - 19456) * m 13 + (19456 * x) * m 14 + (-38912 * x^2 + 38912 * h + 38912) * m 17 + (-53376 * x - 19456 * h - 9865) * m 18) = 0 := by
      linear_combination (19456 * x^2 - 19456 * h - 19456) * e1 - (61 * x^2 - 61 * h - 61) * e13
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (61 : ℝ) ≠ 0) f4)
  have e10_5 : (6832128 * x^2 + 2490368 * x * h + 3451136 * x - 447488 * h - 840719) * m 5 + (-2490368 * x^3 - 797696 * x^2 + 2490368 * x * h + 2490368 * x + 797696 * h + 797696) * m 8 + (-2490368 * x^2 - 797696 * x + 1245184 * h + 1245184) * m 9 + (-2490368 * x^3 - 1595392 * x^2 + 2490368 * x * h + 2490368 * x + 1595392 * h + 1595392) * m 17 + (-4341760 * x^2 - 2490368 * x * h - 3451136 * x - 2042880 * h - 1649649) * m 18 + (797696 * x^2 - 797696 * h - 797696) * m 21 = 0 := by
    have hc : ((x^2 - h - 1)) * ((6832128 * x^2 + 2490368 * x * h + 3451136 * x - 447488 * h - 840719) * m 5 + (-2490368 * x^3 - 797696 * x^2 + 2490368 * x * h + 2490368 * x + 797696 * h + 797696) * m 8 + (-2490368 * x^2 - 797696 * x + 1245184 * h + 1245184) * m 9 + (-2490368 * x^3 - 1595392 * x^2 + 2490368 * x * h + 2490368 * x + 1595392 * h + 1595392) * m 17 + (-4341760 * x^2 - 2490368 * x * h - 3451136 * x - 2042880 * h - 1649649) * m 18 + (797696 * x^2 - 797696 * h - 797696) * m 21) = 0 := by
      linear_combination (19456 * x^2 - 19456 * h - 19456) * e10 - (128 * x^3 + 41 * x^2 - 128 * x * h - 128 * x - 41 * h - 41) * e13
    exact (mul_eq_zero.mp hc).resolve_left f4
  have e12_5 : (-1) * m 5 + (1) * m 18 = 0 := by
    have hc : (-64 * (53376 * x + 19456 * h + 22329) * (x^2 - h - 1)) * ((-1) * m 5 + (1) * m 18) = 0 := by
      linear_combination (19456 * x^2 - 19456 * h - 19456) * e12_0 - (64 * x^2 - 64 * h - 64) * e13
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (-64 : ℝ) ≠ 0) f5) f4)
  have e1_6 : (x^2 - h - 1) * m 0 + (x) * m 1 + (-x^2 + h + 1) * m 13 + (-x) * m 14 + (2 * x^2 - 2 * h - 2) * m 17 = 0 := by
    have hc : (19456) * ((x^2 - h - 1) * m 0 + (x) * m 1 + (-x^2 + h + 1) * m 13 + (-x) * m 14 + (2 * x^2 - 2 * h - 2) * m 17) = 0 := by
      linear_combination (-1) * e1_5 - (53376 * x + 19456 * h + 9865) * e12_5
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (19456 : ℝ) ≠ 0)
  have e10_6 : (128 * x^3 + 41 * x^2 - 128 * x * h - 128 * x - 41 * h - 41) * m 8 + (128 * x^2 + 41 * x - 64 * h - 64) * m 9 + (128 * x^3 + 82 * x^2 - 128 * x * h - 128 * x - 82 * h - 82) * m 17 + (-128 * x^2 + 128 * h + 128) * m 18 + (-41 * x^2 + 41 * h + 41) * m 21 = 0 := by
    have hc : (19456) * ((128 * x^3 + 41 * x^2 - 128 * x * h - 128 * x - 41 * h - 41) * m 8 + (128 * x^2 + 41 * x - 64 * h - 64) * m 9 + (128 * x^3 + 82 * x^2 - 128 * x * h - 128 * x - 82 * h - 82) * m 17 + (-128 * x^2 + 128 * h + 128) * m 18 + (-41 * x^2 + 41 * h + 41) * m 21) = 0 := by
      linear_combination (-1) * e10_5 - (6832128 * x^2 + 2490368 * x * h + 3451136 * x - 447488 * h - 840719) * e12_5
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (19456 : ℝ) ≠ 0)
  have e11_6 : (1) * m 11 + (-1) * m 23 = 0 := by
    have hc : (5) * ((1) * m 11 + (-1) * m 23) = 0 := by
      linear_combination (-1) * e11 - (5) * e12_5
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (5 : ℝ) ≠ 0)
  have e4_9 : (-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (976 * x^2 - 976 * h - 976) * m 10 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14 + (-976 * x^2 + 976 * h + 976) * m 22 = 0 := by
    have hc : (1) * ((-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (976 * x^2 - 976 * h - 976) * m 10 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14 + (-976 * x^2 + 976 * h + 976) * m 22) = 0 := by
      linear_combination (1) * e4 - (336 * x + 1024 * h + 819) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e7_9 : (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 8 + (26624 * x^2 - 4784 * x - 13312 * h - 12061) * m 9 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 10 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 21 + (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 22 = 0 := by
    have hc : (16) * ((26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 8 + (26624 * x^2 - 4784 * x - 13312 * h - 12061) * m 9 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 10 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 21 + (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 22) = 0 := by
      linear_combination (1) * e7_4 - (-159744 * x^2 - 425984 * x * h - 271968 * x + 76544 * h + 54027) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (16 : ℝ) ≠ 0)
  have e15_9 : (-6656 * x^3 - 96 * x^2 + 6656 * x * h + 6656 * x + 96 * h + 96) * m 6 + (-6656 * x^2 + 5024 * x - 4864 * h - 5309) * m 7 + (6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 10 + (16384 * x^3 - 2944 * x^2 - 16384 * x * h - 16384 * x + 2944 * h + 2944) * m 19 + (16384 * x^2 - 5024 * x - 4864 * h - 4419) * m 20 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 22 + (-9728 * x^2 + 9728 * h + 9728) * m 23 = 0 := by
    have hc : (1) * ((-6656 * x^3 - 96 * x^2 + 6656 * x * h + 6656 * x + 96 * h + 96) * m 6 + (-6656 * x^2 + 5024 * x - 4864 * h - 5309) * m 7 + (6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 10 + (16384 * x^3 - 2944 * x^2 - 16384 * x * h - 16384 * x + 2944 * h + 2944) * m 19 + (16384 * x^2 - 5024 * x - 4864 * h - 4419) * m 20 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 22 + (-9728 * x^2 + 9728 * h + 9728) * m 23) = 0 := by
      linear_combination (1) * e15 - (6656 * x^2 - 5024 * x + 4864 * h + 5309) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e18_9 : (-16 * x^2 + 16 * h + 16) * m 8 + (-16 * x + 5) * m 9 + (16 * x^2 - 16 * h - 16) * m 10 + (16 * x^2 - 16 * h - 16) * m 21 + (-16 * x^2 + 16 * h + 16) * m 22 = 0 := by
    have hc : (1) * ((-16 * x^2 + 16 * h + 16) * m 8 + (-16 * x + 5) * m 9 + (16 * x^2 - 16 * h - 16) * m 10 + (16 * x^2 - 16 * h - 16) * m 21 + (-16 * x^2 + 16 * h + 16) * m 22) = 0 := by
      linear_combination (1) * e18 - (16 * x - 5) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e21_9 : (5) * m 10 + (-32 * x + 5) * m 22 + (-32) * m 23 = 0 := by
    have hc : ((x^2 - h - 1)) * ((5) * m 10 + (-32 * x + 5) * m 22 + (-32) * m 23) = 0 := by
      linear_combination (1) * e21_0 - (-5 * x + 16 * h + 16) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left f4
  have e22_9 : (1) * m 10 + (1) * m 22 = 0 := by
    have hc : (304 * (x^2 - h - 1)) * ((1) * m 10 + (1) * m 22) = 0 := by
      linear_combination (1) * e22 - (-720 * x + 89) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (304 : ℝ) ≠ 0) f4)
  have e15_10 : (6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 6 + (6656 * x^2 - 5024 * x + 4864 * h + 5309) * m 7 + (-6656 * x^3 + 1424 * x^2 + 6656 * x * h + 6656 * x - 1424 * h - 1424) * m 10 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 19 + (-16384 * x^2 + 5024 * x + 4864 * h + 4419) * m 20 + (6656 * x^3 - 1424 * x^2 - 6656 * x * h - 6656 * x + 1424 * h + 1424) * m 22 = 0 := by
    have hc : (32) * ((6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 6 + (6656 * x^2 - 5024 * x + 4864 * h + 5309) * m 7 + (-6656 * x^3 + 1424 * x^2 + 6656 * x * h + 6656 * x - 1424 * h - 1424) * m 10 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 19 + (-16384 * x^2 + 5024 * x + 4864 * h + 4419) * m 20 + (6656 * x^3 - 1424 * x^2 - 6656 * x * h - 6656 * x + 1424 * h + 1424) * m 22) = 0 := by
      linear_combination (-32) * e15_9 - (-9728 * x^2 + 9728 * h + 9728) * e21_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (32 : ℝ) ≠ 0)
  have e4_11 : (-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14 + (-1952 * x^2 + 1952 * h + 1952) * m 22 = 0 := by
    have hc : (1) * ((-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14 + (-1952 * x^2 + 1952 * h + 1952) * m 22) = 0 := by
      linear_combination (1) * e4_9 - (976 * x^2 - 976 * h - 976) * e22_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e7_11 : (26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 8 + (26624 * x^2 - 4784 * x - 13312 * h - 12061) * m 9 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 21 + (53248 * x^3 - 9568 * x^2 - 53248 * x * h - 53248 * x + 9568 * h + 9568) * m 22 = 0 := by
    have hc : (1) * ((26624 * x^3 - 4784 * x^2 - 26624 * x * h - 26624 * x + 4784 * h + 4784) * m 8 + (26624 * x^2 - 4784 * x - 13312 * h - 12061) * m 9 + (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * m 21 + (53248 * x^3 - 9568 * x^2 - 53248 * x * h - 53248 * x + 9568 * h + 9568) * m 22) = 0 := by
      linear_combination (1) * e7_9 - (-26624 * x^3 + 4784 * x^2 + 26624 * x * h + 26624 * x - 4784 * h - 4784) * e22_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e15_11 : (6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 6 + (6656 * x^2 - 5024 * x + 4864 * h + 5309) * m 7 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 19 + (-16384 * x^2 + 5024 * x + 4864 * h + 4419) * m 20 + (13312 * x^3 - 2848 * x^2 - 13312 * x * h - 13312 * x + 2848 * h + 2848) * m 22 = 0 := by
    have hc : (1) * ((6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 6 + (6656 * x^2 - 5024 * x + 4864 * h + 5309) * m 7 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 19 + (-16384 * x^2 + 5024 * x + 4864 * h + 4419) * m 20 + (13312 * x^3 - 2848 * x^2 - 13312 * x * h - 13312 * x + 2848 * h + 2848) * m 22) = 0 := by
      linear_combination (1) * e15_10 - (-6656 * x^3 + 1424 * x^2 + 6656 * x * h + 6656 * x - 1424 * h - 1424) * e22_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e18_11 : (-16 * x^2 + 16 * h + 16) * m 8 + (-16 * x + 5) * m 9 + (16 * x^2 - 16 * h - 16) * m 21 + (-32 * x^2 + 32 * h + 32) * m 22 = 0 := by
    have hc : (1) * ((-16 * x^2 + 16 * h + 16) * m 8 + (-16 * x + 5) * m 9 + (16 * x^2 - 16 * h - 16) * m 21 + (-32 * x^2 + 32 * h + 32) * m 22) = 0 := by
      linear_combination (1) * e18_9 - (16 * x^2 - 16 * h - 16) * e22_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e4_12 : (-1624064 * x^3 + 291824 * x^2 + 1624064 * x * h + 1624064 * x - 291824 * h - 291824) * m 0 + (-559104 * x^2 - 1703936 * x * h - 1262352 * x + 306176 * h + 244881) * m 1 + (1624064 * x^3 - 291824 * x^2 - 1624064 * x * h - 1624064 * x + 291824 * h + 291824) * m 8 + (1624064 * x^2 - 291824 * x - 812032 * h - 735721) * m 9 + (1624064 * x^3 - 291824 * x^2 - 1624064 * x * h - 1624064 * x + 291824 * h + 291824) * m 13 + (559104 * x^2 + 1703936 * x * h + 1262352 * x - 306176 * h - 244881) * m 14 + (-1624064 * x^3 + 291824 * x^2 + 1624064 * x * h + 1624064 * x - 291824 * h - 291824) * m 21 = 0 := by
    have hc : (32 * (x^2 - h - 1)) * ((-1624064 * x^3 + 291824 * x^2 + 1624064 * x * h + 1624064 * x - 291824 * h - 291824) * m 0 + (-559104 * x^2 - 1703936 * x * h - 1262352 * x + 306176 * h + 244881) * m 1 + (1624064 * x^3 - 291824 * x^2 - 1624064 * x * h - 1624064 * x + 291824 * h + 291824) * m 8 + (1624064 * x^2 - 291824 * x - 812032 * h - 735721) * m 9 + (1624064 * x^3 - 291824 * x^2 - 1624064 * x * h - 1624064 * x + 291824 * h + 291824) * m 13 + (559104 * x^2 + 1703936 * x * h + 1262352 * x - 306176 * h - 244881) * m 14 + (-1624064 * x^3 + 291824 * x^2 + 1624064 * x * h + 1624064 * x - 291824 * h - 291824) * m 21) = 0 := by
      linear_combination (53248 * x^3 - 9568 * x^2 - 53248 * x * h - 53248 * x + 9568 * h + 9568) * e4_11 - (-1952 * x^2 + 1952 * h + 1952) * e7_11
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (32 : ℝ) ≠ 0) f4)
  have e15_12 : (11075584 * x^4 - 1830400 * x^3 - 11075584 * x^2 * h - 11104288 * x^2 + 1830400 * x * h + 1830400 * x + 28704 * h + 28704) * m 6 + (11075584 * x^3 - 10350080 * x^2 + 8093696 * x * h + 10336352 * x - 1454336 * h - 1587391) * m 7 + (-11075584 * x^4 + 4359680 * x^3 + 11075584 * x^2 * h + 10649808 * x^2 - 4359680 * x * h - 4359680 * x + 425776 * h + 425776) * m 8 + (-11075584 * x^3 + 4359680 * x^2 + 5537792 * x * h + 4591600 * x - 1184768 * h - 1073429) * m 9 + (-27262976 * x^4 + 9797632 * x^3 + 27262976 * x^2 * h + 26382720 * x^2 - 9797632 * x * h - 9797632 * x + 880256 * h + 880256) * m 19 + (-27262976 * x^3 + 13258752 * x^2 + 8093696 * x * h + 5851040 * x - 1454336 * h - 1321281) * m 20 + (11075584 * x^4 - 4359680 * x^3 - 11075584 * x^2 * h - 10649808 * x^2 + 4359680 * x * h + 4359680 * x - 425776 * h - 425776) * m 21 = 0 := by
    have hc : (32 * (x^2 - h - 1)) * ((11075584 * x^4 - 1830400 * x^3 - 11075584 * x^2 * h - 11104288 * x^2 + 1830400 * x * h + 1830400 * x + 28704 * h + 28704) * m 6 + (11075584 * x^3 - 10350080 * x^2 + 8093696 * x * h + 10336352 * x - 1454336 * h - 1587391) * m 7 + (-11075584 * x^4 + 4359680 * x^3 + 11075584 * x^2 * h + 10649808 * x^2 - 4359680 * x * h - 4359680 * x + 425776 * h + 425776) * m 8 + (-11075584 * x^3 + 4359680 * x^2 + 5537792 * x * h + 4591600 * x - 1184768 * h - 1073429) * m 9 + (-27262976 * x^4 + 9797632 * x^3 + 27262976 * x^2 * h + 26382720 * x^2 - 9797632 * x * h - 9797632 * x + 880256 * h + 880256) * m 19 + (-27262976 * x^3 + 13258752 * x^2 + 8093696 * x * h + 5851040 * x - 1454336 * h - 1321281) * m 20 + (11075584 * x^4 - 4359680 * x^3 - 11075584 * x^2 * h - 10649808 * x^2 + 4359680 * x * h + 4359680 * x - 425776 * h - 425776) * m 21) = 0 := by
      linear_combination (53248 * x^3 - 9568 * x^2 - 53248 * x * h - 53248 * x + 9568 * h + 9568) * e15_11 - (13312 * x^3 - 2848 * x^2 - 13312 * x * h - 13312 * x + 2848 * h + 2848) * e7_11
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (32 : ℝ) ≠ 0) f4)
  have e18_12 : (1) * m 9 = 0 := by
    have hc : (128 * (2080 * x - 3328 * h - 3389) * (x^2 - h - 1)) * ((1) * m 9) = 0 := by
      linear_combination (53248 * x^3 - 9568 * x^2 - 53248 * x * h - 53248 * x + 9568 * h + 9568) * e18_11 - (-32 * x^2 + 32 * h + 32) * e7_11
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (128 : ℝ) ≠ 0) f6) f4)
  have e0_13 : (-208 * x^2 + 208 * h + 208) * m 0 + (-208 * x + 417) * m 1 + (208 * x^2 - 208 * h - 208) * m 8 + (208 * x^2 - 208 * h - 208) * m 13 + (208 * x - 417) * m 14 + (-208 * x^2 + 208 * h + 208) * m 21 = 0 := by
    have hc : ((128 * x - 23)) * ((-208 * x^2 + 208 * h + 208) * m 0 + (-208 * x + 417) * m 1 + (208 * x^2 - 208 * h - 208) * m 8 + (208 * x^2 - 208 * h - 208) * m 13 + (208 * x - 417) * m 14 + (-208 * x^2 + 208 * h + 208) * m 21) = 0 := by
      linear_combination (1) * e0_4 - (26624 * x^2 - 4784 * x - 13312 * h - 12061) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left f3
  have e3_13 : (32 * x^3 - 5 * x^2 - 32 * x * h - 32 * x + 5 * h + 5) * m 0 + (32 * x^2 - 5 * x - 16 * h - 16) * m 1 + (-32 * x^3 + 5 * x^2 + 32 * x * h + 32 * x - 5 * h - 5) * m 8 + (5 * x^2 - 5 * h - 5) * m 13 + (5 * x - 16 * h - 16) * m 14 + (-5 * x^2 + 5 * h + 5) * m 21 = 0 := by
    have hc : (1) * ((32 * x^3 - 5 * x^2 - 32 * x * h - 32 * x + 5 * h + 5) * m 0 + (32 * x^2 - 5 * x - 16 * h - 16) * m 1 + (-32 * x^3 + 5 * x^2 + 32 * x * h + 32 * x - 5 * h - 5) * m 8 + (5 * x^2 - 5 * h - 5) * m 13 + (5 * x - 16 * h - 16) * m 14 + (-5 * x^2 + 5 * h + 5) * m 21) = 0 := by
      linear_combination (1) * e3 - (-32 * x^2 + 5 * x + 16 * h + 16) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e4_13 : (-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (976 * x^2 - 976 * h - 976) * m 8 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14 + (-976 * x^2 + 976 * h + 976) * m 21 = 0 := by
    have hc : (13 * (128 * x - 23)) * ((-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (976 * x^2 - 976 * h - 976) * m 8 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14 + (-976 * x^2 + 976 * h + 976) * m 21) = 0 := by
      linear_combination (1) * e4_12 - (1624064 * x^2 - 291824 * x - 812032 * h - 735721) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (13 : ℝ) ≠ 0) f3)
  have e14_13 : (9728 * x^3 + 5152 * x^2 - 9728 * x * h - 9728 * x - 5152 * h - 5152) * m 6 + (9728 * x^2 + 5152 * x - 4864 * h - 6949) * m 7 + (-9728 * x^3 - 5152 * x^2 + 9728 * x * h + 9728 * x + 5152 * h + 5152) * m 8 + (8192 * x^2 - 8192 * h - 8192) * m 19 + (-5152 * x - 4864 * h - 2779) * m 20 + (-8192 * x^2 + 8192 * h + 8192) * m 21 = 0 := by
    have hc : (1) * ((9728 * x^3 + 5152 * x^2 - 9728 * x * h - 9728 * x - 5152 * h - 5152) * m 6 + (9728 * x^2 + 5152 * x - 4864 * h - 6949) * m 7 + (-9728 * x^3 - 5152 * x^2 + 9728 * x * h + 9728 * x + 5152 * h + 5152) * m 8 + (8192 * x^2 - 8192 * h - 8192) * m 19 + (-5152 * x - 4864 * h - 2779) * m 20 + (-8192 * x^2 + 8192 * h + 8192) * m 21) = 0 := by
      linear_combination (1) * e14 - (-9728 * x^2 - 5152 * x + 4864 * h + 6949) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e15_13 : (6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 6 + (6656 * x^2 - 5024 * x + 4864 * h + 5309) * m 7 + (-6656 * x^3 + 1424 * x^2 + 6656 * x * h + 6656 * x - 1424 * h - 1424) * m 8 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 19 + (-16384 * x^2 + 5024 * x + 4864 * h + 4419) * m 20 + (6656 * x^3 - 1424 * x^2 - 6656 * x * h - 6656 * x + 1424 * h + 1424) * m 21 = 0 := by
    have hc : (13 * (128 * x - 23)) * ((6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 6 + (6656 * x^2 - 5024 * x + 4864 * h + 5309) * m 7 + (-6656 * x^3 + 1424 * x^2 + 6656 * x * h + 6656 * x - 1424 * h - 1424) * m 8 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 19 + (-16384 * x^2 + 5024 * x + 4864 * h + 4419) * m 20 + (6656 * x^3 - 1424 * x^2 - 6656 * x * h - 6656 * x + 1424 * h + 1424) * m 21) = 0 := by
      linear_combination (1) * e15_12 - (-11075584 * x^3 + 4359680 * x^2 + 5537792 * x * h + 4591600 * x - 1184768 * h - 1073429) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (13 : ℝ) ≠ 0) f3)
  have e19_13 : (-128 * x - 21) * m 8 + (61) * m 21 = 0 := by
    have hc : (16 * (x^2 - h - 1)) * ((-128 * x - 21) * m 8 + (61) * m 21) = 0 := by
      linear_combination (1) * e19_0 - (-2048 * x^2 - 336 * x + 1024 * h + 1229) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) f4)
  have e20_13 : (-1) * m 8 + (1) * m 21 = 0 := by
    have hc : (304 * (x^2 - h - 1)) * ((-1) * m 8 + (1) * m 21) = 0 := by
      linear_combination (1) * e20 - (-304 * x - 417) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (304 : ℝ) ≠ 0) f4)
  have e0_14 : (-12688 * x^2 + 12688 * h + 12688) * m 0 + (-12688 * x + 25437) * m 1 + (-26624 * x^3 + 8320 * x^2 + 26624 * x * h + 26624 * x - 8320 * h - 8320) * m 8 + (12688 * x^2 - 12688 * h - 12688) * m 13 + (12688 * x - 25437) * m 14 = 0 := by
    have hc : (1) * ((-12688 * x^2 + 12688 * h + 12688) * m 0 + (-12688 * x + 25437) * m 1 + (-26624 * x^3 + 8320 * x^2 + 26624 * x * h + 26624 * x - 8320 * h - 8320) * m 8 + (12688 * x^2 - 12688 * h - 12688) * m 13 + (12688 * x - 25437) * m 14) = 0 := by
      linear_combination (61) * e0_13 - (-208 * x^2 + 208 * h + 208) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e3_14 : (1952 * x^3 - 305 * x^2 - 1952 * x * h - 1952 * x + 305 * h + 305) * m 0 + (1952 * x^2 - 305 * x - 976 * h - 976) * m 1 + (-2592 * x^3 + 200 * x^2 + 2592 * x * h + 2592 * x - 200 * h - 200) * m 8 + (305 * x^2 - 305 * h - 305) * m 13 + (305 * x - 976 * h - 976) * m 14 = 0 := by
    have hc : (1) * ((1952 * x^3 - 305 * x^2 - 1952 * x * h - 1952 * x + 305 * h + 305) * m 0 + (1952 * x^2 - 305 * x - 976 * h - 976) * m 1 + (-2592 * x^3 + 200 * x^2 + 2592 * x * h + 2592 * x - 200 * h - 200) * m 8 + (305 * x^2 - 305 * h - 305) * m 13 + (305 * x - 976 * h - 976) * m 14) = 0 := by
      linear_combination (61) * e3_13 - (-5 * x^2 + 5 * h + 5) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e4_14 : (-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (-2048 * x^3 + 640 * x^2 + 2048 * x * h + 2048 * x - 640 * h - 640) * m 8 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14 = 0 := by
    have hc : (61) * ((-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (-2048 * x^3 + 640 * x^2 + 2048 * x * h + 2048 * x - 640 * h - 640) * m 8 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14) = 0 := by
      linear_combination (61) * e4_13 - (-976 * x^2 + 976 * h + 976) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (61 : ℝ) ≠ 0)
  have e14_14 : (593408 * x^3 + 314272 * x^2 - 593408 * x * h - 593408 * x - 314272 * h - 314272) * m 6 + (593408 * x^2 + 314272 * x - 296704 * h - 423889) * m 7 + (-1641984 * x^3 - 486304 * x^2 + 1641984 * x * h + 1641984 * x + 486304 * h + 486304) * m 8 + (499712 * x^2 - 499712 * h - 499712) * m 19 + (-314272 * x - 296704 * h - 169519) * m 20 = 0 := by
    have hc : (1) * ((593408 * x^3 + 314272 * x^2 - 593408 * x * h - 593408 * x - 314272 * h - 314272) * m 6 + (593408 * x^2 + 314272 * x - 296704 * h - 423889) * m 7 + (-1641984 * x^3 - 486304 * x^2 + 1641984 * x * h + 1641984 * x + 486304 * h + 486304) * m 8 + (499712 * x^2 - 499712 * h - 499712) * m 19 + (-314272 * x - 296704 * h - 169519) * m 20) = 0 := by
      linear_combination (61) * e14_13 - (-8192 * x^2 + 8192 * h + 8192) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e15_14 : (406016 * x^3 + 5856 * x^2 - 406016 * x * h - 406016 * x - 5856 * h - 5856) * m 6 + (406016 * x^2 - 306464 * x + 296704 * h + 323849) * m 7 + (851968 * x^4 - 448512 * x^3 - 851968 * x^2 * h - 795008 * x^2 + 448512 * x * h + 448512 * x - 56960 * h - 56960) * m 8 + (-999424 * x^3 + 179584 * x^2 + 999424 * x * h + 999424 * x - 179584 * h - 179584) * m 19 + (-999424 * x^2 + 306464 * x + 296704 * h + 269559) * m 20 = 0 := by
    have hc : (1) * ((406016 * x^3 + 5856 * x^2 - 406016 * x * h - 406016 * x - 5856 * h - 5856) * m 6 + (406016 * x^2 - 306464 * x + 296704 * h + 323849) * m 7 + (851968 * x^4 - 448512 * x^3 - 851968 * x^2 * h - 795008 * x^2 + 448512 * x * h + 448512 * x - 56960 * h - 56960) * m 8 + (-999424 * x^3 + 179584 * x^2 + 999424 * x * h + 999424 * x - 179584 * h - 179584) * m 19 + (-999424 * x^2 + 306464 * x + 296704 * h + 269559) * m 20) = 0 := by
      linear_combination (61) * e15_13 - (6656 * x^3 - 1424 * x^2 - 6656 * x * h - 6656 * x + 1424 * h + 1424) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e20_14 : (1) * m 8 = 0 := by
    have hc : (8 * (16 * x - 5)) * ((1) * m 8) = 0 := by
      linear_combination (61) * e20_13 - (1) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) f7)
  have e0_15 : (-208 * x^2 + 208 * h + 208) * m 0 + (-208 * x + 417) * m 1 + (208 * x^2 - 208 * h - 208) * m 13 + (208 * x - 417) * m 14 = 0 := by
    have hc : (61) * ((-208 * x^2 + 208 * h + 208) * m 0 + (-208 * x + 417) * m 1 + (208 * x^2 - 208 * h - 208) * m 13 + (208 * x - 417) * m 14) = 0 := by
      linear_combination (1) * e0_14 - (-26624 * x^3 + 8320 * x^2 + 26624 * x * h + 26624 * x - 8320 * h - 8320) * e20_14
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (61 : ℝ) ≠ 0)
  have e3_15 : (32 * x^3 - 5 * x^2 - 32 * x * h - 32 * x + 5 * h + 5) * m 0 + (32 * x^2 - 5 * x - 16 * h - 16) * m 1 + (5 * x^2 - 5 * h - 5) * m 13 + (5 * x - 16 * h - 16) * m 14 = 0 := by
    have hc : (61) * ((32 * x^3 - 5 * x^2 - 32 * x * h - 32 * x + 5 * h + 5) * m 0 + (32 * x^2 - 5 * x - 16 * h - 16) * m 1 + (5 * x^2 - 5 * h - 5) * m 13 + (5 * x - 16 * h - 16) * m 14) = 0 := by
      linear_combination (1) * e3_14 - (-2592 * x^3 + 200 * x^2 + 2592 * x * h + 2592 * x - 200 * h - 200) * e20_14
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (61 : ℝ) ≠ 0)
  have e4_15 : (-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14 = 0 := by
    have hc : (1) * ((-976 * x^2 + 976 * h + 976) * m 0 + (-336 * x - 1024 * h - 819) * m 1 + (976 * x^2 - 976 * h - 976) * m 13 + (336 * x + 1024 * h + 819) * m 14) = 0 := by
      linear_combination (1) * e4_14 - (-2048 * x^3 + 640 * x^2 + 2048 * x * h + 2048 * x - 640 * h - 640) * e20_14
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e14_15 : (9728 * x^3 + 5152 * x^2 - 9728 * x * h - 9728 * x - 5152 * h - 5152) * m 6 + (9728 * x^2 + 5152 * x - 4864 * h - 6949) * m 7 + (8192 * x^2 - 8192 * h - 8192) * m 19 + (-5152 * x - 4864 * h - 2779) * m 20 = 0 := by
    have hc : (61) * ((9728 * x^3 + 5152 * x^2 - 9728 * x * h - 9728 * x - 5152 * h - 5152) * m 6 + (9728 * x^2 + 5152 * x - 4864 * h - 6949) * m 7 + (8192 * x^2 - 8192 * h - 8192) * m 19 + (-5152 * x - 4864 * h - 2779) * m 20) = 0 := by
      linear_combination (1) * e14_14 - (-1641984 * x^3 - 486304 * x^2 + 1641984 * x * h + 1641984 * x + 486304 * h + 486304) * e20_14
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (61 : ℝ) ≠ 0)
  have e15_15 : (6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 6 + (6656 * x^2 - 5024 * x + 4864 * h + 5309) * m 7 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 19 + (-16384 * x^2 + 5024 * x + 4864 * h + 4419) * m 20 = 0 := by
    have hc : (61) * ((6656 * x^3 + 96 * x^2 - 6656 * x * h - 6656 * x - 96 * h - 96) * m 6 + (6656 * x^2 - 5024 * x + 4864 * h + 5309) * m 7 + (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * m 19 + (-16384 * x^2 + 5024 * x + 4864 * h + 4419) * m 20) = 0 := by
      linear_combination (1) * e15_14 - (851968 * x^4 - 448512 * x^3 - 851968 * x^2 * h - 795008 * x^2 + 448512 * x * h + 448512 * x - 56960 * h - 56960) * e20_14
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (61 : ℝ) ≠ 0)
  have e2_16 : (2775552 * x^3 - 692224 * x^2 * h - 3474448 * x^2 - 2775552 * x * h - 2775552 * x + 692224 * h^2 + 4166672 * h + 3474448) * m 0 + (1384448 * x^4 - 4379648 * x^3 - 1384448 * x^2 * h + 1831456 * x^2 + 4379648 * x * h + 4379648 * x - 3215904 * h - 3215904) * m 6 + (1384448 * x^3 - 4379648 * x^2 - 692224 * x * h + 2957360 * x + 1387776 * h + 518331) * m 7 + (-1384448 * x^4 + 2775552 * x^3 + 2076672 * x^2 * h - 705552 * x^2 - 2775552 * x * h - 2775552 * x - 692224 * h^2 + 1397776 * h + 2090000) * m 13 + (-1384448 * x^3 + 2775552 * x^2 + 1384448 * x * h + 1384448 * x - 2775552 * h - 2775552) * m 14 + (-1171456 * x^3 + 2348544 * x^2 + 1171456 * x * h + 1171456 * x - 2348544 * h - 2348544) * m 19 + (1604096 * x^2 - 692224 * x * h - 4341808 * x + 1387776 * h + 2257221) * m 20 = 0 := by
    have hc : (1) * ((2775552 * x^3 - 692224 * x^2 * h - 3474448 * x^2 - 2775552 * x * h - 2775552 * x + 692224 * h^2 + 4166672 * h + 3474448) * m 0 + (1384448 * x^4 - 4379648 * x^3 - 1384448 * x^2 * h + 1831456 * x^2 + 4379648 * x * h + 4379648 * x - 3215904 * h - 3215904) * m 6 + (1384448 * x^3 - 4379648 * x^2 - 692224 * x * h + 2957360 * x + 1387776 * h + 518331) * m 7 + (-1384448 * x^4 + 2775552 * x^3 + 2076672 * x^2 * h - 705552 * x^2 - 2775552 * x * h - 2775552 * x - 692224 * h^2 + 1397776 * h + 2090000) * m 13 + (-1384448 * x^3 + 2775552 * x^2 + 1384448 * x * h + 1384448 * x - 2775552 * h - 2775552) * m 14 + (-1171456 * x^3 + 2348544 * x^2 + 1171456 * x * h + 1171456 * x - 2348544 * h - 2348544) * m 19 + (1604096 * x^2 - 692224 * x * h - 4341808 * x + 1387776 * h + 2257221) * m 20) = 0 := by
      linear_combination (-208 * x + 417) * e2 - (6656 * x^2 - 7712 * x - 3328 * h - 1243) * e0_15
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e3_16 : (13344 * x - 3328 * h - 5413) * m 0 + (-6656 * x^2 + 3328 * h + 5413) * m 13 + (-6656 * x + 13344) * m 14 = 0 := by
    have hc : ((x^2 - h - 1)) * ((13344 * x - 3328 * h - 5413) * m 0 + (-6656 * x^2 + 3328 * h + 5413) * m 13 + (-6656 * x + 13344) * m 14) = 0 := by
      linear_combination (-208 * x + 417) * e3_15 - (32 * x^2 - 5 * x - 16 * h - 16) * e0_15
    exact (mul_eq_zero.mp hc).resolve_left f4
  have e4_16 : (1) * m 0 + (-1) * m 13 = 0 := by
    have hc : (64 * (2080 * x - 3328 * h - 9021) * (x^2 - h - 1)) * ((1) * m 0 + (-1) * m 13) = 0 := by
      linear_combination (-208 * x + 417) * e4_15 - (-336 * x - 1024 * h - 819) * e0_15
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (64 : ℝ) ≠ 0) f9) f4)
  have e2_17 : (2348544 * x^2 - 2348544 * h - 2348544) * m 0 + (-1384448 * x^4 + 4379648 * x^3 + 1384448 * x^2 * h - 1831456 * x^2 - 4379648 * x * h - 4379648 * x + 3215904 * h + 3215904) * m 6 + (-1384448 * x^3 + 4379648 * x^2 + 692224 * x * h - 2957360 * x - 1387776 * h - 518331) * m 7 + (-2775552 * x^3 + 3215904 * x^2 + 2775552 * x * h + 2775552 * x - 3215904 * h - 3215904) * m 13 + (1171456 * x^3 - 2348544 * x^2 - 1171456 * x * h - 1171456 * x + 2348544 * h + 2348544) * m 19 + (-1604096 * x^2 + 692224 * x * h + 4341808 * x - 1387776 * h - 2257221) * m 20 = 0 := by
    have hc : (32 * (208 * x - 417)) * ((2348544 * x^2 - 2348544 * h - 2348544) * m 0 + (-1384448 * x^4 + 4379648 * x^3 + 1384448 * x^2 * h - 1831456 * x^2 - 4379648 * x * h - 4379648 * x + 3215904 * h + 3215904) * m 6 + (-1384448 * x^3 + 4379648 * x^2 + 692224 * x * h - 2957360 * x - 1387776 * h - 518331) * m 7 + (-2775552 * x^3 + 3215904 * x^2 + 2775552 * x * h + 2775552 * x - 3215904 * h - 3215904) * m 13 + (1171456 * x^3 - 2348544 * x^2 - 1171456 * x * h - 1171456 * x + 2348544 * h + 2348544) * m 19 + (-1604096 * x^2 + 692224 * x * h + 4341808 * x - 1387776 * h - 2257221) * m 20) = 0 := by
      linear_combination (-6656 * x + 13344) * e2_16 - (-1384448 * x^3 + 2775552 * x^2 + 1384448 * x * h + 1384448 * x - 2775552 * h - 2775552) * e3_16
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (32 : ℝ) ≠ 0) f8)
  have e2_18 : (-6656 * x^3 + 7712 * x^2 + 6656 * x * h + 6656 * x - 7712 * h - 7712) * m 6 + (-6656 * x^2 + 7712 * x + 3328 * h + 1243) * m 7 + (-13344 * x^2 + 13344 * h + 13344) * m 13 + (5632 * x^2 - 5632 * h - 5632) * m 19 + (-7712 * x + 3328 * h + 5413) * m 20 = 0 := by
    have hc : ((208 * x - 417)) * ((-6656 * x^3 + 7712 * x^2 + 6656 * x * h + 6656 * x - 7712 * h - 7712) * m 6 + (-6656 * x^2 + 7712 * x + 3328 * h + 1243) * m 7 + (-13344 * x^2 + 13344 * h + 13344) * m 13 + (5632 * x^2 - 5632 * h - 5632) * m 19 + (-7712 * x + 3328 * h + 5413) * m 20) = 0 := by
      linear_combination (1) * e2_17 - (2348544 * x^2 - 2348544 * h - 2348544) * e4_16
    exact (mul_eq_zero.mp hc).resolve_left f8
  have e15_20 : (1245184 * x^4 + 861696 * x^3 - 1245184 * x^2 * h - 1357536 * x^2 - 861696 * x * h - 861696 * x + 112352 * h + 112352) * m 6 + (1245184 * x^3 + 861696 * x^2 - 622592 * x * h - 1329504 * x + 423168 * h + 499603) * m 7 + (-1708032 * x^2 - 622592 * x * h + 84320 * x + 423168 * h + 346733) * m 20 = 0 := by
    have hc : (128 * (x^2 - h - 1)) * ((1245184 * x^4 + 861696 * x^3 - 1245184 * x^2 * h - 1357536 * x^2 - 861696 * x * h - 861696 * x + 112352 * h + 112352) * m 6 + (1245184 * x^3 + 861696 * x^2 - 622592 * x * h - 1329504 * x + 423168 * h + 499603) * m 7 + (-1708032 * x^2 - 622592 * x * h + 84320 * x + 423168 * h + 346733) * m 20) = 0 := by
      linear_combination (8192 * x^2 - 8192 * h - 8192) * e15_15 - (-16384 * x^3 + 2944 * x^2 + 16384 * x * h + 16384 * x - 2944 * h - 2944) * e14_15
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (128 : ℝ) ≠ 0) f4)
  have e16_20 : (-396800 * x^3 + 173152 * x^2 + 396800 * x * h + 396800 * x - 173152 * h - 173152) * m 6 + (-396800 * x^2 + 173152 * x + 198400 * h + 163665) * m 7 + (-173152 * x + 198400 * h + 233135) * m 20 = 0 := by
    have hc : (128 * (x^2 - h - 1)) * ((-396800 * x^3 + 173152 * x^2 + 396800 * x * h + 396800 * x - 173152 * h - 173152) * m 6 + (-396800 * x^2 + 173152 * x + 198400 * h + 163665) * m 7 + (-173152 * x + 198400 * h + 233135) * m 20) = 0 := by
      linear_combination (8192 * x^2 - 8192 * h - 8192) * e16_0 - (-384 * x^2 + 384 * h + 384) * e14_15
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (128 : ℝ) ≠ 0) f4)
  have e17_20 : (-184832 * x^3 - 253536 * x^2 + 184832 * x * h + 184832 * x + 253536 * h + 253536) * m 6 + (-184832 * x^2 - 253536 * x + 92416 * h - 81473) * m 7 + (253536 * x + 92416 * h + 266305) * m 20 = 0 := by
    have hc : (128 * (128 * x - 23) * (x^2 - h - 1)) * ((-184832 * x^3 - 253536 * x^2 + 184832 * x * h + 184832 * x + 253536 * h + 253536) * m 6 + (-184832 * x^2 - 253536 * x + 92416 * h - 81473) * m 7 + (253536 * x + 92416 * h + 266305) * m 20) = 0 := by
      linear_combination (8192 * x^2 - 8192 * h - 8192) * e17 - (311296 * x^3 + 99712 * x^2 - 311296 * x * h - 311296 * x - 99712 * h - 99712) * e14_15
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (128 : ℝ) ≠ 0) f3) f4)
  have e15_21 : (-512 * x^2 + 160 * x + 256 * h + 231) * m 6 + (-512 * x + 160) * m 7 = 0 := by
    have hc : (4194304 * (416 * x - 89) * (x^2 - h - 1)) * ((-512 * x^2 + 160 * x + 256 * h + 231) * m 6 + (-512 * x + 160) * m 7) = 0 := by
      linear_combination (-173152 * x + 198400 * h + 233135) * e15_20 - (-1708032 * x^2 - 622592 * x * h + 84320 * x + 423168 * h + 346733) * e16_20
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (4194304 : ℝ) ≠ 0) f11) f4)
  have e17_21 : (126464 * x^2 + 59680 * x - 63232 * h - 100345) * m 6 + (126464 * x + 59680) * m 7 = 0 := by
    have hc : (1048576 * (x^2 - h - 1)) * ((126464 * x^2 + 59680 * x - 63232 * h - 100345) * m 6 + (126464 * x + 59680) * m 7) = 0 := by
      linear_combination (-173152 * x + 198400 * h + 233135) * e17_20 - (253536 * x + 92416 * h + 266305) * e16_20
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (1048576 : ℝ) ≠ 0) f4)
  have e17_22 : (1) * m 6 = 0 := by
    have hc : (128 * (173152 * x - 198400 * h - 233135)) * ((1) * m 6) = 0 := by
      linear_combination (-512 * x + 160) * e17_21 - (126464 * x + 59680) * e15_21
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (128 : ℝ) ≠ 0) f10)
  have z6 : m 6 = 0 := by
    have hc : (1) * m 6 = 0 := by
      linear_combination e17_22
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z7 : m 7 = 0 := by
    have hc : (-32 * (16 * x - 5)) * m 7 = 0 := by
      simp only [z6, mul_zero, zero_add, add_zero] at e15_21
      linear_combination e15_21
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-32 : ℝ) ≠ 0) f7)
  have z20 : m 20 = 0 := by
    have hc : (-1 * (173152 * x - 198400 * h - 233135)) * m 20 = 0 := by
      simp only [z6, z7, mul_zero, zero_add, add_zero] at e16_20
      linear_combination e16_20
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) f10)
  have z19 : m 19 = 0 := by
    have hc : (8192 * (x^2 - h - 1)) * m 19 = 0 := by
      simp only [z6, z7, z20, mul_zero, zero_add, add_zero] at e14_15
      linear_combination e14_15
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (8192 : ℝ) ≠ 0) f4)
  have z13 : m 13 = 0 := by
    have hc : (-13344 * (x^2 - h - 1)) * m 13 = 0 := by
      simp only [z6, z7, z19, z20, mul_zero, zero_add, add_zero] at e2_18
      linear_combination e2_18
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-13344 : ℝ) ≠ 0) f4)
  have z0 : m 0 = 0 := by
    have hc : (1) * m 0 = 0 := by
      simp only [z13, mul_zero, zero_add, add_zero] at e4_16
      linear_combination e4_16
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z14 : m 14 = 0 := by
    have hc : (-32 * (208 * x - 417)) * m 14 = 0 := by
      simp only [z0, z13, mul_zero, zero_add, add_zero] at e3_16
      linear_combination e3_16
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-32 : ℝ) ≠ 0) f8)
  have z1 : m 1 = 0 := by
    have hc : (-1 * (208 * x - 417)) * m 1 = 0 := by
      simp only [z0, z13, z14, mul_zero, zero_add, add_zero] at e0_15
      linear_combination e0_15
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) f8)
  have z8 : m 8 = 0 := by
    have hc : (1) * m 8 = 0 := by
      linear_combination e20_14
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z21 : m 21 = 0 := by
    have hc : (61) * m 21 = 0 := by
      simp only [z8, mul_zero, zero_add, add_zero] at e19_13
      linear_combination e19_13
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (61 : ℝ) ≠ 0)
  have z9 : m 9 = 0 := by
    have hc : (1) * m 9 = 0 := by
      linear_combination e18_12
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z22 : m 22 = 0 := by
    have hc : (416 * (128 * x - 23) * (x^2 - h - 1)) * m 22 = 0 := by
      simp only [z8, z9, z21, mul_zero, zero_add, add_zero] at e7_11
      linear_combination e7_11
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (416 : ℝ) ≠ 0) f3) f4)
  have z10 : m 10 = 0 := by
    have hc : (1) * m 10 = 0 := by
      simp only [z22, mul_zero, zero_add, add_zero] at e22_9
      linear_combination e22_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z23 : m 23 = 0 := by
    have hc : (-32) * m 23 = 0 := by
      simp only [z10, z22, mul_zero, zero_add, add_zero] at e21_9
      linear_combination e21_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (-32 : ℝ) ≠ 0)
  have z11 : m 11 = 0 := by
    have hc : (1) * m 11 = 0 := by
      simp only [z23, mul_zero, zero_add, add_zero] at e11_6
      linear_combination e11_6
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z17 : m 17 = 0 := by
    have hc : (2 * (x^2 - h - 1)) * m 17 = 0 := by
      simp only [z0, z1, z13, z14, mul_zero, zero_add, add_zero] at e1_6
      linear_combination e1_6
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) f4)
  have z18 : m 18 = 0 := by
    have hc : (-128 * (x^2 - h - 1)) * m 18 = 0 := by
      simp only [z8, z9, z17, z21, mul_zero, zero_add, add_zero] at e10_6
      linear_combination e10_6
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-128 : ℝ) ≠ 0) f4)
  have z5 : m 5 = 0 := by
    have hc : (-1) * m 5 = 0 := by
      simp only [z18, mul_zero, zero_add, add_zero] at e12_5
      linear_combination e12_5
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (-1 : ℝ) ≠ 0)
  have z4 : m 4 = 0 := by
    have hc : (19456 * (x^2 - h - 1)) * m 4 = 0 := by
      simp only [z5, z17, z18, mul_zero, zero_add, add_zero] at e13
      linear_combination e13
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (19456 : ℝ) ≠ 0) f4)
  have z15 : m 15 = 0 := by
    have hc : (416 * (128 * x - 23) * (x^2 - h - 1)) * m 15 = 0 := by
      simp only [z8, z9, z21, mul_zero, zero_add, add_zero] at e6_3
      linear_combination e6_3
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (416 : ℝ) ≠ 0) f3) f4)
  have z2 : m 2 = 0 := by
    have hc : (-1) * m 2 = 0 := by
      simp only [z15, mul_zero, zero_add, add_zero] at e8_1
      linear_combination e8_1
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (-1 : ℝ) ≠ 0)
  have z3 : m 3 = 0 := by
    have hc : (86528 * (x^2 - h - 1)) * m 3 = 0 := by
      simp only [z2, z6, z7, z15, z19, z20, mul_zero, zero_add, add_zero] at e5_1
      linear_combination e5_1
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (86528 : ℝ) ≠ 0) f4)
  have z16 : m 16 = 0 := by
    have hc : (417) * m 16 = 0 := by
      simp only [z3, mul_zero, zero_add, add_zero] at e9
      linear_combination e9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (417 : ℝ) ≠ 0)
  have z12 : m 12 = 0 := by
    have hc : (1) * m 12 = 0 := by
      linear_combination e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  funext i
  fin_cases i <;> first | exact z0 | exact z1 | exact z2 | exact z3 | exact z4 | exact z5 | exact z6 | exact z7 | exact z8 | exact z9 | exact z10 | exact z11 | exact z12 | exact z13 | exact z14 | exact z15 | exact z16 | exact z17 | exact z18 | exact z19 | exact z20 | exact z21 | exact z22 | exact z23

set_option maxHeartbeats 0 in
private theorem injective_true (x h : ℝ) (hl : (1 / 6) ≤ x)
    (hu : x ≤ (1 / 2)) (hh : 0 ≤ h) (m : Fin 24 → ℝ)
    (he : ∀ e, edgeDerivative true x (1 - x^2 + h) m e = 0) : m = 0 := by
  have hx : 0 ≤ x := by linarith only [hl]
  have hsq : x^2 ≤ (1 / 4) := by nlinarith only [hu, mul_nonneg (sub_nonneg.mpr hu) (add_nonneg hx (by norm_num : (0 : ℝ) ≤ (1 / 2)))]
  have f0 : (1024 * x - 1) ≠ 0 := ne_of_gt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f1 : (1024 * x - 1025) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f2 : (4096 * h + 73) ≠ 0 := ne_of_gt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f3 : (7168 * x - 8192 * h - 7289) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f4 : (1024 * x + 129) ≠ 0 := ne_of_gt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f5 : (1024 * x - 895) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f6 : (x^2 - h - 1) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f7 : (1024 * x + 8192 * h + 1169) ≠ 0 := ne_of_gt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f8 : (8192 * x - 4096 * h - 7233) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f9 : (1024 * x - 767) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f10 : (8 * x - 7) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f11 : (7 * x - 8 * h - 8) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f12 : (8 * x - 9) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f13 : (8192 * x - 4096 * h - 8257) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have f14 : (8 * x - 4096 * h - 967) ≠ 0 := ne_of_lt (by nlinarith only [hl,hu,hh,hx,hsq])
  have e0 : (8 * x^2 - 8 * h - 8) * m 0 + (8 * x - 9) * m 1 + (-8 * x^2 + 8 * h + 8) * m 2 + (-8 * x + 9) * m 3 + (-8 * x^2 + 8 * h + 8) * m 13 + (-8 * x + 9) * m 14 + (8 * x^2 - 8 * h - 8) * m 15 + (8 * x - 9) * m 16 = 0 := by
    have he' := he 0
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384) * (1024 * x - 1)) * ((8 * x^2 - 8 * h - 8) * m 0 + (8 * x - 9) * m 1 + (-8 * x^2 + 8 * h + 8) * m 2 + (-8 * x + 9) * m 3 + (-8 * x^2 + 8 * h + 8) * m 13 + (-8 * x + 9) * m 14 + (8 * x^2 - 8 * h - 8) * m 15 + (8 * x - 9) * m 16) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : ((1 / 16384) : ℝ) ≠ 0) f0)
  have e1 : (x^2 - h - 1) * m 0 + (x) * m 1 + (-x^2 + h + 1) * m 4 + (-x) * m 5 + (-x^2 + h + 1) * m 13 + (-x) * m 14 + (x^2 - h - 1) * m 17 + (x) * m 18 = 0 := by
    have he' := he 1
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 2048) * (1024 * x - 1025)) * ((x^2 - h - 1) * m 0 + (x) * m 1 + (-x^2 + h + 1) * m 4 + (-x) * m 5 + (-x^2 + h + 1) * m 13 + (-x) * m 14 + (x^2 - h - 1) * m 17 + (x) * m 18) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : ((1 / 2048) : ℝ) ≠ 0) f1)
  have e2 : (128 * x^3 - 128 * x^2 - 128 * x * h - 128 * x + 128 * h + 128) * m 0 + (128 * x^2 - 128 * x - 64 * h - 1) * m 1 + (-128 * x^3 + 128 * x^2 + 128 * x * h + 128 * x - 128 * h - 128) * m 6 + (-128 * x^2 + 128 * x + 64 * h + 1) * m 7 + (-16 * x^2 + 16 * h + 16) * m 13 + (128 * x - 64 * h - 127) * m 14 + (16 * x^2 - 16 * h - 16) * m 19 + (-128 * x + 64 * h + 127) * m 20 = 0 := by
    have he' := he 2
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 256)) * ((128 * x^3 - 128 * x^2 - 128 * x * h - 128 * x + 128 * h + 128) * m 0 + (128 * x^2 - 128 * x - 64 * h - 1) * m 1 + (-128 * x^3 + 128 * x^2 + 128 * x * h + 128 * x - 128 * h - 128) * m 6 + (-128 * x^2 + 128 * x + 64 * h + 1) * m 7 + (-16 * x^2 + 16 * h + 16) * m 13 + (128 * x - 64 * h - 127) * m 14 + (16 * x^2 - 16 * h - 16) * m 19 + (-128 * x + 64 * h + 127) * m 20) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 256) : ℝ) ≠ 0)
  have e3 : (16 * x^3 - 7 * x^2 - 16 * x * h - 16 * x + 7 * h + 7) * m 0 + (16 * x^2 - 7 * x - 8 * h - 8) * m 1 + (-16 * x^3 + 7 * x^2 + 16 * x * h + 16 * x - 7 * h - 7) * m 8 + (-16 * x^2 + 7 * x + 8 * h + 8) * m 9 + (7 * x^2 - 7 * h - 7) * m 13 + (7 * x - 8 * h - 8) * m 14 + (-7 * x^2 + 7 * h + 7) * m 21 = 0 := by
    have he' := he 3
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16)) * ((16 * x^3 - 7 * x^2 - 16 * x * h - 16 * x + 7 * h + 7) * m 0 + (16 * x^2 - 7 * x - 8 * h - 8) * m 1 + (-16 * x^3 + 7 * x^2 + 16 * x * h + 16 * x - 7 * h - 7) * m 8 + (-16 * x^2 + 7 * x + 8 * h + 8) * m 9 + (7 * x^2 - 7 * h - 7) * m 13 + (7 * x - 8 * h - 8) * m 14 + (-7 * x^2 + 7 * h + 7) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16) : ℝ) ≠ 0)
  have e4 : (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 0 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 1 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 10 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 11 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 13 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 14 + (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 22 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 23 = 0 := by
    have he' := he 4
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 0 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 1 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 10 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 11 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 13 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 14 + (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 22 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e5 : (-8184 * x^2 + 8184 * h + 8184) * m 2 + (1032 * x - 4096 * h - 73) * m 3 + (8184 * x^2 - 8184 * h - 8184) * m 6 + (-1032 * x + 4096 * h + 73) * m 7 + (8192 * x^3 - 1032 * x^2 - 8192 * x * h - 8192 * x + 1032 * h + 1032) * m 15 + (8192 * x^2 - 1032 * x - 4096 * h - 8119) * m 16 + (-8192 * x^3 + 1032 * x^2 + 8192 * x * h + 8192 * x - 1032 * h - 1032) * m 19 + (-8192 * x^2 + 1032 * x + 4096 * h + 8119) * m 20 = 0 := by
    have he' := he 5
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((-8184 * x^2 + 8184 * h + 8184) * m 2 + (1032 * x - 4096 * h - 73) * m 3 + (8184 * x^2 - 8184 * h - 8184) * m 6 + (-1032 * x + 4096 * h + 73) * m 7 + (8192 * x^3 - 1032 * x^2 - 8192 * x * h - 8192 * x + 1032 * h + 1032) * m 15 + (8192 * x^2 - 1032 * x - 4096 * h - 8119) * m 16 + (-8192 * x^3 + 1032 * x^2 + 8192 * x * h + 8192 * x - 1032 * h - 1032) * m 19 + (-8192 * x^2 + 1032 * x + 4096 * h + 8119) * m 20) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e6 : (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 2 + (8192 * x^2 + 2056 * x - 8192 * h - 8201) * m 3 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 8 + (-8192 * x^2 - 2056 * x + 8192 * h + 8201) * m 9 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 15 + (-8192 * x^2 - 2056 * x + 8192 * h + 8201) * m 16 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 21 = 0 := by
    have he' := he 6
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 2 + (8192 * x^2 + 2056 * x - 8192 * h - 8201) * m 3 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 8 + (-8192 * x^2 - 2056 * x + 8192 * h + 8201) * m 9 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 15 + (-8192 * x^2 - 2056 * x + 8192 * h + 8201) * m 16 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e7 : (-4096 * x^2 + 4096 * h + 4096) * m 2 + (4096 * x - 4096 * h - 3649) * m 3 + (4096 * x^2 - 4096 * h - 4096) * m 10 + (-4096 * x + 4096 * h + 3649) * m 11 + (4096 * x^2 - 4096 * h - 4096) * m 15 + (-4096 * x + 4096 * h + 3649) * m 16 + (-4096 * x^2 + 4096 * h + 4096) * m 22 + (4096 * x - 4096 * h - 3649) * m 23 = 0 := by
    have he' := he 7
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 8192)) * ((-4096 * x^2 + 4096 * h + 4096) * m 2 + (4096 * x - 4096 * h - 3649) * m 3 + (4096 * x^2 - 4096 * h - 4096) * m 10 + (-4096 * x + 4096 * h + 3649) * m 11 + (4096 * x^2 - 4096 * h - 4096) * m 15 + (-4096 * x + 4096 * h + 3649) * m 16 + (-4096 * x^2 + 4096 * h + 4096) * m 22 + (4096 * x - 4096 * h - 3649) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 8192) : ℝ) ≠ 0)
  have e8 : (-512 * x^2 + 512 * h + 512) * m 2 + (512 * x + 447) * m 3 + (512 * x^2 - 512 * h - 512) * m 12 + (-512 * x^2 + 512 * h + 512) * m 15 + (-512 * x - 447) * m 16 = 0 := by
    have he' := he 8
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 8192)) * ((-512 * x^2 + 512 * h + 512) * m 2 + (512 * x + 447) * m 3 + (512 * x^2 - 512 * h - 512) * m 12 + (-512 * x^2 + 512 * h + 512) * m 15 + (-512 * x - 447) * m 16) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 8192) : ℝ) ≠ 0)
  have e9 : (-1) * m 3 + (1) * m 16 = 0 := by
    have he' := he 9
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 8192) * (4096 * h + 73)) * ((-1) * m 3 + (1) * m 16) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : ((1 / 8192) : ℝ) ≠ 0) f2)
  have e10 : (1024 * x^3 + 129 * x^2 - 1024 * x * h - 1024 * x - 129 * h - 129) * m 4 + (1024 * x^2 + 129 * x - 1024 * h - 1024) * m 5 + (-1024 * x^3 - 129 * x^2 + 1024 * x * h + 1024 * x + 129 * h + 129) * m 8 + (-1024 * x^2 - 129 * x + 1024 * h + 1024) * m 9 + (1024 * x^3 - 129 * x^2 - 1024 * x * h - 1024 * x + 129 * h + 129) * m 17 + (1024 * x^2 - 129 * x - 1024 * h - 1024) * m 18 + (-1024 * x^3 + 129 * x^2 + 1024 * x * h + 1024 * x - 129 * h - 129) * m 21 = 0 := by
    have he' := he 10
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 2048)) * ((1024 * x^3 + 129 * x^2 - 1024 * x * h - 1024 * x - 129 * h - 129) * m 4 + (1024 * x^2 + 129 * x - 1024 * h - 1024) * m 5 + (-1024 * x^3 - 129 * x^2 + 1024 * x * h + 1024 * x + 129 * h + 129) * m 8 + (-1024 * x^2 - 129 * x + 1024 * h + 1024) * m 9 + (1024 * x^3 - 129 * x^2 - 1024 * x * h - 1024 * x + 129 * h + 129) * m 17 + (1024 * x^2 - 129 * x - 1024 * h - 1024) * m 18 + (-1024 * x^3 + 129 * x^2 + 1024 * x * h + 1024 * x - 129 * h - 129) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 2048) : ℝ) ≠ 0)
  have e11 : (7) * m 5 + (-7) * m 11 + (-7) * m 18 + (7) * m 23 = 0 := by
    have he' := he 11
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 114688) * (7168 * x - 8192 * h - 7289)) * ((7) * m 5 + (-7) * m 11 + (-7) * m 18 + (7) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : ((1 / 114688) : ℝ) ≠ 0) f3)
  have e12 : (7168 * x^2 - 7168 * h - 7168) * m 4 + (903) * m 5 + (-7168 * x^2 + 7168 * h + 7168) * m 12 + (7168 * x^2 - 7168 * h - 7168) * m 17 + (-903) * m 18 = 0 := by
    have he' := he 12
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((7168 * x^2 - 7168 * h - 7168) * m 4 + (903) * m 5 + (-7168 * x^2 + 7168 * h + 7168) * m 12 + (7168 * x^2 - 7168 * h - 7168) * m 17 + (-903) * m 18) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e13 : (8192 * x^2 - 8192 * h - 8192) * m 4 + (-1024 * x - 8192 * h - 137) * m 5 + (8192 * x^2 - 8192 * h - 8192) * m 17 + (1024 * x + 8192 * h + 137) * m 18 = 0 := by
    have he' := he 13
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((8192 * x^2 - 8192 * h - 8192) * m 4 + (-1024 * x - 8192 * h - 137) * m 5 + (8192 * x^2 - 8192 * h - 8192) * m 17 + (1024 * x + 8192 * h + 137) * m 18) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e14 : (128 * x^3 + 16 * x^2 - 128 * x * h - 128 * x - 16 * h - 16) * m 6 + (128 * x^2 + 16 * x - 64 * h - 127) * m 7 + (-128 * x^3 - 16 * x^2 + 128 * x * h + 128 * x + 16 * h + 16) * m 8 + (-128 * x^2 - 16 * x + 64 * h + 127) * m 9 + (128 * x^2 - 128 * h - 128) * m 19 + (-16 * x - 64 * h - 1) * m 20 + (-128 * x^2 + 128 * h + 128) * m 21 = 0 := by
    have he' := he 14
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 256)) * ((128 * x^3 + 16 * x^2 - 128 * x * h - 128 * x - 16 * h - 16) * m 6 + (128 * x^2 + 16 * x - 64 * h - 127) * m 7 + (-128 * x^3 - 16 * x^2 + 128 * x * h + 128 * x + 16 * h + 16) * m 8 + (-128 * x^2 - 16 * x + 64 * h + 127) * m 9 + (128 * x^2 - 128 * h - 128) * m 19 + (-16 * x - 64 * h - 1) * m 20 + (-128 * x^2 + 128 * h + 128) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 256) : ℝ) ≠ 0)
  have e15 : (-8 * x^2 + 8 * h + 8) * m 6 + (7160 * x - 4096 * h - 7225) * m 7 + (8 * x^2 - 8 * h - 8) * m 10 + (-7160 * x + 4096 * h + 7225) * m 11 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 19 + (8192 * x^2 - 7160 * x - 4096 * h - 967) * m 20 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 22 + (-8192 * x^2 + 7160 * x + 4096 * h + 967) * m 23 = 0 := by
    have he' := he 15
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((-8 * x^2 + 8 * h + 8) * m 6 + (7160 * x - 4096 * h - 7225) * m 7 + (8 * x^2 - 8 * h - 8) * m 10 + (-7160 * x + 4096 * h + 7225) * m 11 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 19 + (8192 * x^2 - 7160 * x - 4096 * h - 967) * m 20 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 22 + (-8192 * x^2 + 7160 * x + 4096 * h + 967) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e16 : (7160 * x^2 - 7160 * h - 7160) * m 6 + (-8 * x + 4096 * h + 967) * m 7 + (-7160 * x^2 + 7160 * h + 7160) * m 12 + (-8192 * x^3 + 8 * x^2 + 8192 * x * h + 8192 * x - 8 * h - 8) * m 19 + (-8192 * x^2 + 8 * x + 4096 * h + 7225) * m 20 = 0 := by
    have he' := he 16
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((7160 * x^2 - 7160 * h - 7160) * m 6 + (-8 * x + 4096 * h + 967) * m 7 + (-7160 * x^2 + 7160 * h + 7160) * m 12 + (-8192 * x^3 + 8 * x^2 + 8192 * x * h + 8192 * x - 8 * h - 8) * m 19 + (-8192 * x^2 + 8 * x + 4096 * h + 7225) * m 20) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e17 : (8184 * x^2 - 8184 * h - 8184) * m 6 + (-1032 * x - 4096 * h - 73) * m 7 + (8192 * x^3 + 1032 * x^2 - 8192 * x * h - 8192 * x - 1032 * h - 1032) * m 19 + (8192 * x^2 + 1032 * x - 4096 * h - 8119) * m 20 = 0 := by
    have he' := he 17
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((8184 * x^2 - 8184 * h - 8184) * m 6 + (-1032 * x - 4096 * h - 73) * m 7 + (8192 * x^3 + 1032 * x^2 - 8192 * x * h - 8192 * x - 1032 * h - 1032) * m 19 + (8192 * x^2 + 1032 * x - 4096 * h - 8119) * m 20) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e18 : (-8 * x^2 + 8 * h + 8) * m 8 + (-8 * x + 7) * m 9 + (8 * x^2 - 8 * h - 8) * m 10 + (8 * x - 7) * m 11 + (8 * x^2 - 8 * h - 8) * m 21 + (-8 * x^2 + 8 * h + 8) * m 22 + (-8 * x + 7) * m 23 = 0 := by
    have he' := he 18
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384) * (1024 * x + 129)) * ((-8 * x^2 + 8 * h + 8) * m 8 + (-8 * x + 7) * m 9 + (8 * x^2 - 8 * h - 8) * m 10 + (8 * x - 7) * m 11 + (8 * x^2 - 8 * h - 8) * m 21 + (-8 * x^2 + 8 * h + 8) * m 22 + (-8 * x + 7) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : ((1 / 16384) : ℝ) ≠ 0) f4)
  have e19 : (-8192 * x^3 + 6136 * x^2 + 8192 * x * h + 8192 * x - 6136 * h - 6136) * m 8 + (-8192 * x^2 - 1032 * x + 8192 * h + 9095) * m 9 + (8192 * x^3 - 6136 * x^2 - 8192 * x * h - 8192 * x + 6136 * h + 6136) * m 12 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 21 = 0 := by
    have he' := he 19
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384)) * ((-8192 * x^3 + 6136 * x^2 + 8192 * x * h + 8192 * x - 6136 * h - 6136) * m 8 + (-8192 * x^2 - 1032 * x + 8192 * h + 9095) * m 9 + (8192 * x^3 - 6136 * x^2 - 8192 * x * h - 8192 * x + 6136 * h + 6136) * m 12 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16384) : ℝ) ≠ 0)
  have e20 : (-8 * x^2 + 8 * h + 8) * m 8 + (-8 * x - 9) * m 9 + (8 * x^2 - 8 * h - 8) * m 21 = 0 := by
    have he' := he 20
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16384) * (1024 * x - 895)) * ((-8 * x^2 + 8 * h + 8) * m 8 + (-8 * x - 9) * m 9 + (8 * x^2 - 8 * h - 8) * m 21) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : ((1 / 16384) : ℝ) ≠ 0) f5)
  have e21 : (7 * x^2 - 7 * h - 7) * m 10 + (-7 * x + 8 * h + 8) * m 11 + (-7 * x^2 + 7 * h + 7) * m 12 + (-16 * x^3 + 7 * x^2 + 16 * x * h + 16 * x - 7 * h - 7) * m 22 + (-16 * x^2 + 7 * x + 8 * h + 8) * m 23 = 0 := by
    have he' := he 21
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 16)) * ((7 * x^2 - 7 * h - 7) * m 10 + (-7 * x + 8 * h + 8) * m 11 + (-7 * x^2 + 7 * h + 7) * m 12 + (-16 * x^3 + 7 * x^2 + 16 * x * h + 16 * x - 7 * h - 7) * m 22 + (-16 * x^2 + 7 * x + 8 * h + 8) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 16) : ℝ) ≠ 0)
  have e22 : (512 * x^2 - 512 * h - 512) * m 10 + (-512 * x + 447) * m 11 + (512 * x^2 - 512 * h - 512) * m 22 + (512 * x - 447) * m 23 = 0 := by
    have he' := he 22
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    have hc : ((1 / 1024)) * ((512 * x^2 - 512 * h - 512) * m 10 + (-512 * x + 447) * m 11 + (512 * x^2 - 512 * h - 512) * m 22 + (512 * x - 447) * m 23) = 0 := by linear_combination he'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : ((1 / 1024) : ℝ) ≠ 0)
  have e23 : (1) * m 12 = 0 := by
    have he' := he 23
    norm_num [edgeDerivative, edgePeriod, stripPoint, intrinsicPoint,
      translatePoint, halfLengthDerivative, FoldedMotion, IntrinsicMotion] at he'
    simpa using he'.resolve_left (fun hz => f6 (by linarith only [hz]))
  have e8_0 : (-512 * x^2 + 512 * h + 512) * m 2 + (512 * x + 447) * m 3 + (-512 * x^2 + 512 * h + 512) * m 15 + (-512 * x - 447) * m 16 = 0 := by
    have hc : (1) * ((-512 * x^2 + 512 * h + 512) * m 2 + (512 * x + 447) * m 3 + (-512 * x^2 + 512 * h + 512) * m 15 + (-512 * x - 447) * m 16) = 0 := by
      linear_combination (1) * e8 - (512 * x^2 - 512 * h - 512) * e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e12_0 : (1024 * x^2 - 1024 * h - 1024) * m 4 + (129) * m 5 + (1024 * x^2 - 1024 * h - 1024) * m 17 + (-129) * m 18 = 0 := by
    have hc : (7) * ((1024 * x^2 - 1024 * h - 1024) * m 4 + (129) * m 5 + (1024 * x^2 - 1024 * h - 1024) * m 17 + (-129) * m 18) = 0 := by
      linear_combination (1) * e12 - (-7168 * x^2 + 7168 * h + 7168) * e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (7 : ℝ) ≠ 0)
  have e16_0 : (7160 * x^2 - 7160 * h - 7160) * m 6 + (-8 * x + 4096 * h + 967) * m 7 + (-8192 * x^3 + 8 * x^2 + 8192 * x * h + 8192 * x - 8 * h - 8) * m 19 + (-8192 * x^2 + 8 * x + 4096 * h + 7225) * m 20 = 0 := by
    have hc : (1) * ((7160 * x^2 - 7160 * h - 7160) * m 6 + (-8 * x + 4096 * h + 967) * m 7 + (-8192 * x^3 + 8 * x^2 + 8192 * x * h + 8192 * x - 8 * h - 8) * m 19 + (-8192 * x^2 + 8 * x + 4096 * h + 7225) * m 20) = 0 := by
      linear_combination (1) * e16 - (-7160 * x^2 + 7160 * h + 7160) * e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e19_0 : (-8192 * x^3 + 6136 * x^2 + 8192 * x * h + 8192 * x - 6136 * h - 6136) * m 8 + (-8192 * x^2 - 1032 * x + 8192 * h + 9095) * m 9 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 21 = 0 := by
    have hc : (1) * ((-8192 * x^3 + 6136 * x^2 + 8192 * x * h + 8192 * x - 6136 * h - 6136) * m 8 + (-8192 * x^2 - 1032 * x + 8192 * h + 9095) * m 9 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 21) = 0 := by
      linear_combination (1) * e19 - (8192 * x^3 - 6136 * x^2 - 8192 * x * h - 8192 * x + 6136 * h + 6136) * e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e21_0 : (7 * x^2 - 7 * h - 7) * m 10 + (-7 * x + 8 * h + 8) * m 11 + (-16 * x^3 + 7 * x^2 + 16 * x * h + 16 * x - 7 * h - 7) * m 22 + (-16 * x^2 + 7 * x + 8 * h + 8) * m 23 = 0 := by
    have hc : (1) * ((7 * x^2 - 7 * h - 7) * m 10 + (-7 * x + 8 * h + 8) * m 11 + (-16 * x^3 + 7 * x^2 + 16 * x * h + 16 * x - 7 * h - 7) * m 22 + (-16 * x^2 + 7 * x + 8 * h + 8) * m 23) = 0 := by
      linear_combination (1) * e21 - (-7 * x^2 + 7 * h + 7) * e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e0_1 : (8 * x^2 - 8 * h - 8) * m 0 + (8 * x - 9) * m 1 + (-8 * x^2 + 8 * h + 8) * m 2 + (-8 * x^2 + 8 * h + 8) * m 13 + (-8 * x + 9) * m 14 + (8 * x^2 - 8 * h - 8) * m 15 = 0 := by
    have hc : (1) * ((8 * x^2 - 8 * h - 8) * m 0 + (8 * x - 9) * m 1 + (-8 * x^2 + 8 * h + 8) * m 2 + (-8 * x^2 + 8 * h + 8) * m 13 + (-8 * x + 9) * m 14 + (8 * x^2 - 8 * h - 8) * m 15) = 0 := by
      linear_combination (1) * e0 - (8 * x - 9) * e9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e5_1 : (-8184 * x^2 + 8184 * h + 8184) * m 2 + (8192 * x^2 - 8192 * h - 8192) * m 3 + (8184 * x^2 - 8184 * h - 8184) * m 6 + (-1032 * x + 4096 * h + 73) * m 7 + (8192 * x^3 - 1032 * x^2 - 8192 * x * h - 8192 * x + 1032 * h + 1032) * m 15 + (-8192 * x^3 + 1032 * x^2 + 8192 * x * h + 8192 * x - 1032 * h - 1032) * m 19 + (-8192 * x^2 + 1032 * x + 4096 * h + 8119) * m 20 = 0 := by
    have hc : (1) * ((-8184 * x^2 + 8184 * h + 8184) * m 2 + (8192 * x^2 - 8192 * h - 8192) * m 3 + (8184 * x^2 - 8184 * h - 8184) * m 6 + (-1032 * x + 4096 * h + 73) * m 7 + (8192 * x^3 - 1032 * x^2 - 8192 * x * h - 8192 * x + 1032 * h + 1032) * m 15 + (-8192 * x^3 + 1032 * x^2 + 8192 * x * h + 8192 * x - 1032 * h - 1032) * m 19 + (-8192 * x^2 + 1032 * x + 4096 * h + 8119) * m 20) = 0 := by
      linear_combination (1) * e5 - (8192 * x^2 - 1032 * x - 4096 * h - 8119) * e9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e6_1 : (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 2 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 8 + (-8192 * x^2 - 2056 * x + 8192 * h + 8201) * m 9 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 15 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 21 = 0 := by
    have hc : (1) * ((8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 2 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 8 + (-8192 * x^2 - 2056 * x + 8192 * h + 8201) * m 9 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 15 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 21) = 0 := by
      linear_combination (1) * e6 - (-8192 * x^2 - 2056 * x + 8192 * h + 8201) * e9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e7_1 : (-4096 * x^2 + 4096 * h + 4096) * m 2 + (4096 * x^2 - 4096 * h - 4096) * m 10 + (-4096 * x + 4096 * h + 3649) * m 11 + (4096 * x^2 - 4096 * h - 4096) * m 15 + (-4096 * x^2 + 4096 * h + 4096) * m 22 + (4096 * x - 4096 * h - 3649) * m 23 = 0 := by
    have hc : (1) * ((-4096 * x^2 + 4096 * h + 4096) * m 2 + (4096 * x^2 - 4096 * h - 4096) * m 10 + (-4096 * x + 4096 * h + 3649) * m 11 + (4096 * x^2 - 4096 * h - 4096) * m 15 + (-4096 * x^2 + 4096 * h + 4096) * m 22 + (4096 * x - 4096 * h - 3649) * m 23) = 0 := by
      linear_combination (1) * e7 - (-4096 * x + 4096 * h + 3649) * e9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e8_1 : (-1) * m 2 + (-1) * m 15 = 0 := by
    have hc : (512 * (x^2 - h - 1)) * ((-1) * m 2 + (-1) * m 15) = 0 := by
      linear_combination (1) * e8_0 - (-512 * x - 447) * e9
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (512 : ℝ) ≠ 0) f6)
  have e0_3 : (-8 * x^2 + 8 * h + 8) * m 0 + (-8 * x + 9) * m 1 + (8 * x^2 - 8 * h - 8) * m 13 + (8 * x - 9) * m 14 + (-16 * x^2 + 16 * h + 16) * m 15 = 0 := by
    have hc : (1) * ((-8 * x^2 + 8 * h + 8) * m 0 + (-8 * x + 9) * m 1 + (8 * x^2 - 8 * h - 8) * m 13 + (8 * x - 9) * m 14 + (-16 * x^2 + 16 * h + 16) * m 15) = 0 := by
      linear_combination (-1) * e0_1 - (-8 * x^2 + 8 * h + 8) * e8_1
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e6_3 : (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 8 + (8192 * x^2 + 2056 * x - 8192 * h - 8201) * m 9 + (16384 * x^3 - 14320 * x^2 - 16384 * x * h - 16384 * x + 14320 * h + 14320) * m 15 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 21 = 0 := by
    have hc : (1) * ((8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 8 + (8192 * x^2 + 2056 * x - 8192 * h - 8201) * m 9 + (16384 * x^3 - 14320 * x^2 - 16384 * x * h - 16384 * x + 14320 * h + 14320) * m 15 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 21) = 0 := by
      linear_combination (-1) * e6_1 - (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * e8_1
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e7_3 : (-4096 * x^2 + 4096 * h + 4096) * m 10 + (4096 * x - 4096 * h - 3649) * m 11 + (-8192 * x^2 + 8192 * h + 8192) * m 15 + (4096 * x^2 - 4096 * h - 4096) * m 22 + (-4096 * x + 4096 * h + 3649) * m 23 = 0 := by
    have hc : (1) * ((-4096 * x^2 + 4096 * h + 4096) * m 10 + (4096 * x - 4096 * h - 3649) * m 11 + (-8192 * x^2 + 8192 * h + 8192) * m 15 + (4096 * x^2 - 4096 * h - 4096) * m 22 + (-4096 * x + 4096 * h + 3649) * m 23) = 0 := by
      linear_combination (-1) * e7_1 - (-4096 * x^2 + 4096 * h + 4096) * e8_1
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e0_4 : (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 0 + (-8192 * x^2 + 16376 * x - 8055) * m 1 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 8 + (8192 * x^2 + 2056 * x - 8192 * h - 8201) * m 9 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 13 + (8192 * x^2 - 16376 * x + 8055) * m 14 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 21 = 0 := by
    have hc : (16 * (x^2 - h - 1)) * ((-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 0 + (-8192 * x^2 + 16376 * x - 8055) * m 1 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 8 + (8192 * x^2 + 2056 * x - 8192 * h - 8201) * m 9 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 13 + (8192 * x^2 - 16376 * x + 8055) * m 14 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 21) = 0 := by
      linear_combination (16384 * x^3 - 14320 * x^2 - 16384 * x * h - 16384 * x + 14320 * h + 14320) * e0_3 - (-16 * x^2 + 16 * h + 16) * e6_3
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) f6)
  have e7_4 : (4194304 * x^3 - 3665920 * x^2 - 4194304 * x * h - 4194304 * x + 3665920 * h + 3665920) * m 8 + (4194304 * x^2 + 1052672 * x - 4194304 * h - 4198912) * m 9 + (-4194304 * x^3 + 3665920 * x^2 + 4194304 * x * h + 4194304 * x - 3665920 * h - 3665920) * m 10 + (4194304 * x^2 - 4194304 * x * h - 7402496 * x + 3665920 * h + 3265855) * m 11 + (-4194304 * x^3 + 3665920 * x^2 + 4194304 * x * h + 4194304 * x - 3665920 * h - 3665920) * m 21 + (4194304 * x^3 - 3665920 * x^2 - 4194304 * x * h - 4194304 * x + 3665920 * h + 3665920) * m 22 + (-4194304 * x^2 + 4194304 * x * h + 7402496 * x - 3665920 * h - 3265855) * m 23 = 0 := by
    have hc : (16 * (x^2 - h - 1)) * ((4194304 * x^3 - 3665920 * x^2 - 4194304 * x * h - 4194304 * x + 3665920 * h + 3665920) * m 8 + (4194304 * x^2 + 1052672 * x - 4194304 * h - 4198912) * m 9 + (-4194304 * x^3 + 3665920 * x^2 + 4194304 * x * h + 4194304 * x - 3665920 * h - 3665920) * m 10 + (4194304 * x^2 - 4194304 * x * h - 7402496 * x + 3665920 * h + 3265855) * m 11 + (-4194304 * x^3 + 3665920 * x^2 + 4194304 * x * h + 4194304 * x - 3665920 * h - 3665920) * m 21 + (4194304 * x^3 - 3665920 * x^2 - 4194304 * x * h - 4194304 * x + 3665920 * h + 3665920) * m 22 + (-4194304 * x^2 + 4194304 * x * h + 7402496 * x - 3665920 * h - 3265855) * m 23) = 0 := by
      linear_combination (16384 * x^3 - 14320 * x^2 - 16384 * x * h - 16384 * x + 14320 * h + 14320) * e7_3 - (-8192 * x^2 + 8192 * h + 8192) * e6_3
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) f6)
  have e1_5 : (8192 * x^2 - 8192 * h - 8192) * m 0 + (8192 * x) * m 1 + (-9216 * x - 8192 * h - 137) * m 5 + (-8192 * x^2 + 8192 * h + 8192) * m 13 + (-8192 * x) * m 14 + (16384 * x^2 - 16384 * h - 16384) * m 17 + (9216 * x + 8192 * h + 137) * m 18 = 0 := by
    have hc : ((x^2 - h - 1)) * ((8192 * x^2 - 8192 * h - 8192) * m 0 + (8192 * x) * m 1 + (-9216 * x - 8192 * h - 137) * m 5 + (-8192 * x^2 + 8192 * h + 8192) * m 13 + (-8192 * x) * m 14 + (16384 * x^2 - 16384 * h - 16384) * m 17 + (9216 * x + 8192 * h + 137) * m 18) = 0 := by
      linear_combination (8192 * x^2 - 8192 * h - 8192) * e1 - (-x^2 + h + 1) * e13
    exact (mul_eq_zero.mp hc).resolve_left f6
  have e10_5 : (9437184 * x^2 + 8388608 * x * h + 1329152 * x - 7331840 * h - 8370935) * m 5 + (-8388608 * x^3 - 1056768 * x^2 + 8388608 * x * h + 8388608 * x + 1056768 * h + 1056768) * m 8 + (-8388608 * x^2 - 1056768 * x + 8388608 * h + 8388608) * m 9 + (-2113536 * x^2 + 2113536 * h + 2113536) * m 17 + (7340032 * x^2 - 8388608 * x * h - 1329152 * x - 9445376 * h - 8406281) * m 18 + (-8388608 * x^3 + 1056768 * x^2 + 8388608 * x * h + 8388608 * x - 1056768 * h - 1056768) * m 21 = 0 := by
    have hc : ((x^2 - h - 1)) * ((9437184 * x^2 + 8388608 * x * h + 1329152 * x - 7331840 * h - 8370935) * m 5 + (-8388608 * x^3 - 1056768 * x^2 + 8388608 * x * h + 8388608 * x + 1056768 * h + 1056768) * m 8 + (-8388608 * x^2 - 1056768 * x + 8388608 * h + 8388608) * m 9 + (-2113536 * x^2 + 2113536 * h + 2113536) * m 17 + (7340032 * x^2 - 8388608 * x * h - 1329152 * x - 9445376 * h - 8406281) * m 18 + (-8388608 * x^3 + 1056768 * x^2 + 8388608 * x * h + 8388608 * x - 1056768 * h - 1056768) * m 21) = 0 := by
      linear_combination (8192 * x^2 - 8192 * h - 8192) * e10 - (1024 * x^3 + 129 * x^2 - 1024 * x * h - 1024 * x - 129 * h - 129) * e13
    exact (mul_eq_zero.mp hc).resolve_left f6
  have e12_5 : (-1) * m 5 + (1) * m 18 = 0 := by
    have hc : (-1024 * (1024 * x + 8192 * h + 1169) * (x^2 - h - 1)) * ((-1) * m 5 + (1) * m 18) = 0 := by
      linear_combination (8192 * x^2 - 8192 * h - 8192) * e12_0 - (1024 * x^2 - 1024 * h - 1024) * e13
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (-1024 : ℝ) ≠ 0) f7) f6)
  have e1_6 : (-x^2 + h + 1) * m 0 + (-x) * m 1 + (x^2 - h - 1) * m 13 + (x) * m 14 + (-2 * x^2 + 2 * h + 2) * m 17 = 0 := by
    have hc : (8192) * ((-x^2 + h + 1) * m 0 + (-x) * m 1 + (x^2 - h - 1) * m 13 + (x) * m 14 + (-2 * x^2 + 2 * h + 2) * m 17) = 0 := by
      linear_combination (-1) * e1_5 - (-9216 * x - 8192 * h - 137) * e12_5
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (8192 : ℝ) ≠ 0)
  have e10_6 : (1024 * x^3 + 129 * x^2 - 1024 * x * h - 1024 * x - 129 * h - 129) * m 8 + (1024 * x^2 + 129 * x - 1024 * h - 1024) * m 9 + (258 * x^2 - 258 * h - 258) * m 17 + (-2048 * x^2 + 2048 * h + 2048) * m 18 + (1024 * x^3 - 129 * x^2 - 1024 * x * h - 1024 * x + 129 * h + 129) * m 21 = 0 := by
    have hc : (8192) * ((1024 * x^3 + 129 * x^2 - 1024 * x * h - 1024 * x - 129 * h - 129) * m 8 + (1024 * x^2 + 129 * x - 1024 * h - 1024) * m 9 + (258 * x^2 - 258 * h - 258) * m 17 + (-2048 * x^2 + 2048 * h + 2048) * m 18 + (1024 * x^3 - 129 * x^2 - 1024 * x * h - 1024 * x + 129 * h + 129) * m 21) = 0 := by
      linear_combination (-1) * e10_5 - (9437184 * x^2 + 8388608 * x * h + 1329152 * x - 7331840 * h - 8370935) * e12_5
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (8192 : ℝ) ≠ 0)
  have e11_6 : (1) * m 11 + (-1) * m 23 = 0 := by
    have hc : (7) * ((1) * m 11 + (-1) * m 23) = 0 := by
      linear_combination (-1) * e11 - (7) * e12_5
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (7 : ℝ) ≠ 0)
  have e4_9 : (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 0 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 1 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 10 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 13 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 14 + (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 22 = 0 := by
    have hc : (1) * ((8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 0 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 1 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 10 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 13 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 14 + (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 22) = 0 := by
      linear_combination (1) * e4 - (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e7_9 : (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 8 + (8192 * x^2 + 2056 * x - 8192 * h - 8201) * m 9 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 10 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 21 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 22 = 0 := by
    have hc : (512) * ((8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 8 + (8192 * x^2 + 2056 * x - 8192 * h - 8201) * m 9 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 10 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 21 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 22) = 0 := by
      linear_combination (1) * e7_4 - (4194304 * x^2 - 4194304 * x * h - 7402496 * x + 3665920 * h + 3265855) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (512 : ℝ) ≠ 0)
  have e15_9 : (-8 * x^2 + 8 * h + 8) * m 6 + (7160 * x - 4096 * h - 7225) * m 7 + (8 * x^2 - 8 * h - 8) * m 10 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 19 + (8192 * x^2 - 7160 * x - 4096 * h - 967) * m 20 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 22 + (-8192 * x^2 + 8192 * h + 8192) * m 23 = 0 := by
    have hc : (1) * ((-8 * x^2 + 8 * h + 8) * m 6 + (7160 * x - 4096 * h - 7225) * m 7 + (8 * x^2 - 8 * h - 8) * m 10 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 19 + (8192 * x^2 - 7160 * x - 4096 * h - 967) * m 20 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 22 + (-8192 * x^2 + 8192 * h + 8192) * m 23) = 0 := by
      linear_combination (1) * e15 - (-7160 * x + 4096 * h + 7225) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e18_9 : (-8 * x^2 + 8 * h + 8) * m 8 + (-8 * x + 7) * m 9 + (8 * x^2 - 8 * h - 8) * m 10 + (8 * x^2 - 8 * h - 8) * m 21 + (-8 * x^2 + 8 * h + 8) * m 22 = 0 := by
    have hc : (1) * ((-8 * x^2 + 8 * h + 8) * m 8 + (-8 * x + 7) * m 9 + (8 * x^2 - 8 * h - 8) * m 10 + (8 * x^2 - 8 * h - 8) * m 21 + (-8 * x^2 + 8 * h + 8) * m 22) = 0 := by
      linear_combination (1) * e18 - (8 * x - 7) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e21_9 : (7) * m 10 + (-16 * x + 7) * m 22 + (-16) * m 23 = 0 := by
    have hc : ((x^2 - h - 1)) * ((7) * m 10 + (-16 * x + 7) * m 22 + (-16) * m 23) = 0 := by
      linear_combination (1) * e21_0 - (-7 * x + 8 * h + 8) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left f6
  have e22_9 : (1) * m 10 + (1) * m 22 = 0 := by
    have hc : (512 * (x^2 - h - 1)) * ((1) * m 10 + (1) * m 22) = 0 := by
      linear_combination (1) * e22 - (-512 * x + 447) * e11_6
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (512 : ℝ) ≠ 0) f6)
  have e15_10 : (8 * x^2 - 8 * h - 8) * m 6 + (-7160 * x + 4096 * h + 7225) * m 7 + (3576 * x^2 - 3576 * h - 3576) * m 10 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 19 + (-8192 * x^2 + 7160 * x + 4096 * h + 967) * m 20 + (-3576 * x^2 + 3576 * h + 3576) * m 22 = 0 := by
    have hc : (16) * ((8 * x^2 - 8 * h - 8) * m 6 + (-7160 * x + 4096 * h + 7225) * m 7 + (3576 * x^2 - 3576 * h - 3576) * m 10 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 19 + (-8192 * x^2 + 7160 * x + 4096 * h + 967) * m 20 + (-3576 * x^2 + 3576 * h + 3576) * m 22) = 0 := by
      linear_combination (-16) * e15_9 - (-8192 * x^2 + 8192 * h + 8192) * e21_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (16 : ℝ) ≠ 0)
  have e4_11 : (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 0 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 1 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 13 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 14 + (16384 * x^3 - 16400 * x^2 - 16384 * x * h - 16384 * x + 16400 * h + 16400) * m 22 = 0 := by
    have hc : (1) * ((8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 0 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 1 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 13 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 14 + (16384 * x^3 - 16400 * x^2 - 16384 * x * h - 16384 * x + 16400 * h + 16400) * m 22) = 0 := by
      linear_combination (1) * e4_9 - (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * e22_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e7_11 : (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 8 + (8192 * x^2 + 2056 * x - 8192 * h - 8201) * m 9 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 21 + (16384 * x^3 - 14320 * x^2 - 16384 * x * h - 16384 * x + 14320 * h + 14320) * m 22 = 0 := by
    have hc : (1) * ((8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 8 + (8192 * x^2 + 2056 * x - 8192 * h - 8201) * m 9 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 21 + (16384 * x^3 - 14320 * x^2 - 16384 * x * h - 16384 * x + 14320 * h + 14320) * m 22) = 0 := by
      linear_combination (1) * e7_9 - (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * e22_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e15_11 : (8 * x^2 - 8 * h - 8) * m 6 + (-7160 * x + 4096 * h + 7225) * m 7 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 19 + (-8192 * x^2 + 7160 * x + 4096 * h + 967) * m 20 + (-7152 * x^2 + 7152 * h + 7152) * m 22 = 0 := by
    have hc : (1) * ((8 * x^2 - 8 * h - 8) * m 6 + (-7160 * x + 4096 * h + 7225) * m 7 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 19 + (-8192 * x^2 + 7160 * x + 4096 * h + 967) * m 20 + (-7152 * x^2 + 7152 * h + 7152) * m 22) = 0 := by
      linear_combination (1) * e15_10 - (3576 * x^2 - 3576 * h - 3576) * e22_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e18_11 : (-8 * x^2 + 8 * h + 8) * m 8 + (-8 * x + 7) * m 9 + (8 * x^2 - 8 * h - 8) * m 21 + (-16 * x^2 + 16 * h + 16) * m 22 = 0 := by
    have hc : (1) * ((-8 * x^2 + 8 * h + 8) * m 8 + (-8 * x + 7) * m 9 + (8 * x^2 - 8 * h - 8) * m 21 + (-16 * x^2 + 16 * h + 16) * m 22) = 0 := by
      linear_combination (1) * e18_9 - (8 * x^2 - 8 * h - 8) * e22_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e4_12 : (8388608 * x^4 - 15728640 * x^3 - 8388608 * x^2 * h - 1049608 * x^2 + 15728640 * x * h + 15728640 * x - 7339000 * h - 7339000) * m 0 + (8388608 * x^3 - 8388608 * x^2 - 8388608 * x * h - 6540296 * x + 7331840 * h + 6523655) * m 1 + (-8388608 * x^4 + 15728640 * x^3 + 8388608 * x^2 * h + 1049608 * x^2 - 15728640 * x * h - 15728640 * x + 7339000 * h + 7339000) * m 8 + (-8388608 * x^3 + 6291456 * x^2 + 8388608 * x * h + 10505224 * x - 8396800 * h - 8406025) * m 9 + (-8388608 * x^4 + 15728640 * x^3 + 8388608 * x^2 * h + 1049608 * x^2 - 15728640 * x * h - 15728640 * x + 7339000 * h + 7339000) * m 13 + (-8388608 * x^3 + 8388608 * x^2 + 8388608 * x * h + 6540296 * x - 7331840 * h - 6523655) * m 14 + (8388608 * x^4 - 15728640 * x^3 - 8388608 * x^2 * h - 1049608 * x^2 + 15728640 * x * h + 15728640 * x - 7339000 * h - 7339000) * m 21 = 0 := by
    have hc : (16 * (x^2 - h - 1)) * ((8388608 * x^4 - 15728640 * x^3 - 8388608 * x^2 * h - 1049608 * x^2 + 15728640 * x * h + 15728640 * x - 7339000 * h - 7339000) * m 0 + (8388608 * x^3 - 8388608 * x^2 - 8388608 * x * h - 6540296 * x + 7331840 * h + 6523655) * m 1 + (-8388608 * x^4 + 15728640 * x^3 + 8388608 * x^2 * h + 1049608 * x^2 - 15728640 * x * h - 15728640 * x + 7339000 * h + 7339000) * m 8 + (-8388608 * x^3 + 6291456 * x^2 + 8388608 * x * h + 10505224 * x - 8396800 * h - 8406025) * m 9 + (-8388608 * x^4 + 15728640 * x^3 + 8388608 * x^2 * h + 1049608 * x^2 - 15728640 * x * h - 15728640 * x + 7339000 * h + 7339000) * m 13 + (-8388608 * x^3 + 8388608 * x^2 + 8388608 * x * h + 6540296 * x - 7331840 * h - 6523655) * m 14 + (8388608 * x^4 - 15728640 * x^3 - 8388608 * x^2 * h - 1049608 * x^2 + 15728640 * x * h + 15728640 * x - 7339000 * h - 7339000) * m 21) = 0 := by
      linear_combination (16384 * x^3 - 14320 * x^2 - 16384 * x * h - 16384 * x + 14320 * h + 14320) * e4_11 - (16384 * x^3 - 16400 * x^2 - 16384 * x * h - 16384 * x + 16400 * h + 16400) * e7_11
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) f6)
  have e15_12 : (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 6 + (-7331840 * x^2 + 4194304 * x * h + 13806600 * x - 3665920 * h - 6466375) * m 7 + (3661824 * x^3 - 3200520 * x^2 - 3661824 * x * h - 3661824 * x + 3200520 * h + 3200520) * m 8 + (3661824 * x^2 + 919032 * x - 3661824 * h - 3665847) * m 9 + (-8388608 * x^4 + 14663680 * x^3 + 8388608 * x^2 * h + 1980408 * x^2 - 14663680 * x * h - 14663680 * x + 6408200 * h + 6408200) * m 19 + (-8388608 * x^3 + 14663680 * x^2 + 4194304 * x * h - 5417992 * x - 3665920 * h - 865465) * m 20 + (-3661824 * x^3 + 3200520 * x^2 + 3661824 * x * h + 3661824 * x - 3200520 * h - 3200520) * m 21 = 0 := by
    have hc : (16 * (x^2 - h - 1)) * ((8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 6 + (-7331840 * x^2 + 4194304 * x * h + 13806600 * x - 3665920 * h - 6466375) * m 7 + (3661824 * x^3 - 3200520 * x^2 - 3661824 * x * h - 3661824 * x + 3200520 * h + 3200520) * m 8 + (3661824 * x^2 + 919032 * x - 3661824 * h - 3665847) * m 9 + (-8388608 * x^4 + 14663680 * x^3 + 8388608 * x^2 * h + 1980408 * x^2 - 14663680 * x * h - 14663680 * x + 6408200 * h + 6408200) * m 19 + (-8388608 * x^3 + 14663680 * x^2 + 4194304 * x * h - 5417992 * x - 3665920 * h - 865465) * m 20 + (-3661824 * x^3 + 3200520 * x^2 + 3661824 * x * h + 3661824 * x - 3200520 * h - 3200520) * m 21) = 0 := by
      linear_combination (16384 * x^3 - 14320 * x^2 - 16384 * x * h - 16384 * x + 14320 * h + 14320) * e15_11 - (-7152 * x^2 + 7152 * h + 7152) * e7_11
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) f6)
  have e18_12 : (1) * m 9 = 0 := by
    have hc : (32 * (8192 * x - 4096 * h - 7233) * (x^2 - h - 1)) * ((1) * m 9) = 0 := by
      linear_combination (16384 * x^3 - 14320 * x^2 - 16384 * x * h - 16384 * x + 14320 * h + 14320) * e18_11 - (-16 * x^2 + 16 * h + 16) * e7_11
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (32 : ℝ) ≠ 0) f8) f6)
  have e0_13 : (-8 * x^2 + 8 * h + 8) * m 0 + (-8 * x + 9) * m 1 + (8 * x^2 - 8 * h - 8) * m 8 + (8 * x^2 - 8 * h - 8) * m 13 + (8 * x - 9) * m 14 + (-8 * x^2 + 8 * h + 8) * m 21 = 0 := by
    have hc : ((1024 * x - 895)) * ((-8 * x^2 + 8 * h + 8) * m 0 + (-8 * x + 9) * m 1 + (8 * x^2 - 8 * h - 8) * m 8 + (8 * x^2 - 8 * h - 8) * m 13 + (8 * x - 9) * m 14 + (-8 * x^2 + 8 * h + 8) * m 21) = 0 := by
      linear_combination (1) * e0_4 - (8192 * x^2 + 2056 * x - 8192 * h - 8201) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left f5
  have e3_13 : (16 * x^3 - 7 * x^2 - 16 * x * h - 16 * x + 7 * h + 7) * m 0 + (16 * x^2 - 7 * x - 8 * h - 8) * m 1 + (-16 * x^3 + 7 * x^2 + 16 * x * h + 16 * x - 7 * h - 7) * m 8 + (7 * x^2 - 7 * h - 7) * m 13 + (7 * x - 8 * h - 8) * m 14 + (-7 * x^2 + 7 * h + 7) * m 21 = 0 := by
    have hc : (1) * ((16 * x^3 - 7 * x^2 - 16 * x * h - 16 * x + 7 * h + 7) * m 0 + (16 * x^2 - 7 * x - 8 * h - 8) * m 1 + (-16 * x^3 + 7 * x^2 + 16 * x * h + 16 * x - 7 * h - 7) * m 8 + (7 * x^2 - 7 * h - 7) * m 13 + (7 * x - 8 * h - 8) * m 14 + (-7 * x^2 + 7 * h + 7) * m 21) = 0 := by
      linear_combination (1) * e3 - (-16 * x^2 + 7 * x + 8 * h + 8) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e4_13 : (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 0 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 1 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 8 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 13 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 14 + (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 21 = 0 := by
    have hc : ((1024 * x - 895)) * ((8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 0 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 1 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 8 + (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 13 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 14 + (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 21) = 0 := by
      linear_combination (1) * e4_12 - (-8388608 * x^3 + 6291456 * x^2 + 8388608 * x * h + 10505224 * x - 8396800 * h - 8406025) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left f5
  have e14_13 : (128 * x^3 + 16 * x^2 - 128 * x * h - 128 * x - 16 * h - 16) * m 6 + (128 * x^2 + 16 * x - 64 * h - 127) * m 7 + (-128 * x^3 - 16 * x^2 + 128 * x * h + 128 * x + 16 * h + 16) * m 8 + (128 * x^2 - 128 * h - 128) * m 19 + (-16 * x - 64 * h - 1) * m 20 + (-128 * x^2 + 128 * h + 128) * m 21 = 0 := by
    have hc : (1) * ((128 * x^3 + 16 * x^2 - 128 * x * h - 128 * x - 16 * h - 16) * m 6 + (128 * x^2 + 16 * x - 64 * h - 127) * m 7 + (-128 * x^3 - 16 * x^2 + 128 * x * h + 128 * x + 16 * h + 16) * m 8 + (128 * x^2 - 128 * h - 128) * m 19 + (-16 * x - 64 * h - 1) * m 20 + (-128 * x^2 + 128 * h + 128) * m 21) = 0 := by
      linear_combination (1) * e14 - (-128 * x^2 - 16 * x + 64 * h + 127) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e15_13 : (8 * x^2 - 8 * h - 8) * m 6 + (-7160 * x + 4096 * h + 7225) * m 7 + (3576 * x^2 - 3576 * h - 3576) * m 8 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 19 + (-8192 * x^2 + 7160 * x + 4096 * h + 967) * m 20 + (-3576 * x^2 + 3576 * h + 3576) * m 21 = 0 := by
    have hc : ((1024 * x - 895)) * ((8 * x^2 - 8 * h - 8) * m 6 + (-7160 * x + 4096 * h + 7225) * m 7 + (3576 * x^2 - 3576 * h - 3576) * m 8 + (-8192 * x^3 + 7160 * x^2 + 8192 * x * h + 8192 * x - 7160 * h - 7160) * m 19 + (-8192 * x^2 + 7160 * x + 4096 * h + 967) * m 20 + (-3576 * x^2 + 3576 * h + 3576) * m 21) = 0 := by
      linear_combination (1) * e15_12 - (3661824 * x^2 + 919032 * x - 3661824 * h - 3665847) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left f5
  have e19_13 : (-1024 * x + 767) * m 8 + (-1024 * x + 1025) * m 21 = 0 := by
    have hc : (8 * (x^2 - h - 1)) * ((-1024 * x + 767) * m 8 + (-1024 * x + 1025) * m 21) = 0 := by
      linear_combination (1) * e19_0 - (-8192 * x^2 - 1032 * x + 8192 * h + 9095) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) f6)
  have e20_13 : (-1) * m 8 + (1) * m 21 = 0 := by
    have hc : (8 * (x^2 - h - 1)) * ((-1) * m 8 + (1) * m 21) = 0 := by
      linear_combination (1) * e20 - (-8 * x - 9) * e18_12
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) f6)
  have e0_14 : (8192 * x^3 - 6136 * x^2 - 8192 * x * h - 8192 * x + 6136 * h + 6136) * m 0 + (8192 * x^2 - 15352 * x + 6903) * m 1 + (-8192 * x^3 + 6136 * x^2 + 8192 * x * h + 8192 * x - 6136 * h - 6136) * m 13 + (-8192 * x^2 + 15352 * x - 6903) * m 14 + (16384 * x^3 - 14336 * x^2 - 16384 * x * h - 16384 * x + 14336 * h + 14336) * m 21 = 0 := by
    have hc : (1) * ((8192 * x^3 - 6136 * x^2 - 8192 * x * h - 8192 * x + 6136 * h + 6136) * m 0 + (8192 * x^2 - 15352 * x + 6903) * m 1 + (-8192 * x^3 + 6136 * x^2 + 8192 * x * h + 8192 * x - 6136 * h - 6136) * m 13 + (-8192 * x^2 + 15352 * x - 6903) * m 14 + (16384 * x^3 - 14336 * x^2 - 16384 * x * h - 16384 * x + 14336 * h + 14336) * m 21) = 0 := by
      linear_combination (-1024 * x + 767) * e0_13 - (8 * x^2 - 8 * h - 8) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e3_14 : (-16384 * x^4 + 19440 * x^3 + 16384 * x^2 * h + 11015 * x^2 - 19440 * x * h - 19440 * x + 5369 * h + 5369) * m 0 + (-16384 * x^3 + 19440 * x^2 + 8192 * x * h + 2823 * x - 6136 * h - 6136) * m 1 + (-7168 * x^3 + 5369 * x^2 + 7168 * x * h + 7168 * x - 5369 * h - 5369) * m 13 + (-7168 * x^2 + 8192 * x * h + 13561 * x - 6136 * h - 6136) * m 14 + (-16384 * x^4 + 30736 * x^3 + 16384 * x^2 * h + 3840 * x^2 - 30736 * x * h - 30736 * x + 12544 * h + 12544) * m 21 = 0 := by
    have hc : (1) * ((-16384 * x^4 + 19440 * x^3 + 16384 * x^2 * h + 11015 * x^2 - 19440 * x * h - 19440 * x + 5369 * h + 5369) * m 0 + (-16384 * x^3 + 19440 * x^2 + 8192 * x * h + 2823 * x - 6136 * h - 6136) * m 1 + (-7168 * x^3 + 5369 * x^2 + 7168 * x * h + 7168 * x - 5369 * h - 5369) * m 13 + (-7168 * x^2 + 8192 * x * h + 13561 * x - 6136 * h - 6136) * m 14 + (-16384 * x^4 + 30736 * x^3 + 16384 * x^2 * h + 3840 * x^2 - 30736 * x * h - 30736 * x + 12544 * h + 12544) * m 21) = 0 := by
      linear_combination (-1024 * x + 767) * e3_13 - (-16 * x^3 + 7 * x^2 + 16 * x * h + 16 * x - 7 * h - 7) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e4_14 : (-8388608 * x^4 + 14680064 * x^3 + 8388608 * x^2 * h + 2099208 * x^2 - 14680064 * x * h - 14680064 * x + 6289400 * h + 6289400) * m 0 + (-8388608 * x^3 + 7340032 * x^2 + 8388608 * x * h + 6672392 * x - 6283264 * h - 5590663) * m 1 + (8388608 * x^4 - 14680064 * x^3 - 8388608 * x^2 * h - 2099208 * x^2 + 14680064 * x * h + 14680064 * x - 6289400 * h - 6289400) * m 13 + (8388608 * x^3 - 7340032 * x^2 - 8388608 * x * h - 6672392 * x + 6283264 * h + 5590663) * m 14 + (-16777216 * x^4 + 31473664 * x^3 + 16777216 * x^2 * h + 2082816 * x^2 - 31473664 * x * h - 31473664 * x + 14694400 * h + 14694400) * m 21 = 0 := by
    have hc : (1) * ((-8388608 * x^4 + 14680064 * x^3 + 8388608 * x^2 * h + 2099208 * x^2 - 14680064 * x * h - 14680064 * x + 6289400 * h + 6289400) * m 0 + (-8388608 * x^3 + 7340032 * x^2 + 8388608 * x * h + 6672392 * x - 6283264 * h - 5590663) * m 1 + (8388608 * x^4 - 14680064 * x^3 - 8388608 * x^2 * h - 2099208 * x^2 + 14680064 * x * h + 14680064 * x - 6289400 * h - 6289400) * m 13 + (8388608 * x^3 - 7340032 * x^2 - 8388608 * x * h - 6672392 * x + 6283264 * h + 5590663) * m 14 + (-16777216 * x^4 + 31473664 * x^3 + 16777216 * x^2 * h + 2082816 * x^2 - 31473664 * x * h - 31473664 * x + 14694400 * h + 14694400) * m 21) = 0 := by
      linear_combination (-1024 * x + 767) * e4_13 - (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e14_14 : (-131072 * x^4 + 81792 * x^3 + 131072 * x^2 * h + 143344 * x^2 - 81792 * x * h - 81792 * x - 12272 * h - 12272) * m 6 + (-131072 * x^3 + 81792 * x^2 + 65536 * x * h + 142320 * x - 49088 * h - 97409) * m 7 + (-131072 * x^3 + 98176 * x^2 + 131072 * x * h + 131072 * x - 98176 * h - 98176) * m 19 + (16384 * x^2 + 65536 * x * h - 11248 * x - 49088 * h - 767) * m 20 + (-131072 * x^4 + 245888 * x^3 + 131072 * x^2 * h + 49296 * x^2 - 245888 * x * h - 245888 * x + 81776 * h + 81776) * m 21 = 0 := by
    have hc : (1) * ((-131072 * x^4 + 81792 * x^3 + 131072 * x^2 * h + 143344 * x^2 - 81792 * x * h - 81792 * x - 12272 * h - 12272) * m 6 + (-131072 * x^3 + 81792 * x^2 + 65536 * x * h + 142320 * x - 49088 * h - 97409) * m 7 + (-131072 * x^3 + 98176 * x^2 + 131072 * x * h + 131072 * x - 98176 * h - 98176) * m 19 + (16384 * x^2 + 65536 * x * h - 11248 * x - 49088 * h - 767) * m 20 + (-131072 * x^4 + 245888 * x^3 + 131072 * x^2 * h + 49296 * x^2 - 245888 * x * h - 245888 * x + 81776 * h + 81776) * m 21) = 0 := by
      linear_combination (-1024 * x + 767) * e14_13 - (-128 * x^3 - 16 * x^2 + 128 * x * h + 128 * x + 16 * h + 16) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e15_14 : (-8192 * x^3 + 6136 * x^2 + 8192 * x * h + 8192 * x - 6136 * h - 6136) * m 6 + (7331840 * x^2 - 4194304 * x * h - 12890120 * x + 3141632 * h + 5541575) * m 7 + (8388608 * x^4 - 13615104 * x^3 - 8388608 * x^2 * h - 2896888 * x^2 + 13615104 * x * h + 13615104 * x - 5491720 * h - 5491720) * m 19 + (8388608 * x^3 - 13615104 * x^2 - 4194304 * x * h + 4501512 * x + 3141632 * h + 741689) * m 20 + (7323648 * x^3 - 6408192 * x^2 - 7323648 * x * h - 7323648 * x + 6408192 * h + 6408192) * m 21 = 0 := by
    have hc : (1) * ((-8192 * x^3 + 6136 * x^2 + 8192 * x * h + 8192 * x - 6136 * h - 6136) * m 6 + (7331840 * x^2 - 4194304 * x * h - 12890120 * x + 3141632 * h + 5541575) * m 7 + (8388608 * x^4 - 13615104 * x^3 - 8388608 * x^2 * h - 2896888 * x^2 + 13615104 * x * h + 13615104 * x - 5491720 * h - 5491720) * m 19 + (8388608 * x^3 - 13615104 * x^2 - 4194304 * x * h + 4501512 * x + 3141632 * h + 741689) * m 20 + (7323648 * x^3 - 6408192 * x^2 - 7323648 * x * h - 7323648 * x + 6408192 * h + 6408192) * m 21) = 0 := by
      linear_combination (-1024 * x + 767) * e15_13 - (3576 * x^2 - 3576 * h - 3576) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e20_14 : (1) * m 21 = 0 := by
    have hc : (-256 * (8 * x - 7)) * ((1) * m 21) = 0 := by
      linear_combination (-1024 * x + 767) * e20_13 - (-1) * e19_13
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-256 : ℝ) ≠ 0) f10)
  have e0_15 : (8 * x^2 - 8 * h - 8) * m 0 + (8 * x - 9) * m 1 + (-8 * x^2 + 8 * h + 8) * m 13 + (-8 * x + 9) * m 14 = 0 := by
    have hc : ((1024 * x - 767)) * ((8 * x^2 - 8 * h - 8) * m 0 + (8 * x - 9) * m 1 + (-8 * x^2 + 8 * h + 8) * m 13 + (-8 * x + 9) * m 14) = 0 := by
      linear_combination (1) * e0_14 - (16384 * x^3 - 14336 * x^2 - 16384 * x * h - 16384 * x + 14336 * h + 14336) * e20_14
    exact (mul_eq_zero.mp hc).resolve_left f9
  have e3_15 : (-16 * x^3 + 7 * x^2 + 16 * x * h + 16 * x - 7 * h - 7) * m 0 + (-16 * x^2 + 7 * x + 8 * h + 8) * m 1 + (-7 * x^2 + 7 * h + 7) * m 13 + (-7 * x + 8 * h + 8) * m 14 = 0 := by
    have hc : ((1024 * x - 767)) * ((-16 * x^3 + 7 * x^2 + 16 * x * h + 16 * x - 7 * h - 7) * m 0 + (-16 * x^2 + 7 * x + 8 * h + 8) * m 1 + (-7 * x^2 + 7 * h + 7) * m 13 + (-7 * x + 8 * h + 8) * m 14) = 0 := by
      linear_combination (1) * e3_14 - (-16384 * x^4 + 30736 * x^3 + 16384 * x^2 * h + 3840 * x^2 - 30736 * x * h - 30736 * x + 12544 * h + 12544) * e20_14
    exact (mul_eq_zero.mp hc).resolve_left f9
  have e4_15 : (-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 0 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 1 + (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 13 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 14 = 0 := by
    have hc : ((1024 * x - 767)) * ((-8192 * x^3 + 8200 * x^2 + 8192 * x * h + 8192 * x - 8200 * h - 8200) * m 0 + (-8192 * x^2 + 1032 * x + 8192 * h + 7289) * m 1 + (8192 * x^3 - 8200 * x^2 - 8192 * x * h - 8192 * x + 8200 * h + 8200) * m 13 + (8192 * x^2 - 1032 * x - 8192 * h - 7289) * m 14) = 0 := by
      linear_combination (1) * e4_14 - (-16777216 * x^4 + 31473664 * x^3 + 16777216 * x^2 * h + 2082816 * x^2 - 31473664 * x * h - 31473664 * x + 14694400 * h + 14694400) * e20_14
    exact (mul_eq_zero.mp hc).resolve_left f9
  have e14_15 : (-128 * x^3 - 16 * x^2 + 128 * x * h + 128 * x + 16 * h + 16) * m 6 + (-128 * x^2 - 16 * x + 64 * h + 127) * m 7 + (-128 * x^2 + 128 * h + 128) * m 19 + (16 * x + 64 * h + 1) * m 20 = 0 := by
    have hc : ((1024 * x - 767)) * ((-128 * x^3 - 16 * x^2 + 128 * x * h + 128 * x + 16 * h + 16) * m 6 + (-128 * x^2 - 16 * x + 64 * h + 127) * m 7 + (-128 * x^2 + 128 * h + 128) * m 19 + (16 * x + 64 * h + 1) * m 20) = 0 := by
      linear_combination (1) * e14_14 - (-131072 * x^4 + 245888 * x^3 + 131072 * x^2 * h + 49296 * x^2 - 245888 * x * h - 245888 * x + 81776 * h + 81776) * e20_14
    exact (mul_eq_zero.mp hc).resolve_left f9
  have e15_15 : (-8 * x^2 + 8 * h + 8) * m 6 + (7160 * x - 4096 * h - 7225) * m 7 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 19 + (8192 * x^2 - 7160 * x - 4096 * h - 967) * m 20 = 0 := by
    have hc : ((1024 * x - 767)) * ((-8 * x^2 + 8 * h + 8) * m 6 + (7160 * x - 4096 * h - 7225) * m 7 + (8192 * x^3 - 7160 * x^2 - 8192 * x * h - 8192 * x + 7160 * h + 7160) * m 19 + (8192 * x^2 - 7160 * x - 4096 * h - 967) * m 20) = 0 := by
      linear_combination (1) * e15_14 - (7323648 * x^3 - 6408192 * x^2 - 7323648 * x * h - 7323648 * x + 6408192 * h + 6408192) * e20_14
    exact (mul_eq_zero.mp hc).resolve_left f9
  have e0_16 : (-128 * x^2 + 144 * x + 64 * h + 1) * m 0 + (-128 * x + 144) * m 1 + (-64 * h - 1) * m 13 = 0 := by
    have hc : ((x^2 - h - 1)) * ((-128 * x^2 + 144 * x + 64 * h + 1) * m 0 + (-128 * x + 144) * m 1 + (-64 * h - 1) * m 13) = 0 := by
      linear_combination (-7 * x + 8 * h + 8) * e0_15 - (-8 * x + 9) * e3_15
    exact (mul_eq_zero.mp hc).resolve_left f6
  have e2_16 : (1152 * x^4 - 1008 * x^3 - 1728 * x^2 * h - 1287 * x^2 + 1008 * x * h + 1008 * x + 576 * h^2 + 711 * h + 135) * m 0 + (1152 * x^3 - 1008 * x^2 - 1152 * x * h - 1152 * x + 1008 * h + 1008) * m 1 + (896 * x^4 - 1024 * x^3 * h - 1920 * x^3 + 128 * x^2 * h + 128 * x^2 + 1024 * x * h^2 + 2944 * x * h + 1920 * x - 1024 * h^2 - 2048 * h - 1024) * m 6 + (896 * x^3 - 1024 * x^2 * h - 1920 * x^2 + 576 * x * h + 1017 * x + 512 * h^2 + 520 * h + 8) * m 7 + (1008 * x^3 - 576 * x^2 * h - 1017 * x^2 - 1008 * x * h - 1008 * x + 576 * h^2 + 1593 * h + 1017) * m 13 + (-112 * x^3 + 128 * x^2 * h + 128 * x^2 + 112 * x * h + 112 * x - 128 * h^2 - 256 * h - 128) * m 19 + (896 * x^2 - 1472 * x * h - 1913 * x + 512 * h^2 + 1528 * h + 1016) * m 20 = 0 := by
    have hc : (1) * ((1152 * x^4 - 1008 * x^3 - 1728 * x^2 * h - 1287 * x^2 + 1008 * x * h + 1008 * x + 576 * h^2 + 711 * h + 135) * m 0 + (1152 * x^3 - 1008 * x^2 - 1152 * x * h - 1152 * x + 1008 * h + 1008) * m 1 + (896 * x^4 - 1024 * x^3 * h - 1920 * x^3 + 128 * x^2 * h + 128 * x^2 + 1024 * x * h^2 + 2944 * x * h + 1920 * x - 1024 * h^2 - 2048 * h - 1024) * m 6 + (896 * x^3 - 1024 * x^2 * h - 1920 * x^2 + 576 * x * h + 1017 * x + 512 * h^2 + 520 * h + 8) * m 7 + (1008 * x^3 - 576 * x^2 * h - 1017 * x^2 - 1008 * x * h - 1008 * x + 576 * h^2 + 1593 * h + 1017) * m 13 + (-112 * x^3 + 128 * x^2 * h + 128 * x^2 + 112 * x * h + 112 * x - 128 * h^2 - 256 * h - 128) * m 19 + (896 * x^2 - 1472 * x * h - 1913 * x + 512 * h^2 + 1528 * h + 1016) * m 20) = 0 := by
      linear_combination (-7 * x + 8 * h + 8) * e2 - (128 * x - 64 * h - 127) * e3_15
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have e4_16 : (131072 * x^3 - 16512 * x^2 - 196608 * x * h - 232336 * x + 122944 * h + 116623) * m 0 + (131072 * x^2 - 16512 * x - 131072 * h - 116624) * m 1 + (65536 * x * h + 115712 * x - 122944 * h - 116623) * m 13 = 0 := by
    have hc : ((x^2 - h - 1)) * ((131072 * x^3 - 16512 * x^2 - 196608 * x * h - 232336 * x + 122944 * h + 116623) * m 0 + (131072 * x^2 - 16512 * x - 131072 * h - 116624) * m 1 + (65536 * x * h + 115712 * x - 122944 * h - 116623) * m 13) = 0 := by
      linear_combination (-7 * x + 8 * h + 8) * e4_15 - (8192 * x^2 - 1032 * x - 8192 * h - 7289) * e3_15
    exact (mul_eq_zero.mp hc).resolve_left f6
  have e2_17 : (144 * x^2 - 144 * h - 144) * m 0 + (-1024 * x^4 + 2176 * x^3 + 1024 * x^2 * h - 128 * x^2 - 2176 * x * h - 2176 * x + 1152 * h + 1152) * m 6 + (-1024 * x^3 + 2176 * x^2 + 512 * x * h - 1144 * x - 576 * h - 9) * m 7 + (-1152 * x^3 + 1152 * x^2 + 1152 * x * h + 1152 * x - 1152 * h - 1152) * m 13 + (128 * x^3 - 144 * x^2 - 128 * x * h - 128 * x + 144 * h + 144) * m 19 + (-1024 * x^2 + 512 * x * h + 2168 * x - 576 * h - 1143) * m 20 = 0 := by
    have hc : (16 * (7 * x - 8 * h - 8)) * ((144 * x^2 - 144 * h - 144) * m 0 + (-1024 * x^4 + 2176 * x^3 + 1024 * x^2 * h - 128 * x^2 - 2176 * x * h - 2176 * x + 1152 * h + 1152) * m 6 + (-1024 * x^3 + 2176 * x^2 + 512 * x * h - 1144 * x - 576 * h - 9) * m 7 + (-1152 * x^3 + 1152 * x^2 + 1152 * x * h + 1152 * x - 1152 * h - 1152) * m 13 + (128 * x^3 - 144 * x^2 - 128 * x * h - 128 * x + 144 * h + 144) * m 19 + (-1024 * x^2 + 512 * x * h + 2168 * x - 576 * h - 1143) * m 20) = 0 := by
      linear_combination (-128 * x + 144) * e2_16 - (1152 * x^3 - 1008 * x^2 - 1152 * x * h - 1152 * x + 1008 * h + 1008) * e0_16
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) f11)
  have e4_17 : (1) * m 0 + (-1) * m 13 = 0 := by
    have hc : (256 * (7 * x - 8 * h - 8) * (8192 * x - 4096 * h - 8257)) * ((1) * m 0 + (-1) * m 13) = 0 := by
      linear_combination (-128 * x + 144) * e4_16 - (131072 * x^2 - 16512 * x - 131072 * h - 116624) * e0_16
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (256 : ℝ) ≠ 0) f11) f13)
  have e2_18 : (-128 * x^3 + 128 * x^2 + 128 * x * h + 128 * x - 128 * h - 128) * m 6 + (-128 * x^2 + 128 * x + 64 * h + 1) * m 7 + (-144 * x^2 + 144 * h + 144) * m 13 + (16 * x^2 - 16 * h - 16) * m 19 + (-128 * x + 64 * h + 127) * m 20 = 0 := by
    have hc : ((8 * x - 9)) * ((-128 * x^3 + 128 * x^2 + 128 * x * h + 128 * x - 128 * h - 128) * m 6 + (-128 * x^2 + 128 * x + 64 * h + 1) * m 7 + (-144 * x^2 + 144 * h + 144) * m 13 + (16 * x^2 - 16 * h - 16) * m 19 + (-128 * x + 64 * h + 127) * m 20) = 0 := by
      linear_combination (1) * e2_17 - (144 * x^2 - 144 * h - 144) * e4_17
    exact (mul_eq_zero.mp hc).resolve_left f12
  have e14_20 : (114688 * x^2 - 65536 * x * h - 1136 * x - 65472 * h - 115599) * m 6 + (-131072 * x^3 - 16256 * x^2 + 65536 * x * h + 130192 * x - 65600 * h - 15599) * m 19 + (-131072 * x^2 - 16256 * x + 114576) * m 20 = 0 := by
    have hc : (8 * (x^2 - h - 1)) * ((114688 * x^2 - 65536 * x * h - 1136 * x - 65472 * h - 115599) * m 6 + (-131072 * x^3 - 16256 * x^2 + 65536 * x * h + 130192 * x - 65600 * h - 15599) * m 19 + (-131072 * x^2 - 16256 * x + 114576) * m 20) = 0 := by
      linear_combination (-8 * x + 4096 * h + 967) * e14_15 - (-128 * x^2 - 16 * x + 64 * h + 127) * e16_0
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) f6)
  have e15_20 : (-112 * x + 64 * h + 113) * m 6 + (128 * x^2 - 112 * x - 64 * h - 15) * m 19 + (128 * x - 112) * m 20 = 0 := by
    have hc : (457728 * (x^2 - h - 1)) * ((-112 * x + 64 * h + 113) * m 6 + (128 * x^2 - 112 * x - 64 * h - 15) * m 19 + (128 * x - 112) * m 20) = 0 := by
      linear_combination (-8 * x + 4096 * h + 967) * e15_15 - (7160 * x - 4096 * h - 7225) * e16_0
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (457728 : ℝ) ≠ 0) f6)
  have e17_20 : (57216 * x + 491008 * h + 65911) * m 6 + (-66560 * x^2 + 57216 * x + 33280 * h + 7801) * m 19 + (-66560 * x + 57216) * m 20 = 0 := by
    have hc : (128 * (x^2 - h - 1)) * ((57216 * x + 491008 * h + 65911) * m 6 + (-66560 * x^2 + 57216 * x + 33280 * h + 7801) * m 19 + (-66560 * x + 57216) * m 20) = 0 := by
      linear_combination (-8 * x + 4096 * h + 967) * e17 - (-1032 * x - 4096 * h - 73) * e16_0
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (128 : ℝ) ≠ 0) f6)
  have e14_21 : (1) * m 19 = 0 := by
    have hc : (512 * (8 * x - 7) * (8 * x - 4096 * h - 967)) * ((1) * m 19) = 0 := by
      linear_combination (128 * x - 112) * e14_20 - (-131072 * x^2 - 16256 * x + 114576) * e15_20
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (512 : ℝ) ≠ 0) f10) f14)
  have e17_21 : (-1024 * x + 895) * m 6 + (1) * m 19 = 0 := by
    have hc : (16 * (8 * x - 4096 * h - 967)) * ((-1024 * x + 895) * m 6 + (1) * m 19) = 0 := by
      linear_combination (128 * x - 112) * e17_20 - (-66560 * x + 57216) * e15_20
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) f14)
  have e17_22 : (1) * m 6 = 0 := by
    have hc : (-1 * (1024 * x - 895)) * ((1) * m 6) = 0 := by
      linear_combination (1) * e17_21 - (1) * e14_21
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) f5)
  have z6 : m 6 = 0 := by
    have hc : (1) * m 6 = 0 := by
      linear_combination e17_22
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z19 : m 19 = 0 := by
    have hc : (1) * m 19 = 0 := by
      linear_combination e14_21
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z20 : m 20 = 0 := by
    have hc : (16 * (8 * x - 7)) * m 20 = 0 := by
      simp only [z6, z19, mul_zero, zero_add, add_zero] at e15_20
      linear_combination e15_20
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) f10)
  have z7 : m 7 = 0 := by
    have hc : (-1 * (8 * x - 4096 * h - 967)) * m 7 = 0 := by
      simp only [z6, z19, z20, mul_zero, zero_add, add_zero] at e16_0
      linear_combination e16_0
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) f14)
  have z13 : m 13 = 0 := by
    have hc : (-144 * (x^2 - h - 1)) * m 13 = 0 := by
      simp only [z6, z7, z19, z20, mul_zero, zero_add, add_zero] at e2_18
      linear_combination e2_18
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-144 : ℝ) ≠ 0) f6)
  have z0 : m 0 = 0 := by
    have hc : (1) * m 0 = 0 := by
      simp only [z13, mul_zero, zero_add, add_zero] at e4_17
      linear_combination e4_17
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z1 : m 1 = 0 := by
    have hc : (-16 * (8 * x - 9)) * m 1 = 0 := by
      simp only [z0, z13, mul_zero, zero_add, add_zero] at e0_16
      linear_combination e0_16
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-16 : ℝ) ≠ 0) f12)
  have z14 : m 14 = 0 := by
    have hc : (-1 * (7 * x - 8 * h - 8)) * m 14 = 0 := by
      simp only [z0, z1, z13, mul_zero, zero_add, add_zero] at e3_15
      linear_combination e3_15
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) f11)
  have z21 : m 21 = 0 := by
    have hc : (1) * m 21 = 0 := by
      linear_combination e20_14
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z8 : m 8 = 0 := by
    have hc : (-1 * (1024 * x - 767)) * m 8 = 0 := by
      simp only [z21, mul_zero, zero_add, add_zero] at e19_13
      linear_combination e19_13
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) f9)
  have z9 : m 9 = 0 := by
    have hc : (1) * m 9 = 0 := by
      linear_combination e18_12
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z22 : m 22 = 0 := by
    have hc : (16 * (1024 * x - 895) * (x^2 - h - 1)) * m 22 = 0 := by
      simp only [z8, z9, z21, mul_zero, zero_add, add_zero] at e7_11
      linear_combination e7_11
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) f5) f6)
  have z10 : m 10 = 0 := by
    have hc : (1) * m 10 = 0 := by
      simp only [z22, mul_zero, zero_add, add_zero] at e22_9
      linear_combination e22_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z23 : m 23 = 0 := by
    have hc : (-16) * m 23 = 0 := by
      simp only [z10, z22, mul_zero, zero_add, add_zero] at e21_9
      linear_combination e21_9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (-16 : ℝ) ≠ 0)
  have z11 : m 11 = 0 := by
    have hc : (1) * m 11 = 0 := by
      simp only [z23, mul_zero, zero_add, add_zero] at e11_6
      linear_combination e11_6
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z17 : m 17 = 0 := by
    have hc : (-2 * (x^2 - h - 1)) * m 17 = 0 := by
      simp only [z0, z1, z13, z14, mul_zero, zero_add, add_zero] at e1_6
      linear_combination e1_6
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) f6)
  have z18 : m 18 = 0 := by
    have hc : (-2048 * (x^2 - h - 1)) * m 18 = 0 := by
      simp only [z8, z9, z17, z21, mul_zero, zero_add, add_zero] at e10_6
      linear_combination e10_6
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (-2048 : ℝ) ≠ 0) f6)
  have z5 : m 5 = 0 := by
    have hc : (-1) * m 5 = 0 := by
      simp only [z18, mul_zero, zero_add, add_zero] at e12_5
      linear_combination e12_5
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (-1 : ℝ) ≠ 0)
  have z4 : m 4 = 0 := by
    have hc : (8192 * (x^2 - h - 1)) * m 4 = 0 := by
      simp only [z5, z17, z18, mul_zero, zero_add, add_zero] at e13
      linear_combination e13
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (8192 : ℝ) ≠ 0) f6)
  have z15 : m 15 = 0 := by
    have hc : (16 * (1024 * x - 895) * (x^2 - h - 1)) * m 15 = 0 := by
      simp only [z8, z9, z21, mul_zero, zero_add, add_zero] at e6_3
      linear_combination e6_3
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) f5) f6)
  have z2 : m 2 = 0 := by
    have hc : (-1) * m 2 = 0 := by
      simp only [z15, mul_zero, zero_add, add_zero] at e8_1
      linear_combination e8_1
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (-1 : ℝ) ≠ 0)
  have z3 : m 3 = 0 := by
    have hc : (8192 * (x^2 - h - 1)) * m 3 = 0 := by
      simp only [z2, z6, z7, z15, z19, z20, mul_zero, zero_add, add_zero] at e5_1
      linear_combination e5_1
    exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (by norm_num : (8192 : ℝ) ≠ 0) f6)
  have z16 : m 16 = 0 := by
    have hc : (1) * m 16 = 0 := by
      simp only [z3, mul_zero, zero_add, add_zero] at e9
      linear_combination e9
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  have z12 : m 12 = 0 := by
    have hc : (1) * m 12 = 0 := by
      linear_combination e23
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num : (1 : ℝ) ≠ 0)
  funext i
  fin_cases i <;> first | exact z0 | exact z1 | exact z2 | exact z3 | exact z4 | exact z5 | exact z6 | exact z7 | exact z8 | exact z9 | exact z10 | exact z11 | exact z12 | exact z13 | exact z14 | exact z15 | exact z16 | exact z17 | exact z18 | exact z19 | exact z20 | exact z21 | exact z22 | exact z23

/-- The twenty-four selected motions suffice for the twenty-four fixed-period
squared-edge-length equations at every point of both closed strips. -/
public theorem type6_edgeDerivative_injective (second : Bool) (x w : ℝ)
    (hd : chartDomain second x w) (m : Fin 24 → ℝ)
    (he : ∀ e, edgeDerivative second x w m e = 0) : m = 0 := by
  have hw : 0 ≤ w - (1 - x^2) := sub_nonneg.mpr hd.2.2
  have hw' : 1 - x^2 + (w - (1 - x^2)) = w := by ring
  cases second
  · exact injective_false x _ hd.1 hd.2.1 hw m (by simpa only [hw'] using he)
  · exact injective_true x _ hd.1 hd.2.1 hw m (by simpa only [hw'] using he)

end OrigamiTorus
