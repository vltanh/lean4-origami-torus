module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! Kernel-checked dyadic bounds for division and square roots. -/

@[expose] public section

namespace Inclusion.IntervalDyadicReal

private theorem zero_toReal : Dyadic.toReal (0 : Dyadic) = 0 := by
  norm_num [Dyadic.toReal]

/-- Retain enough relative precision for parsed rational literals with large integer denominators. -/
def reciprocalPrecision (a b : Dyadic) (prec : Nat) : Nat :=
  prec + max a.toRat.num.natAbs.log2 b.toRat.num.natAbs.log2 + 1

/-- Invert a finite interval when it is on one side of zero. -/
def inverse (I : Interval Dyadic) (prec : Nat) : Interval Dyadic :=
  match I.lb, I.ub with
  | some a, some b =>
    if 0 < a ∨ b < 0 then Interval.Icc (rat b.toRat⁻¹ (reciprocalPrecision a b prec)).lb
      (rat a.toRat⁻¹ (reciprocalPrecision a b prec)).ub
    else .univ _
  | _, _ => .univ _

@[inclusion_op interval_dyadic_real]
theorem inverse_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : Nat) :
    x⁻¹ ∈ inverse I prec := by
  rw [mem_iff_mem_map, Interval.mem_map_iff] at hx
  rw [mem_iff_mem_map]
  rcases I with ⟨_ | a,_ | b⟩ <;> simp only [inverse]
  all_goals try exact Interval.mem_map_univ _ _
  split
  · rename_i h
    have ha := hx.1 a rfl
    have hb := hx.2 b rfl
    have hr : (Dyadic.toReal b)⁻¹ ≤ x⁻¹ ∧ x⁻¹ ≤ (Dyadic.toReal a)⁻¹ := by
      rcases h with ha' | hb'
      · have hap : 0 < (Dyadic.toReal a) := by simpa only [zero_toReal] using Dyadic.toReal_lt_toReal.mpr ha'
        exact ⟨(inv_le_inv₀ ((hap.trans_le ha).trans_le hb) (hap.trans_le ha)).mpr hb,
          (inv_le_inv₀ (hap.trans_le ha) hap).mpr ha⟩
      · have hbn : (Dyadic.toReal b) < 0 := by simpa only [zero_toReal] using Dyadic.toReal_lt_toReal.mpr hb'
        exact ⟨(inv_le_inv_of_neg hbn (hb.trans_lt hbn)).mpr hb,
          (inv_le_inv_of_neg (hb.trans_lt hbn) (ha.trans_lt (hb.trans_lt hbn))).mpr ha⟩
    apply Interval.mem_Icc_of_le
      (ratCast_mem b.toRat⁻¹ (reciprocalPrecision a b prec)) _ _
      (ratCast_mem a.toRat⁻¹ (reciprocalPrecision a b prec))
    · simpa [Dyadic.toReal] using hr.1
    · simpa [Dyadic.toReal] using hr.2
  · exact Interval.mem_map_univ _ _

@[inclusion_op interval_dyadic_real]
theorem div_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) (prec : Nat) :
    x / y ∈ I.mul (inverse J prec) := by
  simpa only [div_eq_mul_inv] using mul_mem hx (inverse_mem hy prec)

/-- Compute candidate endpoints and check their squares before returning them. -/
def squareRootPoint (p : Dyadic) (prec : Nat) : Interval Dyadic :=
  let q := p.toRat
  let scale := (2 : ℚ)^prec
  let n := (Rat.floor (q * scale^2)).toNat.sqrt
  let lo := (n : ℚ) / scale
  let hi := ((n : ℚ)+1) / scale
  if q ≤ 0 then Interval.singleton 0
  else if 0 ≤ lo ∧ 0 ≤ hi ∧ lo^2 ≤ q ∧ q ≤ hi^2 then
    Interval.Icc (rat lo prec).lb (rat hi prec).ub
  else Interval.univ _

private theorem squareRoot_bounds {q lo hi : ℚ}
    (hq : 0 ≤ q) (hl : 0 ≤ lo) (hh : 0 ≤ hi) (hle : lo^2 ≤ q) (hhi : q ≤ hi^2) (prec : Nat) :
    Real.sqrt (q : ℝ) ∈ (Interval.Icc (rat lo prec).lb (rat hi prec).ub).map Dyadic.toReal := by
  have hq' : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  have hl' : 0 ≤ (lo : ℝ) := by exact_mod_cast hl
  have hh' : 0 ≤ (hi : ℝ) := by exact_mod_cast hh
  have ha' : (lo : ℝ)^2 ≤ (q : ℝ) := by exact_mod_cast hle
  have hb' : (q : ℝ) ≤ (hi : ℝ)^2 := by exact_mod_cast hhi
  exact Interval.mem_Icc_of_le (ratCast_mem lo prec) ((Real.le_sqrt hl' hq').2 ha')
    ((Real.sqrt_le_left hh').2 hb') (ratCast_mem hi prec)

private theorem squareRootPoint_mem (p : Dyadic) (prec : Nat) :
    Real.sqrt (Dyadic.toReal p) ∈ squareRootPoint p prec := by
  rw [mem_iff_mem_map]
  unfold squareRootPoint
  dsimp only
  split
  · rename_i h
    have hp : Dyadic.toReal p ≤ 0 := by
      change (p.toRat : ℝ) ≤ 0
      exact_mod_cast h
    rw [Real.sqrt_eq_zero_of_nonpos hp]
    simpa only [zero_toReal] using Interval.mem_map_singleton (0 : Dyadic) Dyadic.toReal
  · split
    · rename_i hn hs
      exact squareRoot_bounds (le_of_lt (lt_of_not_ge hn)) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 prec
    · exact Interval.mem_map_univ _ _

def squareRoot (I : Interval Dyadic) (prec : Nat) : Interval Dyadic :=
  ⟨match I.lb with
    | some a => (squareRootPoint a prec).lb
    | none => 0,
   match I.ub with
    | some b => (squareRootPoint b prec).ub
    | none => ⊤⟩

@[inclusion_op interval_dyadic_real]
theorem squareRoot_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : Nat) :
    Real.sqrt x ∈ squareRoot I prec := by
  rw [mem_iff_mem_map, Interval.mem_map_iff] at hx
  rw [mem_iff_mem_map]
  have hzero : Dyadic.toReal 0 ≤ Real.sqrt x := by simpa only [zero_toReal] using Real.sqrt_nonneg x
  have h0 := Interval.mem_map_singleton (0 : Dyadic) Dyadic.toReal
  rcases I with ⟨_ | a,_ | b⟩ <;> simp only [squareRoot]
  · exact Interval.mem_Ici_of_le hzero h0
  · exact Interval.mem_Icc_of_le h0 hzero (Real.sqrt_le_sqrt (hx.2 b rfl)) (squareRootPoint_mem b prec)
  · exact Interval.mem_Ici_of_le (Real.sqrt_le_sqrt (hx.1 a rfl)) (squareRootPoint_mem a prec)
  · exact Interval.mem_Icc_of_le (squareRootPoint_mem a prec) (Real.sqrt_le_sqrt (hx.1 a rfl))
      (Real.sqrt_le_sqrt (hx.2 b rfl)) (squareRootPoint_mem b prec)

end Inclusion.IntervalDyadicReal
