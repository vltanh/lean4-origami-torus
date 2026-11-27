module

public import Mathlib.NumberTheory.Modular
import Mathlib.Tactic

/-! Reduction of a pair of generators of a plane lattice to the half-domain. -/

@[expose] public section

open scoped ComplexConjugate MatrixGroups

namespace OrigamiTorus

/-- The lattice with the indicated two complex generators. -/
def complexLattice (u v : ℂ) : Set ℂ :=
  {p | ∃ m n : ℤ, (m : ℂ)*u+(n : ℂ)*v=p}

theorem complexLattice_mul (c u v : ℂ) :
    (fun p => c*p) '' complexLattice u v = complexLattice (c*u) (c*v) := by
  ext p
  constructor
  · rintro ⟨q,⟨m,n,rfl⟩,rfl⟩
    exact ⟨m,n,by ring⟩
  · rintro ⟨m,n,rfl⟩
    exact ⟨_,⟨m,n,rfl⟩,by ring⟩

private theorem complexLattice_conj (u v : ℂ) :
    (conj : ℂ → ℂ) '' complexLattice u v = complexLattice (conj u) (conj v) := by
  ext p
  constructor
  · rintro ⟨q,⟨m,n,rfl⟩,rfl⟩
    exact ⟨m,n,by simp⟩
  · rintro ⟨m,n,rfl⟩
    exact ⟨_,⟨m,n,rfl⟩,by simp⟩

theorem complexLattice_neg_right (u v : ℂ) :
    complexLattice u (-v) = complexLattice u v := by
  ext p
  constructor <;> rintro ⟨m,n,hn⟩ <;> exact ⟨m,-n,by simpa [mul_neg,neg_mul] using hn⟩

private theorem complexLattice_unimodular (u v : ℂ) (a b c d : ℤ) (h : a*d-b*c=1) :
    complexLattice ((c : ℂ)*v+(d : ℂ)*u) ((a : ℂ)*v+(b : ℂ)*u) = complexLattice u v := by
  have hz : (a : ℂ)*(d : ℂ)-(b : ℂ)*(c : ℂ)=1 := by exact_mod_cast h
  ext p
  constructor
  · rintro ⟨m,n,rfl⟩
    refine ⟨d*m+b*n,c*m+a*n,?_⟩
    simp only [Int.cast_add,Int.cast_mul]
    ring
  · rintro ⟨m,n,rfl⟩
    refine ⟨a*m-b*n,d*n-c*m,?_⟩
    simp only [Int.cast_sub,Int.cast_mul]
    linear_combination ((m : ℂ)*u+(n : ℂ)*v)*hz

private theorem modular_lattice (g : SL(2,ℤ)) (τ : UpperHalfPlane) :
    let D := UpperHalfPlane.denom g τ
    D ≠ 0 ∧ (fun p => D*p) '' complexLattice 1 ((g • τ : UpperHalfPlane) : ℂ) =
      complexLattice 1 (τ : ℂ) := by
  dsimp only
  have hD := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) τ
  refine ⟨hD,?_⟩
  let D := UpperHalfPlane.denom g τ
  let A : Matrix (Fin 2) (Fin 2) ℤ := g
  have hM : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact g.det_coe
  have hD1 : D = (A 1 0 : ℂ)*(τ : ℂ)+(A 1 1 : ℂ)*1 := by
    simp [D,ModularGroup.denom_apply,A]
  have hD2 : D*((g • τ : UpperHalfPlane) : ℂ) = (A 0 0 : ℂ)*(τ : ℂ)+(A 0 1 : ℂ)*1 := by
    rw [ModularGroup.sl_moeb, UpperHalfPlane.coe_smul_of_det_pos (by simp)]
    rw [mul_comm D, div_mul_cancel₀ _ hD]
    simp [UpperHalfPlane.num,A]
  change (fun p => D*p) '' complexLattice 1 ((g • τ : UpperHalfPlane) : ℂ) = _
  rw [complexLattice_mul,mul_one,hD2,hD1]
  exact complexLattice_unimodular 1 (τ : ℂ) (A 0 0) (A 0 1) (A 1 0) (A 1 1) hM

/-- Every positively oriented ratio admits the Type 6 half-domain coordinates
after a similarity and a change of lattice generators. -/
theorem reduced_complex_ratio (τ : UpperHalfPlane) :
    ∃ (x y : ℝ) (D : ℂ) (reflect : Bool),
      0 ≤ x ∧ x ≤ 1/2 ∧ 0 < y ∧ 1-x^2 ≤ y^2 ∧ D ≠ 0 ∧
      (fun p => D*(if reflect then conj p else p)) '' complexLattice 1 (x+y*Complex.I) =
        complexLattice 1 (τ : ℂ) := by
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd τ
  let σ := g • τ
  let D := UpperHalfPlane.denom g τ
  have hn : 1 ≤ Complex.normSq (σ : ℂ) := hg.1
  have hx : |σ.re| ≤ (1 : ℝ)/2 := hg.2
  have hw : 1-|σ.re|^2 ≤ σ.im^2 := by
    rw [sq_abs]
    have h : 1 ≤ σ.re^2+σ.im^2 := by
      simpa only [Complex.normSq_apply, ← sq, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] using hn
    linarith
  obtain ⟨hD,hL⟩ := modular_lattice g τ
  by_cases hx₀ : 0 ≤ σ.re
  · refine ⟨|σ.re|,σ.im,D,false,abs_nonneg _,hx,σ.im_pos,hw,hD,?_⟩
    change (fun p => D*p) '' complexLattice 1 ((|σ.re| : ℝ)+σ.im*Complex.I) = _
    have hc : (σ.re : ℂ)+σ.im*Complex.I = (σ : ℂ) := by
      simpa only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im] using Complex.re_add_im (σ : ℂ)
    rw [abs_of_nonneg hx₀,hc]
    exact hL
  · refine ⟨|σ.re|,σ.im,D,true,abs_nonneg _,hx,σ.im_pos,hw,hD,?_⟩
    have hc : conj ((|σ.re| : ℝ) + σ.im*Complex.I : ℂ) = -(σ : ℂ) := by
      apply Complex.ext <;> simp [abs_of_neg (lt_of_not_ge hx₀)]
    change ((fun p => D*p) ∘ (conj : ℂ → ℂ)) ''
      complexLattice 1 ((|σ.re| : ℝ)+σ.im*Complex.I) = _
    rw [Set.image_comp, complexLattice_conj, map_one,hc,complexLattice_neg_right]
    exact hL

/-- Every pair of real-linearly independent period vectors can be represented
by a half-domain lattice under an explicit complex similarity. -/
theorem reduced_complex_lattice (u v : ℂ) (hu : u ≠ 0) (hv : (v/u).im ≠ 0) :
    ∃ (x y : ℝ) (D : ℂ) (reflect : Bool),
      0 ≤ x ∧ x ≤ 1/2 ∧ 0 < y ∧ 1-x^2 ≤ y^2 ∧ D ≠ 0 ∧
      (fun p => D*(if reflect then conj p else p)) '' complexLattice 1 (x+y*Complex.I) =
        complexLattice u v := by
  have reduce (w : ℂ) (hw : 0 < (w/u).im) :
      ∃ (x y : ℝ) (D : ℂ) (reflect : Bool),
        0 ≤ x ∧ x ≤ 1/2 ∧ 0 < y ∧ 1-x^2 ≤ y^2 ∧ D ≠ 0 ∧
        (fun p => D*(if reflect then conj p else p)) '' complexLattice 1 (x+y*Complex.I) =
          complexLattice u w := by
    obtain ⟨x,y,D,reflect,hx,hx',hy,hw',hD,hL⟩ := reduced_complex_ratio ⟨w/u,hw⟩
    refine ⟨x,y,u*D,reflect,hx,hx',hy,hw',mul_ne_zero hu hD,?_⟩
    have hcomp : (fun p => (u*D)*(if reflect then conj p else p)) =
        (fun p => u*p) ∘ (fun p => D*(if reflect then conj p else p)) := by
      funext p
      exact mul_assoc _ _ _
    rw [hcomp,Set.image_comp,hL,complexLattice_mul,mul_one]
    change complexLattice u (u*(w/u)) = _
    rw [mul_comm u,div_mul_cancel₀ _ hu]
  rcases hv.lt_or_gt with hneg | hpos
  · have hp : 0 < ((-v)/u).im := by simpa [neg_div] using neg_pos.mpr hneg
    simpa [complexLattice_neg_right] using reduce (-v) hp
  · exact reduce v hpos

theorem complex_similarity_dist (D : ℂ) (reflect : Bool) (p q : ℂ) :
    dist (D*(if reflect then conj p else p)) (D*(if reflect then conj q else q)) = ‖D‖*dist p q := by
  cases reflect <;> simp [dist_eq_norm, ← mul_sub, ← map_sub]

end OrigamiTorus
