module

public import OrigamiTorus.EightVertex.Type5.Reconstruction
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic

/-! Determinant area in the planar coordinates used by the lifted triangulations. -/

public section

open Set MeasureTheory
open scoped ENNReal

namespace OrigamiTorus

local notation "planeVolume" => (MeasureTheory.volume : Measure (ℝ × ℝ))

local instance : Measure.IsAddHaarMeasure planeVolume := by
  change Measure.IsAddHaarMeasure ((MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure ℝ))
  infer_instance

theorem volume_planarTranslate (t : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    planeVolume ((fun p => p+t) '' S) = planeVolume S := by
  let e := Homeomorph.addRight t
  have hm := measurePreserving_add_right planeVolume t
  change planeVolume (e '' S) = planeVolume S
  calc
    _ = (Measure.map e planeVolume) (e '' S) := congrArg (fun μ => μ (e '' S)) hm.map_eq.symm
    _ = planeVolume (e ⁻¹' (e '' S)) := e.measurableEmbedding.map_apply _ _
    _ = _ := by rw [Set.preimage_image_eq _ e.injective]

theorem volume_planarTranslate_preimage (t : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    planeVolume ((fun p => p+t) ⁻¹' S) = planeVolume S := by
  have h := volume_planarTranslate t ((fun p => p+t) ⁻¹' S)
  have hs : Function.Surjective (fun p : ℝ × ℝ => p+t) := (Homeomorph.addRight t).surjective
  rw [Set.image_preimage_eq _ hs] at h
  exact h.symm

private def unitTriangle : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1}

private theorem isClosed_unitTriangle : IsClosed unitTriangle := by
  change IsClosed ({p : ℝ × ℝ | 0 ≤ p.1} ∩ ({p | 0 ≤ p.2} ∩ {p | p.1+p.2 ≤ 1}))
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

private theorem isCompact_unitTriangle : IsCompact unitTriangle := by
  have hc : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  refine hc.of_isClosed_subset isClosed_unitTriangle ?_
  rintro p ⟨h₁,h₂,h₃⟩
  exact ⟨⟨h₁,by linarith⟩,⟨h₂,by linarith⟩⟩

private theorem volume_antidiagonal :
    planeVolume {p : ℝ × ℝ | p.1+p.2=1} = 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1+p.2=1} :=
    (isClosed_eq (continuous_fst.add continuous_snd) continuous_const).measurableSet
  apply (Measure.measure_prod_null hm).mpr
  apply Filter.Eventually.of_forall
  intro x
  have he : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1+p.2=1} = {1-x} := by
    ext y
    change x+y=1 ↔ y=1-x
    constructor <;> intro h <;> linarith
  simp [he]

private theorem volume_unitTriangle : planeVolume unitTriangle = ENNReal.ofReal (1/2) := by
  let square := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let r : ℝ × ℝ → ℝ × ℝ := fun p => (1,1)-p
  let upper := r '' unitTriangle
  have hu : upper = {p : ℝ × ℝ | p.1 ≤ 1 ∧ p.2 ≤ 1 ∧ 1 ≤ p.1+p.2} := by
    ext p
    constructor
    · rintro ⟨q,⟨h₁,h₂,h₃⟩,rfl⟩
      change 1-q.1 ≤ 1 ∧ 1-q.2 ≤ 1 ∧ 1 ≤ (1-q.1)+(1-q.2)
      exact ⟨by linarith,by linarith,by linarith⟩
    · rintro ⟨h₁,h₂,h₃⟩
      refine ⟨r p,?_,?_⟩
      · change 0 ≤ 1-p.1 ∧ 0 ≤ 1-p.2 ∧ (1-p.1)+(1-p.2) ≤ 1
        exact ⟨by linarith,by linarith,by linarith⟩
      · apply Prod.ext <;> simp [r]
  have he : unitTriangle ∪ upper = square := by
    ext p
    change p ∈ unitTriangle ∨ p ∈ upper ↔ p ∈ square
    rw [hu]
    change (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1) ∨
      (p.1 ≤ 1 ∧ p.2 ≤ 1 ∧ 1 ≤ p.1+p.2) ↔
      (0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1)
    constructor
    · rintro (⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,h₃⟩)
      · exact ⟨⟨h₁,by linarith⟩,⟨h₂,by linarith⟩⟩
      · exact ⟨⟨by linarith,h₁⟩,⟨by linarith,h₂⟩⟩
    · rintro ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩
      exact (le_total (p.1+p.2) (1 : ℝ)).imp (⟨h₁,h₃,·⟩) (⟨h₂,h₄,·⟩)
  have hzu : planeVolume (unitTriangle ∩ upper) = 0 := by
    apply measure_mono_null (t := {p : ℝ × ℝ | p.1+p.2=1}) ?_ volume_antidiagonal
    rw [hu]
    rintro p ⟨⟨_,_,h₁⟩,⟨_,_,h₂⟩⟩
    exact le_antisymm h₁ h₂
  have hmeas : MeasurableSet upper := by
    rw [hu]
    change MeasurableSet ({p : ℝ × ℝ | p.1 ≤ 1} ∩ ({p | p.2 ≤ 1} ∩ {p | 1 ≤ p.1+p.2}))
    exact ((isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le continuous_snd continuous_const).inter
        (isClosed_le continuous_const (continuous_fst.add continuous_snd)))).measurableSet
  have hsymm : planeVolume upper = planeVolume unitTriangle := by
    let b := Module.Basis.finTwoProd ℝ
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![-1,0;0,-1]
    let L := Matrix.toLin b b M
    have hL (p : ℝ × ℝ) : L p = -p := by
      change Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
        !![(-1 : ℝ),0;0,-1] p = -p
      simp [Matrix.toLin_finTwoProd_apply]
      rfl
    have hcomp : r = (fun p : ℝ × ℝ => p+(1,1)) ∘ L := by
      funext p
      simp [r,hL,sub_eq_add_neg,add_comm]
    change planeVolume (r '' unitTriangle) = _
    rw [hcomp, Set.image_comp, volume_planarTranslate, Measure.addHaar_image_linearMap,
      LinearMap.det_toLin b M]
    norm_num [M,Matrix.det_fin_two_of]
  have hsquare : planeVolume square = 1 := by
    change ((MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure ℝ))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1
    simp only [Measure.prod_prod,Real.volume_Icc]
    norm_num
  have hs := measure_union_add_inter (μ := planeVolume) unitTriangle hmeas
  rw [he,hzu,add_zero,hsymm,hsquare] at hs
  apply (ENNReal.mul_left_inj (c := 2) (by norm_num) (by norm_num)).mp
  rw [mul_two, ← hs, mul_two, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- The closed affine triangle with the three given corners. -/
@[expose] def planarTriangle (A B C : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s+t ≤ 1 ∧ p = A+s • (B-A)+t • (C-A)}

private theorem planarTriangle_image (A B C : ℝ × ℝ) :
    planarTriangle A B C = (fun p : ℝ × ℝ => A+p.1 • (B-A)+p.2 • (C-A)) '' unitTriangle := by
  ext p
  exact ⟨fun ⟨s,t,hs,ht,hst,hp⟩ => ⟨(s,t),⟨hs,ht,hst⟩,hp.symm⟩,
    fun ⟨q,⟨hs,ht,hst⟩,hp⟩ => ⟨q.1,q.2,hs,ht,hst,hp.symm⟩⟩

theorem isCompact_planarTriangle (A B C : ℝ × ℝ) : IsCompact (planarTriangle A B C) := by
  rw [planarTriangle_image]
  exact isCompact_unitTriangle.image (by fun_prop)

/-- The area of a closed triangle is half its absolute oriented double area. -/
theorem volume_planarTriangle (A B C : ℝ × ℝ) :
    planeVolume (planarTriangle A B C) = ENNReal.ofReal (|Type5.cross (B-A) (C-A)|/2) := by
  let u := B-A
  let v := C-A
  let b := Module.Basis.finTwoProd ℝ
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![u.1,v.1;u.2,v.2]
  let L := Matrix.toLin b b M
  have hL (p : ℝ × ℝ) : L p = p.1 • u + p.2 • v := by
    change Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      !![u.1,v.1;u.2,v.2] p = p.1 • u + p.2 • v
    rw [Matrix.toLin_finTwoProd_apply]
    have h (a : ℝ) (q : ℝ × ℝ) : a • q = (a*q.1,a*q.2) := rfl
    apply Prod.ext <;> simp only [h,Prod.fst_add,Prod.snd_add] <;> ring
  have hcomp : (fun p : ℝ × ℝ => A+p.1 • (B-A)+p.2 • (C-A)) =
      (fun p : ℝ × ℝ => p+A) ∘ L := by
    funext p
    rw [Function.comp_apply,hL]
    change A+p.1 • u+p.2 • v = p.1 • u+p.2 • v+A
    abel
  rw [planarTriangle_image, hcomp, Set.image_comp, volume_planarTranslate,
    Measure.addHaar_image_linearMap,LinearMap.det_toLin b M,volume_unitTriangle,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  have he : M.det = Type5.cross (B-A) (C-A) := by
    simp only [M,Matrix.det_fin_two_of,Type5.cross,u,v]
    ring
  rw [he]
  congr 1
  ring

end OrigamiTorus
