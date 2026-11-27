module

public import OrigamiTorus.EdgeFaceSeparation
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic

/-! The passage from the disjoint edge–triangle tests to geometric simplices. -/

open Finset
open scoped BigOperators

namespace OrigamiTorus

@[expose] public section

private def homogenize (a : Point3) : Fin 4 → ℝ := ![1, a.1, a.2.1, a.2.2]

private theorem homogeneous_det (a b c d : Point3) :
    (Matrix.of (![homogenize a, homogenize b, homogenize c, homogenize d])).det =
      affineBracket a b c d := by
  rw [Matrix.det_succ_column_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  norm_num [homogenize, affineBracket, determinant3, Fin.succAbove, Fin.predAbove]
  ring

/-- Nonvanishing of the spatial affine bracket gives affine independence. -/
theorem affineIndependent_of_bracket_ne_zero (a b c d : Point3)
    (h : affineBracket a b c d ≠ 0) :
    AffineIndependent ℝ (![a,b,c,d] : Fin 4 → Point3) := by
  have hl : LinearIndependent ℝ (![homogenize a, homogenize b, homogenize c, homogenize d]) :=
    Matrix.linearIndependent_rows_of_det_ne_zero (homogeneous_det a b c d ▸ h)
  rw [affineIndependent_iff_of_fintype]
  intro w hw hc
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hc
  apply (Fintype.linearIndependent_iff.mp hl) w
  ext j
  fin_cases j
  · simpa [Fin.sum_univ_succ, homogenize] using hw
  · simpa [Fin.sum_univ_succ, homogenize] using congrArg Prod.fst hc
  · simpa [Fin.sum_univ_succ, homogenize] using congrArg (fun x => x.2.1) hc
  · simpa [Fin.sum_univ_succ, homogenize] using congrArg (fun x => x.2.2) hc

/-- General position of the determinant tests gives affine independence on every
set of at most four vertex labels. -/
theorem generic_affineIndependentOn (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (h : GenericLift p z)
    (s : Finset Vertex) (hs : s.card ≤ 4) :
    AffineIndepOn ℝ (fun i => ((p i).1, (p i).2, z i)) (s : Set Vertex) := by
  obtain ⟨S, hsub, _, hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ s) hs (by decide : 4 ≤ (Finset.univ : Finset Vertex).card)
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := Finset.card_eq_four.mp hcard
  let q (i : Vertex) : Point3 := ((p i).1,(p i).2,z i)
  have hg : affineBracket (q a) (q b) (q c) (q d) ≠ 0 := by
    rw [← volume_eq_affineBracket]
    exact generic_volume_ne p z h a b c d (by simp [List.pairwise_cons, *])
  let labels : Fin 4 → Vertex := ![a,b,c,d]
  have hrange : Set.range labels = (↑({a,b,c,d} : Finset Vertex) : Set Vertex) := by
    ext i
    constructor
    · rintro ⟨j,rfl⟩
      fin_cases j <;> simp [labels]
    · intro hi
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  apply AffineIndepOn.mono _ (Finset.coe_subset.mpr hsub)
  rw [← hrange]
  have hinj : Function.Injective labels := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [labels]
  rw [affineIndepOn_range_iff hinj]
  have he : q ∘ labels = ![q a,q b,q c,q d] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact affineIndependent_of_bracket_ne_zero _ _ _ _ hg

theorem generic_point_injective (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (h : GenericLift p z) :
    Function.Injective (fun i => ((p i).1, (p i).2, z i)) := by
  classical
  intro i j hij
  let s : Finset Vertex := {i,j}
  have hcard : s.card ≤ 4 :=
    (Finset.card_insert_le _ _).trans (by simp)
  exact (generic_affineIndependentOn p z h s hcard).injOn (by simp [s]) (by simp [s]) hij

/-- The closed convex hull of a finite set of labeled vertices. -/
def vertexHull {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (q : ι → E) (s : Finset ι) : Set E :=
  convexHull ℝ (q '' (s : Set ι))

theorem vertexHull_mono {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (q : ι → E) {s t : Finset ι} (hst : s ⊆ t) : vertexHull q s ⊆ vertexHull q t :=
  convexHull_mono (Set.image_mono (Finset.coe_subset.mpr hst))

theorem weighted_mem_vertexHull {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (q : ι → E) (s : Finset ι) (w : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i • q i) ∈ vertexHull q s := by
  rw [vertexHull, ← Finset.centerMass_eq_of_sum_1 _ _ hmass]
  exact s.centerMass_mem_convexHull hpos (by rw [hmass]; norm_num) (fun i hi => ⟨i, hi, rfl⟩)

theorem weights_of_mem_vertexHull {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (q : ι → E) (s : Finset ι) {x : E}
    (hx : x ∈ vertexHull q s) :
    ∃ w : ι → ℝ, (∀ i ∈ s, 0 ≤ w i) ∧ (∑ i ∈ s, w i = 1) ∧ ∑ i ∈ s, w i • q i = x := by
  classical
  let p (i : s) := q i
  have hr : q '' (s : Set ι) = Set.range p := by
    ext y
    exact ⟨fun ⟨i,hi,h⟩ => ⟨⟨i,hi⟩,h⟩, fun ⟨⟨i,hi⟩,h⟩ => ⟨i,hi,h⟩⟩
  rw [vertexHull, hr, convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨t,v,hp,ht,hx⟩ := hx
  let w (i : ι) : ℝ := if hi : i ∈ s then if (⟨i,hi⟩ : s) ∈ t then v ⟨i,hi⟩ else 0 else 0
  have hw (i : s) : w i = if i ∈ t then v i else 0 := by simp [w,i.property]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i hi
    change 0 ≤ w (⟨i,hi⟩ : s)
    rw [hw]
    split_ifs with ht'
    · exact hp _ ht'
    · exact le_rfl
  · rw [← Finset.sum_attach, ← Finset.univ_eq_attach]
    simpa only [hw, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] using ht
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ ht] at hx
    rw [← Finset.sum_attach, ← Finset.univ_eq_attach]
    simpa only [hw, p, ite_smul, zero_smul, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter] using hx

private theorem sum_signed_parts {ι E : Type*} [Fintype ι] [AddCommMonoid E]
    (w : ι → ℝ) (f : ι → E) (hzero : ∀ i, w i = 0 → f i = 0) :
    (∑ i ∈ (Finset.univ.filter fun i => 0 < w i), f i) +
      (∑ i ∈ (Finset.univ.filter fun i => w i < 0), f i) = ∑ i, f i := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases lt_trichotomy (w i) 0 with hlt | he | hgt
  · simp [hlt, not_lt_of_ge hlt.le]
  · simp [he, hzero i he]
  · simp [hgt, not_lt_of_ge hgt.le]

/-- The two strict sign supports of a nonzero affine relation have intersecting hulls. -/
theorem vertexHull_inter_of_signed_relation {ι E : Type*} [Fintype ι] [AddCommGroup E]
    [Module ℝ E] (q : ι → E) (w : ι → ℝ) (hne : w ≠ 0)
    (hsum : ∑ i, w i = 0) (hvec : ∑ i, w i • q i = 0) :
    (vertexHull q (Finset.univ.filter fun i => 0 < w i) ∩
      vertexHull q (Finset.univ.filter fun i => w i < 0)).Nonempty := by
  classical
  let s := Finset.univ.filter fun i => 0 < w i
  let t := Finset.univ.filter fun i => w i < 0
  have hs (i : ι) (hi : i ∈ s) : 0 < w i := (Finset.mem_filter.mp hi).2
  have ht (i : ι) (hi : i ∈ t) : w i < 0 := (Finset.mem_filter.mp hi).2
  have hm : (∑ i ∈ s, w i) + (∑ i ∈ t, w i) = 0 := (sum_signed_parts w w (fun _ h => h)).trans hsum
  have hv : (∑ i ∈ s, w i • q i) + (∑ i ∈ t, w i • q i) = 0 :=
    (sum_signed_parts w (fun i => w i • q i) (by intro i h; simp [h])).trans hvec
  let m := ∑ i ∈ s, w i
  have hmpos : 0 < m := by
    by_contra! h
    have hms : (∑ i ∈ s, w i) = 0 := le_antisymm h (Finset.sum_nonneg fun i hi => (hs i hi).le)
    have hmt : (∑ i ∈ t, -w i) = 0 := by rw [Finset.sum_neg_distrib]; linarith
    apply hne
    funext i
    rcases lt_trichotomy (w i) 0 with hneg | he | hpos
    · have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => (neg_pos.mpr (ht j hj)).le)).mp
          hmt i (by simp [t, hneg])
      exact neg_eq_zero.mp hzero
    · exact he
    · exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => (hs j hj).le)).mp hms i (by simp [s, hpos])
  have hmt : (∑ i ∈ t, -w i) = m := by rw [Finset.sum_neg_distrib]; linarith
  have hv' : (∑ i ∈ t, (-w i) • q i) = ∑ i ∈ s, w i • q i := by
    simp_rw [neg_smul, Finset.sum_neg_distrib]
    apply neg_eq_iff_add_eq_zero.mpr
    simpa only [add_comm] using hv
  let p := m⁻¹ • (∑ i ∈ s, w i • q i)
  refine ⟨p,?_,?_⟩
  · have he := weighted_mem_vertexHull q s (fun i => m⁻¹*w i)
      (fun i hi => mul_nonneg (inv_nonneg.mpr hmpos.le) (hs i hi).le)
      (by rw [← Finset.mul_sum, inv_mul_cancel₀ hmpos.ne'])
    simpa only [p, mul_smul, ← Finset.smul_sum] using he
  · have he := weighted_mem_vertexHull q t (fun i => m⁻¹*(-w i))
      (fun i hi => mul_nonneg (inv_nonneg.mpr hmpos.le) (neg_nonneg.mpr (ht i hi).le))
      (by rw [← Finset.mul_sum, hmt, inv_mul_cancel₀ hmpos.ne'])
    simpa only [p, mul_smul, ← Finset.smul_sum, hv'] using he

private theorem weighted_sum_eq_or_disjoint {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] (q : ι → E) {s t : Finset ι} {u v : ι → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hU : ∑ i, u i = 1) (hV : ∑ i, v i = 1)
    (hus : ∀ i ∉ s, u i = 0) (hvt : ∀ i ∉ t, v i = 0)
    (hp : (∑ i, u i • q i) = ∑ i, v i • q i) :
    u = v ∨
      ∃ s' ⊆ s, ∃ t' ⊆ t, Disjoint s' t' ∧ (vertexHull q s' ∩ vertexHull q t').Nonempty := by
  by_cases he : u = v
  · exact Or.inl he
  right
  let w (i : ι) := u i - v i
  let S := Finset.univ.filter fun i => 0 < w i
  let T := Finset.univ.filter fun i => w i < 0
  have hsS : S ⊆ s := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    by_contra h
    exact (not_lt_of_ge (hv i)) (by simpa [w, hus i h] using hi')
  have htT : T ⊆ t := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    by_contra h
    exact (not_lt_of_ge (hu i)) (by simpa [w, hvt i h] using hi')
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    exact fun _ hi hj => (Finset.mem_filter.mp hi).2.not_gt (Finset.mem_filter.mp hj).2
  have hw : ∑ i, w i = 0 := by simp [w, Finset.sum_sub_distrib, hU, hV]
  have hwq : ∑ i, w i • q i = 0 := by
    simp [w, sub_smul, Finset.sum_sub_distrib, hp]
  have hwne : ∃ i ∈ (Finset.univ : Finset ι), w i ≠ 0 := by
    by_contra! h
    apply he
    ext i
    exact sub_eq_zero.mp (h i (Finset.mem_univ _))
  obtain ⟨i, _, hpos⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero w hw hwne
  let m := ∑ i ∈ S, w i
  have hm : 0 < m := by
    apply Finset.sum_pos'
    · exact fun j hj => (Finset.mem_filter.mp hj).2.le
    · exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩, hpos⟩
  have hsum : ∑ i ∈ T, -w i = m := by
    rw [Finset.sum_neg_distrib]
    have hh := (sum_signed_parts w w (fun _ h => h)).trans hw
    change m + (∑ i ∈ T, w i) = 0 at hh
    linarith
  have hpoint : (∑ i ∈ S, w i • q i) = ∑ i ∈ T, (-w i) • q i := by
    simp only [neg_smul, Finset.sum_neg_distrib]
    exact eq_neg_of_add_eq_zero_left ((sum_signed_parts w (fun i => w i • q i)
      (fun i h => by simp [h])).trans hwq)
  let X := m⁻¹ • (∑ i ∈ S, w i • q i)
  refine ⟨S, hsS, T, htT, hdisj, X, ?_, ?_⟩
  · have hM : ∑ i ∈ S, m⁻¹ * w i = 1 := by
      rw [← Finset.mul_sum, inv_mul_cancel₀ hm.ne']
    have hmem := weighted_mem_vertexHull q S (fun i => m⁻¹ * w i)
      (fun i hi => mul_nonneg (inv_nonneg.mpr hm.le) (Finset.mem_filter.mp hi).2.le) hM
    simpa only [X, mul_smul, Finset.smul_sum] using hmem
  · have hM : ∑ i ∈ T, m⁻¹ * -w i = 1 := by
      rw [← Finset.mul_sum, hsum, inv_mul_cancel₀ hm.ne']
    have hmem := weighted_mem_vertexHull q T (fun i => m⁻¹ * -w i)
      (fun i hi => mul_nonneg (inv_nonneg.mpr hm.le) (neg_nonneg.mpr (Finset.mem_filter.mp hi).2.le)) hM
    change m⁻¹ • (∑ i ∈ S, w i • q i) ∈ vertexHull q T
    rw [hpoint]
    simpa only [mul_smul, Finset.smul_sum] using hmem

private theorem subtract_common_weights {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] (q : ι → E)
    {s t : Finset ι} {x : E} (hs : x ∈ vertexHull q s) (ht : x ∈ vertexHull q t) :
    x ∈ vertexHull q (s ∩ t) ∨
      ∃ s' ⊆ s, ∃ t' ⊆ t, Disjoint s' t' ∧ (vertexHull q s' ∩ vertexHull q t').Nonempty := by
  obtain ⟨us, hus, hsumu, hpointu⟩ := weights_of_mem_vertexHull q s hs
  obtain ⟨vt, hvt, hsumv, hpointv⟩ := weights_of_mem_vertexHull q t ht
  let u (i : ι) : ℝ := if i ∈ s then us i else 0
  let v (i : ι) : ℝ := if i ∈ t then vt i else 0
  have hu (i : ι) : 0 ≤ u i := by
    by_cases hi : i ∈ s <;> simp [u, hi, hus]
  have hv (i : ι) : 0 ≤ v i := by
    by_cases hi : i ∈ t <;> simp [v, hi, hvt]
  have hU : ∑ i, u i = 1 := by simpa [u, ← Finset.sum_filter] using hsumu
  have hV : ∑ i, v i = 1 := by simpa [v, ← Finset.sum_filter] using hsumv
  have hpU : ∑ i, u i • q i = x := by
    simpa [u, ite_smul, ← Finset.sum_filter] using hpointu
  have hpV : ∑ i, v i • q i = x := by
    simpa [v, ite_smul, ← Finset.sum_filter] using hpointv
  rcases weighted_sum_eq_or_disjoint q hu hv hU hV
      (fun _ hi => ite_eq_right hi) (fun _ hi => ite_eq_right hi) (hpU.trans hpV.symm) with he | hd
  · left
    have hun (i : ι) (hi : i ∉ s ∩ t) : u i = 0 := by
      by_cases his : i ∈ s
      · have hit : i ∉ t := fun hit => hi (Finset.mem_inter.mpr ⟨his,hit⟩)
        simp [he, v, hit]
      · simp [u, his]
    have hm : ∑ i ∈ s ∩ t, u i = 1 := by
      rw [Finset.sum_subset (Finset.subset_univ _)]
      · exact hU
      · exact fun i _ hi => hun i hi
    have hp : ∑ i ∈ s ∩ t, u i • q i = x := by
      rw [Finset.sum_subset (Finset.subset_univ _)]
      · exact hpU
      · intro i _ hi
        simp [hun i hi]
    rw [← hp]
    exact weighted_mem_vertexHull q _ u (fun i _ => hu i) hm
  · exact Or.inr hd

private def signedVertex {ι : Type*} [DecidableEq ι]
    (q : ι → Point3) (s : Finset ι) (i : ι) : Point3 × ℝ :=
  if i ∈ s then (q i, 1) else (-q i, 0)

private theorem signedVertex_injective {ι : Type*} [DecidableEq ι]
    (q : ι → Point3) (hq : Function.Injective q) (s : Finset ι) :
    Function.Injective (signedVertex q s) := by
  intro i j h
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;>
    simp [signedVertex, hi, hj] at h
  · exact hq h
  · exact hq h

private theorem signedVertex_sum {ι : Type*} [DecidableEq ι] (q : ι → Point3)
    (s S T : Finset ι) (hs : S ⊆ s) (ht : Disjoint s T) (w : ι → ℝ) :
    (∑ i ∈ S ∪ T, w i • signedVertex q s i) =
      ((∑ i ∈ S, w i • q i) - ∑ i ∈ T, w i • q i, ∑ i ∈ S, w i) := by
  have hp : ∑ i ∈ S, w i • signedVertex q s i =
      ∑ i ∈ S, (w i • q i, w i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [signedVertex, hs hi]
  have hn : ∑ i ∈ T, w i • signedVertex q s i =
      ∑ i ∈ T, (-(w i • q i), 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ∉ s := fun hm => Finset.disjoint_left.mp ht hm hi
    simp [signedVertex, hi']
  rw [Finset.sum_union (ht.mono_left hs), hp, hn]
  apply Prod.ext
  · simp [Prod.fst_sum, sub_eq_add_neg]
  · simp [Prod.snd_sum]

/-- A convex intersection on two disjoint sets of labels has witness subsets with
at most five vertices total. The auxiliary coordinate records the mass on the
first side, while the spatial coordinates record the difference of the two sums. -/
private theorem shrink_disjoint_intersection {ι : Type*} [DecidableEq ι]
    (q : ι → Point3) (hq : Function.Injective q)
    {s t : Finset ι} (hst : Disjoint s t)
    (hx : (vertexHull q s ∩ vertexHull q t).Nonempty) :
    ∃ S ⊆ s, ∃ T ⊆ t, S.card + T.card ≤ 5 ∧
      (vertexHull q S ∩ vertexHull q T).Nonempty := by
  classical
  obtain ⟨x, hx₁, hx₂⟩ := hx
  obtain ⟨u, hupos, hu, hxu⟩ := weights_of_mem_vertexHull q s hx₁
  obtain ⟨v, hvpos, hv, hxv⟩ := weights_of_mem_vertexHull q t hx₂
  let w (i : ι) : ℝ := if i ∈ s then (1/2)*u i else (1/2)*v i
  have hL (i : ι) (hi : i ∈ s) : w i = (1/2)*u i := ite_eq_left hi
  have hR (i : ι) (hi : i ∈ t) : w i = (1/2)*v i :=
    ite_eq_right (fun h => Finset.disjoint_left.mp hst h hi)
  have hw (i : ι) (hi : i ∈ s ∪ t) : 0 ≤ w i := by
    rcases Finset.mem_union.mp hi with hi | hi
    · rw [hL i hi]
      exact mul_nonneg (by norm_num) (hupos i hi)
    · rw [hR i hi]
      exact mul_nonneg (by norm_num) (hvpos i hi)
  have hSL : ∑ i ∈ s, w i = 1/2 := by
    rw [Finset.sum_congr rfl hL, ← Finset.mul_sum, hu, mul_one]
  have hSR : ∑ i ∈ t, w i = 1/2 := by
    rw [Finset.sum_congr rfl hR, ← Finset.mul_sum, hv, mul_one]
  have hM : ∑ i ∈ s ∪ t, w i = 1 := by
    rw [Finset.sum_union hst, hSL, hSR]
    norm_num
  have hxL : ∑ i ∈ s, w i • q i = (1/2 : ℝ) • x := by
    rw [Finset.sum_congr rfl (fun i hi => congrArg (· • q i) (hL i hi))]
    simp only [mul_smul, ← Finset.smul_sum, hxu]
  have hxR : ∑ i ∈ t, w i • q i = (1/2 : ℝ) • x := by
    rw [Finset.sum_congr rfl (fun i hi => congrArg (· • q i) (hR i hi))]
    simp only [mul_smul, ← Finset.smul_sum, hxv]
  let q' := signedVertex q s
  have hq' : Function.Injective q' := signedVertex_injective q hq s
  have hmid : (0, (1/2 : ℝ)) ∈ vertexHull q' (s ∪ t) := by
    have hmem := weighted_mem_vertexHull q' _ w hw hM
    change (∑ i ∈ s ∪ t, w i • signedVertex q s i) ∈ _ at hmem
    rw [signedVertex_sum q s s t (by rfl) hst, hxL, hxR, sub_self, hSL] at hmem
    exact hmem
  rw [vertexHull, convexHull_eq_union] at hmid
  simp only [Set.mem_iUnion, exists_prop] at hmid
  obtain ⟨U, hUsub, hUind, hUmem⟩ := hmid
  have hUcard : U.card ≤ 5 := by
    have hbound := hUind.card_le_finrank_succ
    have hdim : Module.finrank ℝ (Point3 × ℝ) = 4 := by
      norm_num [Point3, Module.finrank_prod]
    have hspan := Submodule.finrank_le
      (vectorSpan ℝ (Set.range ((↑) : U → Point3 × ℝ)))
    rw [hdim] at hspan
    simpa using hbound.trans (Nat.add_le_add_right hspan 1)
  let D := (s ∪ t).filter (fun i => q' i ∈ U)
  have hDsub : D ⊆ s ∪ t := Finset.filter_subset _ _
  have hDimage : D.image q' = U := by
    ext y
    constructor
    · rintro hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hi).2
    · intro hy
      obtain ⟨i, hi, rfl⟩ := hUsub (Finset.mem_coe.mpr hy)
      exact Finset.mem_image_of_mem q' (Finset.mem_filter.mpr ⟨hi, hy⟩)
  have hDcard : D.card ≤ 5 := by
    rwa [← hDimage, Finset.card_image_of_injective _ hq'] at hUcard
  have hDmem : (0, (1/2 : ℝ)) ∈ vertexHull q' D := by
    rw [vertexHull, ← Finset.coe_image, hDimage]
    exact hUmem
  obtain ⟨f, hfpos, hf, hpoint⟩ := weights_of_mem_vertexHull q' D hDmem
  let S := D ∩ s
  let T := D ∩ t
  have hsS : S ⊆ s := Finset.inter_subset_right
  have htT : T ⊆ t := Finset.inter_subset_right
  have hST : Disjoint S T := hst.mono hsS htT
  have hUnion : S ∪ T = D := by
    ext i
    simp only [S, T, Finset.mem_union, Finset.mem_inter]
    by_cases hi : i ∈ D
    · simpa [hi] using hDsub hi
    · simp [hi]
  have hC : S.card + T.card ≤ 5 := by
    rw [← Finset.card_union_of_disjoint hST, hUnion]
    exact hDcard
  rw [← hUnion, Finset.sum_union hST] at hf
  rw [← hUnion, signedVertex_sum q s S T hsS (hst.mono_right htT)] at hpoint
  have hmS : ∑ i ∈ S, f i = 1/2 := congrArg Prod.snd hpoint
  have hmT : ∑ i ∈ T, f i = 1/2 := by linarith
  have hp : (∑ i ∈ S, f i • q i) = ∑ i ∈ T, f i • q i :=
    sub_eq_zero.mp (congrArg Prod.fst hpoint)
  let X := (2 : ℝ) • (∑ i ∈ S, f i • q i)
  refine ⟨S, hsS, T, htT, hC, X, ?_, ?_⟩
  · have hM' : ∑ i ∈ S, (2 : ℝ) * f i = 1 := by
      rw [← Finset.mul_sum, hmS]
      norm_num
    have hmem := weighted_mem_vertexHull q S (fun i => (2 : ℝ)*f i)
      (fun i hi => mul_nonneg (by norm_num) (hfpos i (Finset.mem_inter.mp hi).1)) hM'
    simpa only [X, mul_smul, Finset.smul_sum] using hmem
  · have hM' : ∑ i ∈ T, (2 : ℝ) * f i = 1 := by
      rw [← Finset.mul_sum, hmT]
      norm_num
    have hmem := weighted_mem_vertexHull q T (fun i => (2 : ℝ)*f i)
      (fun i hi => mul_nonneg (by norm_num) (hfpos i (Finset.mem_inter.mp hi).1)) hM'
    change (2 : ℝ) • (∑ i ∈ S, f i • q i) ∈ vertexHull q T
    rw [hp]
    simpa only [mul_smul, Finset.smul_sum] using hmem

private theorem vertexHull_inter_of_independent {ι E : Type*} [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] (q : ι → E) (hq : Function.Injective q)
    (s t : Finset ι) (hind : AffineIndepOn ℝ q (↑(s ∪ t) : Set ι)) :
    vertexHull q s ∩ vertexHull q t = vertexHull q (s ∩ t) := by
  classical
  have hp : AffineIndependent ℝ ((↑) : ((s ∪ t).image q) → E) := by
    change AffineIndepOn ℝ id (↑((s ∪ t).image q) : Set E)
    rw [Finset.coe_image]
    exact hind.id_image
  rw [vertexHull, vertexHull, vertexHull, ← Finset.coe_image, ← Finset.coe_image,
    ← Finset.coe_image, Finset.image_inter s t hq]
  simpa only [Finset.coe_inter] using (hp.convexHull_inter
    (Finset.image_subset_image Finset.subset_union_left)
    (Finset.image_subset_image Finset.subset_union_right)).symm

/-- In general position, every intersection of two simplices of dimension at most
two is their shared face if the disjoint edge–triangle tests hold. -/
theorem vertexHull_inter_of_edgeTriangle {p : Vertex → ℝ × ℝ} {z : Vertex → ℝ}
    (hg : GenericLift p z) (s t : Finset Vertex) (hs : s.card ≤ 3) (ht : t.card ≤ 3) :
    let q : Vertex → Point3 := fun i => ((p i).1,(p i).2,z i)
    (∀ e ⊆ s, e.card = 2 → t.card = 3 → Disjoint e t →
      Disjoint (vertexHull q e) (vertexHull q t)) →
    (∀ e ⊆ t, e.card = 2 → s.card = 3 → Disjoint e s →
      Disjoint (vertexHull q e) (vertexHull q s)) →
    vertexHull q s ∩ vertexHull q t = vertexHull q (s ∩ t) := by
  classical
  dsimp only
  intro sepST sepTS
  let q (i : Vertex) : Point3 := ((p i).1,(p i).2,z i)
  change vertexHull q s ∩ vertexHull q t = vertexHull q (s ∩ t)
  have hinj : Function.Injective q := generic_point_injective p z hg
  apply Set.Subset.antisymm ?_ (Set.subset_inter
    (vertexHull_mono q Finset.inter_subset_left) (vertexHull_mono q Finset.inter_subset_right))
  rintro x ⟨hx, hy⟩
  rcases subtract_common_weights q hx hy with h | ⟨s', hs', t', ht', hd', hm⟩
  · exact h
  obtain ⟨S, hS, T, hT, hcard, hinter⟩ := shrink_disjoint_intersection q hinj hd' hm
  have hS' := hS.trans hs'
  have hT' := hT.trans ht'
  have hST := hd'.mono hS hT
  exfalso
  by_cases hle : S.card + T.card ≤ 4
  · have hind := generic_affineIndependentOn p z hg (S ∪ T)
      (by rwa [Finset.card_union_of_disjoint hST])
    rw [vertexHull_inter_of_independent q hinj S T hind, Finset.disjoint_iff_inter_eq_empty.mp hST]
      at hinter
    simp [vertexHull] at hinter
  · have hSC := (Finset.card_le_card hS').trans hs
    have hTC := (Finset.card_le_card hT').trans ht
    have hex : (S.card = 2 ∧ T.card = 3) ∨ (S.card = 3 ∧ T.card = 2) := by omega
    rcases hex with ⟨hSc, hTc⟩ | ⟨hSc, hTc⟩
    · have he : T = t := Finset.eq_of_subset_of_card_le hT' (by omega)
      subst t
      exact (Set.disjoint_iff_inter_eq_empty.mp (sepST S hS' hSc hTc hST) ▸ hinter).ne_empty rfl
    · have he : S = s := Finset.eq_of_subset_of_card_le hS' (by omega)
      subst s
      rw [Set.inter_comm] at hinter
      exact (Set.disjoint_iff_inter_eq_empty.mp (sepTS T hT' hTc hSc hST.symm) ▸ hinter).ne_empty rfl

/-- The set of labels in one triangle of the face list. -/
def triangleVertexSet (f : Triangle) : Finset Vertex := (triangleVertices f).toFinset

@[simp]
theorem mem_triangleVertexSet (i : Vertex) (f : Triangle) :
    i ∈ triangleVertexSet f ↔ i ∈ triangleVertices f := List.mem_toFinset

theorem triangleVertexSet_card_le (f : Triangle) : (triangleVertexSet f).card ≤ 3 :=
  (List.toFinset_card_le _).trans (by simp [triangleVertices])

theorem triangleVertexSet_eq (a b c : Vertex) : triangleVertexSet (a,b,c) = {a,b,c} := by
  simp [triangleVertexSet, triangleVertices]

theorem vertexHull_pair (q : Vertex → Point3) (a b : Vertex) :
    vertexHull q {a,b} = segment ℝ (q a) (q b) := by
  simp [vertexHull, convexHull_pair]

theorem vertexHull_triangle (q : Vertex → Point3) (a b c : Vertex) :
    vertexHull q (triangleVertexSet (a,b,c)) =
    convexHull ℝ (Set.range (![q a,q b,q c] : Fin 3 → Point3)) := by
  simp [vertexHull, triangleVertexSet_eq, Matrix.range_cons]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem orderedEdge_labelSet (a b : Vertex) :
    ({(orderedEdge a b).1, (orderedEdge a b).2} : Finset Vertex) = {a,b} := by
  rcases le_total a b with h | h
  · simp [orderedEdge, min_eq_left h, max_eq_right h]
  · simp [orderedEdge, min_eq_right h, max_eq_left h, Finset.pair_comm]

private theorem orderedEdge_mem_of_pair_subset {a b : Vertex} {f : Triangle}
    (hab : a ≠ b) (hs : {a,b} ⊆ triangleVertexSet f) :
    orderedEdge a b ∈ faceEdges f := by
  rcases f with ⟨u,v,w⟩
  have ha := hs (Finset.mem_insert_self _ _ : a ∈ ({a,b} : Finset Vertex))
  have hb := hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self b) : b ∈ ({a,b} : Finset Vertex))
  simp only [triangleVertexSet_eq, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> subst a <;> subst b <;>
    first | contradiction | simp [faceEdges, orderedEdge, min_comm, max_comm]

/-- The disjoint edge–triangle separation tests for an oriented face list. -/
def EdgeTriangleSeparated (q : Vertex → Point3) (fs : List Triangle) : Prop :=
  ∀ e ∈ fs.flatMap faceEdges, ∀ f ∈ fs,
    Disjoint ({e.1,e.2} : Finset Vertex) (triangleVertexSet f) →
    Disjoint (vertexHull q {e.1,e.2}) (vertexHull q (triangleVertexSet f))

/-- All nonempty subsets of the triangles in the labeled face list. -/
def triangleComplex (fs : List Triangle) : PreAbstractSimplicialComplex Vertex where
  faces := {s | s.Nonempty ∧ ∃ f ∈ fs, s ⊆ triangleVertexSet f}
  isRelLowerSet_faces := by
    rintro s ⟨hs, f, hf, hb⟩
    exact ⟨hs, fun t ht hn => ⟨hn, f, hf, ht.trans hb⟩⟩

private theorem sep_subfaces {p : Vertex → ℝ × ℝ} {z : Vertex → ℝ}
    {fs : List Triangle} (s t : Finset Vertex)
    (hs : s ∈ (triangleComplex fs).faces) (ht : t ∈ (triangleComplex fs).faces) :
    let q (i : Vertex) : Point3 := ((p i).1,(p i).2,z i)
    EdgeTriangleSeparated q fs →
    ∀ e ⊆ s, e.card = 2 → t.card = 3 → Disjoint e t →
      Disjoint (vertexHull q e) (vertexHull q t) := by
  dsimp only
  intro hsep e he hcard hc hd
  obtain ⟨_, F, hF, hsubF⟩ := hs
  obtain ⟨_, G, hG, hsubG⟩ := ht
  have hgEq : t = triangleVertexSet G :=
    Finset.eq_of_subset_of_card_le hsubG (hc ▸ triangleVertexSet_card_le G)
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hcard
  have hE : orderedEdge a b ∈ fs.flatMap faceEdges :=
    List.mem_flatMap.mpr ⟨F, hF, orderedEdge_mem_of_pair_subset hab (he.trans hsubF)⟩
  rw [hgEq] at hd ⊢
  have h := hsep (orderedEdge a b) hE G hG (by rwa [orderedEdge_labelSet])
  rwa [orderedEdge_labelSet] at h

end

/-- The spatial triangles and all their subfaces form a geometric simplicial complex. -/
public noncomputable def spatialTriangleComplex (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ)
    (fs : List Triangle) (hg : GenericLift p z)
    (hsep : EdgeTriangleSeparated (fun i => ((p i).1,(p i).2,z i)) fs) :
    Geometry.SimplicialComplex ℝ Point3 := by
  classical
  let q (i : Vertex) : Point3 := ((p i).1,(p i).2,z i)
  have hq : Function.Injective q := generic_point_injective p z hg
  have card_bound {s : Finset Vertex} (hs : s ∈ (triangleComplex fs).faces) : s.card ≤ 3 := by
    obtain ⟨_, f, _, hf⟩ := hs
    exact (Finset.card_le_card hf).trans (triangleVertexSet_card_le f)
  refine { (triangleComplex fs).map q with
    indep := ?_, inter_subset_convexHull := ?_ }
  · rintro _ ⟨s, hs, rfl⟩
    change AffineIndepOn ℝ id (↑(Finset.image q s) : Set Point3)
    rw [Finset.coe_image]
    exact (generic_affineIndependentOn p z hg s ((card_bound hs).trans (by decide))).id_image
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    have h := vertexHull_inter_of_edgeTriangle hg s t (card_bound hs) (card_bound ht)
      (sep_subfaces s t hs ht hsep) (sep_subfaces t s ht hs hsep)
    change (convexHull ℝ ↑(s.image q) ∩ convexHull ℝ ↑(t.image q)) ⊆
      convexHull ℝ ((↑(s.image q) : Set Point3) ∩ ↑(t.image q))
    rw [← Finset.coe_inter, ← Finset.image_inter s t hq]
    simpa only [vertexHull, ← Finset.coe_image] using h.le

/-- The geometric complex retains exactly the subfaces of the labeled triangles. -/
public theorem spatialTriangleComplex_faces (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ)
    (fs : List Triangle) (hg : GenericLift p z)
    (hsep : EdgeTriangleSeparated (fun i => ((p i).1,(p i).2,z i)) fs) :
    (spatialTriangleComplex p z fs hg hsep).faces =
      ((triangleComplex fs).map (fun i => ((p i).1,(p i).2,z i))).faces := by
  rw [spatialTriangleComplex]

@[expose] public section

/-- Barycentric coordinates supported on a prescribed face. -/
def faceWeights (s : Finset Vertex) : Set (Vertex → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ ∀ i ∉ s, w i = 0}

theorem faceWeights_mono {s t : Finset Vertex} (h : s ⊆ t) :
    faceWeights s ⊆ faceWeights t :=
  fun _ hw => ⟨hw.1, hw.2.1, fun i hi => hw.2.2 i (hi ∘ @h i)⟩

theorem isCompact_faceWeights (s : Finset Vertex) : IsCompact (faceWeights s) := by
  have he : faceWeights s =
      (⋂ i : Vertex, {w | 0 ≤ w i}) ∩ {w | ∑ i, w i = (1 : ℝ)} ∩
        ⋂ i : Vertex, ⋂ _ : i ∉ s, {w | w i = 0} := by
    ext w
    simp only [faceWeights, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    tauto
  have hc : IsClosed (faceWeights s) := by
    rw [he]
    refine ((isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)).inter ?_
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply i) continuous_const
  apply isCompact_Icc.of_isClosed_subset hc
  intro w hw
  exact ⟨hw.1, fun i => hw.2.1 ▸ Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)⟩

/-- The labeled realization obtained by gluing the coordinate simplices along common faces. -/
def triangleWeightSpace (fs : List Triangle) : Set (Vertex → ℝ) :=
  {w | ∃ f ∈ fs, w ∈ faceWeights (triangleVertexSet f)}

theorem isCompact_triangleWeightSpace (fs : List Triangle) : IsCompact (triangleWeightSpace fs) := by
  have he : triangleWeightSpace fs =
      ⋃ f ∈ (fs.toFinset : Set Triangle), faceWeights (triangleVertexSet f) := by
    ext w
    simp [triangleWeightSpace]
  rw [he]
  exact fs.toFinset.finite_toSet.isCompact_biUnion fun f _ => isCompact_faceWeights _

/-- The affine evaluation map on barycentric coordinates. -/
noncomputable def evaluateWeights (q : Vertex → Point3) (w : Vertex → ℝ) : Point3 :=
  ∑ i, w i • q i

/-- The spatial realization map is affine in the weights on each face. -/
noncomputable def evaluateTriangles (fs : List Triangle) (q : Vertex → Point3)
    (w : triangleWeightSpace fs) : Point3 := evaluateWeights q w.val

theorem evaluateTriangles_comp_linear (fs : List Triangle) (q : Vertex → Point3)
    (L : Point3 →ₗ[ℝ] Point3) :
    evaluateTriangles fs (L ∘ q) = L ∘ evaluateTriangles fs q := by
  funext w
  simp [evaluateTriangles,evaluateWeights,Function.comp_apply,map_sum]

/-- Barycentric evaluation commutes with subtracting a common origin. -/
theorem evaluateTriangles_sub_origin (fs : List Triangle) (q : Vertex → Point3) (o : Point3)
    (w : triangleWeightSpace fs) :
    evaluateTriangles fs (fun i => q i-o) w = evaluateTriangles fs q w-o := by
  have hm : ∑ i, w.val i = 1 := by
    obtain ⟨f,hf,hw⟩ := w.property
    exact hw.2.1
  simp only [evaluateTriangles,evaluateWeights,smul_sub,Finset.sum_sub_distrib,
    ← Finset.sum_smul,hm,one_smul]

private theorem continuous_evaluateWeights :
    Continuous (fun p : (Vertex → Point3) × (Vertex → ℝ) => evaluateWeights p.1 p.2) := by
  unfold evaluateWeights
  fun_prop

theorem continuous_evaluateTriangles (fs : List Triangle) (q : Vertex → Point3) :
    Continuous (evaluateTriangles fs q) :=
  continuous_evaluateWeights.comp (continuous_const.prodMk continuous_subtype_val)

private theorem evaluateWeights_of_mem_vertexHull (q : Vertex → Point3) (s : Finset Vertex)
    {x : Point3} (hx : x ∈ vertexHull q s) :
    ∃ w ∈ faceWeights s, evaluateWeights q w = x := by
  obtain ⟨u, hpos, hmass, hpoint⟩ := weights_of_mem_vertexHull q s hx
  let w (i : Vertex) : ℝ := if i ∈ s then u i else 0
  refine ⟨w, ⟨fun i => ?_, ?_, fun _ hi => ite_eq_right hi⟩, ?_⟩
  · by_cases hi : i ∈ s <;> simp [w, hi, hpos]
  · simpa [w, ← Finset.sum_filter] using hmass
  · simpa [w, evaluateWeights, ite_smul, ← Finset.sum_filter] using hpoint

/-- An embedding excludes intersection of the convex hulls of label-disjoint subfaces. -/
theorem disjoint_vertexHull_of_injective_evaluateTriangles (fs : List Triangle)
    (q : Vertex → Point3) (hinj : Function.Injective (evaluateTriangles fs q))
    (s t : Finset Vertex) (hs : s ∈ (triangleComplex fs).faces)
    (ht : t ∈ (triangleComplex fs).faces) (hd : Disjoint s t) :
    Disjoint (vertexHull q s) (vertexHull q t) := by
  rw [Set.disjoint_left]
  intro x hxs hxt
  obtain ⟨u,hu,hxu⟩ := evaluateWeights_of_mem_vertexHull q s hxs
  obtain ⟨v,hv,hxv⟩ := evaluateWeights_of_mem_vertexHull q t hxt
  obtain ⟨_,f,hf,hsf⟩ := hs
  obtain ⟨_,g,hg,htg⟩ := ht
  let U : triangleWeightSpace fs := ⟨u,f,hf,faceWeights_mono hsf hu⟩
  let V : triangleWeightSpace fs := ⟨v,g,hg,faceWeights_mono htg hv⟩
  have he : U = V := hinj (hxu.trans hxv.symm)
  have h : u = v := congrArg Subtype.val he
  have hz (i : Vertex) : u i = 0 := by
    by_cases hi : i ∈ s
    · exact h ▸ hv.2.2 i (Finset.disjoint_left.mp hd hi)
    · exact hu.2.2 i hi
  have hmass := hu.2.1
  simp [hz] at hmass

/-- Testing disjoint label subfaces for actual convex intersection is
equivalent to injectivity of the entire piecewise-affine map. -/
theorem evaluateTriangles_injective_iff_disjoint_subfaces (fs : List Triangle) (q : Vertex → Point3) :
    Function.Injective (evaluateTriangles fs q) ↔
      ∀ s t : Finset Vertex, s ∈ (triangleComplex fs).faces → t ∈ (triangleComplex fs).faces →
      Disjoint s t → Disjoint (vertexHull q s) (vertexHull q t) := by
  constructor
  · exact disjoint_vertexHull_of_injective_evaluateTriangles fs q
  · intro H u v hpoint
    obtain ⟨f,hf,hu,hU,hus⟩ := u.property
    obtain ⟨g,hg,hv,hV,hvt⟩ := v.property
    rcases weighted_sum_eq_or_disjoint q hu hv hU hV hus hvt hpoint with h | ⟨s,hs,t,ht,hd,x,hxs,hxt⟩
    · exact Subtype.ext h
    · have hn (S : Finset Vertex) (h : x ∈ vertexHull q S) : S.Nonempty := by
        by_contra! hempty
        simp [hempty,vertexHull] at h
      exact (Set.disjoint_left.mp (H s t ⟨hn s hxs,f,hf,hs⟩ ⟨hn t hxt,g,hg,ht⟩ hd) hxs hxt).elim

theorem vertex_injective_of_injective_evaluateTriangles (fs : List Triangle) (q : Vertex → Point3)
    (hcover : ∀ a : Vertex, ∃ f ∈ fs, a ∈ triangleVertexSet f)
    (hinj : Function.Injective (evaluateTriangles fs q)) : Function.Injective q := by
  have singleton_face (a : Vertex) : {a} ∈ (triangleComplex fs).faces := by
    obtain ⟨f,hf,ha⟩ := hcover a
    exact ⟨Finset.singleton_nonempty a,f,hf,Finset.singleton_subset_iff.mpr ha⟩
  intro a b he
  by_contra hn
  have hd := disjoint_vertexHull_of_injective_evaluateTriangles fs q hinj
    {a} {b} (singleton_face a) (singleton_face b) (Finset.disjoint_singleton.mpr hn)
  exact Set.disjoint_left.mp hd (subset_convexHull ℝ _ ⟨a,by simp,rfl⟩)
    (subset_convexHull ℝ _ ⟨b,by simp,he.symm⟩)

/-- An injective affine realization remains injective under small changes of its vertices. -/
theorem isOpen_injective_evaluateTriangles (fs : List Triangle) :
    IsOpen {q | Function.Injective (evaluateTriangles fs q)} := by
  let W := triangleWeightSpace fs
  let _ : CompactSpace W := isCompact_iff_compactSpace.mp (isCompact_triangleWeightSpace fs)
  let B : Set ((Vertex → Point3) × (W × W)) := {p |
    evaluateTriangles fs p.1 p.2.1 = evaluateTriangles fs p.1 p.2.2 ∧
      ∀ i, (p.2.1.val i) * (p.2.2.val i) = 0}
  have hc : IsClosed B := by
    rw [show B = {p : (Vertex → Point3) × (W × W) |
      evaluateTriangles fs p.1 p.2.1 = evaluateTriangles fs p.1 p.2.2} ∩
      ⋂ i : Vertex, {p | (p.2.1.val i) * (p.2.2.val i) = 0} by ext p; simp [B]]
    have ha : Continuous (fun p : (Vertex → Point3) × (W × W) => p.2.1.val) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    have hb : Continuous (fun p : (Vertex → Point3) × (W × W) => p.2.2.val) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    have he₁ : Continuous (fun p : (Vertex → Point3) × (W × W) =>
        evaluateTriangles fs p.1 p.2.1) :=
      continuous_evaluateWeights.comp (continuous_fst.prodMk ha)
    have he₂ : Continuous (fun p : (Vertex → Point3) × (W × W) =>
        evaluateTriangles fs p.1 p.2.2) :=
      continuous_evaluateWeights.comp (continuous_fst.prodMk hb)
    refine (isClosed_eq he₁ he₂).inter (isClosed_iInter fun i => ?_)
    exact isClosed_eq (((continuous_apply i).comp ha).mul ((continuous_apply i).comp hb))
      continuous_const
  have hbad : Prod.fst '' B = {q | Function.Injective (evaluateTriangles fs q)}ᶜ := by
    ext q
    constructor
    · rintro ⟨⟨q,u,v⟩, ⟨he,hs⟩, rfl⟩ hinj
      have huv : u = v := hinj he
      subst v
      obtain ⟨f,_,_,hmass,_⟩ := u.property
      have hn : ∀ i, u.val i = 0 := fun i => (mul_eq_zero.mp (hs i)).elim id id
      simp [hn] at hmass
    · intro hinj
      change ¬ Function.Injective (evaluateTriangles fs q) at hinj
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨u,v,hpoint,hne⟩ := hinj
      obtain ⟨f,hf,hu,hU,hus⟩ := u.property
      obtain ⟨g,hg,hv,hV,hvt⟩ := v.property
      rcases weighted_sum_eq_or_disjoint q hu hv hU hV hus hvt hpoint with he |
          ⟨s,hs,t,ht,hd,x,hxs,hxt⟩
      · exact (hne (Subtype.ext he)).elim
      obtain ⟨a,ha,hea⟩ := evaluateWeights_of_mem_vertexHull q s hxs
      obtain ⟨b,hb,heb⟩ := evaluateWeights_of_mem_vertexHull q t hxt
      let A : W := ⟨a, f, hf, faceWeights_mono hs ha⟩
      let C : W := ⟨b, g, hg, faceWeights_mono ht hb⟩
      refine ⟨(q,A,C), ⟨hea.trans heb.symm, fun i => ?_⟩, rfl⟩
      change a i * b i = 0
      by_cases hi : i ∈ s
      · rw [hb.2.2 i (Finset.disjoint_left.mp hd hi), mul_zero]
      · rw [ha.2.2 i hi, zero_mul]
  simpa only [hbad, compl_compl] using (isClosedMap_fst_of_compactSpace _ hc).isOpen_compl

/-- A geometric complex with the prescribed faces realizes the labeled weight space. -/
theorem evaluateTriangles_isClosedEmbedding (fs : List Triangle) (q : Vertex → Point3)
    (hq : Function.Injective q) (K : Geometry.SimplicialComplex ℝ Point3)
    (hK : K.faces = ((triangleComplex fs).map q).faces) :
    Topology.IsClosedEmbedding (evaluateTriangles fs q) := by
  let _ : CompactSpace (triangleWeightSpace fs) :=
    isCompact_iff_compactSpace.mp (isCompact_triangleWeightSpace fs)
  apply (continuous_evaluateTriangles fs q).isClosedEmbedding
  intro u v hpoint
  obtain ⟨f,hf,hu,hU,hus⟩ := u.property
  obtain ⟨g,hg,hv,hV,hvt⟩ := v.property
  rcases weighted_sum_eq_or_disjoint q hu hv hU hV hus hvt hpoint with he |
      ⟨s,hs,t,ht,hd,x,hxs,hxt⟩
  · exact Subtype.ext he
  exfalso
  have hn {s : Finset Vertex} (hx : x ∈ vertexHull q s) : s.Nonempty := by
    by_contra! h
    simp [h, vertexHull] at hx
  have H₁ : s.image q ∈ K.faces := hK ▸ ⟨s, ⟨hn hxs, f, hf, hs⟩, rfl⟩
  have H₂ : t.image q ∈ K.faces := hK ▸ ⟨t, ⟨hn hxt, g, hg, ht⟩, rfl⟩
  have h := K.inter_subset_convexHull H₁ H₂
  rw [← Finset.coe_inter, ← Finset.image_inter s t hq, Finset.disjoint_iff_inter_eq_empty.mp hd] at h
  have hx := h (show x ∈ convexHull ℝ ↑(s.image q) ∩ convexHull ℝ ↑(t.image q) from by
    simpa only [Set.mem_inter_iff, Finset.coe_image, vertexHull] using And.intro hxs hxt)
  simp at hx

/-- The strict edge–face tests give a topological embedding of the labeled complex. -/
theorem spatialTriangles_isClosedEmbedding (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ)
    (fs : List Triangle) (hg : GenericLift p z)
    (hsep : EdgeTriangleSeparated (fun i => ((p i).1,(p i).2,z i)) fs) :
    Topology.IsClosedEmbedding (evaluateTriangles fs (fun i => ((p i).1,(p i).2,z i))) :=
  evaluateTriangles_isClosedEmbedding fs _ (generic_point_injective p z hg)
    (spatialTriangleComplex p z fs hg hsep) (spatialTriangleComplex_faces p z fs hg hsep)

end

end OrigamiTorus
