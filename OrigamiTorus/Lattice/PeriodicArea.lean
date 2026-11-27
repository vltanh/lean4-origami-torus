module

public import OrigamiTorus.Geometry.PlanarArea
public import OrigamiTorus.EightVertex.Type6.IntrinsicMap
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! Area of integer translates clipped to a fundamental cell. -/

public section

open Set MeasureTheory
open scoped ENNReal

namespace OrigamiTorus

local notation "planeVolume" => (MeasureTheory.volume : Measure (ℝ × ℝ))

/-- Representatives in the half-open unit square. -/
@[expose] def unitCell : Set (ℝ × ℝ) := Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1

theorem measurableSet_unitCell : MeasurableSet unitCell :=
  measurableSet_Ico.prod measurableSet_Ico

theorem volume_unitCell : planeVolume unitCell = 1 := by
  change ((MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure ℝ))
    (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) = 1
  simp only [Measure.prod_prod,Real.volume_Ico]
  norm_num

private def shiftedCell (d : Period) : Set (ℝ × ℝ) :=
  {p | (⌊p.1⌋, ⌊p.2⌋) = d}

private theorem measurableSet_shiftedCell (d : Period) : MeasurableSet (shiftedCell d) := by
  have he : shiftedCell d =
      Ico (d.1 : ℝ) ((d.1 : ℝ)+1) ×ˢ Ico (d.2 : ℝ) ((d.2 : ℝ)+1) := by
    ext p
    change (⌊p.1⌋, ⌊p.2⌋) = d ↔
      ((d.1 : ℝ) ≤ p.1 ∧ p.1 < (d.1 : ℝ)+1) ∧ ((d.2 : ℝ) ≤ p.2 ∧ p.2 < (d.2 : ℝ)+1)
    rcases d with ⟨m,n⟩
    rw [Prod.mk.injEq,Int.floor_eq_iff,Int.floor_eq_iff]
  rw [he]
  exact measurableSet_Ico.prod measurableSet_Ico

private theorem shiftedCell_preimage (d : Period) :
    (fun p => p+realPeriod d) ⁻¹' shiftedCell d = unitCell := by
  rcases d with ⟨m,n⟩
  ext p
  change (⌊p.1+(m : ℝ)⌋, ⌊p.2+(n : ℝ)⌋) = (m,n) ↔
    (0 ≤ p.1 ∧ p.1 < 1) ∧ (0 ≤ p.2 ∧ p.2 < 1)
  rw [Prod.mk.injEq,Int.floor_eq_iff,Int.floor_eq_iff]
  constructor
  · rintro ⟨⟨hm,hm'⟩,⟨hn,hn'⟩⟩
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  · rintro ⟨⟨hm,hm'⟩,⟨hn,hn'⟩⟩
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

/-- The portion of a lifted set in cell `d`, represented in the unit square. -/
@[expose] def cellPiece (S : Set (ℝ × ℝ)) (d : Period) : Set (ℝ × ℝ) :=
  unitCell ∩ (fun p => p+realPeriod d) ⁻¹' S

theorem measurableSet_cellPiece {S : Set (ℝ × ℝ)} (hs : MeasurableSet S) (d : Period) :
    MeasurableSet (cellPiece S d) :=
  measurableSet_unitCell.inter (hs.preimage (continuous_id.add continuous_const).measurable)

/-- The sum of clipped areas equals the area of the lifted set. -/
theorem volume_eq_tsum_cellPiece {S : Set (ℝ × ℝ)} (hs : MeasurableSet S) :
    planeVolume S = ∑' d : Period, planeVolume (cellPiece S d) := by
  have hu : (⋃ d : Period, shiftedCell d ∩ S) = S := by
    ext p
    exact ⟨fun h => (mem_iUnion.mp h).choose_spec.2,
      fun h => mem_iUnion.mpr ⟨(⌊p.1⌋,⌊p.2⌋),rfl,h⟩⟩
  have hp : Pairwise (Function.onFun Disjoint fun d => shiftedCell d ∩ S) := by
    intro d e hde
    change Disjoint (shiftedCell d ∩ S) (shiftedCell e ∩ S)
    rw [Set.disjoint_left]
    intro p hp hq
    exact hde (hp.1.symm.trans hq.1)
  have hm : ∀ d : Period, MeasurableSet (shiftedCell d ∩ S) :=
    fun d => (measurableSet_shiftedCell d).inter hs
  calc
    planeVolume S = ∑' d : Period, planeVolume (shiftedCell d ∩ S) :=
      (congrArg planeVolume hu.symm).trans (measure_iUnion hp hm)
    _ = _ := tsum_congr fun d => by
      rw [← volume_planarTranslate_preimage (realPeriod d) (shiftedCell d ∩ S),
        preimage_inter,shiftedCell_preimage]
      rfl

/-- Two planar representatives project to the same point exactly when their difference
has integral coordinates. -/
theorem projectPeriods_eq_iff (p q : ℝ × ℝ) :
    projectPeriods p = projectPeriods q ↔ ∃ d : Period, p + realPeriod d = q := by
  have hcoords (r : ℝ × ℝ) : periodCoordinates 0 1 r = r := by
    apply Prod.ext <;> simp [periodCoordinates]
  have h := periodCoordinates_project_eq_iff 0 1 (by norm_num) p q
  simp only [hcoords] at h
  rw [h]
  apply exists_congr
  intro d
  have he : translatePoint 0 1 d p = p + realPeriod d := by
    apply Prod.ext <;> simp [translatePoint,realPeriod]
  rw [he]

private theorem projectPeriods_continuous : Continuous projectPeriods :=
  ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)

private theorem projectPeriods_surjective : Function.Surjective projectPeriods := by
  rintro ⟨u,v⟩
  obtain ⟨a,ha⟩ := QuotientAddGroup.mk_surjective u
  obtain ⟨b,hb⟩ := QuotientAddGroup.mk_surjective v
  exact ⟨(a,b),Prod.ext ha hb⟩

/-- A nonempty open subset of the marked torus has a positive-area preimage in
the unit square. -/
theorem volume_pos_unitCell_preimage {S : Set MarkedTorus} (ho : IsOpen S) (hn : S.Nonempty) :
    0 < planeVolume (unitCell ∩ projectPeriods ⁻¹' S) := by
  let T := projectPeriods ⁻¹' S
  have ht : IsOpen T := ho.preimage projectPeriods_continuous
  have hpos : 0 < planeVolume T := ht.measure_pos _ (hn.preimage projectPeriods_surjective)
  have he (d : Period) : cellPiece T d = unitCell ∩ projectPeriods ⁻¹' S := by
    ext p
    change (p ∈ unitCell ∧ projectPeriods (p+realPeriod d) ∈ S) ↔
      (p ∈ unitCell ∧ projectPeriods p ∈ S)
    rw [((projectPeriods_eq_iff p (p+realPeriod d)).mpr ⟨d,rfl⟩).symm]
  by_contra! hzero
  have hz := le_antisymm hzero bot_le
  rw [volume_eq_tsum_cellPiece ht.measurableSet] at hpos
  simp only [he,hz,tsum_zero,lt_self_iff_false] at hpos

/-- If a countable measurable cover uses exactly the area of its union,
every pair of distinct pieces has null intersection. -/
theorem volume_inter_eq_zero_of_union_eq_tsum {ι : Type*} [Countable ι]
    (S : ι → Set (ℝ × ℝ)) (hm : ∀ i, MeasurableSet (S i))
    (hfin : (∑' i, planeVolume (S i)) ≠ ∞)
    (harea : planeVolume (⋃ i, S i) = ∑' i, planeVolume (S i))
    {i j : ι} (hij : i ≠ j) : planeVolume (S i ∩ S j) = 0 := by
  classical
  let ids : Finset ι := {i,j}
  let Others := ((ids : Set ι)ᶜ)
  let rest : Set (ℝ × ℝ) := ⋃ k : Others, S k.val
  let m := ∑' k : Others, planeVolume (S k.val)
  have hrest : planeVolume rest ≤ m := measure_iUnion_le _
  have he : (⋃ k, S k) = (S i ∪ S j) ∪ rest := by
    ext p
    constructor
    · intro hp
      obtain ⟨k,hk⟩ := mem_iUnion.mp hp
      by_cases hi : k = i
      · exact Or.inl (Or.inl (hi ▸ hk))
      by_cases hj : k = j
      · exact Or.inl (Or.inr (hj ▸ hk))
      exact Or.inr <| mem_iUnion.mpr ⟨⟨k,by simp [Others,ids,hi,hj]⟩,hk⟩
    · rintro ((hi | hj) | hr)
      · exact mem_iUnion.mpr ⟨i,hi⟩
      · exact mem_iUnion.mpr ⟨j,hj⟩
      · obtain ⟨k,hk⟩ := mem_iUnion.mp hr
        exact mem_iUnion.mpr ⟨k.val,hk⟩
  have hsum : (planeVolume (S i) + planeVolume (S j)) + m = ∑' k, planeVolume (S k) := by
    have h := sum_add_tsum_compl ids (fun k => planeVolume (S k))
    rw [show ids = {i,j} from rfl,Finset.sum_pair hij] at h
    exact h
  let budget := planeVolume (S i ∪ S j) + m
  have htotal : budget + planeVolume (S i ∩ S j) = ∑' k, planeVolume (S k) := by
    change (planeVolume (S i ∪ S j)+m)+planeVolume (S i ∩ S j) = _
    rw [add_right_comm,measure_union_add_inter _ (hm j),hsum]
  have hfinite : budget ≠ ∞ := (ENNReal.add_ne_top.mp (htotal ▸ hfin)).1
  have hle : (∑' k, planeVolume (S k)) ≤ budget := by
    rw [← harea,he]
    exact (measure_union_le _ _).trans (add_le_add le_rfl hrest)
  by_contra hne
  have hlt := ENNReal.add_lt_add_left hfinite (pos_iff_ne_zero.mpr hne)
  rw [add_zero,htotal] at hlt
  exact hlt.not_ge hle

/-- An open surjection with injective local lifts and total lifted area one
has only one preimage at every point. -/
theorem injective_of_openMap_of_periodic_area {X ι : Type*} [TopologicalSpace X] [T2Space X] [Fintype ι]
    (F : X → MarkedTorus) (ho : IsOpenMap F) (hs : Function.Surjective F)
    (D : ι → Set X) (L : ι → X → ℝ × ℝ) (T : ι → Set (ℝ × ℝ))
    (hcover : ∀ u : X, ∃ j, u ∈ D j)
    (hlift : ∀ j u, u ∈ D j → L j u ∈ T j ∧ F u = projectPeriods (L j u))
    (hinj : ∀ j, Set.InjOn (L j) (D j)) (hm : ∀ j, MeasurableSet (T j))
    (harea : ∑ j, planeVolume (T j) = 1) : Function.Injective F := by
  let I := ι × Period
  let R (i : I) := cellPiece (T i.1) i.2
  have hfind (p : ℝ × ℝ) (hp : p ∈ unitCell) (u : X) (he : F u = projectPeriods p) :
      ∃ i : I, u ∈ D i.1 ∧ p+realPeriod i.2 = L i.1 u ∧ p ∈ R i := by
    obtain ⟨j,hj⟩ := hcover u
    obtain ⟨hmem,hproj⟩ := hlift j u hj
    obtain ⟨d,hd⟩ := (projectPeriods_eq_iff p (L j u)).mp (he.symm.trans hproj)
    refine ⟨(j,d),hj,hd,hp,?_⟩
    change p+realPeriod d ∈ T j
    rwa [hd]
  have hunion : (⋃ i : I, R i) = unitCell := by
    ext p
    constructor
    · intro hp
      obtain ⟨i,hi⟩ := mem_iUnion.mp hp
      exact hi.1
    · intro hp
      obtain ⟨u,hu⟩ := hs (projectPeriods p)
      obtain ⟨i,_,_,hi⟩ := hfind p hp u hu
      exact mem_iUnion.mpr ⟨i,hi⟩
  have hsum : ∑' i : I, planeVolume (R i) = 1 := by
    calc
      _ = ∑' j : ι, ∑' d : Period, planeVolume (cellPiece (T j) d) := tsum_prod'
      _ = ∑' j : ι, planeVolume (T j) :=
        tsum_congr fun j => (volume_eq_tsum_cellPiece (hm j)).symm
      _ = _ := (tsum_fintype _).trans harea
  have hnull {i j : I} (hij : i ≠ j) : planeVolume (R i ∩ R j) = 0 :=
    volume_inter_eq_zero_of_union_eq_tsum R (fun i => measurableSet_cellPiece (hm i.1) i.2)
      (by rw [hsum]; exact ENNReal.one_ne_top) (by rw [hunion,volume_unitCell,hsum]) hij
  intro u v huv
  by_contra hne
  obtain ⟨U,V,hU,hV,hu,hv,hdisj⟩ := t2_separation hne
  let W := F '' U ∩ F '' V
  have hWo : IsOpen W := (ho U hU).inter (ho V hV)
  have hWn : W.Nonempty := ⟨F u,⟨u,hu,rfl⟩,⟨v,hv,huv.symm⟩⟩
  have hpos := volume_pos_unitCell_preimage hWo hWn
  let bad : Set (ℝ × ℝ) := ⋃ i : I, ⋃ j : I, ⋃ _ : i ≠ j, R i ∩ R j
  have hb : planeVolume bad = 0 :=
    measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun h => hnull h
  have hsub : unitCell ∩ projectPeriods ⁻¹' W ⊆ bad := by
    rintro p ⟨hp,⟨⟨a,ha,hea⟩,⟨b,hb,heb⟩⟩⟩
    obtain ⟨i,hai,hAi,hpi⟩ := hfind p hp a hea
    obtain ⟨j,hbj,hBj,hpj⟩ := hfind p hp b heb
    have hne : i ≠ j := by
      rintro rfl
      have hab := hinj i.1 hai hbj (hAi.symm.trans hBj)
      exact Set.disjoint_left.mp hdisj (hab ▸ ha) hb
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hne,hpi,hpj⟩⟩⟩
  exact hpos.ne' (measure_mono_null hsub hb)

namespace PeriodicFaceSystem

variable {ι : Type*} [Fintype ι] [Nonempty ι] {fs : List Triangle} {lift : ι → LiftedFace}

/-- An open development of positive triangles with total lattice area one is injective. -/
theorem injective (S : PeriodicFaceSystem fs lift) (x w : ℝ) (hw : 0 < w)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : ι, 0 < periodicFaceArea x w q (lift j))
    (htotal : ∑ j : ι, latticeFaceArea x w q (lift j) = 2) :
    Function.Injective (periodicDevelopment lift S.cover x w q) := by
  let f := periodicDevelopment lift S.cover x w q
  let D (j : ι) : Set (triangleWeightSpace fs) :=
    {u | u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift j)))}
  let L (j : ι) (u : triangleWeightSpace fs) :=
    facePeriodPoint x w q (lift j) u.val
  let T (j : ι) := latticeTriangle x w q (lift j)
  have harea (j : ι) : 0 < latticeFaceArea x w q (lift j) := by
    rw [latticeFaceArea_eq x w hw.ne']
    exact div_pos (hpos j) hw
  refine injective_of_openMap_of_periodic_area f
    (S.isOpenMap x w hw.ne' q hpos)
    (S.surjective x w hw.ne' q hpos) D L T
    S.cover (fun j u hu => ?_) (fun j u hu v hv he => ?_) (fun j => ?_) ?_
  · exact ⟨facePeriodPoint_mem_latticeTriangle x w hw.ne' q (lift j) (S.distinct j) u.val hu,
      periodicDevelopment_on_face lift S.cover S.shared x w q j u hu⟩
  · exact Subtype.ext (facePeriodPoint_injOn x w hw.ne' q (lift j) (S.distinct j) (harea j).ne' hu hv he)
  · exact (isCompact_planarTriangle _ _ _).isClosed.measurableSet
  · have hm (j : ι) : MeasureTheory.volume (T j) =
        ENNReal.ofReal (latticeFaceArea x w q (lift j) / 2) := by
      unfold T latticeTriangle
      rw [volume_planarTriangle]
      change ENNReal.ofReal (|latticeFaceArea x w q (lift j)|/2) = _
      rw [abs_of_pos (harea j)]
    simp_rw [hm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => div_nonneg (harea j).le (by norm_num)),
      ← Finset.sum_div, htotal]
    norm_num

/-- The compatible lifts of total lattice area one triangulate the marked quotient. -/
noncomputable def homeomorph (S : PeriodicFaceSystem fs lift) (x w : ℝ) (hw : 0 < w)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : ι, 0 < periodicFaceArea x w q (lift j))
    (htotal : ∑ j : ι, latticeFaceArea x w q (lift j) = 2) :
    triangleWeightSpace fs ≃ₜ MarkedTorus :=
  (Equiv.ofBijective (periodicDevelopment lift S.cover x w q)
    ⟨S.injective x w hw q hpos htotal, S.surjective x w hw.ne' q hpos⟩).toHomeomorphOfContinuousOpen
      (periodicDevelopment_continuous lift S.cover S.shared x w q) (S.isOpenMap x w hw.ne' q hpos)

theorem homeomorph_apply (S : PeriodicFaceSystem fs lift) (x w : ℝ) (hw : 0 < w)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : ι, 0 < periodicFaceArea x w q (lift j))
    (htotal : ∑ j : ι, latticeFaceArea x w q (lift j) = 2) (u : triangleWeightSpace fs) :
    S.homeomorph x w hw q hpos htotal u = periodicDevelopment lift S.cover x w q u := by
  unfold homeomorph
  rfl

end PeriodicFaceSystem

end OrigamiTorus
