module

public import OrigamiTorus.Type6.MarkedShape
public import OrigamiTorus.Lattice.FaceTransitions
import Mathlib.Tactic

/-! A positively oriented Type 6 periodic sheet has zero cone deficits in its
edge metric. The angle sum at each vertex is a positive integral turn, and
the sums over all sixteen faces give exactly eight turns. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus

open InnerProductGeometry

private theorem turn_angle_sum_ge {n : ℕ} (hn : 0 < n) (r : Fin n → ℂ)
    (hp : ∀ i, 0 < complexCross (r i) (r (finRotate n i))) :
    2*Real.pi ≤ ∑ i, angle (r i) (r (finRotate n i)) := by
  let σ := finRotate n
  let θ i := angle (r i) (r (σ i))
  have hr (i : Fin n) : r i ≠ 0 := by
    intro he
    have h := hp i
    simp [he,complexCross] at h
  have harg (i : Fin n) : ((θ i : ℝ) : Real.Angle) = (r (σ i)).arg-(r i).arg := by
    change ((angle (r i) (r (σ i)) : ℝ) : Real.Angle) = _
    rw [← arg_div_eq_angle_of_cross_pos _ _ (hp i)]
    exact Complex.arg_div_coe_angle (hr _) (hr _)
  have hzero : ((∑ i, θ i : ℝ) : Real.Angle) = 0 := by
    change Real.Angle.coeHom (∑ i, θ i) = 0
    rw [map_sum]
    simp only [Real.Angle.coe_coeHom,harg,Finset.sum_sub_distrib]
    rw [show (∑ i, ((r (σ i)).arg : Real.Angle)) = ∑ i, ((r i).arg : Real.Angle) from
      Equiv.sum_comp σ (fun i => ((r i).arg : Real.Angle)),sub_self]
  obtain ⟨m,hm⟩ := Real.Angle.coe_eq_zero_iff.mp hzero
  have hθ (i : Fin n) : 0 < θ i := by
    change 0 < angle (r i) (r (σ i))
    rw [← arg_div_eq_angle_of_cross_pos _ _ (hp i)]
    apply Type7.positiveArg
    change 0 < ((r (σ i))/(r i)).im
    rw [show ((r (σ i))/(r i)).im = complexCross (r i) (r (σ i))/Complex.normSq (r i) by
      simp only [Complex.div_im,complexCross_apply]; ring]
    exact div_pos (hp i) (Complex.normSq_pos.mpr (hr i))
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hpos : 0 < ∑ i, θ i := Finset.sum_pos (fun i _ => hθ i) Finset.univ_nonempty
  change 2*Real.pi ≤ ∑ i, θ i
  rw [← hm,zsmul_eq_mul]
  rw [← hm,zsmul_eq_mul] at hpos
  have hmpos : (0 : ℝ) < m := pos_of_mul_pos_left hpos Real.two_pi_pos.le
  have hone : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by exact_mod_cast hmpos)
  simpa using mul_le_mul_of_nonneg_right hone Real.two_pi_pos.le

private def linkRay (p : Vertex → ℂ) (U V : ℂ) (v a : Vertex) : ℂ :=
  type6ComplexCorner p U V (a,(type6_edgeShift v a).getD 0)-p v

private theorem complexCorner_sub (p : Vertex → ℂ) (U V : ℂ) (a b : Corner) :
    type6ComplexCorner p U V b-type6ComplexCorner p U V a =
      type6ComplexCorner p U V (b.1,b.2-a.2)-p a.1 := by
  simp only [type6ComplexCorner,Prod.fst_sub,Prod.snd_sub,Int.cast_sub]
  ring

private def linkPair (v : Vertex) (i : Fin (type6_linkCycle v).length) : Edge :=
  ((type6_linkCycle v).get i,(type6_linkCycle v).get (finRotate _ i))

private theorem type6_linkPair_perm (v : Vertex) :
    (List.ofFn (linkPair v)).Perm (type6FlippedFaces.filterMap (cornerRays v)) := by
  fin_cases v <;> decide +kernel

private theorem metricAngle_of_complex_lengths (a b c : ℂ) :
    squaredLengthAngle (Complex.normSq (b-a)) (Complex.normSq (c-a)) (Complex.normSq (c-b)) =
      angle (b-a) (c-a) := by
  rw [angle_eq_squaredLengthAngle,show b-a-(c-a) = -(c-b) by abel,norm_neg]
  simp only [Complex.normSq_eq_norm_sq]

private theorem metric_linkCorner {s : Vertex → Vertex → ℝ} (hs : ∀ a b, s a b = s b a)
    (p : Vertex → ℂ) (U V : ℂ)
    (h : ∀ j : Fin 16, OrientedMetricLift s (type6ComplexCorner p U V) (liftedFaces j))
    (v : Vertex) (i : Fin (type6_linkCycle v).length) :
    let (a,b) := linkPair v i
    0 < complexCross (linkRay p U V v a) (linkRay p U V v b) ∧
    squaredLengthAngle (s v a) (s v b) (s a b) =
      angle (linkRay p U V v a) (linkRay p U V v b) := by
  obtain ⟨j,r,ha,hb,hc,hshift₁,hshift₂⟩ := type6_link_corner_data v i
  let f := rotateCorners r (liftedFaces j)
  let P := type6ComplexCorner p U V
  have he₁ : linkRay p U V v (linkPair v i).1 = P f.2.1-P f.1 := by
    change f.2.1.1 = (linkPair v i).1 at hb
    change f.1.1 = v at ha
    rw [← hb,← ha,linkRay,hshift₁]
    exact (complexCorner_sub p U V f.1 f.2.1).symm
  have he₂ : linkRay p U V v (linkPair v i).2 = P f.2.2-P f.1 := by
    change f.2.2.1 = (linkPair v i).2 at hc
    change f.1.1 = v at ha
    rw [← hc,← ha,linkRay,hshift₂]
    exact (complexCorner_sub p U V f.1 f.2.2).symm
  have hface : OrientedMetricLift s P f := orientedMetricLift_rotate s hs P _ r (h j)
  obtain ⟨hs₁,hs₂,hs₃,ho⟩ := hface
  change 0 < complexCross (linkRay p U V v (linkPair v i).1) (linkRay p U V v (linkPair v i).2) ∧
    squaredLengthAngle (s v (linkPair v i).1) (s v (linkPair v i).2) (s (linkPair v i).1 (linkPair v i).2) =
      angle (linkRay p U V v (linkPair v i).1) (linkRay p U V v (linkPair v i).2)
  rw [he₁,he₂]
  refine ⟨ho,?_⟩
  change f.2.1.1 = (linkPair v i).1 at hb
  change f.2.2.1 = (linkPair v i).2 at hc
  rw [← hb,← hc,← ha]
  change squaredLengthAngle (s f.1.1 f.2.1.1) (s f.1.1 f.2.2.1) (s f.2.1.1 f.2.2.1) = _
  change s f.1.1 f.2.1.1 = _ at hs₁
  change s f.1.1 f.2.2.1 = _ at hs₂
  change s f.2.1.1 f.2.2.1 = _ at hs₃
  rw [hs₁,hs₂,hs₃]
  exact metricAngle_of_complex_lengths _ _ _

private theorem metricCornerAngle_filterMap (fs : List Triangle) (s : Vertex → Vertex → ℝ) (v : Vertex) :
    (fs.map (metricCornerAngle s v)).sum =
      ((fs.filterMap (cornerRays v)).map fun e => squaredLengthAngle (s v e.1) (s v e.2) (s e.1 e.2)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases h : cornerRays v f <;>
      simp only [List.map_cons,List.filterMap_cons,h,metricCornerAngle,List.sum_cons,ih,zero_add]

private theorem metricConeAngles_ge {s : Vertex → Vertex → ℝ} (hs : ∀ a b, s a b = s b a)
    (p : Vertex → ℂ) (U V : ℂ)
    (h : ∀ j : Fin 16, OrientedMetricLift s (type6ComplexCorner p U V) (liftedFaces j)) (v : Vertex) :
    2*Real.pi ≤ metricConeAngles type6FlippedFaces s v := by
  let f : Edge → ℝ := fun e => squaredLengthAngle (s v e.1) (s v e.2) (s e.1 e.2)
  let r (i : Fin (type6_linkCycle v).length) := linkRay p U V v ((type6_linkCycle v).get i)
  have hn : 0 < (type6_linkCycle v).length := by
    have h := (type6_linkCycle_checked v).2.1
    omega
  have hlink (i : Fin (type6_linkCycle v).length) := metric_linkCorner hs p U V h v i
  have hp (i : Fin (type6_linkCycle v).length) : 0 < complexCross (r i) (r (finRotate _ i)) := (hlink i).1
  have he : metricConeAngles type6FlippedFaces s v = ∑ i, angle (r i) (r (finRotate _ i)) := by
    unfold metricConeAngles
    rw [← List.sum_ofFn]
    have hlist :
        List.ofFn (fun i : Fin type6FlippedFaces.length => metricCornerAngle s v (type6FlippedFaces.get i)) =
        type6FlippedFaces.map (metricCornerAngle s v) :=
      List.ofFn_getElem_eq_map _ _
    rw [hlist,metricCornerAngle_filterMap]
    change ((type6FlippedFaces.filterMap (cornerRays v)).map f).sum = _
    rw [((type6_linkPair_perm v).map f).sum_eq.symm,List.map_ofFn,List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    exact (hlink i).2
  rw [he]
  exact turn_angle_sum_ge hn r hp

private theorem metricCornerAngle_sum_face {s : Vertex → Vertex → ℝ} (hs : ∀ a b, s a b = s b a)
    {P : Corner → ℂ} {f : LiftedFace} (hnd : (triangleVertices (liftedVertices f)).Nodup)
    (h : OrientedMetricLift s P f) :
    (∑ v, metricCornerAngle s v (liftedVertices f)) = Real.pi := by
  obtain ⟨a,b,c⟩ := f
  obtain ⟨hab,hac,hbc,hpos⟩ := h
  have hnd' : a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ b.1 ≠ c.1 := by
    simp [triangleVertices,liftedVertices] at hnd
    tauto
  obtain ⟨hAB,hAC,hBC⟩ := hnd'
  let q (i : Vertex) := if i = a.1 then P a else if i = b.1 then P b else P c
  have qa : q a.1 = P a := by simp [q]
  have qb : q b.1 = P b := by simp [q,hAB.symm]
  have qc : q c.1 = P c := by simp [q,hAC.symm,hBC.symm]
  have hne : P a ≠ P b := by
    intro he
    change 0 < complexCross (P b-P a) (P c-P a) at hpos
    simp [← he,complexCross] at hpos
  have he (v : Vertex) : metricCornerAngle s v (liftedVertices (a,b,c)) =
      coneAngles [liftedVertices (a,b,c)] q v := by
    have A := metricAngle_of_complex_lengths (P a) (P b) (P c)
    have B := metricAngle_of_complex_lengths (P b) (P c) (P a)
    have C := metricAngle_of_complex_lengths (P c) (P a) (P b)
    change s a.1 b.1 = _ at hab
    change s a.1 c.1 = _ at hac
    change s b.1 c.1 = _ at hbc
    by_cases ha : v = a.1
    · subst v
      simpa [metricCornerAngle,coneAngles,cornerRays,liftedVertices,qa,qb,qc,hab,hac,hbc] using A
    by_cases hb : v = b.1
    · subst v
      rw [normSq_sub_rev (P a) (P b),normSq_sub_rev (P a) (P c)] at B
      simpa [metricCornerAngle,coneAngles,cornerRays,liftedVertices,ha,qa,qb,qc,
        hs b.1 a.1,hs c.1 a.1,hab,hac,hbc] using B
    by_cases hc : v = c.1
    · subst v
      rw [normSq_sub_rev (P a) (P c),normSq_sub_rev (P b) (P c)] at C
      simpa [metricCornerAngle,coneAngles,cornerRays,liftedVertices,ha,hb,qa,qb,qc,
        hs c.1 a.1,hs c.1 b.1,hab,hac,hbc] using C
    simp [metricCornerAngle,coneAngles,cornerRays,liftedVertices,ha,hb,hc]
  simp_rw [he]
  have H := sum_coneAngles [liftedVertices (a,b,c)] q
    (by
      intro g hg
      obtain rfl : g = liftedVertices (a,b,c) := by simpa using hg
      exact hnd)
    (by
      intro g hg
      obtain rfl : g = liftedVertices (a,b,c) := by simpa using hg
      simpa [liftedVertices,qa,qb] using hne)
  simpa using H

/-- Positive orientations give flat cone-angle sums on the Type 6 periodic
sheet, for arbitrary nearby period vectors and intrinsic vertex positions. -/
theorem type6_metricConeAngles_flat {s : Vertex → Vertex → ℝ} (hs : ∀ a b, s a b = s b a)
    (p : Vertex → ℂ) (U V : ℂ)
    (h : ∀ j : Fin 16, OrientedMetricLift s (type6ComplexCorner p U V) (liftedFaces j)) (v : Vertex) :
    metricConeAngles type6FlippedFaces s v = 2*Real.pi := by
  have hf : type6FlippedFaces = List.ofFn (fun j : Fin 16 => liftedVertices (liftedFaces j)) := by decide +kernel
  have hnd : ∀ j : Fin 16, (triangleVertices (liftedVertices (liftedFaces j))).Nodup := by decide +kernel
  have hv (v : Vertex) : metricConeAngles type6FlippedFaces s v =
      ∑ j : Fin 16, metricCornerAngle s v (liftedVertices (liftedFaces j)) := by
    rw [hf,metricConeAngles,← List.sum_ofFn,← List.sum_ofFn]
    congr 1
  have hall : ∑ v, metricConeAngles type6FlippedFaces s v = ∑ _ : Vertex, (2*Real.pi) := by
    simp_rw [hv]
    rw [Finset.sum_comm]
    simp_rw [fun j : Fin 16 => metricCornerAngle_sum_face hs (hnd j) (h j)]
    norm_num
    ring
  have hl (v : Vertex) := metricConeAngles_ge hs p U V h v
  apply le_antisymm _ (hl v)
  by_contra! hgt
  exact (ne_of_gt (Finset.sum_lt_sum (fun v _ => hl v) ⟨v,Finset.mem_univ _,hgt⟩)) hall

end OrigamiTorus
