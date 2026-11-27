module

public import OrigamiTorus.Lattice.FaceDevelopment
public import OrigamiTorus.Geometry.MetricAngleRank
public import OrigamiTorus.EightVertex.Type6.IntrinsicMap
import Mathlib.Tactic

/-! Develop two short strips from the root face 167 to the two translated
copies of vertex 1. These developments define a smooth marked shape function
of the Type 6 squared edge lengths. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus

open Type7 (triangleCorner)

def attachMetricCorner (s : Vertex → Vertex → ℝ) (a b c : Vertex) (A B : ℂ) : ℂ :=
  A+(B-A)*triangleCorner s true a b c

theorem type6VertexCount_neZero : NeZero 8 := @Nat.instNeZeroSucc 7

/-- The two marked displacements in the chart taking vertex 1 to 0 and
vertex 7 to 1. The first strip crosses the flipped diagonal 05. -/
def type6MetricDisplacements (s : Vertex → Vertex → ℝ) : ℂ × ℂ :=
  letI : NeZero 8 := type6VertexCount_neZero
  let z6 := triangleCorner s false 1 7 6
  let z2 := attachMetricCorner s 7 6 2 1 z6
  let z5 := attachMetricCorner s 7 2 5 1 z2
  let z0 := attachMetricCorner s 5 2 0 z5 z2
  let u := attachMetricCorner s 5 0 1 z5 z0
  let z3 := attachMetricCorner s 7 5 3 1 z5
  let z6' := attachMetricCorner s 3 5 6 z3 z5
  let v := attachMetricCorner s 3 6 1 z3 z6'
  (u,v)

/-- The marked period ratio, also defined on nearby nonflat metrics. -/
def type6MetricShape (s : Vertex → Vertex → ℝ) : ℂ :=
  (type6MetricDisplacements s).2/(type6MetricDisplacements s).1

/-- Complex positions on the periodic intrinsic sheet. -/
def type6ComplexCorner (p : Vertex → ℂ) (U V : ℂ) (c : Corner) : ℂ :=
  p c.1 + (c.2.1 : ℂ)*U + (c.2.2 : ℂ)*V

/-- An oriented lifted triangle has the given squared edge lengths. -/
def OrientedMetricLift (s : Vertex → Vertex → ℝ) (P : Corner → ℂ) (f : LiftedFace) : Prop :=
  let (a,b,c) := f
  let A := P a
  let B := P b
  let C := P c
  s a.1 b.1 = Complex.normSq (B-A) ∧ s a.1 c.1 = Complex.normSq (C-A) ∧
    s b.1 c.1 = Complex.normSq (C-B) ∧ 0 < complexCross (B-A) (C-A)

theorem OrientedMetricLift.nondegenerate {s : Vertex → Vertex → ℝ} {P : Corner → ℂ}
    {f : LiftedFace} (h : OrientedMetricLift s P f) :
    MetricFaceNondegenerate s (liftedVertices f) := by
  obtain ⟨a,b,c⟩ := f
  obtain ⟨hab,hac,hbc,hpos⟩ := h
  change 0 < complexCross (P b-P a) (P c-P a) at hpos
  have hAB : P b-P a ≠ 0 := by
    intro he
    simp [he,complexCross] at hpos
  have hAC : P c-P a ≠ 0 := by
    intro he
    simp [he,complexCross] at hpos
  have hBC : P c-P b ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    simp [he',complexCross_apply,mul_comm] at hpos
  change 0 < s a.1 b.1 ∧ 0 < s a.1 c.1 ∧ 0 < s b.1 c.1 ∧
    0 < metricGram (s a.1 b.1) (s a.1 c.1) (s b.1 c.1)
  have hg : metricGram (s a.1 b.1) (s a.1 c.1) (s b.1 c.1) =
      (complexCross (P b-P a) (P c-P a))^2 := by
    rw [hab,hac,hbc]
    simp only [metricGram,metricDot,Complex.normSq_apply,complexCross_apply,Complex.sub_re,Complex.sub_im]
    ring
  rw [hg,hab,hac,hbc]
  exact ⟨Complex.normSq_pos.mpr hAB,Complex.normSq_pos.mpr hAC,
    Complex.normSq_pos.mpr hBC,sq_pos_of_pos hpos⟩

private theorem orientedMetricLift_cycle {s : Vertex → Vertex → ℝ} (hs : ∀ a b, s a b = s b a)
    {P : Corner → ℂ} {a b c : Corner} (h : OrientedMetricLift s P (a,b,c)) :
    OrientedMetricLift s P (b,c,a) := by
  obtain ⟨hab,hac,hbc,hpos⟩ := h
  change s b.1 c.1 = Complex.normSq (P c-P b) ∧ s b.1 a.1 = Complex.normSq (P a-P b) ∧
    s c.1 a.1 = Complex.normSq (P a-P c) ∧ 0 < complexCross (P c-P b) (P a-P b)
  exact ⟨hbc, by rw [hs b.1 a.1,normSq_sub_rev]; exact hab,
    by rw [hs c.1 a.1,normSq_sub_rev]; exact hac, by rwa [complexCross_cycle]⟩

theorem orientedMetricLift_rotate (s : Vertex → Vertex → ℝ) (hs : ∀ a b, s a b = s b a)
    (P : Corner → ℂ) (f : LiftedFace) (r : Fin 3)
    (h : OrientedMetricLift s P f) : OrientedMetricLift s P (rotateCorners r f) := by
  obtain ⟨a,b,c⟩ := f
  fin_cases r <;> norm_num [rotateCorners]
  · exact h
  · exact orientedMetricLift_cycle hs h
  · exact orientedMetricLift_cycle hs (orientedMetricLift_cycle hs h)

private def translateMetricLift (d : Period) (f : LiftedFace) : LiftedFace :=
  ((f.1.1,f.1.2+d),(f.2.1.1,f.2.1.2+d),(f.2.2.1,f.2.2.2+d))

private theorem orientedMetricLift_translate (s : Vertex → Vertex → ℝ) (p : Vertex → ℂ)
    (U V : ℂ) (d : Period) (f : LiftedFace)
    (h : OrientedMetricLift s (type6ComplexCorner p U V) f) :
    OrientedMetricLift s (type6ComplexCorner p U V) (translateMetricLift d f) := by
  obtain ⟨a,b,c⟩ := f
  have he (a b : Corner) :
      type6ComplexCorner p U V (b.1,b.2+d)-type6ComplexCorner p U V (a.1,a.2+d) =
        type6ComplexCorner p U V b-type6ComplexCorner p U V a := by
    simp only [type6ComplexCorner,Prod.fst_add,Prod.snd_add,Int.cast_add]
    ring
  simpa only [translateMetricLift,OrientedMetricLift,he] using h

private theorem triangleCorner_eq_ratio (s : Vertex → Vertex → ℝ) (P : Corner → ℂ)
    (a b c : Corner) (pos : Bool)
    (hab : s a.1 b.1 = Complex.normSq (P b-P a))
    (hac : s a.1 c.1 = Complex.normSq (P c-P a))
    (hbc : s b.1 c.1 = Complex.normSq (P c-P b))
    (hpos : if pos then 0 < complexCross (P b-P a) (P c-P a)
      else complexCross (P b-P a) (P c-P a) < 0) :
    triangleCorner s pos a.1 b.1 c.1 = (P c-P a)/(P b-P a) := by
  have he : P b-P a ≠ 0 := by
    intro hz
    cases pos <;> simp [hz,complexCross] at hpos
  have hi : ((P c-P a)/(P b-P a)).im =
      complexCross (P b-P a) (P c-P a)/Complex.normSq (P b-P a) := by
    simp only [Complex.div_im,complexCross_apply]
    ring
  unfold triangleCorner
  rw [hab,hac,hbc,show P c-P b = (P c-P a)-(P b-P a) by ring]
  apply developedCorner_planar _ _ _ he
  rw [hi]
  have hnorm := Complex.normSq_nonneg (P b-P a)
  cases pos
  · exact div_nonpos_of_nonpos_of_nonneg (le_of_lt hpos) hnorm
  · exact div_nonneg (le_of_lt hpos) hnorm

private theorem attachMetricCorner_eq (s : Vertex → Vertex → ℝ) (P : Corner → ℂ)
    (a b c : Corner) (h : OrientedMetricLift s P (a,b,c)) (anchor d : ℂ) (hd : d ≠ 0) :
    attachMetricCorner s a.1 b.1 c.1 ((P a-anchor)/d) ((P b-anchor)/d) = (P c-anchor)/d := by
  obtain ⟨hab,hac,hbc,hpos⟩ := h
  have he : P b-P a ≠ 0 := by
    intro hz
    change 0 < complexCross (P b-P a) (P c-P a) at hpos
    simp [hz,complexCross] at hpos
  unfold attachMetricCorner
  rw [triangleCorner_eq_ratio s P a b c true hab hac hbc hpos]
  field_simp [hd,he]
  ring

/-- On a periodic intrinsic chart the two developments recover its actual
periods in the same root coordinates. -/
theorem type6MetricDisplacements_of_periodic (s : Vertex → Vertex → ℝ) (hs : ∀ a b, s a b = s b a)
    (p : Vertex → ℂ) (U V : ℂ)
    (h : ∀ j : Fin 16, OrientedMetricLift s (type6ComplexCorner p U V) (liftedFaces j)) :
    type6MetricDisplacements s = (U/(p 7-p 1),V/(p 7-p 1)) := by
  let P := type6ComplexCorner p U V
  let d := p 7-p 1
  let N (c : Corner) := (P c-p 1)/d
  have root : OrientedMetricLift s P ((1,(0,0)),(6,(0,0)),(7,(0,0))) := h 6
  obtain ⟨h16,h17,h67,hpos⟩ := root
  have hd : d ≠ 0 := by
    intro he
    simp [P,type6ComplexCorner] at hpos
    change p 7-p 1 = 0 at he
    simp [he,complexCross] at hpos
  have n7 : N (7,(0,0)) = 1 := by simp [N,P,type6ComplexCorner,d,hd]
  have z6 : triangleCorner s false 1 7 6 = N (6,(0,0)) := by
    have hneg : complexCross (P (7,(0,0))-P (1,(0,0))) (P (6,(0,0))-P (1,(0,0))) < 0 := by
      rw [complexCross_swap]
      exact neg_neg_of_pos hpos
    have h76 : s 7 6 = Complex.normSq (P (6,(0,0))-P (7,(0,0))) := by
      rw [hs 7 6,normSq_sub_rev]
      exact h67
    have he := triangleCorner_eq_ratio s P (1,(0,0)) (7,(0,0)) (6,(0,0))
      false h17 h16 h76 hneg
    simpa [N,P,type6ComplexCorner,d] using he
  have step (j : Fin 16) (r : Fin 3) (w : Period) :
      OrientedMetricLift s P (translateMetricLift w (rotateCorners r (liftedFaces j))) :=
    orientedMetricLift_translate s p U V w _
      (orientedMetricLift_rotate s hs P (liftedFaces j) r (h j))
  have z2 := attachMetricCorner_eq s P (7,(0,0)) (6,(0,0)) (2,(1,0)) (step 9 1 (0,0)) (p 1) d hd
  have z5 := attachMetricCorner_eq s P (7,(0,0)) (2,(1,0)) (5,(1,0)) (step 8 2 (0,0)) (p 1) d hd
  have z0 := attachMetricCorner_eq s P (5,(1,0)) (2,(1,0)) (0,(1,0)) (step 15 1 (1,0)) (p 1) d hd
  have u := attachMetricCorner_eq s P (5,(1,0)) (0,(1,0)) (1,(1,0)) (step 14 2 (1,0)) (p 1) d hd
  have z3 := attachMetricCorner_eq s P (7,(0,0)) (5,(1,0)) (3,(0,1)) (step 12 1 (0,0)) (p 1) d hd
  have z6' := attachMetricCorner_eq s P (3,(0,1)) (5,(1,0)) (6,(0,1)) (step 11 0 (0,1)) (p 1) d hd
  have v := attachMetricCorner_eq s P (3,(0,1)) (6,(0,1)) (1,(0,1)) (step 3 1 (0,1)) (p 1) d hd
  change attachMetricCorner s 7 6 2 (N (7,(0,0))) (N (6,(0,0))) = N (2,(1,0)) at z2
  change attachMetricCorner s 7 2 5 (N (7,(0,0))) (N (2,(1,0))) = N (5,(1,0)) at z5
  change attachMetricCorner s 5 2 0 (N (5,(1,0))) (N (2,(1,0))) = N (0,(1,0)) at z0
  change attachMetricCorner s 5 0 1 (N (5,(1,0))) (N (0,(1,0))) = N (1,(1,0)) at u
  change attachMetricCorner s 7 5 3 (N (7,(0,0))) (N (5,(1,0))) = N (3,(0,1)) at z3
  change attachMetricCorner s 3 5 6 (N (3,(0,1))) (N (5,(1,0))) = N (6,(0,1)) at z6'
  change attachMetricCorner s 3 6 1 (N (3,(0,1))) (N (6,(0,1))) = N (1,(0,1)) at v
  rw [n7] at z2 z5 z3
  simp only [type6MetricDisplacements,z6,z2,z5,z0,u,z3,z6',v]
  apply Prod.ext <;> simp [N,P,type6ComplexCorner,d]

/-- The shape function reads the geometric marked modulus on a flat sheet. -/
theorem type6MetricShape_of_periodic (s : Vertex → Vertex → ℝ) (hs : ∀ a b, s a b = s b a)
    (p : Vertex → ℂ) (U V : ℂ)
    (h : ∀ j : Fin 16, OrientedMetricLift s (type6ComplexCorner p U V) (liftedFaces j)) :
    type6MetricShape s = V/U := by
  obtain ⟨_,_,_,hpos⟩ := h 6
  have hd : p 7-p 1 ≠ 0 := by
    intro he
    simp [liftedFaces,type6ComplexCorner,he,complexCross] at hpos
  rw [type6MetricShape,type6MetricDisplacements_of_periodic s hs p U V h]
  exact div_div_div_cancel_right₀ hd V U

/-- A marked shape chart is smooth near the squared lengths of any positively
oriented periodic intrinsic placement. -/
theorem contDiffAt_type6MetricShape_of_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : E → Vertex → Vertex → ℝ} {x : E}
    (hd : ∀ a b, ContDiffAt ℝ 1 (fun q => s q a b) x)
    (hs : ∀ a b, s x a b = s x b a) (p : Vertex → ℂ) (U V : ℂ) (hU : U ≠ 0)
    (h : ∀ j : Fin 16, OrientedMetricLift (s x) (type6ComplexCorner p U V) (liftedFaces j)) :
    ContDiffAt ℝ 1 (fun q => type6MetricShape (s q)) x := by
  have hc (a b c : Vertex) (sign : Bool) (hm : MetricFaceNondegenerate (s x) (a,b,c)) :
      ContDiffAt ℝ 1 (fun q => triangleCorner (s q) sign a b c) x := by
    obtain ⟨hab,_,_,hg⟩ := hm
    change 0 < s x a b at hab
    have hheight :
        developedHeightSq (s x a b) (s x a c) (s x b c) =
          metricGram (s x a b) (s x a c) (s x b c)/(s x a b)^2 := by
      unfold developedHeightSq developedRe metricGram metricDot
      field_simp [hab.ne']
    exact contDiffAt_developedCorner sign (hd a b) (hd a c) (hd b c) hab.ne'
      (by rw [hheight]; exact (div_pos hg (sq_pos_of_pos hab)).ne')
  have hr (j : Fin 16) (r : Fin 3) := (orientedMetricLift_rotate (s x) hs _ (liftedFaces j) r (h j)).nondegenerate
  have hroot : MetricFaceNondegenerate (s x) (1,7,6) := by
    obtain ⟨ha,hb,hc,hg⟩ := (h 6).nondegenerate
    refine ⟨hb,ha,?_,?_⟩
    · change 0 < s x 7 6
      rwa [hs 7 6]
    · change 0 < metricGram (s x 1 7) (s x 1 6) (s x 7 6)
      rw [hs 7 6,metricGram_left_comm]
      exact hg
  let z6 (q : E) := triangleCorner (s q) false 1 7 6
  let z2 q := attachMetricCorner (s q) 7 6 2 1 (z6 q)
  let z5 q := attachMetricCorner (s q) 7 2 5 1 (z2 q)
  let z0 q := attachMetricCorner (s q) 5 2 0 (z5 q) (z2 q)
  let u q := attachMetricCorner (s q) 5 0 1 (z5 q) (z0 q)
  let z3 q := attachMetricCorner (s q) 7 5 3 1 (z5 q)
  let z6' q := attachMetricCorner (s q) 3 5 6 (z3 q) (z5 q)
  let v q := attachMetricCorner (s q) 3 6 1 (z3 q) (z6' q)
  have attach (a b c : Vertex) {A B : E → ℂ} (hA : ContDiffAt ℝ 1 A x)
      (hB : ContDiffAt ℝ 1 B x) (hm : MetricFaceNondegenerate (s x) (a,b,c)) :
      ContDiffAt ℝ 1 (fun q => attachMetricCorner (s q) a b c (A q) (B q)) x :=
    hA.add ((hB.sub hA).mul (hc a b c true hm))
  have h6 : ContDiffAt ℝ 1 z6 x := hc 1 7 6 false hroot
  have h2 : ContDiffAt ℝ 1 z2 x := attach 7 6 2 contDiffAt_const h6 (hr 9 1)
  have h5 : ContDiffAt ℝ 1 z5 x := attach 7 2 5 contDiffAt_const h2 (hr 8 2)
  have h0 : ContDiffAt ℝ 1 z0 x := attach 5 2 0 h5 h2 (hr 15 1)
  have hu : ContDiffAt ℝ 1 u x := attach 5 0 1 h5 h0 (hr 14 2)
  have h3 : ContDiffAt ℝ 1 z3 x := attach 7 5 3 contDiffAt_const h5 (hr 12 1)
  have h6' : ContDiffAt ℝ 1 z6' x := attach 3 5 6 h3 h5 (hr 11 0)
  have hv : ContDiffAt ℝ 1 v x := attach 3 6 1 h3 h6' (hr 3 1)
  have hne : u x ≠ 0 := by
    change (type6MetricDisplacements (s x)).1 ≠ 0
    rw [type6MetricDisplacements_of_periodic _ hs p U V h]
    have he : p 7-p 1 ≠ 0 := by
      intro he
      obtain ⟨_,_,_,hh⟩ := h 6
      simp [type6ComplexCorner,he,complexCross] at hh
    exact div_ne_zero hU he
  change ContDiffAt ℝ 1 (fun q => v q/u q) x
  simpa only [div_eq_mul_inv] using hv.mul (hu.fun_inv hne)

end OrigamiTorus
