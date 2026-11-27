module

public import OrigamiTorus.Type7.Angles
public import OrigamiTorus.Type4.Angles
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-! Differentiating a planar corner in the upper half-plane gives the imaginary
part of the difference of the two edge logarithmic derivatives. -/

@[expose] public section

open Filter InnerProductGeometry
open scoped Topology

namespace OrigamiTorus

/-- The derivative of the argument of a differentiable complex-valued curve away
from the nonpositive real axis. -/
theorem hasDerivAt_argument {f : ℝ → ℂ} {z : ℂ} {t : ℝ}
    (hf : HasDerivAt f z t) (hs : f t ∈ Complex.slitPlane) :
    HasDerivAt (fun a => (f a).arg) (z/f t).im t := by
  have hlog := (Complex.hasStrictFDerivAt_log_real hs).hasFDerivAt.comp_hasDerivAt t hf
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog
  simpa [Function.comp_def,Complex.log_im,Complex.imCLM_apply,div_eq_mul_inv,mul_comm] using him

private theorem hasDerivAt_ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u U : E) :
    HasDerivAt (fun t : ℝ => u+t • U) U 0 := by
  have h := (hasDerivAt_const (0 : ℝ) u).add
    ((hasDerivAt_id (0 : ℝ)).smul (hasDerivAt_const (0 : ℝ) U))
  convert h using 1
  · rfl
  · simp

/-- The signed logarithmic derivative formula for a positively oriented corner. -/
theorem hasDerivAt_planar_corner (u v U V : ℂ)
    (hpos : 0 < ((starRingEnd ℂ) u*v).im) :
    HasDerivAt (fun t : ℝ => angle (u+t • U) (v+t • V)) (V/v-U/u).im 0 := by
  let f (t : ℝ) := (starRingEnd ℂ) (u+t • U)*(v+t • V)
  have hu := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_ray u U)
  have hc : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (u+t • U)) ((starRingEnd ℂ) U) 0 := hu
  have hprod : HasDerivAt f ((starRingEnd ℂ) U*v+(starRingEnd ℂ) u*V) 0 := by
    convert hc.mul (hasDerivAt_ray v V) using 1 <;> simp [f,add_comm]
  have h0 : f 0 = (starRingEnd ℂ) u*v := by simp [f]
  have hnU : u ≠ 0 := by intro h; simp [h] at hpos
  have hnV : v ≠ 0 := by intro h; simp [h] at hpos
  have hv := hasDerivAt_argument hprod (Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [h0]; exact hpos.ne')))
  have he : ((starRingEnd ℂ) U*v+(starRingEnd ℂ) u*V)/f 0 =
      V/v+(starRingEnd ℂ) (U/u) := by
    rw [h0,map_div₀]
    field_simp [hnU,hnV,(map_ne_zero (starRingEnd ℂ)).mpr hnU] <;> ring
  rw [he,Complex.add_im,Complex.conj_im,← sub_eq_add_neg,← Complex.sub_im] at hv
  refine hv.congr_of_eventuallyEq ?_
  have hp : ∀ᶠ t : ℝ in 𝓝 0, 0 < (f t).im := by
    apply (continuous_const.continuousAt.eventually_lt (Continuous.continuousAt ?_) ?_)
    · unfold f
      fun_prop
    · simpa [h0] using hpos
  filter_upwards [hp] with t ht
  have h := Type7.complexCorner_arg_angle true 0 (u+t • U) (v+t • V)
  simpa [f,Type7.complexCorner] using (h (by simpa [f,Type7.complexCorner] using ht)).symm

/-- A negatively oriented corner uses the opposite sign in the logarithmic derivative. -/
theorem hasDerivAt_planar_corner_neg (u v U V : ℂ)
    (hneg : ((starRingEnd ℂ) u*v).im < 0) :
    HasDerivAt (fun t : ℝ => angle (u+t • U) (v+t • V)) (U/u-V/v).im 0 := by
  have he : ((starRingEnd ℂ) v*u).im = -((starRingEnd ℂ) u*v).im := by
    simp only [Complex.mul_im,Complex.conj_re,Complex.conj_im]
    ring
  have hpos : 0 < ((starRingEnd ℂ) v*u).im := he ▸ neg_pos.mpr hneg
  convert hasDerivAt_planar_corner v u V U hpos using 1
  funext t
  exact angle_comm _ _

/-- The two rays at a face corner in cyclic face order. -/
def cornerRays (v : Vertex) (f : Triangle) : Option Edge :=
  let (a,b,c) := f
  if v = a then some (b,c) else if v = b then some (c,a) else if v = c then some (a,b) else none

/-- Sum the Euclidean face angles at a labeled vertex of a spatial or planar placement. -/
noncomputable def coneAngles {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (fs : List Triangle) (q : Vertex → E) (v : Vertex) : ℝ :=
  (fs.map fun f => match cornerRays v f with
    | none => 0
    | some (a,b) => angle (q a-q v) (q b-q v)).sum

/-- Keep the cone angles at vertices 1 through 7. -/
noncomputable def sevenConeAngles {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (fs : List Triangle) (q : Vertex → E) (v : Fin 7) : ℝ :=
  coneAngles fs q v.succ

theorem coneAngles_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (fs : List Triangle) (p : Vertex → E) {c : ℝ} (hc : c ≠ 0) (i : Vertex) :
    coneAngles fs (fun j => c • p j) i = coneAngles fs p i := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro f _
  cases hr : cornerRays i f with
  | none => rfl
  | some e =>
    obtain ⟨a,b⟩ := e
    exact (by simpa only [← smul_sub] using angle_smul_smul hc (p a-p i) (p b-p i))

/-- The sum of all labeled cone angles is π times the number of faces. -/
theorem sum_coneAngles {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (fs : List Triangle) (q : Vertex → E)
    (hfs : ∀ f ∈ fs, (triangleVertices f).Nodup)
    (hq : ∀ f ∈ fs, q f.1 ≠ q f.2.1) :
    (∑ v, coneAngles fs q v) = (fs.length : ℝ)*Real.pi := by
  induction fs with
  | nil => simp [coneAngles]
  | cons f fs ih =>
    obtain ⟨a,b,c⟩ := f
    have hdistinct := hfs (a,b,c) List.mem_cons_self
    have hab : a ≠ b := by
      intro he
      simpa [triangleVertices,he] using hdistinct
    have hac : a ≠ c := by
      intro he
      simpa [triangleVertices,he] using hdistinct
    have hbc : b ≠ c := by
      intro he
      simpa [triangleVertices,he] using hdistinct
    let A := angle (q b-q a) (q c-q a)
    let B := angle (q c-q b) (q a-q b)
    let C := angle (q a-q c) (q b-q c)
    have hface : A+B+C = Real.pi := by
      have ht := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (q c)
        (show q b ≠ q a from (hq (a,b,c) List.mem_cons_self).symm)
      change angle (q a-q b) (q c-q b)+angle (q b-q c) (q a-q c)+angle (q c-q a) (q b-q a) = _ at ht
      rw [angle_comm (q a-q b),angle_comm (q b-q c),angle_comm (q c-q a)] at ht
      change B+C+A = _ at ht
      linarith only [ht]
    have hc (v : Vertex) :
        coneAngles ((a,b,c)::fs) q v =
          ((if v = a then A else 0)+(if v = b then B else 0)+(if v = c then C else 0))+
            coneAngles fs q v := by
      by_cases ha : v = a
      · subst v
        simp [coneAngles,cornerRays,hab,hac,A]
      by_cases hb : v = b
      · subst v
        simp [coneAngles,cornerRays,ha,hbc,B]
      by_cases hc : v = c
      · subst v
        simp [coneAngles,cornerRays,ha,hb,C]
      · simp [coneAngles,cornerRays,ha,hb,hc]
    have ht := ih (fun f hf => hfs f (List.mem_cons_of_mem _ hf)) (fun f hf => hq f (List.mem_cons_of_mem _ hf))
    simp only [hc,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hface,ht,
      List.length_cons,Nat.cast_succ,add_mul,one_mul]
    ring

/-- Interpret a tag on a planar face as its orientation sign. -/
def planarOrientationSign (positive : Bool) : ℤ := if positive then 1 else -1

/-- The contribution of one face corner to a ray's turning coefficient. -/
def cornerCoefficient (v w : Vertex) (f : Triangle × Bool) : ℤ :=
  match cornerRays v f.1 with
  | none => 0
  | some (a,b) =>
    (if w = b then planarOrientationSign f.2 else 0) - (if w = a then planarOrientationSign f.2 else 0)

/-- Aggregate the entries and exits of the signed corners at one ray. -/
def planarTurnCoefficient (faces : List (Triangle × Bool)) (v w : Vertex) : ℤ :=
  (faces.map (cornerCoefficient v w)).sum

/-- The derivative of a planar ray divided by the ray itself. -/
noncomputable def rayVariation (z δ : Vertex → ℂ) (v w : Vertex) : ℂ :=
  (δ w - δ v) / (z w - z v)

private theorem chartEuclideanCorner_eq_rays (z : Vertex → ℂ) (v : Vertex) (f : Triangle) :
    Type4.chartEuclideanCorner z v f =
      match cornerRays v f with
      | none => 0
      | some (a,b) => angle (z a - z v) (z b - z v) := by
  rcases f with ⟨a,b,c⟩
  by_cases ha : v = a
  · subst v
    simp [Type4.chartEuclideanCorner,cornerRays]
  by_cases hb : v = b
  · subst v
    simp [Type4.chartEuclideanCorner,cornerRays,ha]
  by_cases hc : v = c
  · subst v
    simp [Type4.chartEuclideanCorner,cornerRays,ha,hb]
  · simp [Type4.chartEuclideanCorner,cornerRays,ha,hb,hc]

theorem coneAngles_eq_chart (fs : List (Triangle × Bool)) (z : Vertex → ℂ) (v : Vertex) :
    coneAngles (fs.map Prod.fst) z v = (fs.map fun f => Type4.chartEuclideanCorner z v f.1).sum := by
  simp only [coneAngles,List.map_map,Function.comp_def,chartEuclideanCorner_eq_rays]

theorem coneAngles_eq_chart_list (fs : List Triangle) (z : Vertex → ℂ) (v : Vertex) :
    coneAngles fs z v = (fs.map (Type4.chartEuclideanCorner z v)).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro f _
  exact (chartEuclideanCorner_eq_rays z v f).symm

/-- Cone angles vary smoothly near a placement whose face corners have nonzero
rays and angles strictly between zero and π. -/
theorem contDiffAt_coneAngles {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : WithTop ℕ∞} (fs : List Triangle) (p : Vertex → E)
    (hp : ∀ f ∈ fs, ∀ v a b, cornerRays v f = some (a,b) →
      p a ≠ p v ∧ p b ≠ p v ∧ 0 < angle (p a-p v) (p b-p v) ∧ angle (p a-p v) (p b-p v) < Real.pi) :
    ContDiffAt ℝ n (coneAngles fs : (Vertex → E) → Vertex → ℝ) p := by
  apply contDiffAt_pi.mpr
  intro v
  induction fs with
  | nil =>
    simpa only [coneAngles,List.map_nil,List.sum_nil] using
      (contDiffAt_const : ContDiffAt ℝ n (fun _ : Vertex → E => (0 : ℝ)) p)
  | cons f fs ih =>
    have htail := ih (fun g hg => hp g (List.mem_cons_of_mem _ hg))
    have hhead : ContDiffAt ℝ n (fun q : Vertex → E => match cornerRays v f with
      | none => 0
      | some (a,b) => angle (q a-q v) (q b-q v)) p := by
      cases hcorner : cornerRays v f with
      | none => exact contDiffAt_const
      | some e =>
        obtain ⟨a,b⟩ := e
        obtain ⟨ha,hb,hpos,hpi⟩ := hp f List.mem_cons_self v a b hcorner
        let u (q : Vertex → E) := q a-q v
        let v' (q : Vertex → E) := q b-q v
        have hu : ContDiffAt ℝ n u p := (contDiffAt_apply ℝ _ a p).sub (contDiffAt_apply ℝ _ v p)
        have hv : ContDiffAt ℝ n v' p := (contDiffAt_apply ℝ _ b p).sub (contDiffAt_apply ℝ _ v p)
        have hnu : u p ≠ 0 := sub_ne_zero.mpr ha
        have hnv : v' p ≠ 0 := sub_ne_zero.mpr hb
        have hdenom : ‖u p‖ * ‖v' p‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hnu) (norm_ne_zero_iff.mpr hnv)
        have hquot := (hu.inner ℝ hv).div ((hu.norm ℝ hnu).mul (hv.norm ℝ hnv)) hdenom
        have hlo : -1 < Real.cos (angle (u p) (v' p)) := by
          rw [← Real.cos_pi]
          exact Real.cos_lt_cos_of_nonneg_of_le_pi (angle_nonneg _ _) le_rfl hpi
        have hhi : Real.cos (angle (u p) (v' p)) < 1 := by
          rw [← Real.cos_zero]
          exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (angle_le_pi _ _) hpos
        rw [cos_angle] at hlo hhi
        exact (Real.contDiffAt_arccos hlo.ne' hhi.ne).comp p hquot
    exact hhead.add htail

/-- A directional derivative along an affine line agrees with the application
of the Fréchet derivative to its velocity. -/
theorem deriv_line_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : DifferentiableAt ℝ f z) (δ : E) :
    deriv (fun t : ℝ => f (z+t • δ)) 0 = fderiv ℝ f z δ := by
  have hline : (fun t : ℝ => z+t • δ) 0 = z := by simp
  have hf' : HasFDerivAt f (fderiv ℝ f z) ((fun t : ℝ => z+t • δ) 0) := by
    rw [hline]
    exact hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt 0 (hasDerivAt_ray z δ)).deriv

/-- A strict corner orientation gives the nondegeneracy required by the
spatial cone-angle map. -/
theorem planarAngle_nondegenerate (positive : Bool) (u v : ℂ)
    (hs : if positive then 0 < ((starRingEnd ℂ) u*v).im else ((starRingEnd ℂ) u*v).im < 0) :
    u ≠ 0 ∧ v ≠ 0 ∧ 0 < angle u v ∧ angle u v < Real.pi := by
  have hp : 0 < (Type7.complexCorner positive 0 u v).im := by
    cases positive
    · simp only [Type7.complexCorner,Bool.false_eq_true,ite_false,sub_zero]
      simp only [Bool.false_eq_true,ite_false,Complex.mul_im,Complex.conj_re,Complex.conj_im] at hs ⊢
      linarith only [hs]
    · simpa only [Type7.complexCorner,ite_true,sub_zero] using hs
  have hn1 : u ≠ 0 := by
    intro h; cases positive <;> simp [h,Type7.complexCorner] at hp
  have hn2 : v ≠ 0 := by
    intro h; cases positive <;> simp [h,Type7.complexCorner] at hp
  have he : (Type7.complexCorner positive 0 u v).arg = angle u v := by
    simpa only [sub_zero] using Type7.complexCorner_arg_angle positive 0 u v hp
  exact ⟨hn1,hn2,he ▸ Type7.positiveArg hp,he ▸ Complex.arg_lt_pi_iff.mpr (Or.inr hp.ne')⟩

private theorem hasDerivAt_tagged_corner (z δ : Vertex → ℂ) (v : Vertex) (f : Triangle × Bool)
    (h : ∀ a b, cornerRays v f.1 = some (a,b) →
      if f.2 then 0 < ((starRingEnd ℂ) (z a-z v)*(z b-z v)).im
      else ((starRingEnd ℂ) (z a-z v)*(z b-z v)).im < 0) :
    HasDerivAt (fun t : ℝ => Type4.chartEuclideanCorner (fun j => z j + t • δ j) v f.1)
      (∑ w, (cornerCoefficient v w f : ℂ) * rayVariation z δ v w).im 0 := by
  simp only [chartEuclideanCorner_eq_rays]
  cases hR : cornerRays v f.1 with
  | none => simpa [cornerCoefficient,hR] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  | some e =>
    obtain ⟨a,b⟩ := e
    have hC :
        (∑ w, (cornerCoefficient v w f : ℂ) * rayVariation z δ v w) =
          (planarOrientationSign f.2 : ℂ) * (rayVariation z δ v b - rayVariation z δ v a) := by
      simp only [cornerCoefficient,hR,Int.cast_sub,Int.cast_ite,Int.cast_zero,sub_mul,
        Finset.sum_sub_distrib,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_sub]
    have hm (t : ℝ) (w : Vertex) :
        z w + t • δ w - (z v + t • δ v) = (z w - z v) + t • (δ w - δ v) := by
      rw [smul_sub]
      abel
    have hs := h a b hR
    rw [hC]
    simp only [hm]
    cases hB : f.2
    · have hneg : ((starRingEnd ℂ) (z a-z v)*(z b-z v)).im < 0 := by simpa [hB] using hs
      have hnegated (A B : ℂ) : (-1 : ℂ)*(B-A) = A-B := by ring
      simpa [planarOrientationSign,hB,rayVariation,hnegated] using
        hasDerivAt_planar_corner_neg (z a-z v) (z b-z v) (δ a-δ v) (δ b-δ v) hneg
    · have hpos : 0 < ((starRingEnd ℂ) (z a-z v)*(z b-z v)).im := by simpa [hB] using hs
      simpa [planarOrientationSign,hB,rayVariation] using
        hasDerivAt_planar_corner (z a-z v) (z b-z v) (δ a-δ v) (δ b-δ v) hpos

/-- The cone-angle derivative is the sum of the logarithmic derivatives of
its rays with coefficients given by the signed corner incidences. -/
theorem hasDerivAt_planar_cone (faces : List (Triangle × Bool)) (z δ : Vertex → ℂ) (v : Vertex)
    (h : ∀ f ∈ faces, ∀ a b, cornerRays v f.1 = some (a,b) →
      if f.2 then 0 < ((starRingEnd ℂ) (z a-z v)*(z b-z v)).im
      else ((starRingEnd ℂ) (z a-z v)*(z b-z v)).im < 0) :
    HasDerivAt (fun t : ℝ => (faces.map
      (fun f => Type4.chartEuclideanCorner (fun j => z j + t • δ j) v f.1)).sum)
      (∑ w, (planarTurnCoefficient faces v w : ℂ) * rayVariation z δ v w).im 0 := by
  induction faces with
  | nil => simpa [planarTurnCoefficient] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  | cons f faces ih =>
    have hf := hasDerivAt_tagged_corner z δ v f
      (fun a b hR => h f List.mem_cons_self a b hR)
    have htail := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    have hsum := hf.add htail
    change HasDerivAt (fun t =>
      Type4.chartEuclideanCorner (fun j => z j + t • δ j) v f.1 +
      (faces.map (fun g => Type4.chartEuclideanCorner (fun j => z j + t • δ j) v g.1)).sum) _ 0 at hsum
    simpa only [List.map_cons,List.sum_cons,planarTurnCoefficient,Int.cast_add,
      add_mul,Finset.sum_add_distrib,Complex.add_im] using hsum

/-- The signed corner incidence coefficients are skew-symmetric in the
shared labeling of the Type 7 and pre-flip Type 4 planar charts. -/
theorem planarTurnCoefficient_type7_antisymm (v w : Vertex) :
    planarTurnCoefficient Type7.orientedFaces w v = -planarTurnCoefficient Type7.orientedFaces v w := by
  revert v w
  decide +kernel

/-- Entries and exits of the negative blocks in the oriented vertex links.
An exit contributes (+1) and an entrance contributes (-1). -/
def negativeBlockCoefficient (v w : Vertex) : ℤ :=
  let rays : Vertex → List (Vertex × ℤ) :=
    ![[(1,1),(5,1),(2,1),(3,-1),(6,-1),(7,-1)],
      [(3,1),(7,1),(0,-1),(4,-1)],
      [(4,1),(0,-1)],
      [(4,1),(0,1),(6,-1),(1,-1)],
      [(1,1),(5,1),(3,-1),(2,-1)],
      [(7,1),(6,1),(4,-1),(0,-1)],
      [(0,1),(3,1),(5,-1),(7,-1)],
      [(6,1),(0,1),(5,-1),(1,-1)]]
  (((rays v).filter fun e => e.1 == w).map Prod.snd).sum

/-- Reversing the turns of the negative faces subtracts twice the turns
of their blocks from the telescoping full link sum. -/
theorem planarTurnCoefficient_type7_eq_negativeBlocks (v w : Vertex) :
    planarTurnCoefficient Type7.orientedFaces v w = -2 * negativeBlockCoefficient v w := by
  revert v w
  decide +kernel

/-- The sign of each cyclic corner follows from its face's oriented area. -/
theorem planarCornerSigns_of_face_areas (faces : List (Triangle × Bool)) (p : Vertex → ℝ × ℝ)
    (w : ℝ) (hw : 0 < w)
    (h : ∀ f ∈ faces, if f.2 then 0 < area p f.1.1 f.1.2.1 f.1.2.2
      else area p f.1.1 f.1.2.1 f.1.2.2 < 0) :
    let z := Type7.physicalComplex w ∘ p
    ∀ v (f : Triangle × Bool), f ∈ faces → ∀ a b,
      cornerRays v f.1 = some (a,b) →
      if f.2 then 0 < ((starRingEnd ℂ) (z a-z v)*(z b-z v)).im
      else ((starRingEnd ℂ) (z a-z v)*(z b-z v)).im < 0 := by
  let z := Type7.physicalComplex w ∘ p
  have him (i j k : Vertex) : ((starRingEnd ℂ) (z j-z i)*(z k-z i)).im =
      Real.sqrt w * area p i j k := by
    simp only [z,Function.comp_apply,Type7.physicalComplex,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      Complex.sub_re,Complex.sub_im,area]
    ring
  have hcyclic (i j k : Vertex) : area p j k i = area p i j k := by
    simp only [area]
    ring
  have hsign (s : Bool) (i j k : Vertex) (hs : if s then 0 < area p i j k else area p i j k < 0) :
      if s then 0 < ((starRingEnd ℂ) (z j-z i)*(z k-z i)).im
      else ((starRingEnd ℂ) (z j-z i)*(z k-z i)).im < 0 := by
    rw [him]
    cases s
    · exact mul_neg_of_pos_of_neg (Real.sqrt_pos.mpr hw) hs
    · exact mul_pos (Real.sqrt_pos.mpr hw) hs
  dsimp only
  intro v f hf a b he
  obtain ⟨⟨i,j,k⟩,s⟩ := f
  by_cases hvi : v = i
  · subst v
    have ht : (j,k) = (a,b) := by simpa [cornerRays] using he
    obtain ⟨ha,hb⟩ := Prod.mk.inj ht
    rw [← ha,← hb]
    exact hsign s _ _ _ (h _ hf)
  by_cases hvj : v = j
  · subst v
    have ht : (k,i) = (a,b) := by simpa [cornerRays,hvi] using he
    obtain ⟨ha,hb⟩ := Prod.mk.inj ht
    rw [← ha,← hb]
    exact hsign s _ _ _ (by rw [hcyclic]; exact h _ hf)
  by_cases hvk : v = k
  · subst v
    have ht : (i,j) = (a,b) := by simpa [cornerRays,hvi,hvj] using he
    obtain ⟨ha,hb⟩ := Prod.mk.inj ht
    rw [← ha,← hb]
    exact hsign s _ _ _ (by rw [hcyclic j k i,hcyclic i j k]; exact h _ hf)
  · simp [cornerRays,hvi,hvj,hvk] at he

/-- Nonzero signed face areas give nondegenerate Euclidean corners. -/
theorem planarCorners_nondegenerate_of_face_areas (fs : List (Triangle × Bool))
    (p : Vertex → ℝ × ℝ) (w : ℝ) (hw : 0 < w)
    (h : ∀ f ∈ fs, if f.2 then 0 < area p f.1.1 f.1.2.1 f.1.2.2
      else area p f.1.1 f.1.2.1 f.1.2.2 < 0) :
    let z := Type7.physicalComplex w ∘ p
    ∀ f ∈ fs.map Prod.fst, ∀ v a b, cornerRays v f = some (a,b) →
      z a ≠ z v ∧ z b ≠ z v ∧ 0 < angle (z a-z v) (z b-z v) ∧
        angle (z a-z v) (z b-z v) < Real.pi := by
  dsimp only
  intro f hf v a b hcorner
  obtain ⟨g,hg,hgf⟩ := List.mem_map.mp hf
  subst f
  obtain ⟨ha,hb,hp,hpi⟩ := planarAngle_nondegenerate g.2 _ _
    (planarCornerSigns_of_face_areas fs p w hw h v g hg a b hcorner)
  exact ⟨sub_ne_zero.mp ha,sub_ne_zero.mp hb,hp,hpi⟩

end OrigamiTorus
