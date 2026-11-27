module

public import OrigamiTorus.Geometry.AngleDerivative
public import OrigamiTorus.Geometry.MetricAngleVariation
import Mathlib.Tactic

/-! The seven cone angles have independent differentials in squared-length
space. Vertex scaling detects the full cokernel by the triangle energy. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus

/-- Positive sides and a positive Gram determinant for a face. -/
def MetricFaceNondegenerate (s : Vertex → Vertex → ℝ) (f : Triangle) : Prop :=
  let a := s f.1 f.2.1
  let b := s f.1 f.2.2
  let c := s f.2.1 f.2.2
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < metricGram a b c

def metricCornerAngle (s : Vertex → Vertex → ℝ) (v : Vertex) (f : Triangle) : ℝ :=
  match cornerRays v f with
  | none => 0
  | some (a,b) => squaredLengthAngle (s v a) (s v b) (s a b)

/-- Cone angles computed from squared edge lengths. -/
def metricConeAngles (fs : List Triangle) (s : Vertex → Vertex → ℝ) (v : Vertex) : ℝ :=
  ∑ j : Fin fs.length, metricCornerAngle s v (fs.get j)

def metricSevenConeAngles (fs : List Triangle) (s : Vertex → Vertex → ℝ) (i : Fin 7) : ℝ :=
  metricConeAngles fs s i.succ

theorem metricConeAngles_eq_coneAngles_of_corner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (fs : List Triangle) (q : Vertex → E) (s : Vertex → Vertex → ℝ)
    (v : Vertex) (hs : ∀ f ∈ fs, ∀ a b, cornerRays v f = some (a,b) →
      s v a = ‖q a-q v‖^2 ∧ s v b = ‖q b-q v‖^2 ∧ s a b = ‖q b-q a‖^2) :
    metricConeAngles fs s v = coneAngles fs q v := by
  have he (f : Triangle) (hf : f ∈ fs) : metricCornerAngle s v f = (match cornerRays v f with
      | none => 0
      | some (a,b) => InnerProductGeometry.angle (q a-q v) (q b-q v)) := by
    unfold metricCornerAngle
    cases h : cornerRays v f with
    | none => rfl
    | some e =>
      obtain ⟨a,b⟩ := e
      obtain ⟨ha,hb,hab⟩ := hs f hf a b h
      change squaredLengthAngle (s v a) (s v b) (s a b) = InnerProductGeometry.angle (q a-q v) (q b-q v)
      rw [angle_eq_squaredLengthAngle,ha,hb,hab]
      rw [show q a-q v-(q b-q v) = -(q b-q a) by abel,norm_neg]
  unfold metricConeAngles coneAngles
  rw [← List.sum_ofFn]
  let angle (f : Triangle) := match cornerRays v f with
    | none => 0
    | some (a,b) => InnerProductGeometry.angle (q a-q v) (q b-q v)
  change (List.ofFn (fun i : Fin fs.length => metricCornerAngle s v fs[i.val])).sum = (fs.map angle).sum
  rw [← List.ofFn_getElem_eq_map fs angle,List.sum_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact he _ (List.getElem_mem i.isLt)

theorem metricConeAngles_eq_coneAngles {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (fs : List Triangle) (q : Vertex → E) (s : Vertex → Vertex → ℝ)
    (hs : ∀ a b, s a b = ‖q b-q a‖^2) (v : Vertex) :
    metricConeAngles fs s v = coneAngles fs q v :=
  metricConeAngles_eq_coneAngles_of_corner fs q s v (fun _ _ a b _ => ⟨hs v a,hs v b,hs a b⟩)

theorem metricGram_left_comm (a b c : ℝ) :
    metricGram a b c = metricGram b a c := by unfold metricGram metricDot; ring

theorem metricGram_right_comm (a b c : ℝ) :
    metricGram a b c = metricGram a c b := by unfold metricGram metricDot; ring

private theorem metricCorner_ne {s : Vertex → Vertex → ℝ} (hs : ∀ a b, s a b = s b a)
    {f : Triangle} (hf : MetricFaceNondegenerate s f)
    {v a b : Vertex} (h : cornerRays v f = some (a,b)) :
    0 < s v a ∧ 0 < s v b ∧ 0 < metricGram (s v a) (s v b) (s a b) := by
  obtain ⟨i,j,k⟩ := f
  obtain ⟨hi,hj,hk,hg⟩ := hf
  simp only [cornerRays] at h
  split at h
  · rename_i he
    subst v
    obtain ⟨ha,hb⟩ := Prod.mk.inj (Option.some.inj h).symm
    subst a
    subst b
    exact ⟨hi,hj,hg⟩
  · split at h
    · rename_i he
      subst v
      obtain ⟨ha,hb⟩ := Prod.mk.inj (Option.some.inj h).symm
      subst a
      subst b
      rw [hs j i,hs k i,metricGram_left_comm (s j k),← metricGram_right_comm]
      exact ⟨hk,hi,hg⟩
    · split at h
      · rename_i he
        subst v
        obtain ⟨ha,hb⟩ := Prod.mk.inj (Option.some.inj h).symm
        subst a
        subst b
        rw [hs k i,hs k j,← metricGram_right_comm,← metricGram_left_comm]
        exact ⟨hj,hk,hg⟩
      · cases h

/-- The metric cone-angle map is smooth where every face is nondegenerate. -/
theorem contDiffAt_metricSevenConeAngles (fs : List Triangle) (s : Vertex → Vertex → ℝ)
    (hs : ∀ a b, s a b = s b a) (hf : ∀ f ∈ fs, MetricFaceNondegenerate s f) :
    ContDiffAt ℝ 1 (metricSevenConeAngles fs) s := by
  apply contDiffAt_pi.mpr
  intro i
  change ContDiffAt ℝ 1 (fun t => ∑ j : Fin fs.length, metricCornerAngle t i.succ (fs.get j)) s
  apply ContDiffAt.sum
  intro j _
  unfold metricCornerAngle
  cases h : cornerRays i.succ (fs.get j) with
  | none => exact contDiffAt_const
  | some p =>
    obtain ⟨a,b⟩ := p
    obtain ⟨ha,hb,hg⟩ := metricCorner_ne hs (hf _ (List.get_mem _ _)) h
    exact contDiffAt_squaredLengthAngle (by fun_prop) (by fun_prop) (by fun_prop) ha hb hg

/-- Each infinitesimal vertex weight changes a squared edge length by its
length times the sum of the weights at its endpoints. -/
def conformalEdgeVariation (s : Vertex → Vertex → ℝ) (u : Vertex → ℝ)
    (a b : Vertex) : ℝ :=
  (u a+u b)*s a b

def metricCornerConformalVelocity (s : Vertex → Vertex → ℝ) (u : Vertex → ℝ)
    (v : Vertex) (f : Triangle) : ℝ :=
  match cornerRays v f with
  | none => 0
  | some (a,b) => conformalAngleVelocity (s v a) (s v b) (s a b) (u v) (u a) (u b)

theorem hasDerivAt_metricConeAngles_conformal (fs : List Triangle) (s : Vertex → Vertex → ℝ)
    (hs : ∀ a b, s a b = s b a) (hf : ∀ f ∈ fs, MetricFaceNondegenerate s f)
    (u : Vertex → ℝ) (v : Vertex) :
    HasDerivAt (fun t : ℝ => metricConeAngles fs (s+t • conformalEdgeVariation s u) v)
      (∑ j : Fin fs.length, metricCornerConformalVelocity s u v (fs.get j)) 0 := by
  unfold metricConeAngles
  apply HasDerivAt.fun_sum
  intro j _
  unfold metricCornerAngle metricCornerConformalVelocity
  cases h : cornerRays v (fs.get j) with
  | none => exact hasDerivAt_const _ _
  | some p =>
    obtain ⟨a,b⟩ := p
    obtain ⟨ha,hb,hg⟩ := metricCorner_ne hs (hf _ (List.get_mem _ _)) h
    exact hasDerivAt_squaredLengthAngle_conformal ha hb hg (u v) (u a) (u b)

private theorem conformalAngleVelocity_left_comm (a b c u v w : ℝ) :
    conformalAngleVelocity a b c u v w = conformalAngleVelocity b a c u w v := by
  unfold conformalAngleVelocity
  rw [metricGram_left_comm,show metricDot a b c = metricDot b a c by unfold metricDot; ring,add_comm]

private theorem metricFaceConformal_energy {s : Vertex → Vertex → ℝ} (hs : ∀ a b, s a b = s b a)
    {f : Triangle} (hn : (triangleVertices f).Nodup) (hf : MetricFaceNondegenerate s f)
    (u : Vertex → ℝ) :
    let E := -(∑ v, u v * metricCornerConformalVelocity s u v f)
    0 ≤ E ∧ (E = 0 ↔ u f.1 = u f.2.1 ∧ u f.1 = u f.2.2) := by
  obtain ⟨a,b,c⟩ := f
  have hnd : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    simp [triangleVertices] at hn
    tauto
  obtain ⟨hab,hac,hbc⟩ := hnd
  let A := conformalAngleVelocity (s a b) (s a c) (s b c) (u a) (u b) (u c)
  let B := conformalAngleVelocity (s a b) (s b c) (s a c) (u b) (u a) (u c)
  let C := conformalAngleVelocity (s a c) (s b c) (s a b) (u c) (u a) (u b)
  have hva : metricCornerConformalVelocity s u a (a,b,c) = A := by
    simp [metricCornerConformalVelocity,cornerRays,A]
  have hvb : metricCornerConformalVelocity s u b (a,b,c) = B := by
    simp only [metricCornerConformalVelocity,cornerRays,hab.symm,ite_false,ite_true,B]
    rw [hs b a,hs c a,conformalAngleVelocity_left_comm]
  have hvc : metricCornerConformalVelocity s u c (a,b,c) = C := by
    simp only [metricCornerConformalVelocity,cornerRays,hac.symm,hbc.symm,ite_false,ite_true,C]
    rw [hs c a,hs c b]
  have hterm (v : Vertex) : u v * metricCornerConformalVelocity s u v (a,b,c) =
        (if v = a then u a*A else 0)+(if v = b then u b*B else 0)+(if v = c then u c*C else 0) := by
    by_cases ha : v = a
    · subst v
      simp [hab,hac,hva]
    by_cases hb : v = b
    · subst v
      simp [hab.symm,hbc,hvb]
    by_cases hc : v = c
    · subst v
      simp [hac.symm,hbc.symm,hvc]
    simp [metricCornerConformalVelocity,cornerRays,ha,hb,hc]
  have he : (∑ v, u v * metricCornerConformalVelocity s u v (a,b,c)) = u a*A+u b*B+u c*C := by
    simp only [hterm,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  dsimp only
  rw [he]
  exact conformalAngle_energy hf.1 hf.2.2.2 (u a) (u b) (u c)

/-- The derivative of the seven cone angles is already onto on the
infinitesimal vertex-scaling directions, with the weight of vertex zero fixed. -/
theorem metricSevenConeAngles_conformal_surjective (fs : List Triangle) (s : Vertex → Vertex → ℝ)
    (hs : ∀ a b, s a b = s b a) (hn : ∀ f ∈ fs, (triangleVertices f).Nodup)
    (hf : ∀ f ∈ fs, MetricFaceNondegenerate s f)
    (hconnected : ∀ u : Vertex → ℝ,
      (∀ f ∈ fs, u f.1 = u f.2.1 ∧ u f.1 = u f.2.2) → ∀ v, u v = u 0) :
    Function.Surjective (fun u : Fin 7 → ℝ =>
      fderiv ℝ (metricSevenConeAngles fs) s (conformalEdgeVariation s (Fin.cases 0 u))) := by
  let full (u : Fin 7 → ℝ) : Vertex → ℝ := Fin.cases 0 u
  let V : (Fin 7 → ℝ) →ₗ[ℝ] (Vertex → Vertex → ℝ) :=
    { toFun := fun u => conformalEdgeVariation s (full u)
      map_add' := by
        intro u v
        have h (i : Vertex) : full (u+v) i = full u i+full v i := by
          cases i using Fin.cases <;> simp [full]
        ext a b
        simp only [conformalEdgeVariation,Pi.add_apply,h]
        ring
      map_smul' := by
        intro r u
        have h (i : Vertex) : full (r • u) i = r*full u i := by
          cases i using Fin.cases <;> simp [full]
        ext a b
        simp only [conformalEdgeVariation,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,h]
        ring }
  let D := fderiv ℝ (metricSevenConeAngles fs) s
  let L := D.toLinearMap.comp V
  change Function.Surjective L
  apply LinearMap.injective_iff_surjective.mp
  apply (injective_iff_map_eq_zero L).mpr
  intro u hu
  let w : Vertex → ℝ := Fin.cases 0 u
  have hfderiv : HasFDerivAt (metricSevenConeAngles fs) D s :=
    ((contDiffAt_metricSevenConeAngles fs s hs hf).differentiableAt (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => s+t • conformalEdgeVariation s w)
      (conformalEdgeVariation s w) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (conformalEdgeVariation s w)).const_add s)
  have hD := hfderiv.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hj (i : Fin 7) :
      (∑ j : Fin fs.length, metricCornerConformalVelocity s w i.succ (fs.get j)) = 0 := by
    let P : (Fin 7 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 7 => ℝ) i
    have hp := P.hasFDerivAt.comp_hasDerivAt 0 hD
    have he := hasDerivAt_metricConeAngles_conformal fs s hs hf w i.succ
    change HasDerivAt (fun t => metricConeAngles fs (s+t • conformalEdgeVariation s w) i.succ)
      (L u i) 0 at hp
    rw [hu] at hp
    exact he.unique hp
  have htotal : (∑ v, w v * ∑ j : Fin fs.length, metricCornerConformalVelocity s w v (fs.get j)) = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [show w 0 = 0 from rfl,zero_mul,zero_add,hj,mul_zero,Finset.sum_const_zero]
  let E (j : Fin fs.length) := -(∑ v, w v * metricCornerConformalVelocity s w v (fs.get j))
  have hE (j : Fin fs.length) :
      0 ≤ E j ∧ (E j = 0 ↔ w (fs.get j).1 = w (fs.get j).2.1 ∧ w (fs.get j).1 = w (fs.get j).2.2) :=
    metricFaceConformal_energy hs (hn (fs.get j) (List.get_mem _ _)) (hf (fs.get j) (List.get_mem _ _)) w
  have hEtotal : ∑ j, E j = 0 := by
    calc
      _ = -(∑ j : Fin fs.length, ∑ v, w v * metricCornerConformalVelocity s w v (fs.get j)) := by
        simp only [E,Finset.sum_neg_distrib]
      _ = -(∑ v, ∑ j : Fin fs.length, w v * metricCornerConformalVelocity s w v (fs.get j)) := by
        rw [Finset.sum_comm]
      _ = 0 := by
        simpa only [Finset.mul_sum,neg_zero] using congrArg Neg.neg htotal
  have hz : ∀ j : Fin fs.length, E j = 0 := by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hE j).1)).mp hEtotal
  have hcontr := hconnected w (fun f hmem => by
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hmem
    rw [← hj]
    exact (hE j).2.mp (hz j))
  funext i
  simpa [w] using hcontr i.succ

end OrigamiTorus
