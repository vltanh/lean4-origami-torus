module

public import OrigamiTorus.Geometry.AngleDerivative
public import OrigamiTorus.Geometry.Inflation
public import OrigamiTorus.Type2.Links
import Mathlib.Tactic

/-! Positive-height inflation preserving all Euclidean cone angles. -/

@[expose] public section

namespace OrigamiTorus

open Filter InnerProductGeometry
open scoped Topology

private abbrev Space := EuclideanSpace ℝ (Fin 3)

private noncomputable def planePoint : ℂ →ₗ[ℝ] Point3 :=
  Complex.reCLM.toLinearMap.prod (Complex.imCLM.toLinearMap.prod 0)

private noncomputable def planeIso : ℂ →ₗᵢ[ℝ] Space where
  toLinearMap := Type2.euclideanPoint.comp planePoint
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, ← Complex.normSq_eq_norm_sq]
    norm_num [Type2.euclideanPoint,planePoint, Fin.sum_univ_succ, Complex.normSq_apply, pow_two]

/-- Lift a complex placement vertically using a prescribed height direction. -/
def angleLift (p : Vertex → ℂ) (h : Vertex → ℝ) (t : ℝ) : Vertex → Point3 :=
  fun i => ((p i).re,(p i).im,t*h i)

private def spatialPlacement (h : Vertex → ℝ) (x : ℝ × (Vertex → ℂ)) : Vertex → Space :=
  Type2.euclideanPoint ∘ angleLift x.2 h x.1

private theorem spatialPlacement_zero (h : Vertex → ℝ) (p : Vertex → ℂ) :
    spatialPlacement h (0,p) = planeIso ∘ p := by
  funext i
  change Type2.euclideanPoint ((p i).re,(p i).im,0*h i) =
    Type2.euclideanPoint ((p i).re,(p i).im,0)
  rw [zero_mul]

theorem contDiff_angleLift (h : Vertex → ℝ) :
    ContDiff ℝ 1 (fun x : ℝ × (Vertex → ℂ) => angleLift x.2 h x.1) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ 1 (fun x : ℝ × (Vertex → ℂ) =>
    (Complex.reCLM (x.2 i),Complex.imCLM (x.2 i),x.1*h i))
  fun_prop

noncomputable def liftedAngles (fs : List Triangle) (h : Vertex → ℝ)
    (x : ℝ × (Vertex → ℂ)) : Fin 7 → ℝ :=
  sevenConeAngles fs (Type2.euclideanPoint ∘ angleLift x.2 h x.1)

theorem liftedAngles_zero (fs : List Triangle) (h : Vertex → ℝ) (p : Vertex → ℂ) :
    liftedAngles fs h (0,p) = sevenConeAngles fs p := by
  funext i
  change sevenConeAngles fs (spatialPlacement h (0,p)) i = _
  rw [spatialPlacement_zero]
  apply congrArg List.sum
  apply List.map_congr_left
  intro f _
  cases hr : cornerRays i.succ f with
  | none => rfl
  | some e =>
    obtain ⟨a,b⟩ := e
    simp only [Function.comp_apply, ← map_sub, LinearIsometry.angle_map]

theorem contDiffAt_spatialConeAngles_angleLift_zero (fs : List Triangle) (h : Vertex → ℝ)
    (z : Vertex → ℂ)
    (hn : ∀ f ∈ fs, ∀ v a b, cornerRays v f = some (a,b) →
      z a ≠ z v ∧ z b ≠ z v ∧ 0 < angle (z a-z v) (z b-z v) ∧
        angle (z a-z v) (z b-z v) < Real.pi) :
    ContDiffAt ℝ 1 (fun q : Vertex → Point3 =>
      sevenConeAngles fs (Type2.euclideanPoint ∘ q)) (angleLift z h 0) := by
  have hnr : ∀ f ∈ fs, ∀ v a b, cornerRays v f = some (a,b) →
      spatialPlacement h (0,z) a ≠ spatialPlacement h (0,z) v ∧
      spatialPlacement h (0,z) b ≠ spatialPlacement h (0,z) v ∧
      0 < angle (spatialPlacement h (0,z) a-spatialPlacement h (0,z) v)
        (spatialPlacement h (0,z) b-spatialPlacement h (0,z) v) ∧
      angle (spatialPlacement h (0,z) a-spatialPlacement h (0,z) v)
        (spatialPlacement h (0,z) b-spatialPlacement h (0,z) v) < Real.pi := by
    intro f hf v a b hr
    obtain ⟨ha,hb,hzero,hpi⟩ := hn f hf v a b hr
    rw [spatialPlacement_zero]
    simp only [Function.comp_apply, ← map_sub, LinearIsometry.angle_map]
    exact ⟨planeIso.injective.ne ha,planeIso.injective.ne hb,hzero,hpi⟩
  have hcd := contDiffAt_coneAngles (n := 1) fs _ hnr
  have hcd7 : ContDiffAt ℝ 1 (sevenConeAngles fs) (spatialPlacement h (0,z)) :=
    contDiffAt_pi.mpr (fun i => (contDiffAt_pi.mp hcd) i.succ)
  have hE : ContDiff ℝ 1 (fun q : Vertex → Point3 => Type2.euclideanPoint ∘ q) := by
    apply contDiff_pi.mpr
    intro i
    exact Type2.euclideanPoint.toContinuousLinearMap.contDiff.comp (by fun_prop)
  exact hcd7.comp (g := sevenConeAngles fs) (f := fun q => Type2.euclideanPoint ∘ q)
    (angleLift z h 0) hE.contDiffAt

theorem contDiffAt_liftedAngles (fs : List Triangle) (h : Vertex → ℝ)
    (z : Vertex → ℂ)
    (hn : ∀ f ∈ fs, ∀ v a b, cornerRays v f = some (a,b) →
      z a ≠ z v ∧ z b ≠ z v ∧ 0 < angle (z a-z v) (z b-z v) ∧
        angle (z a-z v) (z b-z v) < Real.pi) :
    ContDiffAt ℝ 1 (liftedAngles fs h) (0,z) := by
  let A (q : Vertex → Point3) := sevenConeAngles fs (Type2.euclideanPoint ∘ q)
  let B (x : ℝ × (Vertex → ℂ)) := angleLift x.2 h x.1
  have hA : ContDiffAt ℝ 1 A (B (0,z)) := contDiffAt_spatialConeAngles_angleLift_zero fs h z hn
  have hB : ContDiffAt ℝ 1 B (0,z) := (contDiff_angleLift h).contDiffAt
  change ContDiffAt ℝ 1 (A ∘ B) (0,z)
  exact hA.comp (0,z) hB

/-- Scale the second and third coordinates by nonzero factors. -/
theorem evaluateTriangles_rescale_injective (fs : List Triangle) (q : Vertex → Point3)
    {y t : ℝ} (hy : y ≠ 0) (ht : t ≠ 0)
    (hq : Function.Injective (evaluateTriangles fs q)) :
    Function.Injective (evaluateTriangles fs (fun i => ((q i).1,y*(q i).2.1,t*(q i).2.2))) := by
  let L : Point3 →ₗ[ℝ] Point3 :=
    { toFun := fun p => (p.1,y*p.2.1,t*p.2.2)
      map_add' := by intro a b; ext <;> simp [mul_add]
      map_smul' := by intro r p; ext <;> simp [mul_comm r, ← mul_assoc] }
  have hi : Function.Injective L := by
    intro a b he
    change (a.1,y*a.2.1,t*a.2.2) = (b.1,y*b.2.1,t*b.2.2) at he
    obtain ⟨h₁,h₂,h₃⟩ := Prod.mk.inj he |>.imp_right Prod.mk.inj
    exact Prod.ext h₁ (Prod.ext (mul_left_cancel₀ hy h₂) (mul_left_cancel₀ ht h₃))
  change Function.Injective (evaluateTriangles fs (L ∘ q))
  rw [evaluateTriangles_comp_linear]
  exact hi.comp hq

/-- Inflate an embedded height direction while preserving smooth constraints
that include the seven independent cone angles and a condition holding near
the base point. -/
theorem exists_embedded_flat_inflation_of_constraints_near
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
    (fs : List Triangle) (z : Vertex → ℂ) (h : Vertex → ℝ)
    (hcover : ∀ a : Vertex, ∃ f ∈ fs, a ∈ triangleVertexSet f)
    (hfs : ∀ f ∈ fs, (triangleVertices f).Nodup) (hcount : fs.length = 16)
    (hangle : ∀ v, coneAngles fs z v = 2*Real.pi)
    (hz : Function.Injective (evaluateTriangles fs (angleLift z h 1)))
    (f : ℝ × (Vertex → ℂ) → F) (hd : ContDiffAt ℝ 1 f (0,z))
    (hs : Function.Surjective (fderiv ℝ (fun p => f (0,p)) z))
    {P : ℝ × (Vertex → ℂ) → Prop} (hP : ∀ᶠ q in 𝓝 (0,z), P q)
    (hangles : ∀ t p, f (t,p) = f (0,z) → liftedAngles fs h (t,p) = liftedAngles fs h (0,z)) :
    ∃ t : ℝ, 0 < t ∧ ∃ p : Vertex → ℂ,
      Topology.IsClosedEmbedding (evaluateTriangles fs (angleLift p h t)) ∧
      (∀ v, coneAngles fs (Type2.euclideanPoint ∘ angleLift p h t) v = 2*Real.pi) ∧
      f (t,p) = f (0,z) ∧ P (t,p) := by
  let U := (fun p => angleLift p h 1) ⁻¹'
    {q | Function.Injective (evaluateTriangles fs q)}
  have hc : Continuous (fun p : Vertex → ℂ => angleLift p h 1) :=
    (contDiff_angleLift h).continuous.comp (continuous_const.prodMk continuous_id)
  have hU : IsOpen U := (isOpen_injective_evaluateTriangles fs).preimage hc
  have hf := hd.hasStrictFDerivAt_fderiv (by norm_num)
  have hpartial := (hf.hasFDerivAt.comp z (ContinuousLinearMap.inr ℝ ℝ (Vertex → ℂ)).hasFDerivAt).fderiv
  have hs' : Function.Surjective (fderiv ℝ f (0,z) ∘L ContinuousLinearMap.inr ℝ ℝ (Vertex → ℂ)) := by
    rwa [← hpartial]
  have hNear : ∀ᶠ q : ℝ × (Vertex → ℂ) in 𝓝 (0,z), q.2 ∈ U :=
    continuous_snd.continuousAt (hU.mem_nhds hz)
  obtain ⟨t,ht,p,⟨hp,hP'⟩,he⟩ :=
    exists_pos_preserving_of_surjective_eventually hf hs' (hNear.and hP)
  let q := angleLift p h t
  have hscale := evaluateTriangles_rescale_injective fs (angleLift p h 1) (y := 1)
    (t := t) one_ne_zero ht.ne' hp
  have hq : Function.Injective (evaluateTriangles fs q) := by
    change Function.Injective (evaluateTriangles fs (fun i => ((p i).re,(p i).im,t*h i)))
    simpa only [angleLift,one_mul] using hscale
  let _ : CompactSpace (triangleWeightSpace fs) :=
    isCompact_iff_compactSpace.mp (isCompact_triangleWeightSpace fs)
  refine ⟨t,ht,p,(continuous_evaluateTriangles fs q).isClosedEmbedding hq,?_,he,hP'⟩
  let Q := Type2.euclideanPoint ∘ q
  have hqi := Type2.euclideanPoint_injective.comp (vertex_injective_of_injective_evaluateTriangles fs q hcover hq)
  have htotal := sum_coneAngles fs Q hfs (fun f hf => by
    apply hqi.ne
    have hm : f.1 ∉ [f.2.1, f.2.2] := (List.nodup_cons.mp (hfs f hf)).1
    exact fun he => hm (by simp [he]))
  have hseven (i : Fin 7) : coneAngles fs Q i.succ = 2*Real.pi := by
    have he' := hangles t p he
    rw [liftedAngles_zero] at he'
    exact (congrFun he' i).trans (hangle i.succ)
  have hzero : coneAngles fs Q 0 = 2*Real.pi := by
    rw [Fin.sum_univ_succ,hcount] at htotal
    simp only [hseven,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at htotal
    linarith only [htotal]
  exact Fin.cases hzero hseven

/-- Inflate while preserving smooth constraints that include the seven cone angles. -/
theorem exists_embedded_flat_inflation_of_constraints
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
    (fs : List Triangle) (z : Vertex → ℂ) (h : Vertex → ℝ)
    (hcover : ∀ a : Vertex, ∃ f ∈ fs, a ∈ triangleVertexSet f)
    (hfs : ∀ f ∈ fs, (triangleVertices f).Nodup) (hcount : fs.length = 16)
    (hangle : ∀ v, coneAngles fs z v = 2*Real.pi)
    (hz : Function.Injective (evaluateTriangles fs (angleLift z h 1)))
    (f : ℝ × (Vertex → ℂ) → F) (hd : ContDiffAt ℝ 1 f (0,z))
    (hs : Function.Surjective (fderiv ℝ (fun p => f (0,p)) z))
    (hangles : ∀ t p, f (t,p) = f (0,z) → liftedAngles fs h (t,p) = liftedAngles fs h (0,z)) :
    ∃ t : ℝ, 0 < t ∧ ∃ p : Vertex → ℂ,
      Topology.IsClosedEmbedding (evaluateTriangles fs (angleLift p h t)) ∧
      (∀ v, coneAngles fs (Type2.euclideanPoint ∘ angleLift p h t) v = 2*Real.pi) ∧
      f (t,p) = f (0,z) := by
  obtain ⟨t,ht,p,hp,ha,hf,_⟩ :=
    exists_embedded_flat_inflation_of_constraints_near fs z h hcover hfs hcount hangle hz f hd hs
      (P := fun _ => True) (Filter.Eventually.of_forall fun _ => trivial) hangles
  exact ⟨t,ht,p,hp,ha,hf⟩

/-- An embedded height direction and a surjective planar angle derivative yield
an embedded spatial realization with flat vertex stars. -/
theorem exists_embedded_flat_inflation (fs : List Triangle) (z : Vertex → ℂ) (h : Vertex → ℝ)
    (hcover : ∀ a : Vertex, ∃ f ∈ fs, a ∈ triangleVertexSet f)
    (hfs : ∀ f ∈ fs, (triangleVertices f).Nodup) (hcount : fs.length = 16)
    (hn : ∀ f ∈ fs, ∀ v a b, cornerRays v f = some (a,b) →
      z a ≠ z v ∧ z b ≠ z v ∧ 0 < angle (z a-z v) (z b-z v) ∧
        angle (z a-z v) (z b-z v) < Real.pi)
    (hangle : ∀ v, coneAngles fs z v = 2*Real.pi)
    (hs : Function.Surjective (fderiv ℝ (sevenConeAngles fs : (Vertex → ℂ) → Fin 7 → ℝ) z))
    (hz : Function.Injective (evaluateTriangles fs (angleLift z h 1))) :
    ∃ q : Vertex → Point3, Topology.IsClosedEmbedding (evaluateTriangles fs q) ∧
      ∀ v, coneAngles fs (Type2.euclideanPoint ∘ q) v = 2*Real.pi := by
  have he : (fun p => liftedAngles fs h (0,p)) = sevenConeAngles fs := funext (liftedAngles_zero fs h)
  obtain ⟨t,_,p,hp,ha,_⟩ := exists_embedded_flat_inflation_of_constraints fs z h hcover hfs hcount hangle hz
    (liftedAngles fs h) (contDiffAt_liftedAngles fs h z hn) (by simpa only [he] using hs) (fun _ _ h => h)
  exact ⟨angleLift p h t,hp,ha⟩

end OrigamiTorus
