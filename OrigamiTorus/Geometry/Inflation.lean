module

public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The positive-parameter implicit-function step used in planar inflation. -/

public section

open Filter Set
open scoped Topology

namespace OrigamiTorus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The positive-height branch can satisfy any condition holding near the
base point in the joint space of heights and horizontal coordinates. -/
theorem exists_pos_preserving_eventually
    {f : ℝ × E → F} {f' : (ℝ × E) →L[ℝ] F} {u : E}
    (hf : HasStrictFDerivAt f f' (0,u))
    (hinv : (f' ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible)
    {P : ℝ × E → Prop} (hP : ∀ᶠ q in 𝓝 (0,u), P q) :
    ∃ t : ℝ, 0 < t ∧ ∃ v, P (t,v) ∧ f (t,v) = f (0,u) := by
  let v := hf.implicitFunctionOfProdDomain hinv
  have hv : Tendsto v (𝓝 (0 : ℝ)) (𝓝 u) :=
    hf.tendsto_implicitFunctionOfProdDomain hinv
  have hP' : ∀ᶠ t in 𝓝 (0 : ℝ), P (t,v t) := (tendsto_id.prodMk_nhds hv) hP
  have hEq : ∀ᶠ t in 𝓝 (0 : ℝ), f (t,v t) = f (0,u) :=
    hf.eventually_apply_implicitFunctionOfProdDomain hinv
  have hb := (hP'.and hEq).filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hvt,hEqt⟩ := (hpos.and hb).exists
  exact ⟨t,ht,v t,hvt,hEqt⟩

/-- An invertible horizontal derivative gives solutions for positive vertical parameters
with horizontal coordinates in any prescribed open neighborhood of the base point. -/
theorem exists_pos_preserving {f : ℝ × E → F} {f' : (ℝ × E) →L[ℝ] F} {u : E}
    (hf : HasStrictFDerivAt f f' (0,u))
    (hinv : (f' ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible)
    {U : Set E} (ho : IsOpen U) (hu : u ∈ U) :
    ∃ t : ℝ, 0 < t ∧ ∃ v ∈ U, f (t,v) = f (0,u) :=
  exists_pos_preserving_eventually hf hinv (continuous_snd.continuousAt (ho.mem_nhds hu))

omit [CompleteSpace E] in
/-- A continuous family of linear maps remains surjective near a surjective
map when the codomain is finite dimensional. -/
theorem eventually_surjective_of_continuousAt [FiniteDimensional ℝ F]
    {X : Type*} [TopologicalSpace X]
    {f : X → E →L[ℝ] F} {u : X} (hc : ContinuousAt f u) (hs : Function.Surjective (f u)) :
    ∀ᶠ v in 𝓝 u, Function.Surjective (f v) := by
  obtain ⟨R,hR⟩ := (f u).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  let g (v : X) := (f v).comp R
  have hg : ContinuousAt g u := by
    let T : (E →L[ℝ] F) → F →L[ℝ] F := fun L => L.comp R
    have ht : Continuous T := (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := F) (F := E) (G := F)).continuous_left
    exact ht.continuousAt.comp hc
  have hi : (g u).IsInvertible := by
    change ((f u).comp R).IsInvertible
    rw [hR]
    exact ⟨ContinuousLinearEquiv.refl ℝ F,rfl⟩
  filter_upwards [hg hi.eventually_nhds] with v hv
  have he : Function.Surjective ((f v) ∘ R) := hv.surjective
  exact he.of_comp

omit [CompleteSpace E] in
/-- A continuous right inverse supplies the correcting horizontal directions
when the horizontal derivative is surjective onto a finite-dimensional space. -/
theorem exists_pos_preserving_of_surjective_eventually [FiniteDimensional ℝ F]
    {f : ℝ × E → F} {f' : (ℝ × E) →L[ℝ] F} {u : E}
    (hf : HasStrictFDerivAt f f' (0,u))
    (hs : Function.Surjective (f' ∘L ContinuousLinearMap.inr ℝ ℝ E))
    {P : ℝ × E → Prop} (hP : ∀ᶠ q in 𝓝 (0,u), P q) :
    ∃ t : ℝ, 0 < t ∧ ∃ v, P (t,v) ∧ f (t,v) = f (0,u) := by
  let H := f' ∘L ContinuousLinearMap.inr ℝ ℝ E
  obtain ⟨R,hR⟩ := H.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  let T : (ℝ × F) →L[ℝ] (ℝ × E) :=
    (ContinuousLinearMap.fst ℝ ℝ F).prod (R.comp (ContinuousLinearMap.snd ℝ ℝ F))
  let G (x : ℝ × F) := (0,u)+T x
  let g := f ∘ G
  have hbase : G (0,0) = (0,u) := by simp [G,← Prod.zero_eq_mk]
  have hT : HasStrictFDerivAt G T (0,0) := T.hasStrictFDerivAt.const_add (0,u)
  have hg : HasStrictFDerivAt g (f'.comp T) (0,0) := (hbase.symm ▸ hf).comp (0,0) hT
  have hId : (f'.comp T) ∘L ContinuousLinearMap.inr ℝ ℝ F = ContinuousLinearMap.id ℝ F := by
    ext x
    exact congrArg (fun (L : F →L[ℝ] F) => L x) hR
  have hinv : ((f'.comp T) ∘L ContinuousLinearMap.inr ℝ ℝ F).IsInvertible := by
    rw [hId]
    exact ⟨ContinuousLinearEquiv.refl ℝ F,rfl⟩
  have hPG : ∀ᶠ q in 𝓝 ((0,0) : ℝ × F), P (G q) :=
    hT.continuousAt (by rwa [hbase])
  obtain ⟨t,ht,v,hv,he⟩ := exists_pos_preserving_eventually hg hinv hPG
  have hGt : G (t,v) = (t,u+R v) := by simp [G,T]
  refine ⟨t,ht,u+R v,hGt ▸ hv,?_⟩
  change f (G (t,v)) = f (G (0,0)) at he
  rwa [hGt,hbase] at he

omit [CompleteSpace E] in
/-- A surjective horizontal derivative suffices when the range is finite dimensional. -/
theorem exists_pos_preserving_of_surjective [FiniteDimensional ℝ F]
    {f : ℝ × E → F} {f' : (ℝ × E) →L[ℝ] F} {u : E}
    (hf : HasStrictFDerivAt f f' (0,u))
    (hs : Function.Surjective (f' ∘L ContinuousLinearMap.inr ℝ ℝ E))
    {U : Set E} (ho : IsOpen U) (hu : u ∈ U) :
    ∃ t : ℝ, 0 < t ∧ ∃ v ∈ U, f (t,v) = f (0,u) :=
  exists_pos_preserving_of_surjective_eventually hf hs (continuous_snd.continuousAt (ho.mem_nhds hu))

end OrigamiTorus
