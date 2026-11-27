module

public import OrigamiTorus.Type6Metric
import OrigamiTorus.Type6Rank
public import OrigamiTorus.Inflation
public import OrigamiTorus.Type6Lift
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! Inflation with the two lattice periods held fixed. -/

@[expose] public section

open Filter Set
open scoped Topology ContDiff
namespace OrigamiTorus

private theorem foldedMotion_smul (t : ℝ) (m : SheetMotion) (v : Vertex) :
    FoldedMotion (t • m) v = t • FoldedMotion m v := by
  fin_cases v <;> simp [FoldedMotion]

private theorem intrinsicMotion_smul (t : ℝ) (m : SheetMotion) (v : Vertex) :
    IntrinsicMotion (t • m) v = t • IntrinsicMotion m v := by
  fin_cases v <;> simp [IntrinsicMotion]

theorem residual_smooth (second : Bool) (x w : ℝ) (z : Vertex → ℝ) :
    ContDiff ℝ 1 (lengthResidual second x w z) := by
  have hp (v : Vertex) : ContDiff ℝ 1 (fun s : ℝ × SheetMotion => FoldedMotion s.2 v) := by
    fin_cases v <;> simp [FoldedMotion] <;> fun_prop
  have hq (v : Vertex) : ContDiff ℝ 1 (fun s : ℝ × SheetMotion => IntrinsicMotion s.2 v) := by
    fin_cases v <;> simp [IntrinsicMotion] <;> fun_prop
  apply contDiff_pi.mpr
  intro e
  simp only [lengthResidual, scaledSquaredDistance, translatePoint, Prod.fst_add, Prod.snd_add]
  fun_prop (disch := assumption)

private theorem residual_at_base (second : Bool) (x w : ℝ) (z : Vertex → ℝ) :
    lengthResidual second x w z (0, 0) = 0 := by
  funext e
  have hp (v : Vertex) : FoldedMotion 0 v = 0 := by fin_cases v <;> simp [FoldedMotion]
  have hq (v : Vertex) : IntrinsicMotion 0 v = 0 := by fin_cases v <;> simp [IntrinsicMotion]
  simpa [lengthResidual, hp, hq, foldedEdgeSquared, intrinsicEdgeSquared]
    using sub_eq_zero.mpr (type6_samePlanarLengths second x w e)

private theorem smul_pair (t : ℝ) (p : ℝ × ℝ) :
    t • p = (t*p.1, t*p.2) := rfl

private theorem residual_lineDerivative
    (second : Bool) (x w : ℝ) (z : Vertex → ℝ) (m : SheetMotion) (e : EdgeIndex) :
    HasDerivAt (fun t : ℝ => lengthResidual second x w z (0, t • m) e)
      (2 * edgeDerivative second x w m e) 0 := by
  let a := (edgePeriod e).1.1
  let b := (edgePeriod e).1.2
  let P := FoldedMotion m
  let Q := IntrinsicMotion m
  let C := scaledSquaredDistance w (P a) (P b) - scaledSquaredDistance w (Q a) (Q b)
  let D := 2 * edgeDerivative second x w m e
  have hformula (t : ℝ) : lengthResidual second x w z (0, t • m) e = D * t + C * t^2 := by
    have hbase := type6_samePlanarLengths second x w e
    simp only [lengthResidual, foldedEdgeSquared, intrinsicEdgeSquared, edgeDerivative,
      foldedMotion_smul, intrinsicMotion_smul, a, b, P, Q, C, D, halfLengthDerivative,
      translatePoint, scaledSquaredDistance, Prod.fst_add, Prod.snd_add, smul_pair, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at hbase ⊢
    linear_combination hbase
  simp_rw [hformula]
  convert (((hasDerivAt_id (0 : ℝ)).const_mul D).add
      ((hasDerivAt_pow 2 (0 : ℝ)).const_mul C)) using 1
  · rfl
  · norm_num [D]

private theorem horizontalDeriv_eq {f' : (ℝ × SheetMotion) →L[ℝ] SheetMotion}
    {second : Bool} {x w : ℝ} {z : Vertex → ℝ}
    (hf : HasFDerivAt (lengthResidual second x w z) f' (0, 0))
    (m : SheetMotion) (e : EdgeIndex) :
    (f' (0,m)) e = 2 * edgeDerivative second x w m e := by
  have hline : HasDerivAt (fun t : ℝ => ((0 : ℝ), t • m)) (0,m) 0 := by
    convert (hasDerivAt_id (0 : ℝ)).smul_const ((0 : ℝ),m) using 1
    · funext t
      change ((0 : ℝ), t • m) = (t * 0, t • m)
      simp
    · simp
  have hv := hf.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  let projection := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : EdgeIndex => ℝ) e
  have hcoord := projection.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv
  exact hcoord.unique (residual_lineDerivative second x w z m e)

private theorem partial_isInvertible {f' : (ℝ × SheetMotion) →L[ℝ] SheetMotion}
    {second : Bool} {x w : ℝ} {z : Vertex → ℝ} (hd : chartDomain second x w)
    (hf : HasFDerivAt (lengthResidual second x w z) f' (0, 0)) :
    (f' ∘L ContinuousLinearMap.inr ℝ ℝ SheetMotion).IsInvertible := by
  let g := f' ∘L ContinuousLinearMap.inr ℝ ℝ SheetMotion
  have hi : Function.Injective g := by
    apply (injective_iff_map_eq_zero g).mpr
    intro v hv
    apply type6_edgeDerivative_injective second x w hd
    intro e
    have he := congrFun hv e
    change (f' (0,v)) e = 0 at he
    rw [horizontalDeriv_eq hf] at he
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  have hs : Function.Surjective g := LinearMap.injective_iff_surjective.mp hi
  exact ⟨(LinearEquiv.ofBijective g.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv,
    ContinuousLinearMap.ext fun _ => rfl⟩

/-- At the positive-height solution the length-matching derivative with
respect to the horizontal coordinates is still invertible. -/
theorem type6_lengthInflation_regular (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    (z : Vertex → ℝ) {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ t : ℝ, 0 < t ∧ ∃ m ∈ U, lengthResidual second x w z (t,m) = 0 ∧
      ((fderiv ℝ (lengthResidual second x w z) (t,m)) ∘L
        ContinuousLinearMap.inr ℝ ℝ SheetMotion).IsInvertible := by
  let f := lengthResidual second x w z
  let B := ContinuousLinearMap.inr ℝ ℝ SheetMotion
  let P (q : ℝ × SheetMotion) := (fderiv ℝ f q).comp B
  have hC := (residual_smooth second x w z).contDiffAt (x := (0,0))
  have hF := hC.hasStrictFDerivAt_fderiv (by decide : (1 : ℕ∞ω) ≠ 0)
  have hI : (P (0,0)).IsInvertible := partial_isInvertible hd hF.hasFDerivAt
  have ht : Continuous (fun L : (ℝ × SheetMotion) →L[ℝ] SheetMotion => L.comp B) :=
    (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := SheetMotion)
      (F := ℝ × SheetMotion) (G := SheetMotion)).continuous_left
  have hP : ContinuousAt P (0,0) := ht.continuousAt.comp (hC.continuousAt_fderiv (by decide))
  have hn : ∀ᶠ q : ℝ × SheetMotion in 𝓝 (0,0), q.2 ∈ U :=
    continuous_snd.continuousAt (hU.mem_nhds hbase)
  obtain ⟨t,ht,m,⟨hm,hinv⟩,he⟩ :=
    exists_pos_preserving_eventually hF hI (hn.and (hP hI.eventually_nhds))
  exact ⟨t,ht,m,hm,he.trans (residual_at_base second x w z),hinv⟩

/-- Match all twenty-four edge lengths while keeping the lattice periods fixed. -/
theorem type6_lengthInflation (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    (z : Vertex → ℝ) {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ t : ℝ, 0 < t ∧ ∃ m ∈ U, lengthResidual second x w z (t,m) = 0 := by
  obtain ⟨t,ht,m,hm,he,_⟩ := type6_lengthInflation_regular second x w hd z hU hbase
  exact ⟨t,ht,m,hm,he⟩


private theorem movedFoldedPoint_zero (second : Bool) (x w : ℝ) :
    movedFoldedPoint second x w 0 = stripPoint second x w := by
  funext v
  fin_cases v <;> simp [movedFoldedPoint, FoldedMotion]

private theorem volume_continuous (second : Bool) (x w : ℝ) (z : Vertex → ℝ)
    (a b c d : Vertex) :
    Continuous (fun m : SheetMotion => volume (movedFoldedPoint second x w m) z a b c d) := by
  have hv (v : Vertex) : Continuous (fun m : SheetMotion => movedFoldedPoint second x w m v) := by
    fin_cases v <;> simp [movedFoldedPoint, FoldedMotion]
    all_goals constructor <;> fun_prop
  unfold volume area
  fun_prop (disch := assumption)

private theorem separated_open (second : Bool) (x w : ℝ) (z : Vertex → ℝ)
    (pair : Edge × Triangle) :
    IsOpen {m : SheetMotion | isSeparated (movedFoldedPoint second x w m) z pair} := by
  obtain ⟨⟨a,b⟩,c,d,e⟩ := pair
  simp only [isSeparated, separates, ofPred_or]
  have hv (a b c d : Vertex) := volume_continuous second x w z a b c d
  apply IsOpen.union (isOpen_lt continuous_const ((hv b c d e).mul (hv a c d e)))
  apply IsOpen.union (isOpen_lt continuous_const ((hv a b d e).mul (hv a b c e)))
  apply IsOpen.union (isOpen_lt continuous_const ((hv a b c e).mul (hv a b c d)))
  exact isOpen_lt ((hv a b d e).mul (hv a b c d)) continuous_const

private theorem volume_scale (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (t : ℝ)
    (a b c d : Vertex) :
    volume p (fun v => t * z v) a b c d = t * volume p z a b c d := by
  unfold volume
  ring

private theorem separates_scale {t u v r s q : ℝ} (ht : 0 < t) (hp : separates u v r s q) :
    separates (t*u) (t*v) (t*r) (t*s) (t*q) := by
  unfold separates at hp ⊢
  have scale (x y : ℝ) : (t*x)*(t*y)=t^2*(x*y) := by ring
  simp only [scale]
  rcases hp with hp | hp | hp | hp
  · exact Or.inl (mul_pos (sq_pos_of_pos ht) hp)
  · exact Or.inr (Or.inl (mul_pos (sq_pos_of_pos ht) hp))
  · exact Or.inr (Or.inr (Or.inl (mul_pos (sq_pos_of_pos ht) hp)))
  · exact Or.inr (Or.inr (Or.inr (mul_neg_of_pos_of_neg (sq_pos_of_pos ht) hp)))

/-- At each modulus there are corrected intrinsic and extrinsic coordinates with all
twenty-four lengths matched, with general position and strict edge–face separation. -/
theorem type6_lengthMatchedLift_regular (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion), 0 < t ∧ m ∈ U ∧
      lengthResidual second x w z (t,m) = 0 ∧
      ((fderiv ℝ (lengthResidual second x w z) (t,m)) ∘L
        ContinuousLinearMap.inr ℝ ℝ SheetMotion).IsInvertible ∧
      GenericLift (movedFoldedPoint second x w m) (fun v => t * z v) ∧
      ∀ pair ∈ type6DisjointPairs,
        isSeparated (movedFoldedPoint second x w m) (fun v => t * z v) pair := by
  obtain ⟨z, hgen, hsep⟩ := type6_genericSeparatingLift second x w hd
  let Data (m : SheetMotion) :=
    GenericLift (movedFoldedPoint second x w m) z ∧
      ∀ pair ∈ type6DisjointPairs, isSeparated (movedFoldedPoint second x w m) z pair
  have hg : ∀ᶠ m in 𝓝 (0 : SheetMotion), GenericLift (movedFoldedPoint second x w m) z := by
    unfold GenericLift
    simp only [eventually_all]
    intro a b c d hab hbc hcd
    refine ((volume_continuous second x w z a b c d).continuousAt).eventually_ne ?_
    simpa only [movedFoldedPoint_zero] using hgen a b c d hab hbc hcd
  have hs : ∀ᶠ m in 𝓝 (0 : SheetMotion), ∀ pair ∈ type6DisjointPairs,
      isSeparated (movedFoldedPoint second x w m) z pair := by
    simp only [eventually_all]
    intro pair hp
    apply (separated_open second x w z pair).mem_nhds
    simpa only [mem_ofPred_eq, movedFoldedPoint_zero] using hsep pair hp
  obtain ⟨V, hsub, hopen, hzero⟩ := mem_nhds_iff.mp (show {m | Data m} ∈ 𝓝 0 from hg.and hs)
  obtain ⟨t, ht, m, hm, he,hi⟩ := type6_lengthInflation_regular second x w hd z (hopen.inter hU) ⟨hzero,hbase⟩
  have hp : Data m := hsub hm.1
  refine ⟨z, t, m, ht, hm.2, he, hi, ?_, ?_⟩
  · intro a b c d hab hbc hcd
    rw [volume_scale]
    exact mul_ne_zero ht.ne' (hp.1 a b c d hab hbc hcd)
  · rintro ⟨⟨a,b⟩,c,d,e⟩ h
    have hh := hp.2 _ h
    simp only [isSeparated, volume_scale] at hh ⊢
    exact separates_scale ht hh

/-- The matched length solution supplies a generic separating spatial lift. -/
theorem type6_lengthMatchedLift (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion), 0 < t ∧ m ∈ U ∧
      lengthResidual second x w z (t,m) = 0 ∧
      GenericLift (movedFoldedPoint second x w m) (fun v => t * z v) ∧
      ∀ pair ∈ type6DisjointPairs,
        isSeparated (movedFoldedPoint second x w m) (fun v => t * z v) pair := by
  obtain ⟨z,t,m,ht,hm,he,_,hg,hs⟩ := type6_lengthMatchedLift_regular second x w hd hU hbase
  exact ⟨z,t,m,ht,hm,he,hg,hs⟩

end OrigamiTorus
