module

public import OrigamiTorus.EightVertex.Type5.HarmonicObstruction
import Mathlib.Tactic

/-! A scale-independent separation between the harmonic edge lengths and
the spatial length data, including limits of degenerating period metrics. -/

public section

namespace OrigamiTorus.Type5

open Winding Winding.Hexagonal
open scoped RealInnerProductSpace

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private noncomputable def scalarEdge (u v : ℝ) (i j : Vertex) : ℝ :=
  let d := markedDisplacement .type5 periodIdentity i j
  (d.1 : ℝ)*u + d.2*v

/-- The anchor face collapses to a line under a rank-one period map.
The distances to leaves 6 and 7 give incompatible projections on this line. -/
private theorem harmonic_rankOne_impossible (u v : ℝ) (huv : u ≠ 0 ∨ v ≠ 0) :
    ¬ ∃ q : Vertex → E3, ∀ i j, Type2.Adjacent faces i j →
      dist (q i) (q j)^2 = (scalarEdge u v i j)^2 := by
  rintro ⟨q,hq⟩
  let s := scalarEdge u v
  let r := fun i : Vertex => q i - q 1
  let edges : List (Vertex × Vertex) := [(1,2),(1,5),(1,6),(1,7),(2,5),(2,6),(2,7),(5,6),(5,7)]
  have coords :
      edges.map (fun e => markedDisplacement .type5 periodIdentity e.1 e.2) =
      [(-1/2,1/4),(-1/4,1/2),(7/20,-7/20),(3/20,1/4),(1/4,1/4),
       (-3/20,2/5),(-7/20,0),(-2/5,3/20),(2/5,-1/4)] := by decide +kernel
  simp only [edges,List.map_cons,List.map_nil,List.cons.injEq,and_true] at coords
  obtain ⟨c12,c15,c16,c17,c25,c26,c27,c56,c57⟩ := coords
  have inn (i j : Vertex) (hi : (1,i) ∈ edges) (hj : (1,j) ∈ edges)
      (hij : i = j ∨ (i,j) ∈ edges) :
      ⟪r i,r j⟫ = (s 1 i ^ 2 + s 1 j ^ 2 - s i j ^ 2)/2 := by
    have hE : ∀ e ∈ edges, Type2.Adjacent faces e.1 e.2 := by
      simp_rw [adjacency_test]
      decide +kernel
    have hD {a b} (h : (a,b) ∈ edges) : dist (q a) (q b)^2 = s a b ^ 2 := hq _ _ (hE _ h)
    have hn (a : Vertex) : ‖r a‖ = dist (q 1) (q a) := (dist_eq_norm_sub' _ _).symm
    have hh : dist (q i) (q j)^2 = s i j ^ 2 := by
      rcases hij with rfl | he
      · have hdiag : ∀ i : Vertex, markedDisplacement .type5 periodIdentity i i = 0 := by decide +kernel
        simp [s,scalarEdge,hdiag]
      · exact hD he
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    simp only [← sq,hn,show ‖r i-r j‖ = dist (q i) (q j) by simp [r,dist_eq_norm],hD hi,hD hj,hh]
  have hx : s 1 5 • r 2 - s 1 2 • r 5 = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℝ)]
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
      real_inner_comm (r 2) (r 5)]
    rw [inn 2 2 (by decide) (by decide) (.inl rfl),inn 5 5 (by decide) (by decide) (.inl rfl),
      inn 2 5 (by decide) (by decide) (.inr (by decide))]
    have hd : ∀ i : Vertex, markedDisplacement .type5 periodIdentity i i = 0 := by decide +kernel
    norm_num [s,scalarEdge,c12,c15,c25,hd]
    ring
  have proj (j : Vertex) : s 1 5 * ⟪r 2,r j⟫ - s 1 2 * ⟪r 5,r j⟫ = 0 := by
    simpa only [inner_sub_left,real_inner_smul_left,inner_zero_left] using
      congrArg (fun z : E3 => ⟪z,r j⟫) hx
  have p := proj 6
  have p' := proj 7
  rw [inn 2 6 (by decide) (by decide) (.inr (by decide)),
    inn 5 6 (by decide) (by decide) (.inr (by decide))] at p
  rw [inn 2 7 (by decide) (by decide) (.inr (by decide)),
    inn 5 7 (by decide) (by decide) (.inr (by decide))] at p'
  norm_num [s,scalarEdge,c12,c15,c16,c17,c26,c27,c56,c57] at p p'
  have h₆ : (u-v)^2*(u+v) = 0 := by linear_combination -80/3*p
  have h₇ : u^2*(u-2*v) = 0 := by linear_combination -80/3*p'
  rcases mul_eq_zero.mp h₆ with h | h <;> rcases mul_eq_zero.mp h₇ with h' | h'
    <;> (try simp only [sq_eq_zero_iff] at h h') <;> rcases huv with hu | hv
    <;> first | exact hu (by linarith) | exact hv (by linarith)

private theorem semidefinite_impossible (A B C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hd : B^2 ≤ A*C) (hpos : 0 < A+C) :
    ¬ ∃ q : Vertex → E3, ∀ i j, Type2.Adjacent faces i j →
      let d := markedDisplacement .type5 periodIdentity i j
      dist (q i) (q j)^2 = A*(d.1 : ℝ)^2 + 2*B*d.1*d.2 + C*(d.2 : ℝ)^2 := by
  have singular (u v : ℝ) (hu : u^2 = A) (huv : u*v = B) (hv : v^2 = C) :
      ¬ ∃ q : Vertex → E3, ∀ i j, Type2.Adjacent faces i j →
        let d := markedDisplacement .type5 periodIdentity i j
        dist (q i) (q j)^2 = A*(d.1 : ℝ)^2 + 2*B*d.1*d.2 + C*(d.2 : ℝ)^2 := by
    rintro ⟨q,hq⟩
    have hn : u ≠ 0 ∨ v ≠ 0 := by by_contra! hz; simp [hz.1,hz.2] at hu hv; linarith
    apply harmonic_rankOne_impossible u v hn
    refine ⟨q,fun i j he => ?_⟩
    rw [hq _ _ he,← hu,← huv,← hv]
    unfold scalarEdge
    ring
  rcases eq_or_lt_of_le hA with ha | ha
  · have hb : B = 0 := by nlinarith
    exact singular 0 (Real.sqrt C) (by simpa using ha) (by simp [hb]) (Real.sq_sqrt hC)
  rcases eq_or_lt_of_le hd with he | he
  · have hs := Real.sq_sqrt hA
    have hp := Real.sqrt_pos.mpr ha
    apply singular (Real.sqrt A) (B/Real.sqrt A) hs (by field_simp)
    rw [div_pow,hs,div_eq_iff ha.ne']
    linarith
  · exact harmonic_lengths_impossible A B C ha he

/-- Sum over the 24 edges of the squared differences in squared lengths.
The vectors U and V give the two physical periods in the dual cycle basis. -/
noncomputable def harmonicLengthError (U V : Plane ℝ) (q : Vertex → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ e ∈ edgeList.toFinset,
    (dist (q e.1) (q e.2)^2 -
      (let d := markedDisplacement .type5 periodIdentity e.1 e.2
       squared2 U*(d.1 : ℝ)^2 + 2*dot U V*d.1*d.2 + squared2 V*(d.2 : ℝ)^2))^2

private abbrev Data := (Plane ℝ × Plane ℝ) × (Vertex → E3)

attribute [local irreducible] markedDisplacement

private theorem error_pos (z : Data) (hbase : z.2 1 = 0) (hz : z ≠ 0) :
    0 < harmonicLengthError z.1.1 z.1.2 z.2 := by
  let U := z.1.1
  let V := z.1.2
  let q := z.2
  have hz' : 0 ≤ harmonicLengthError U V q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_contra! h
  have hsum := (Finset.sum_eq_zero_iff_of_nonneg (fun (e : Vertex × Vertex) (_ : e ∈ edgeList.toFinset) =>
    sq_nonneg (dist (q e.1) (q e.2)^2 -
      (let d := markedDisplacement .type5 periodIdentity e.1 e.2
       squared2 U*(d.1 : ℝ)^2 + 2*dot U V*d.1*d.2 + squared2 V*(d.2 : ℝ)^2)))).mp
    (le_antisymm h hz')
  have he (i j : Vertex) (hij : Type2.Adjacent faces i j) :
      let d := markedDisplacement .type5 periodIdentity i j
      dist (q i) (q j)^2 = squared2 U*(d.1 : ℝ)^2 + 2*dot U V*d.1*d.2 + squared2 V*(d.2 : ℝ)^2 := by
    have symmD : ∀ i j : Vertex, markedDisplacement .type5 periodIdentity j i =
        -(markedDisplacement .type5 periodIdentity i j) := by decide +kernel
    have hm := (adjacency_test i j).mp hij
    by_cases hl : i ≤ j
    · have hmem : (i,j) ∈ edgeList.toFinset := by simpa [orderedEdge,min_eq_left hl,max_eq_right hl] using hm
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hsum (i,j) hmem))
    · have hji := le_of_not_ge hl
      have hmem : (j,i) ∈ edgeList.toFinset := by
        simpa [orderedEdge,min_eq_right hji,max_eq_left hji] using hm
      have hh := sub_eq_zero.mp (sq_eq_zero_iff.mp (hsum (j,i) hmem))
      simp only [symmD i j,Prod.fst_neg,Prod.snd_neg,Rat.cast_neg,dist_comm (q j) (q i)] at hh
      linarith only [hh]
  have hU : 0 ≤ squared2 U := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hV : 0 ≤ squared2 V := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hdet : dot U V^2 ≤ squared2 U*squared2 V := by
    simp [squared2,dot]
    nlinarith [sq_nonneg (U.1*V.2-U.2*V.1)]
  by_cases hn : 0 < squared2 U+squared2 V
  · exact semidefinite_impossible _ _ _ hU hV hdet hn ⟨q,he⟩
  · have zU : U = 0 := by
      ext <;> simp [squared2,dot] at hn hV ⊢ <;> nlinarith [sq_nonneg U.1,sq_nonneg U.2]
    have zV : V = 0 := by
      ext <;> simp [squared2,dot] at hn hU ⊢ <;> nlinarith [sq_nonneg V.1,sq_nonneg V.2]
    have zq : q = 0 := by
      funext j
      by_cases hj : j = 1
      · simpa [hj] using hbase
      · have hE : ∀ j : Vertex, j ≠ 1 → Type2.Adjacent faces 1 j := by
          simp_rw [adjacency_test]
          decide +kernel
        have h := he 1 j (hE j hj)
        simp [zU,zV,squared2,dot] at h
        simpa [← h] using hbase
    exact hz (Prod.ext (Prod.ext zU zV) zq)

private theorem error_continuous :
    Continuous (fun z : Data => harmonicLengthError z.1.1 z.1.2 z.2) := by
  unfold harmonicLengthError
  apply continuous_finsetSum
  intro e _
  generalize markedDisplacement .type5 periodIdentity e.1 e.2 = d
  unfold squared2 dot
  fun_prop

attribute [local irreducible] harmonicLengthError

private theorem compact_gap (err : Data → ℝ) (hc : Continuous err)
    (ep : ∀ z : Data, z.2 1 = 0 → z ≠ 0 → 0 < err z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : Data, z.2 1 = 0 → ‖z‖ = 1 → ε ≤ err z := by
  let K : Set Data := Metric.sphere 0 1 ∩ {z | z.2 1 = 0}
  have hK : IsCompact K := (isCompact_sphere _ _).inter_right
    (isClosed_eq ((continuous_apply (1 : Vertex)).comp continuous_snd) continuous_const)
  let p : Data := (((1,0),(0,0)),0)
  have hp : p ∈ K := by norm_num [K,p,Metric.mem_sphere,Prod.norm_def]
  obtain ⟨m,hm,hmin⟩ := hK.exists_isMinOn ⟨p,hp⟩ hc.continuousOn
  have hn : ‖m‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hm.1
  exact ⟨err m,ep m hm.2 (fun h => by simp [h] at hn),
    fun z hq hz => hmin (show z ∈ K from ⟨by simpa only [Metric.mem_sphere,dist_zero_right] using hz,hq⟩)⟩

/-- After translating vertex 1 to the origin and rescaling the combined
period vectors and spatial coordinates to norm one, there is a single
positive lower bound on the harmonic length error for all moduli. -/
private theorem normalized_gap : ∃ ε : ℝ, 0 < ε ∧
    ∀ (U V : Plane ℝ) (q : Vertex → EuclideanSpace ℝ (Fin 3)),
      q 1 = 0 → ‖((U,V),q)‖ = 1 → ε ≤ harmonicLengthError U V q := by
  obtain ⟨ε,hε,h⟩ := compact_gap _ error_continuous error_pos
  exact ⟨ε,hε,fun U V q => h ((U,V),q)⟩

private theorem error_scale (a : ℝ) (U V : Plane ℝ) (q : Vertex → E3) :
    harmonicLengthError (a • U) (a • V) (a • q) = a^4 * harmonicLengthError U V q := by
  unfold harmonicLengthError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hd : dist (a • q e.1) (a • q e.2)^2 = a^2*dist (q e.1) (q e.2)^2 := by
    rw [dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,← dist_eq_norm]
  simp only [Pi.smul_apply,hd,squared2,dot,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

/-- Uniform separation of all spatial squared edge lengths from the harmonic
model, relative to the period scale. This also covers rank-one limits. -/
theorem harmonic_uniform_gap : ∃ ε : ℝ, 0 < ε ∧
    ∀ (U V : Plane ℝ) (q : Vertex → EuclideanSpace ℝ (Fin 3)),
      ε * (max ‖U‖ ‖V‖)^4 ≤ harmonicLengthError U V q := by
  obtain ⟨ε,hε,hbound⟩ := normalized_gap
  refine ⟨ε,hε,fun U V q => ?_⟩
  let r := fun j : Vertex => q j - q 1
  let z : Data := ((U,V),r)
  have htrans : harmonicLengthError U V r = harmonicLengthError U V q := by
    unfold harmonicLengthError
    simp only [r,dist_sub_right]
  have hb : max ‖U‖ ‖V‖ ≤ ‖z‖ := le_max_left ‖(U,V)‖ ‖r‖
  rcases eq_or_lt_of_le (norm_nonneg z) with hz | hz
  · have hz' : max ‖U‖ ‖V‖ = 0 := le_antisymm (by linarith) ((norm_nonneg _).trans (le_max_left ..))
    rw [hz']
    simp only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    unfold harmonicLengthError
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · have hs : ‖‖z‖⁻¹ • z‖ = 1 := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hz),inv_mul_cancel₀ hz.ne']
    have h := hbound (‖z‖⁻¹ • U) (‖z‖⁻¹ • V) (‖z‖⁻¹ • r) (by simp [r]) hs
    rw [error_scale,htrans,inv_pow,← div_eq_inv_mul] at h
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ((norm_nonneg _).trans (le_max_left ..)) hb 4) hε.le).trans
      ((le_div_iff₀ (pow_pos hz 4)).mp h)

end OrigamiTorus.Type5
