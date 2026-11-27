module

public import OrigamiTorus.Geometry.EmbeddedEdges
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

/-! The affine dependence obstruction to a straight-line planar complete graph on five vertices. -/

public section

open Filter
open scoped Topology

namespace OrigamiTorus

private def ThreePositive (w : Fin 5 → ℝ) : Prop :=
  ∃ s : Finset (Fin 5), s.card = 3 ∧ ∀ i ∈ s, 0 < w i

private theorem card_filter_pos_le_two (w : Fin 5 → ℝ) (h : ¬ ThreePositive w) :
    (Finset.univ.filter fun i => 0 < w i).card ≤ 2 := by
  by_contra! hlarge
  obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq hlarge
  exact h ⟨s,hcard,fun i hi => (Finset.mem_filter.mp (hs hi)).2⟩

private theorem threePositive_or_of_disjoint_small_hulls {E : Type*} [AddCommGroup E] [Module ℝ E]
    (q : Fin 5 → E) (w : Fin 5 → ℝ) (hne : w ≠ 0) (hm : ∑ i, w i = 0)
    (hv : ∑ i, w i • q i = 0)
    (hd : ∀ s t : Finset (Fin 5), s.card ≤ 2 → t.card ≤ 2 → Disjoint s t →
      (∀ i ∈ s, 0 < w i) → (∀ i ∈ t, w i < 0) →
      Disjoint (vertexHull q s) (vertexHull q t)) : ThreePositive w ∨ ThreePositive (-w) := by
  by_contra! h
  have hs := card_filter_pos_le_two w h.1
  have ht : (Finset.univ.filter fun i => w i < 0).card ≤ 2 := by
    simpa only [Pi.neg_apply, neg_pos] using card_filter_pos_le_two (-w) h.2
  have hst : Disjoint (Finset.univ.filter fun i => 0 < w i) (Finset.univ.filter fun i => w i < 0) := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun _ hpos hneg => (not_lt_of_gt hpos) hneg
  obtain ⟨p,hp,hp'⟩ := vertexHull_inter_of_signed_relation q w hne hm hv
  exact Set.disjoint_left.mp (hd _ _ hs ht hst
    (fun _ hi => (Finset.mem_filter.mp hi).2) (fun _ hi => (Finset.mem_filter.mp hi).2)) hp hp'

private theorem isOpen_threePositive (w : ℝ → Fin 5 → ℝ) (h : ∀ i, Continuous (fun t => w t i)) :
    IsOpen {t | ThreePositive (w t)} := by
  have he : {t | ThreePositive (w t)} =
      ⋃ (s : Finset (Fin 5)) (_ : s.card = 3), ⋂ i ∈ s, {t | 0 < w t i} := by
    ext t
    simp [ThreePositive]
  rw [he]
  exact isOpen_iUnion fun s => isOpen_iUnion fun _ =>
    isOpen_biInter_finset fun i _ => isOpen_lt continuous_const (h i)

private theorem eventually_threePositive_on_line (u v : Fin 5 → ℝ) (h : ThreePositive v) :
    ∀ᶠ t : ℝ in atTop, ThreePositive (u + t • v) := by
  obtain ⟨s,hcard,hs⟩ := h
  have he : ∀ᶠ t : ℝ in atTop, ∀ i ∈ s, 0 < (u + t • v) i := by
    refine (s.eventually_all).mpr fun i hi => ?_
    filter_upwards [eventually_gt_atTop (-u i / v i)] with t ht
    change 0 < u i + t * v i
    have hp := (div_lt_iff₀ (hs i hi)).mp ht
    linarith
  filter_upwards [he] with _ ht
  exact ⟨s,hcard,ht⟩

private theorem threePositive_disjoint (w : Fin 5 → ℝ) :
    ThreePositive w → ThreePositive (-w) → False := by
  rintro ⟨s,hs,hpos⟩ ⟨t,ht,hneg⟩
  have hst : Disjoint s t := Finset.disjoint_left.mpr fun i hi hj =>
    (not_lt_of_gt (hpos i hi)) (neg_pos.mp (hneg i hj))
  have hcard := Finset.card_le_card (Finset.subset_univ (s ∪ t))
  rw [Finset.card_union_of_disjoint hst, hs, ht, Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- Among five points in a space of dimension at most two, the convex hulls
of two disjoint sets of at most two labels intersect. -/
theorem exists_small_intersection_of_five_planar_points {E : Type*} [AddCommGroup E]
    [Module ℝ E] [FiniteDimensional ℝ E] (q : Fin 5 → E) (hdim : Module.finrank ℝ E ≤ 2) :
    ∃ s t : Finset (Fin 5), s.card ≤ 2 ∧ t.card ≤ 2 ∧ Disjoint s t ∧
      (vertexHull q s ∩ vertexHull q t).Nonempty := by
  classical
  by_contra! h
  have hdisj (s t : Finset (Fin 5)) (hs : s.card ≤ 2) (ht : t.card ≤ 2) (hst : Disjoint s t) :
      Disjoint (vertexHull q s) (vertexHull q t) := Set.disjoint_iff_inter_eq_empty.mpr (h s t hs ht hst)
  let L : (Fin 5 → ℝ) →ₗ[ℝ] (ℝ × E) :=
    { toFun := fun w => (∑ i, w i, ∑ i, w i • q i)
      map_add' := by intro u v; simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by intro c u; simp [← Finset.mul_sum, mul_smul, Finset.smul_sum] }
  have hrank : Module.finrank ℝ L.range ≤ 3 := by
    have he := Submodule.finrank_le L.range
    simp only [Module.finrank_prod, Module.finrank_self] at he
    omega
  have hre := L.finrank_range_add_finrank_ker
  rw [Module.finrank_fin_fun] at hre
  have hdimK : 2 ≤ Module.finrank ℝ L.ker := by omega
  let B := Module.finBasis ℝ L.ker
  let i : Fin (Module.finrank ℝ L.ker) := ⟨0,by omega⟩
  let j : Fin (Module.finrank ℝ L.ker) := ⟨1,by omega⟩
  have hji : j ≠ i := by intro h; have he := congrArg Fin.val h; simp [j,i] at he
  let u := B i
  let v := B j
  let r (t : ℝ) : Fin 5 → ℝ := ↑(u + t • v : L.ker)
  have hr (t : ℝ) (k : Fin 5) : r t k = (u.val k) + t * (v.val k) := rfl
  have hne (t : ℝ) : r t ≠ 0 := by
    intro hz
    have he : (u + t • v : L.ker) = 0 := Subtype.ext hz
    have hn := congrArg (fun w => B.repr w i) he
    simp [u,v,map_add,map_smul,Module.Basis.repr_self,hji] at hn
  have hsign (w : L.ker) (hw : w.val ≠ 0) : ThreePositive w.val ∨ ThreePositive (-w.val) := by
    have hz := LinearMap.mem_ker.mp w.property
    exact threePositive_or_of_disjoint_small_hulls q w.val hw
      (congrArg Prod.fst hz) (congrArg Prod.snd hz) (fun s t hs ht hd _ _ => hdisj s t hs ht hd)
  let U : Set ℝ := {t | ThreePositive (r t)}
  let V : Set ℝ := {t | ThreePositive (-r t)}
  have hcont (k : Fin 5) : Continuous (fun t => r t k) := by
    simp only [hr]
    fun_prop
  have hU : IsOpen U := isOpen_threePositive r hcont
  have hV : IsOpen V := isOpen_threePositive (fun t => -r t) fun k => (hcont k).neg
  have hcov (t : ℝ) : t ∈ U ∨ t ∈ V := hsign (u + t • v) (hne t)
  have hcom : Uᶜ = V := by
    ext t
    refine ⟨fun hu => (hcov t).resolve_left hu, fun hv hu => ?_⟩
    exact threePositive_disjoint (r t) hu hv
  have hvne : v.val ≠ 0 := by
    intro hz
    have he : v = 0 := Subtype.ext hz
    exact (B.ne_zero j) he
  have hnonempty : U.Nonempty ∧ V.Nonempty := by
    rcases hsign v hvne with hp | hn
    · obtain ⟨s,hs⟩ := (eventually_threePositive_on_line u.val v.val hp).exists
      obtain ⟨t,ht⟩ := (eventually_threePositive_on_line (-u.val) v.val hp).exists
      refine ⟨⟨s,hs⟩,⟨-t,?_⟩⟩
      change ThreePositive (-r (-t))
      simpa only [show -r (-t) = -u.val + t • v.val from by ext k; simp [hr]; ring] using ht
    · obtain ⟨s,hs⟩ := (eventually_threePositive_on_line u.val (-v.val) hn).exists
      obtain ⟨t,ht⟩ := (eventually_threePositive_on_line (-u.val) (-v.val) hn).exists
      refine ⟨⟨-s,?_⟩,⟨t,?_⟩⟩
      · change ThreePositive (r (-s))
        simpa only [show r (-s) = u.val + s • (-v.val) from by ext k; simp [hr]] using hs
      · change ThreePositive (-r t)
        simpa only [show -r t = -u.val + t • (-v.val) from by ext k; simp [hr]; ring] using ht
  have hclosed : IsClosed U := isOpen_compl_iff.mp (hcom.symm ▸ hV)
  have hfull := IsClopen.eq_univ ⟨hclosed,hU⟩ hnonempty.1
  obtain ⟨t,ht⟩ := hnonempty.2
  have hu : t ∈ U := hfull.symm ▸ Set.mem_univ t
  exact threePositive_disjoint (r t) hu ht

private theorem not_threePositive_of_nonpos_triple (w : Fin 5 → ℝ)
    (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : w a ≤ 0) (hb : w b ≤ 0) (hc : w c ≤ 0) : ¬ ThreePositive w := by
  rintro ⟨s,hs,hpos⟩
  let t : Finset (Fin 5) := {a,b,c}
  have ht : t.card = 3 := by simp [t,hab,hac,hbc]
  have hst : Disjoint s t := by
    refine Finset.disjoint_left.mpr fun i hi hj => (not_le_of_gt (hpos i hi)) ?_
    simp only [t,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> assumption
  have h := Finset.card_le_card (Finset.subset_univ (s ∪ t))
  rw [Finset.card_union_of_disjoint hst,hs,ht,Finset.card_univ,Fintype.card_fin] at h
  omega

/-- In a straight-line planar complete graph on five vertices with the edge 34
omitted, the two remaining vertices cannot both lie outside the anchor triangle.
The hull hypothesis is exactly the disjointness of label-disjoint edges and
vertices of that graph. -/
theorem planar_missing_edge_root_in_triangle {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (q : Fin 5 → E) (hdim : Module.finrank ℝ E ≤ 2)
    (hanchor : AffineIndependent ℝ (fun i : Fin 3 => q (i.castAdd 2)))
    (hd : ∀ s t : Finset (Fin 5), s.card ≤ 2 → t.card ≤ 2 → Disjoint s t →
      ¬ ({3,4} : Finset (Fin 5)) ⊆ s → ¬ ({3,4} : Finset (Fin 5)) ⊆ t →
      Disjoint (vertexHull q s) (vertexHull q t)) :
    q 3 ∈ vertexHull q ({0,1,2} : Finset (Fin 5)) ∨ q 4 ∈ vertexHull q {0,1,2} := by
  classical
  by_contra! hout
  let T : (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × E) :=
    { toFun := fun w => (∑ i, w i, ∑ i, w i • q (i.castAdd 2))
      map_add' := by intro u v; simp [Finset.sum_add_distrib,add_smul]
      map_smul' := by intro c u; simp [← Finset.mul_sum,mul_smul,Finset.smul_sum] }
  have hTi : Function.Injective T := by
    apply (injective_iff_map_eq_zero T).mpr
    intro w hz
    have hh : (∑ i, w i) = 0 := congrArg Prod.fst hz
    have he : (∑ i, w i • q (i.castAdd 2)) = 0 := congrArg Prod.snd hz
    apply funext
    apply ((affineIndependent_iff_of_fintype ℝ _).mp hanchor) w hh
    rwa [Finset.weightedVSub_eq_linear_combination _ hh]
  have hdimT : Module.finrank ℝ (Fin 3 → ℝ) = Module.finrank ℝ (ℝ × E) := by
    have hle := Submodule.finrank_le T.range
    rw [LinearMap.finrank_range_of_inj hTi] at hle
    simp only [Module.finrank_fin_fun,Module.finrank_prod,Module.finrank_self] at hle ⊢
    omega
  have hT := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimT).mp hTi
  obtain ⟨a,ha⟩ := hT (1,q 3)
  obtain ⟨b,hb⟩ := hT (1,q 4)
  have hnegative (w : Fin 3 → ℝ) (i : Fin 5)
      (hw : T w = (1,q i)) (hn : q i ∉ vertexHull q {0,1,2}) : ∃ j, w j < 0 := by
    by_contra! hpos
    have hsum : (∑ j, w j) = 1 := congrArg Prod.fst hw
    have hq : (∑ j, w j • q (j.castAdd 2)) = q i := congrArg Prod.snd hw
    let anchors := (Finset.univ : Finset (Fin 3)).map (Fin.castAddEmb 2)
    have hanchors : anchors = {0,1,2} := by decide +kernel
    rw [← hanchors] at hn
    apply hn
    rw [← hq]
    let w' : Fin 5 → ℝ := @Fin.addCases 3 2 (fun _ => ℝ) w (fun _ => 0)
    have hw' (k : Fin 3) : w' (Fin.castAddEmb 2 k) = w k := Fin.addCases_left k
    convert weighted_mem_vertexHull q anchors w' ?_ ?_ using 1
    · rw [Finset.sum_map]
      simp only [hw']; rfl
    · intro j hj
      obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp hj
      simpa only [hw'] using hpos k
    · rw [Finset.sum_map]
      simpa only [hw'] using hsum
  obtain ⟨ia,hia⟩ := hnegative a 3 ha hout.1
  obtain ⟨ib,hib⟩ := hnegative b 4 hb hout.2
  let u : Fin 5 → ℝ := @Fin.addCases 3 2 (fun _ => ℝ) (-a) ![1,0]
  let v : Fin 5 → ℝ := @Fin.addCases 3 2 (fun _ => ℝ) b ![0,-1]
  let S : (Fin 5 → ℝ) →ₗ[ℝ] (ℝ × E) :=
    { toFun := fun w => (∑ i, w i, ∑ i, w i • q i)
      map_add' := by intro w z; simp [Finset.sum_add_distrib,add_smul]
      map_smul' := by intro c w; simp [← Finset.mul_sum,mul_smul,Finset.smul_sum] }
  have hu : S u = 0 := by
    have hm : (∑ j, a j) = 1 := congrArg Prod.fst ha
    have hq : (∑ j, a j • q (j.castAdd 2)) = q 3 := congrArg Prod.snd ha
    apply Prod.ext
    · change (∑ j, u j) = 0
      rw [Fin.sum_univ_add (a := 3) (b := 2)]
      simp [u,Fin.sum_univ_two]
      rw [hm,neg_add_cancel]
    · change (∑ j, u j • q j) = 0
      rw [Fin.sum_univ_add (a := 3) (b := 2)]
      simp [u,Fin.sum_univ_two]
      rw [hq,neg_add_cancel]
  have hv : S v = 0 := by
    have hm : (∑ j, b j) = 1 := congrArg Prod.fst hb
    have hq : (∑ j, b j • q (j.castAdd 2)) = q 4 := congrArg Prod.snd hb
    apply Prod.ext
    · change (∑ j, v j) = 0
      rw [Fin.sum_univ_add (a := 3) (b := 2)]
      simp [v,Fin.sum_univ_two,hm]
    · change (∑ j, v j • q j) = 0
      rw [Fin.sum_univ_add (a := 3) (b := 2)]
      simp [v,Fin.sum_univ_two,hq]
  have hu3 : u 3 = 1 := Fin.addCases_right (0 : Fin 2)
  have hu4 : u 4 = 0 := Fin.addCases_right (1 : Fin 2)
  have hv3 : v 3 = 0 := Fin.addCases_right (0 : Fin 2)
  have hv4 : v 4 = -1 := Fin.addCases_right (1 : Fin 2)
  have hsign (w : Fin 5 → ℝ) (hne : w ≠ 0) (hzero : S w = 0)
      (h3 : 0 ≤ w 3) (h4 : w 4 ≤ 0) : ThreePositive w ∨ ThreePositive (-w) := by
    apply threePositive_or_of_disjoint_small_hulls q w hne
      (congrArg Prod.fst hzero) (congrArg Prod.snd hzero)
    intro s t hs ht hst hpos hneg
    exact hd s t hs ht hst
      (fun h => (not_lt_of_ge h4) (hpos 4 (h (by simp))))
      (fun h => (not_lt_of_ge h3) (hneg 3 (h (by simp))))
  have hcast3 (i : Fin 3) : i.castAdd 2 ≠ (3 : Fin 5) := by
    intro h
    have := congrArg Fin.val h
    simpa using (show (i : ℕ) ≠ 3 by omega) this
  have hcast4 (i : Fin 3) : i.castAdd 2 ≠ (4 : Fin 5) := by
    intro h
    have := congrArg Fin.val h
    simpa using (show (i : ℕ) ≠ 4 by omega) this
  have hpu : ThreePositive u := by
    have hn : u ≠ 0 := fun h => by simp [h] at hu3
    refine (hsign u hn hu (by rw [hu3]; norm_num) (by rw [hu4])).resolve_right ?_
    apply not_threePositive_of_nonpos_triple (-u) (ia.castAdd 2) 3 4 (hcast3 _) (hcast4 _) (by decide)
    · simpa [u] using hia.le
    · simp [hu3]
    · simp [hu4]
  have hpv : ThreePositive (-v) := by
    have hn : v ≠ 0 := fun h => by simp [h] at hv4
    refine (hsign v hn hv (by rw [hv3]) (by rw [hv4]; norm_num)).resolve_left ?_
    exact not_threePositive_of_nonpos_triple v (ib.castAdd 2) 3 4 (hcast3 _) (hcast4 _)
      (by decide) (by simpa [v] using hib.le) (by rw [hv3]) (by rw [hv4]; norm_num)
  let w (r : ℝ) : Fin 5 → ℝ := u + r • v
  let U : Set ℝ := {r | ThreePositive (w r)}
  let V : Set ℝ := {r | ThreePositive (-w r)}
  have hcont (i : Fin 5) : Continuous (fun r => w r i) := by
    change Continuous (fun r => u i+r*v i)
    fun_prop
  have hU : IsOpen U := isOpen_threePositive w hcont
  have hV : IsOpen V := isOpen_threePositive (fun r => -w r) fun i => (hcont i).neg
  have hUV : Disjoint U V := Set.disjoint_left.mpr fun r hr hs => threePositive_disjoint (w r) hr hs
  have hcov : Set.Ioi (0 : ℝ) ⊆ U ∪ V := by
    intro r hr
    have h3 : w r 3 = 1 := by simp [w,hu3,hv3]
    have h4 : w r 4 = -r := by simp [w,hu4,hv4]
    exact hsign (w r) (fun h => by simp [h] at h3) (by simp [w,hu,hv])
      (by rw [h3]; norm_num) (by rw [h4]; exact neg_nonpos.mpr hr.le)
  have hpU : (Set.Ioi (0 : ℝ) ∩ U).Nonempty := by
    have hzero : 0 ∈ U := by simpa [U,w] using hpu
    have hnear : ∀ᶠ r in 𝓝[Set.Ioi (0 : ℝ)] 0, r ∈ U :=
      (nhdsWithin_le_nhds (hU.mem_nhds hzero))
    have hpos : ∀ᶠ r in 𝓝[Set.Ioi (0 : ℝ)] 0, r ∈ Set.Ioi (0 : ℝ) := self_mem_nhdsWithin
    exact (hpos.and hnear).exists
  have hpV : (Set.Ioi (0 : ℝ) ∩ V).Nonempty := by
    have hnear := eventually_threePositive_on_line (-u) (-v) hpv
    have hn : ∀ᶠ r : ℝ in atTop, r ∈ Set.Ioi (0 : ℝ) ∧ r ∈ V := by
      filter_upwards [eventually_gt_atTop (0 : ℝ),hnear] with r hr hp
      exact ⟨hr, by simpa [V,w,neg_add,smul_neg,add_comm] using hp⟩
    exact hn.exists
  obtain ⟨r,hr,hvr⟩ := hpV
  exact Set.disjoint_left.mp hUV
    (IsPreconnected.subset_left_of_subset_union hU hV hUV hcov hpU isPreconnected_Ioi hr) hvr

private theorem almostClique_small_face {fs : List Triangle} (k : Fin 5 → Vertex)
    (hcover : ∀ i, ∃ f ∈ fs, k i ∈ triangleVertexSet f)
    (hedge : ∀ i j, i ≠ j → ¬ ({3,4} : Finset (Fin 5)) ⊆ {i,j} → Type2.Adjacent fs (k i) (k j))
    (s : Finset (Fin 5)) (hs : s.Nonempty) (hc : s.card ≤ 2)
    (hm : ¬ ({3,4} : Finset (Fin 5)) ⊆ s) : s.image k ∈ (triangleComplex fs).faces := by
  have hle := Finset.one_le_card.mpr hs
  rcases (show s.card = 1 ∨ s.card = 2 by omega) with he | he
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp he
    simpa only [Finset.image_singleton] using covered_singleton_face (hcover a)
  · obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp he
    simpa only [Finset.image_insert,Finset.image_singleton] using adjacent_pair_face (hedge a b hab hm)

private theorem almostClique_anchor_independent {fs : List Triangle}
    (q : Vertex → Point3) (he : Function.Injective (evaluateTriangles fs q))
    (k : Fin 5 → Vertex) (hki : Function.Injective k)
    (hcover : ∀ i, ∃ f ∈ fs, k i ∈ triangleVertexSet f)
    (hedge : ∀ i j, i ≠ j → ¬ ({3,4} : Finset (Fin 5)) ⊆ {i,j} → Type2.Adjacent fs (k i) (k j)) :
    AffineIndependent ℝ (![q (k 0),q (k 1),q (k 2)] : Fin 3 → Point3) := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hc
  rcases hc.wbtw_or_wbtw_or_wbtw with hx | hx | hx
  · exact not_mem_edge_of_embedding q he (hcover 1)
      (hedge 0 2 (by decide) (by decide)) (hki.ne (by decide)) (hki.ne (by decide)) hx.mem_segment
  · exact not_mem_edge_of_embedding q he (hcover 2)
      (hedge 1 0 (by decide) (by decide)) (hki.ne (by decide)) (hki.ne (by decide)) hx.mem_segment
  · exact not_mem_edge_of_embedding q he (hcover 0)
      (hedge 2 1 (by decide) (by decide)) (hki.ne (by decide)) (hki.ne (by decide)) hx.mem_segment

/-- Five labeled vertices with all pairs connected except possibly 34 cannot
be coplanar if the first three are a filled face of the embedding. -/
theorem almostClique_not_in_plane {fs : List Triangle} (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles fs q)) (k : Fin 5 → Vertex)
    (hki : Function.Injective k) (hcover : ∀ i, ∃ f ∈ fs, k i ∈ triangleVertexSet f)
    (hedge : ∀ i j, i ≠ j → ¬ ({3,4} : Finset (Fin 5)) ⊆ {i,j} → Type2.Adjacent fs (k i) (k j))
    (hface : ({k 0,k 1,k 2} : Finset Vertex) ∈ (triangleComplex fs).faces)
    (o : Point3) (P : Submodule ℝ Point3) (hP : Module.finrank ℝ P ≤ 2)
    (hcore : ∀ i : Fin 5, q (k i)-o ∈ P) : False := by
  classical
  let r (i : Fin 5) : P := ⟨q (k i)-o,hcore i⟩
  let A : P →ᵃ[ℝ] Point3 :=
    (AffineEquiv.constVAdd ℝ Point3 o).toAffineMap.comp P.subtype.toAffineMap
  have hA (i : Fin 5) : A (r i) = q (k i) := by
    change o + (q (k i)-o) = q (k i)
    abel
  have hmap (s : Finset (Fin 5)) : A '' vertexHull r s = vertexHull q (s.image k) := by
    rw [vertexHull,A.image_convexHull,Set.image_image,vertexHull,Finset.coe_image,Set.image_image]
    exact congrArg (convexHull ℝ) (Set.image_congr (fun i _ => hA i))
  have hAi : AffineIndependent ℝ (fun i : Fin 3 => r (i.castAdd 2)) := by
    apply AffineIndependent.of_comp A
    have hf : A ∘ (fun i : Fin 3 => r (i.castAdd 2)) = ![q (k 0),q (k 1),q (k 2)] := by
      funext i
      change A (r (i.castAdd 2)) = _
      rw [hA]
      fin_cases i <;> rfl
    rw [hf]
    exact almostClique_anchor_independent q he k hki hcover hedge
  have hD (s t : Finset (Fin 5)) (hs : s.card ≤ 2) (ht : t.card ≤ 2) (hst : Disjoint s t)
      (hms : ¬ ({3,4} : Finset (Fin 5)) ⊆ s) (hmt : ¬ ({3,4} : Finset (Fin 5)) ⊆ t) :
      Disjoint (vertexHull r s) (vertexHull r t) := by
    rw [Set.disjoint_left]
    intro p hp hpt
    have hne (d : Finset (Fin 5)) (hp : p ∈ vertexHull r d) : d.Nonempty := by
      by_contra! h
      simp [h,vertexHull] at hp
    have hdisj := disjoint_vertexHull_of_injective_evaluateTriangles fs q he
      (s.image k) (t.image k) (almostClique_small_face k hcover hedge s (hne s hp) hs hms)
      (almostClique_small_face k hcover hedge t (hne t hpt) ht hmt) ((Finset.disjoint_image hki).mpr hst)
    exact Set.disjoint_left.mp hdisj (hmap s ▸ Set.mem_image_of_mem A hp)
      (hmap t ▸ Set.mem_image_of_mem A hpt)
  have hanchor : ({0,1,2} : Finset (Fin 5)).image k = {k 0,k 1,k 2} := by simp
  have hout (i : Fin 5) (hi : i = 3 ∨ i = 4) : r i ∉ vertexHull r {0,1,2} := by
    intro hp
    have hdi : Disjoint ({k i} : Finset Vertex) {k 0,k 1,k 2} := by
      rcases hi with rfl | rfl <;> simp [hki.eq_iff] <;> decide
    have hdis := disjoint_vertexHull_of_injective_evaluateTriangles fs q he
      {k i} {k 0,k 1,k 2} (covered_singleton_face (hcover i)) hface hdi
    apply Set.disjoint_left.mp hdis (subset_convexHull ℝ _ ⟨k i,by simp,rfl⟩)
    rw [← hanchor,← hmap,← hA]
    exact Set.mem_image_of_mem A hp
  exact (planar_missing_edge_root_in_triangle r hP hAi hD).elim (hout 3 (Or.inl rfl)) (hout 4 (Or.inr rfl))

end OrigamiTorus
