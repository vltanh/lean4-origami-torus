module

public import OrigamiTorus.EightVertex.Type4.Circles
public import OrigamiTorus.EightVertex.Type7.Angles
import Mathlib.Tactic

/-! The algebraic cone-angle check shared by the two Type 4 planar charts. -/

@[expose] public section

namespace OrigamiTorus.Type4

open Type7 (orientedFaces physicalComplex physicalComplex_one physicalComplex_mul)
open Type5 (Plane)

/-- The set of neighbors in the original oriented face list. -/
def neighborList (v : Vertex) : List Vertex :=
  ((Type7.faces.filter (fun f => (triangleVertices f).contains v)).flatMap triangleVertices).eraseDups.filter
    (· != v)

def nonCreaseList (v : Vertex) : List Vertex :=
  ![[],[6,2],[5,3,1,7],[5,2],[6,7],[3,2],[4,1],[4,2]] v

theorem nonCreaseList_checked (v : Vertex) :
    let (s,t) := negativeBlocks v
    let expected := (neighborList v).filter (fun i => !(s.contains i || t.contains i))
    (nonCreaseList v).all expected.contains = true ∧ expected.all (nonCreaseList v).contains = true := by
  fin_cases v <;> decide +kernel

noncomputable def cornerFromRays (r : Vertex → ℂ) (i : Vertex) (f : Triangle × Bool) : ℂ :=
  let ((a,b,c),pos) := f
  let product (u v : Vertex) := if pos then (starRingEnd ℂ) (r u)*r v else r u*(starRingEnd ℂ) (r v)
  if i = a then product b c else if i = b then product c a else if i = c then product a b else 1

noncomputable def blockPhase (r : Vertex → ℂ) (v : Vertex) : ℂ :=
  ((negativeBlocks v).1.map r).prod * (starRingEnd ℂ) (((negativeBlocks v).2.map r).prod)

noncomputable def nonCreaseNorms (r : Vertex → ℂ) (v : Vertex) : ℝ :=
  ((nonCreaseList v).map (fun i => Complex.normSq (r i))).prod

noncomputable def angleProduct (r : Vertex → ℂ) (v : Vertex) : ℂ :=
  (orientedFaces.map (cornerFromRays r v)).prod

set_option maxHeartbeats 0 in
private theorem angleProduct_factor (r : Vertex → ℂ) (v : Vertex) :
    angleProduct r v = (nonCreaseNorms r v : ℂ)*(blockPhase r v)^2 ∨
    angleProduct r v = (nonCreaseNorms r v : ℂ)*((starRingEnd ℂ) (blockPhase r v))^2 := by
  fin_cases v <;>
    norm_num [angleProduct,blockPhase,nonCreaseNorms,nonCreaseList,negativeBlocks,
      orientedFaces,Type7.faces,cornerFromRays,triangleVertices,Complex.ofReal_mul,
      Complex.normSq_eq_conj_mul_self,map_mul] <;>
    first | (left; ring; done) | (right; ring)

private theorem block_lists_neighbors (v : Vertex) :
    let (s,t) := negativeBlocks v
    ((s++t)++nonCreaseList v).all (neighborList v).contains = true := by
  fin_cases v <;> decide +kernel

private theorem ray_list_product_ne_zero (r : Vertex → ℂ) (l : List Vertex)
    (hn : ∀ v ∈ l, r v ≠ 0) : (l.map r).prod ≠ 0 := by
  apply List.prod_ne_zero
  intro hz
  obtain ⟨v,hv,he⟩ := List.mem_map.mp hz
  exact hn v hv he

private theorem angleProduct_pos_of_block_real (r : Vertex → ℂ) (v : Vertex)
    (hn : ∀ i ∈ neighborList v, r i ≠ 0) (hr : (blockPhase r v).im = 0) :
    0 < (angleProduct r v).re ∧ (angleProduct r v).im = 0 := by
  have hn' : ∀ i ∈ ((negativeBlocks v).1++(negativeBlocks v).2)++nonCreaseList v, r i ≠ 0 := by
    intro i hi
    have hh := (List.all_eq_true.mp (block_lists_neighbors v)) i hi
    exact hn i (List.contains_iff_mem.mp hh)
  have hN : ((negativeBlocks v).1.map r).prod ≠ 0 :=
    ray_list_product_ne_zero r _ (fun i hi => hn' i (by simp [hi]))
  have hD : ((negativeBlocks v).2.map r).prod ≠ 0 :=
    ray_list_product_ne_zero r _ (fun i hi => hn' i (by simp [hi]))
  have hnorm : 0 < nonCreaseNorms r v := by
    apply List.prod_pos
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact Complex.normSq_pos.mpr (hn' i (by simp [hi]))
  have he : blockPhase r v ≠ 0 := by
    unfold blockPhase
    exact mul_ne_zero hN ((map_ne_zero _).mpr hD)
  have hRe : (blockPhase r v).re ≠ 0 := by
    intro hz
    apply he
    apply Complex.ext <;> simp [hz,hr]
  have hp (z : ℂ) (hz : z.im = 0) (hr' : z.re ≠ 0) :
      0 < ((nonCreaseNorms r v : ℂ)*z^2).re ∧ ((nonCreaseNorms r v : ℂ)*z^2).im = 0 := by
    simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hz,
      mul_zero,zero_mul,sub_zero,add_zero]
    exact ⟨mul_pos hnorm (mul_self_pos.mpr hr'),trivial⟩
  rcases angleProduct_factor r v with h | h
  · rw [h]
    exact hp _ hr hRe
  · rw [h]
    exact hp _ (by simp [Complex.conj_im,hr]) hRe

private theorem physical_rayProduct (w : ℝ) (hw : 0 ≤ w) (p : Vertex → Plane ℝ) (v : Vertex)
    (l : List Vertex) :
    physicalComplex w (rayProduct w p v l) =
      (l.map (fun i => physicalComplex w (p i-p v))).prod := by
  have aux (l : List Vertex) (acc : Plane ℝ) :
      physicalComplex w (l.foldl (fun a i => Type7.multiplyComplex w a (p i-p v)) acc) =
        physicalComplex w acc * (l.map (fun i => physicalComplex w (p i-p v))).prod := by
    induction l generalizing acc with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldl_cons,List.map_cons,List.prod_cons]
      rw [ih,physicalComplex_mul w hw,mul_assoc]
  rw [rayProduct,aux,physicalComplex_one,one_mul]

private theorem physicalComplex_sub (w : ℝ) (u v : Plane ℝ) :
    physicalComplex w (u-v) = physicalComplex w u-physicalComplex w v := by
  apply Complex.ext <;> simp [physicalComplex,mul_sub]

/-- The product of the signed physical corner factors at a Type 4 vertex is
positive real. All rays cited in the formula are edges of the marked face table. -/
theorem trapezoid_corner_product_positive (x w c H : ℝ) (hw : 0 ≤ w) (hc : 1-c ≠ 0)
    (v : Vertex) (hn : ∀ i ∈ neighborList v, polynomialPoints x w c H 1 i ≠ polynomialPoints x w c H 1 v) :
    let p := polynomialPoints x w c H 1
    let r (i : Vertex) := physicalComplex w (p i-p v)
    0 < w →
    0 < (angleProduct r v).re ∧ (angleProduct r v).im = 0 := by
  let p := polynomialPoints x w c H 1
  let r (i : Vertex) := physicalComplex w (p i-p v)
  dsimp only
  intro hw'
  have hn' (i : Vertex) (hi : i ∈ neighborList v) : r i ≠ 0 := by
    intro hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    change (p i).1-(p v).1 = 0 at h1
    change Real.sqrt w*((p i).2-(p v).2)=0 at h2
    exact hn i hi (Prod.ext (sub_eq_zero.mp h1)
      (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (Real.sqrt_pos.2 hw').ne')))
  apply angleProduct_pos_of_block_real r v hn'
  unfold blockPhase
  have hx := negative_blocks_collinear x w c H hc v
  dsimp only at hx
  rw [← physical_rayProduct w hw p v _, ← physical_rayProduct w hw p v _]
  simp only [physicalComplex,Complex.mul_im,Complex.conj_re,Complex.conj_im,Type5.cross] at hx ⊢
  linear_combination -Real.sqrt w*hx

noncomputable def chartCorner (p : Vertex → ℂ) (v : Vertex) (f : Triangle × Bool) : ℂ :=
  cornerFromRays (fun i => p i-p v) v f

private theorem chartCorner_arguments (p : Vertex → ℂ) (f : Triangle × Bool) (hf : f ∈ orientedFaces)
    (hs : ∀ v ∈ triangleVertices f.1, 0 < (chartCorner p v f).im) :
    ∑ v : Vertex, (chartCorner p v f).arg = Real.pi := by
  rcases f with ⟨⟨a,b,c⟩,s⟩
  have distinct : ∀ g : Triangle × Bool, g ∈ orientedFaces →
      g.1.1 ≠ g.1.2.1 ∧ g.1.1 ≠ g.1.2.2 ∧ g.1.2.1 ≠ g.1.2.2 := by decide +kernel
  obtain ⟨hab,hac,hbc⟩ := distinct ((a,b,c),s) hf
  let z (v : Vertex) := chartCorner p v ((a,b,c),s)
  have ha : z a = Type7.complexCorner s (p a) (p b) (p c) := by
    simp [z,chartCorner,cornerFromRays,Type7.complexCorner]
  have hb : z b = Type7.complexCorner s (p b) (p c) (p a) := by
    simp [z,chartCorner,cornerFromRays,Type7.complexCorner,hab.symm]
  have hc : z c = Type7.complexCorner s (p c) (p a) (p b) := by
    simp [z,chartCorner,cornerFromRays,Type7.complexCorner,hac.symm,hbc.symm]
  have he : (z a).arg+(z b).arg+(z c).arg = Real.pi := by
    have h1 : 0 < (z a).im := hs a (by simp [triangleVertices])
    have h2 : 0 < (z b).im := hs b (by simp [triangleVertices])
    have h3 : 0 < (z c).im := hs c (by simp [triangleVertices])
    rw [ha] at h1
    rw [hb] at h2
    rw [hc] at h3
    rw [ha,hb,hc]
    exact Type7.complexCorner_total s _ _ _ h1 h2 h3
  change ∑ v : Vertex, (z v).arg = Real.pi
  let vs : Finset Vertex := {a,b,c}
  rw [← Finset.sum_subset (Finset.subset_univ vs)]
  · have hsum : ∑ v ∈ vs, (z v).arg = (z a).arg+((z b).arg+(z c).arg) := by
      simp [vs,Finset.sum_insert,hab,hac,hbc]
    rw [hsum,← add_assoc]
    exact he
  · intro v _ hv
    have hn : v ≠ a ∧ v ≠ b ∧ v ≠ c := by simpa [vs] using hv
    simp [z,chartCorner,cornerFromRays,hn.1,hn.2.1,hn.2.2]

private theorem integral_cone (p : Vertex → ℂ) (v : Vertex)
    (hs : ∀ f ∈ orientedFaces, v ∈ triangleVertices f.1 → 0 < (chartCorner p v f).im)
    (hprod : 0 < (angleProduct (fun i => p i-p v) v).re ∧
      (angleProduct (fun i => p i-p v) v).im = 0) :
    2*Real.pi ≤ (orientedFaces.map (fun f => (chartCorner p v f).arg)).sum := by
  let cs := orientedFaces.map (chartCorner p v)
  have hother (f : Triangle × Bool) (hi : v ∉ triangleVertices f.1) : chartCorner p v f = 1 := by
    rcases f with ⟨⟨a,b,c⟩,s⟩
    have h : v ≠ a ∧ v ≠ b ∧ v ≠ c := by simpa [triangleVertices] using hi
    simp [chartCorner,cornerFromRays,h.1,h.2.1,h.2.2]
  have hn : ∀ z ∈ cs, z ≠ 0 := by
    intro z hz
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hz
    by_cases hi : v ∈ triangleVertices f.1
    · intro he
      exact (hs f hf hi).ne' (congrArg Complex.im he)
    · simp [hother f hi]
  have harg : cs.prod.arg = 0 := Complex.arg_eq_zero_iff.mpr ⟨hprod.1.le,hprod.2⟩
  have hmod := Type7.complex_arg_list_product cs hn
  rw [harg,Real.Angle.coe_zero] at hmod
  obtain ⟨n,hn⟩ := Real.Angle.coe_eq_zero_iff.mp (show
      ((cs.map Complex.arg).sum : Real.Angle) = 0 by
        rw [Type7.coe_list_sum,List.map_map]
        exact hmod.symm)
  change (2*Real.pi) ≤ (cs.map Complex.arg).sum
  have incident : ∀ i : Vertex, ∃ f ∈ orientedFaces, i ∈ triangleVertices f.1 := by decide +kernel
  obtain ⟨f,hf,hv⟩ := incident v
  have hpos : 0 < (cs.map Complex.arg).sum := by
    let χ (g : Triangle × Bool) := (chartCorner p v g).arg
    have hall (g : Triangle × Bool) (hg : g ∈ orientedFaces) : 0 ≤ χ g := by
      by_cases hi : v ∈ triangleVertices g.1
      · exact (Type7.positiveArg (hs g hg hi)).le
      · simp [χ,hother g hi]
    have sumpositive (l : List (Triangle × Bool)) (hl : ∀ g ∈ l, 0 ≤ χ g) (hm : f ∈ l) :
        0 < (l.map χ).sum := by
      induction l with
      | nil => simp at hm
      | cons h l ih =>
        simp only [List.map_cons,List.sum_cons]
        rcases List.mem_cons.mp hm with rfl | hm
        · apply add_pos_of_pos_of_nonneg (Type7.positiveArg (hs f hf hv))
          apply List.sum_nonneg
          intro x hx
          obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hx
          exact hl g (List.mem_cons_of_mem _ hg)
        · exact add_pos_of_nonneg_of_pos (hl h List.mem_cons_self)
            (ih (fun g hg => hl g (List.mem_cons_of_mem _ hg)) hm)
    exact sumpositive orientedFaces hall hf
  rw [← hn,zsmul_eq_mul] at hpos ⊢
  have hn' : 0 < (n : ℝ) := pos_of_mul_pos_left hpos Real.two_pi_pos.le
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by exact_mod_cast hn')
  nlinarith only [mul_nonneg (sub_nonneg.mpr h1) Real.two_pi_pos.le]

private theorem chart_cones_eq (p : Vertex → ℂ)
    (hs : ∀ f ∈ orientedFaces, ∀ v ∈ triangleVertices f.1, 0 < (chartCorner p v f).im)
    (hprod : ∀ v : Vertex, 0 < (angleProduct (fun i => p i-p v) v).re ∧
      (angleProduct (fun i => p i-p v) v).im = 0) (v : Vertex) :
    (orientedFaces.map (fun f => (chartCorner p v f).arg)).sum = 2*Real.pi := by
  let χ (i : Vertex) (f : Triangle × Bool) := (chartCorner p i f).arg
  let A (i : Vertex) := (orientedFaces.map (χ i)).sum
  have hsum (l : List (Triangle × Bool)) :
      ∑ i : Vertex, (l.map (χ i)).sum = (l.map (fun f => ∑ i : Vertex, χ i f)).sum := by
    induction l with
    | nil => simp
    | cons f l ih => simp [Finset.sum_add_distrib,ih]
  have hfaces : (orientedFaces.map (fun f => ∑ i : Vertex, χ i f)) =
      orientedFaces.map (fun _ => Real.pi) := by
    apply List.map_congr_left
    exact fun f hf => chartCorner_arguments p f hf (hs f hf)
  have htotal : ∑ i : Vertex, A i = 16*Real.pi := by
    change ∑ i : Vertex, (orientedFaces.map (χ i)).sum = _
    rw [hsum,hfaces,List.map_const',show orientedFaces.length = 16 by decide +kernel,
      List.sum_replicate,nsmul_eq_mul]
    norm_num
  have hmin (i : Vertex) : 2*Real.pi ≤ A i :=
    integral_cone p i (fun f hf hv => hs f hf i hv) (hprod i)
  apply le_antisymm _ (hmin v)
  by_contra! h
  have hlt : ∑ _i : Vertex, (2*Real.pi) < ∑ i : Vertex, A i :=
    Finset.sum_lt_sum (fun i _ => hmin i) ⟨v,Finset.mem_univ _,h⟩
  rw [htotal] at hlt
  norm_num [Finset.sum_const,nsmul_eq_mul] at hlt
  linarith

private theorem cross_area (p : Vertex → Plane ℝ) (a b c : Vertex) :
    Type5.cross (p b-p a) (p c-p a) = area p a b c := by
  simp only [area,Type5.cross,Prod.fst_sub,Prod.snd_sub]
  ring

private theorem area_cycle (p : Vertex → Plane ℝ) (a b c : Vertex) :
    area p b c a = area p a b c := by unfold area; ring

private theorem chart_corner_im (w : ℝ) (hw : 0 ≤ w) (p : Vertex → Plane ℝ)
    (f : Triangle × Bool) (v : Vertex) (hv : v ∈ triangleVertices f.1) :
    (chartCorner (physicalComplex w ∘ p) v f).im =
      Real.sqrt w * (if f.2 then area p f.1.1 f.1.2.1 f.1.2.2 else -area p f.1.1 f.1.2.1 f.1.2.2) := by
  rcases f with ⟨⟨a,b,c⟩,s⟩
  have h (u j k : Vertex) := congrArg Complex.im (Type7.physical_complex_corner w hw s (p u) (p j) (p k))
  by_cases ha : v = a
  · subst v
    simpa [chartCorner,cornerFromRays,Type7.complexCorner,physicalComplex,cross_area] using (h a b c).symm
  by_cases hb : v = b
  · subst v
    simpa [chartCorner,cornerFromRays,Type7.complexCorner,physicalComplex,ha,cross_area,
      area_cycle p a b c] using (h b c a).symm
  have hc : v = c := by simpa [triangleVertices,ha,hb] using hv
  subst v
  simpa [chartCorner,cornerFromRays,Type7.complexCorner,physicalComplex,ha,hb,cross_area,
    area_cycle p b c a,area_cycle p a b c] using (h c a b).symm

private theorem neighbors_distinct (p : Vertex → Plane ℝ)
    (hf : ∀ f ∈ Type7.faces, area p f.1 f.2.1 f.2.2 ≠ 0)
    (v i : Vertex) (hi : i ∈ neighborList v) : p i ≠ p v := by
  simp only [neighborList,List.mem_filter,List.mem_eraseDups,List.mem_flatMap,bne_iff_ne] at hi
  obtain ⟨⟨⟨a,b,c⟩,hf',hi⟩,hne⟩ := hi
  obtain ⟨hmem,hv⟩ := hf'
  have harea := hf (a,b,c) hmem
  change area p a b c ≠ 0 at harea
  simp only [List.contains_iff_mem] at hv
  simp only [triangleVertices,List.mem_cons,List.not_mem_nil,or_false] at hi hv
  intro h
  apply harea
  rcases hi with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl <;>
    first | contradiction | (simp only [area,h] <;> ring)

/-- The tagged face orientations of the polynomially scaled trapezoidal charts. -/
theorem poly_chart_face_signs {nearEndpoint : Bool} {x w : ℝ}
    (hd : domain nearEndpoint x w) :
    let H := trapezoidHeight nearEndpoint x
    let c : ℝ := if nearEndpoint then 2/3 else 1/3
    let p := polynomialPoints x w c H 1
    ∀ f ∈ orientedFaces,
      0 < (if f.2 then area p f.1.1 f.1.2.1 f.1.2.2 else -area p f.1.1 f.1.2.1 f.1.2.2) := by
  obtain ⟨hx,_,hw⟩ := domain_bounds hd
  let H := trapezoidHeight nearEndpoint x
  let c : ℝ := if nearEndpoint then 2/3 else 1/3
  let D := H-1+H*x
  let Q := D^2+H^2*w
  have hH : 1 < H := height_gt_one hd
  have hH₀ : 0 < H := by linarith
  have hD : 0 < D := add_pos_of_pos_of_nonneg (sub_pos.mpr hH) (mul_nonneg hH₀.le hx)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hc : 1-c ≠ 0 := by cases nearEndpoint <;> norm_num [c]
  have hp (v : Vertex) :
      polynomialPoints x w c H 1 v =
      (Q*(planarPoint nearEndpoint x w v).1,Q*(planarPoint nearEndpoint x w v).2) := by
    simpa only [div_one,one_mul,planarPoint,trapezoidCut,neg_mul,D,Q] using
      polynomial_rescale x w c H 1 one_ne_zero hH₀.ne' hc hD.ne' hQ.ne' v
  have h (i j k : Vertex) : area (polynomialPoints x w c H 1) i j k =
      Q^2*area (planarPoint nearEndpoint x w) i j k := by
    simp only [area,hp]
    ring
  change ∀ f : Triangle × Bool, f ∈ orientedFaces →
    0 < (if f.2 then area (polynomialPoints x w c H 1) f.1.1 f.1.2.1 f.1.2.2
      else -area (polynomialPoints x w c H 1) f.1.1 f.1.2.1 f.1.2.2)
  rintro ⟨⟨a,b,d⟩,s⟩ hf
  have hor := (planar_faceSigns hd).2 (a,b,d) s hf
  change 0 < (if s then area (polynomialPoints x w c H 1) a b d
    else -area (polynomialPoints x w c H 1) a b d)
  rw [h]
  cases s
  · exact neg_pos.mpr (mul_neg_of_pos_of_neg (sq_pos_of_pos hQ) hor)
  · exact mul_pos (sq_pos_of_pos hQ) hor

private theorem chart_face_nonzero {nearEndpoint : Bool} {x w : ℝ}
    (hd : domain nearEndpoint x w) :
    let p := polynomialPoints x w (if nearEndpoint then 2/3 else 1/3) (trapezoidHeight nearEndpoint x) 1
    ∀ f ∈ Type7.faces, area p f.1 f.2.1 f.2.2 ≠ 0 := by
  have tagged : Type7.faces.all (fun f =>
    orientedFaces.contains (f,false) || orientedFaces.contains (f,true)) = true := by decide +kernel
  dsimp only
  intro f hf
  have h := (List.all_eq_true.mp tagged) f hf
  simp only [Bool.or_eq_true] at h
  rcases h with hf' | hf'
  · exact (neg_pos.mp (poly_chart_face_signs hd (f,false) (List.contains_iff_mem.mp hf'))).ne
  · exact (poly_chart_face_signs hd (f,true) (List.contains_iff_mem.mp hf')).ne'

/-- Before the diagonal flip, the corner angles of each chart sum to a full turn
at every vertex. Coordinates have the common polynomial scale and the physical
vertical scale sqrt(w). -/
theorem trapezoid_cone_angle {nearEndpoint : Bool} {x w : ℝ} (hd : domain nearEndpoint x w)
    (v : Vertex) :
    let p := polynomialPoints x w (if nearEndpoint then 2/3 else 1/3) (trapezoidHeight nearEndpoint x) 1
    let q := physicalComplex w ∘ p
    (orientedFaces.map (fun f => (chartCorner q v f).arg)).sum = 2*Real.pi := by
  let c : ℝ := if nearEndpoint then 2/3 else 1/3
  let H := trapezoidHeight nearEndpoint x
  let p := polynomialPoints x w c H 1
  let q := physicalComplex w ∘ p
  obtain ⟨_,_,hw⟩ := domain_bounds hd
  have hc : 1-c ≠ 0 := by cases nearEndpoint <;> norm_num [c]
  apply chart_cones_eq q
  · intro f hf i hi
    rw [chart_corner_im w hw.le p f i hi]
    exact mul_pos (Real.sqrt_pos.2 hw) (poly_chart_face_signs hd f hf)
  · intro i
    have hn := neighbors_distinct p (chart_face_nonzero hd) i
    have he := trapezoid_corner_product_positive x w c H hw.le hc i hn hw
    simpa only [q,Function.comp_apply,physicalComplex_sub] using he

/-- Euclidean angle at a vertex in one of the planar chart's faces. -/
noncomputable def chartEuclideanCorner (q : Vertex → ℂ) (i : Vertex) (f : Triangle) : ℝ :=
  let (a,b,c) := f
  if i = a then InnerProductGeometry.angle (q b-q a) (q c-q a)
  else if i = b then InnerProductGeometry.angle (q c-q b) (q a-q b)
  else if i = c then InnerProductGeometry.angle (q a-q c) (q b-q c)
  else 0

private theorem chart_corner_euclidean (q : Vertex → ℂ) (v : Vertex) (f : Triangle × Bool)
    (h : v ∈ triangleVertices f.1 → 0 < (chartCorner q v f).im) :
    chartEuclideanCorner q v f.1 = (chartCorner q v f).arg := by
  rcases f with ⟨⟨a,b,c⟩,pos⟩
  by_cases ha : v=a
  · subst v
    have hp : 0 < (Type7.complexCorner pos (q a) (q b) (q c)).im := by
      simpa [chartCorner,cornerFromRays,Type7.complexCorner] using h (by simp [triangleVertices])
    simpa [chartEuclideanCorner,chartCorner,cornerFromRays,Type7.complexCorner] using
      (Type7.complexCorner_arg_angle pos _ _ _ hp).symm
  by_cases hb : v=b
  · subst v
    have hp : 0 < (Type7.complexCorner pos (q b) (q c) (q a)).im := by
      simpa [chartCorner,cornerFromRays,Type7.complexCorner,ha] using h (by simp [triangleVertices])
    simpa [chartEuclideanCorner,chartCorner,cornerFromRays,Type7.complexCorner,ha] using
      (Type7.complexCorner_arg_angle pos _ _ _ hp).symm
  by_cases hc : v=c
  · subst v
    have hp : 0 < (Type7.complexCorner pos (q c) (q a) (q b)).im := by
      simpa [chartCorner,cornerFromRays,Type7.complexCorner,ha,hb] using h (by simp [triangleVertices])
    simpa [chartEuclideanCorner,chartCorner,cornerFromRays,Type7.complexCorner,ha,hb] using
      (Type7.complexCorner_arg_angle pos _ _ _ hp).symm
  · simp [chartEuclideanCorner,chartCorner,cornerFromRays,ha,hb,hc]

/-- The Euclidean angle sums of the two Type 4 charts, in the original labeling before the flip. -/
theorem trapezoid_euclidean_cone_angle {nearEndpoint : Bool} {x w : ℝ}
    (hd : domain nearEndpoint x w) (v : Vertex) :
    let p := polynomialPoints x w (if nearEndpoint then 2/3 else 1/3) (trapezoidHeight nearEndpoint x) 1
    let q := physicalComplex w ∘ p
    (orientedFaces.map (fun f => chartEuclideanCorner q v f.1)).sum = 2*Real.pi := by
  let p := polynomialPoints x w (if nearEndpoint then 2/3 else 1/3) (trapezoidHeight nearEndpoint x) 1
  let q := physicalComplex w ∘ p
  obtain ⟨_,_,hw⟩ := domain_bounds hd
  have he : orientedFaces.map (fun f => chartEuclideanCorner q v f.1) =
      orientedFaces.map (fun f => (chartCorner q v f).arg) := by
    apply List.map_congr_left
    intro f hf
    apply chart_corner_euclidean
    intro hv
    rw [chart_corner_im w hw.le p f v hv]
    exact mul_pos (Real.sqrt_pos.2 hw) (poly_chart_face_signs hd f hf)
  change (orientedFaces.map (fun f => chartEuclideanCorner q v f.1)).sum = 2*Real.pi
  rw [he]
  exact trapezoid_cone_angle hd v

end OrigamiTorus.Type4
