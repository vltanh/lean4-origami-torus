module

public import OrigamiTorus.AffineDeterminants
public import OrigamiTorus.Defs
public import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

/-! The determinant witness used by the lift certificates excludes a convex edge–face intersection. -/

@[expose] public section

namespace OrigamiTorus

private theorem bracket_functional (a b c d e p q r : Point3) (s t u v w : ℝ)
    (hedge : s+t=1) (hface : u+v+w=1)
    (hxyz : s • a+t • b = u • c+v • d+w • e) :
    s*affineBracket p q r a+t*affineBracket p q r b =
      u*affineBracket p q r c+v*affineBracket p q r d+w*affineBracket p q r e := by
  have hx := congrArg Prod.fst hxyz
  have hy := congrArg (fun x : Point3 => x.2.1) hxyz
  have hz := congrArg (fun x : Point3 => x.2.2) hxyz
  change s*a.1+t*b.1 = u*c.1+v*d.1+w*e.1 at hx
  change s*a.2.1+t*b.2.1 = u*c.2.1+v*d.2.1+w*e.2.1 at hy
  change s*a.2.2+t*b.2.2 = u*c.2.2+v*d.2.2+w*e.2.2 at hz
  simp only [affineBracket, determinant3, Prod.fst_sub, Prod.snd_sub]
  linear_combination
    ((q.2.1-p.2.1)*(r.2.2-p.2.2)-(q.2.2-p.2.2)*(r.2.1-p.2.1)) * (hx - p.1*(hedge-hface)) +
    ((q.2.2-p.2.2)*(r.1-p.1)-(q.1-p.1)*(r.2.2-p.2.2)) * (hy - p.2.1*(hedge-hface)) +
    ((q.1-p.1)*(r.2.1-p.2.1)-(q.2.1-p.2.1)*(r.1-p.1)) * (hz - p.2.2*(hedge-hface))

private theorem bracket_repeat₁ (a b c : Point3) : affineBracket a b c a = 0 := by
  simp [affineBracket,determinant3]

private theorem bracket_repeat₂ (a b c : Point3) : affineBracket a b c b = 0 := by
  simp [affineBracket,determinant3]
  ring

private theorem bracket_repeat₃ (a b c : Point3) : affineBracket a b c c = 0 := by
  simp [affineBracket,determinant3]
  ring

private theorem bracket_cycle (a b c d : Point3) : affineBracket b c d a = -affineBracket a b c d := by
  simp only [affineBracket, determinant3, Prod.fst_sub, Prod.snd_sub]
  ring

private theorem bracket_swap_last (a b c d : Point3) : affineBracket a b d c = -affineBracket a b c d := by
  simp only [affineBracket, determinant3, Prod.fst_sub, Prod.snd_sub]
  ring

/-- In general position, a common point of the closed convex edge and closed convex
triangle forces all four of the complementary-minor sign relations. -/
theorem intersection_forces_signs (a b c d e : Point3)
    (h₀ : affineBracket b c d e ≠ 0) (h₁ : affineBracket a c d e ≠ 0)
    (h₂ : affineBracket a b d e ≠ 0) (h₃ : affineBracket a b c e ≠ 0)
    (h₄ : affineBracket a b c d ≠ 0)
    (s t u v w : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hedge : s+t=1) (hface : u+v+w=1)
    (hxyz : s • a+t • b = u • c+v • d+w • e) :
    let m₀ := affineBracket b c d e
    let m₁ := affineBracket a c d e
    let m₂ := affineBracket a b d e
    let m₃ := affineBracket a b c e
    let m₄ := affineBracket a b c d
    m₀*m₁ < 0 ∧ m₂*m₃ < 0 ∧ m₃*m₄ < 0 ∧ 0 < m₂*m₄ := by
  let m₀ := affineBracket b c d e
  let m₁ := affineBracket a c d e
  let m₂ := affineBracket a b d e
  let m₃ := affineBracket a b c e
  let m₄ := affineBracket a b c d
  change m₀*m₁ < 0 ∧ m₂*m₃ < 0 ∧ m₃*m₄ < 0 ∧ 0 < m₂*m₄
  have hz₀ : m₀ ≠ 0 := h₀
  have hb : t*m₀ = -s*m₁ := by
    have hh := bracket_functional a b c d e c d e s t u v w hedge hface hxyz
    rw [bracket_cycle a c d e, bracket_cycle b c d e] at hh
    simp only [bracket_repeat₁,bracket_repeat₂,bracket_repeat₃,mul_zero,add_zero,mul_neg] at hh
    change -(s*m₁) + -(t*m₀) = 0 at hh
    linarith only [hh]
  have hc : u*m₀ = -s*m₂ := by
    have hh := bracket_functional a b c d e b d e s t u v w hedge hface hxyz
    rw [bracket_cycle a b d e] at hh
    simp only [bracket_repeat₁,bracket_repeat₂,bracket_repeat₃,mul_zero,add_zero] at hh
    have hc' : affineBracket b d e c = m₀ := by
      simp only [m₀, affineBracket,determinant3,Prod.fst_sub,Prod.snd_sub]
      ring
    simpa [m₂, hc', mul_neg, neg_mul] using hh.symm
  have hd : v*m₀ = s*m₃ := by
    have hh := bracket_functional a b c d e b c e s t u v w hedge hface hxyz
    rw [bracket_cycle a b c e, bracket_swap_last b c d e] at hh
    simp only [bracket_repeat₁,bracket_repeat₂,bracket_repeat₃,mul_zero,zero_add,add_zero] at hh
    have hh' : -(s*m₃) = -(v*m₀) := by simpa [m₃,m₀,mul_neg] using hh
    linarith only [hh']
  have he : w*m₀ = -s*m₄ := by
    have hh := bracket_functional a b c d e b c d s t u v w hedge hface hxyz
    rw [bracket_cycle a b c d] at hh
    simpa [m₀,m₄,bracket_repeat₁,bracket_repeat₂,bracket_repeat₃,mul_neg,neg_mul] using hh.symm
  have hs' : 0 < s := by
    by_contra! h
    have hsz : s=0 := le_antisymm h hs
    have ht' : t=1 := by linarith only [hedge,hsz]
    exact hz₀ (by simpa [hsz,ht'] using hb)
  have positive (k m : ℝ) (hk : 0 ≤ k) (hm : m ≠ 0) (h : k*m₀ = s*m) : 0 < k := by
    by_contra! hn
    have hkz : k=0 := le_antisymm hn hk
    exact (mul_ne_zero hs'.ne' hm) (by simpa [hkz] using h.symm)
  have ht' : 0 < t := positive t (-m₁) ht (neg_ne_zero.mpr h₁) (by rw [hb]; ring)
  have hu' : 0 < u := positive u (-m₂) hu (neg_ne_zero.mpr h₂) (by rw [hc]; ring)
  have hv' : 0 < v := positive v m₃ hv h₃ hd
  have hw' : 0 < w := positive w (-m₄) hw (neg_ne_zero.mpr h₄) (by rw [he]; ring)
  have hs2 : 0 < s^2 := sq_pos_of_pos hs'
  have hm2 : 0 < m₀^2 := sq_pos_of_ne_zero hz₀
  refine ⟨?_,?_,?_,?_⟩
  · have hh : -(s*(m₀*m₁)) = t*m₀^2 := by linear_combination -m₀*hb
    have hp : 0 < t*m₀^2 := mul_pos ht' hm2
    rw [← hh, neg_pos] at hp
    exact neg_of_mul_neg_right hp hs
  · have hh : -(s^2*(m₂*m₃)) = u*v*m₀^2 := by
      linear_combination -u*m₀*hd-s*m₃*hc
    have hp : 0 < u*v*m₀^2 := mul_pos (mul_pos hu' hv') hm2
    rw [← hh,neg_pos] at hp
    exact neg_of_mul_neg_right hp hs2.le
  · have hh : -(s^2*(m₃*m₄)) = v*w*m₀^2 := by
      linear_combination -w*m₀*hd-s*m₃*he
    have hp : 0 < v*w*m₀^2 := mul_pos (mul_pos hv' hw') hm2
    rw [← hh,neg_pos] at hp
    exact neg_of_mul_neg_right hp hs2.le
  · have hh : s^2*(m₂*m₄) = u*w*m₀^2 := by
      linear_combination -u*m₀*he+s*m₄*hc
    apply (mul_pos_iff_of_pos_left hs2).mp
    rw [hh]
    exact mul_pos (mul_pos hu' hw') hm2

/-- The determinant computed from planar coordinates and heights is the spatial affine bracket. -/
theorem volume_eq_affineBracket (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (a b c d : Vertex) :
    let q (i : Vertex) : Point3 := ((p i).1,(p i).2,z i)
    volume p z a b c d = affineBracket (q a) (q b) (q c) (q d) := by
  simp only [volume,area,affineBracket,determinant3,Prod.fst_sub,Prod.snd_sub]
  ring

private theorem leftSwap (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (a b c d : Vertex) :
    volume p z b a c d = -volume p z a b c d := by
  simp only [volume,area]
  ring

private theorem middleSwap (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (a b c d : Vertex) :
    volume p z a c b d = -volume p z a b c d := by
  simp only [volume,area]
  ring

private theorem rightSwap (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (a b c d : Vertex) :
    volume p z a b d c = -volume p z a b c d := by
  simp only [volume,area]
  ring

private def compareLeft (q : Tetrahedron) : Tetrahedron :=
  let (a,b,c,d) := q
  if a < b then q else (b,a,c,d)

private def compareMiddle (q : Tetrahedron) : Tetrahedron :=
  let (a,b,c,d) := q
  if b < c then q else (a,c,b,d)

private def compareRight (q : Tetrahedron) : Tetrahedron :=
  let (a,b,c,d) := q
  if c < d then q else (a,b,d,c)

private def tetVolume (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (q : Tetrahedron) : ℝ :=
  volume p z q.1 q.2.1 q.2.2.1 q.2.2.2

private theorem compareLeft_ne (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (q : Tetrahedron) :
    tetVolume p z (compareLeft q) ≠ 0 ↔ tetVolume p z q ≠ 0 := by
  rcases q with ⟨a,b,c,d⟩
  by_cases h : a < b
  · simp [compareLeft,h]
  · simp [compareLeft,h,tetVolume]
    rw [leftSwap p z a b c d, neg_eq_zero]

private theorem compareMiddle_ne (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (q : Tetrahedron) :
    tetVolume p z (compareMiddle q) ≠ 0 ↔ tetVolume p z q ≠ 0 := by
  rcases q with ⟨a,b,c,d⟩
  by_cases h : b < c
  · simp [compareMiddle,h]
  · simp [compareMiddle,h,tetVolume]
    rw [middleSwap p z a b c d, neg_eq_zero]

private theorem compareRight_ne (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (q : Tetrahedron) :
    tetVolume p z (compareRight q) ≠ 0 ↔ tetVolume p z q ≠ 0 := by
  rcases q with ⟨a,b,c,d⟩
  by_cases h : c < d
  · simp [compareRight,h]
  · simp [compareRight,h,tetVolume]
    rw [rightSwap p z a b c d, neg_eq_zero]

private def orderedTet (q : Tetrahedron) : Tetrahedron :=
  compareLeft (compareMiddle (compareLeft (compareRight (compareMiddle (compareLeft q)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem orderedTet_strict (a b c d : Vertex)
    (h : [a,b,c,d].Pairwise (· ≠ ·)) :
    let q := orderedTet (a,b,c,d)
    q.1 < q.2.1 ∧ q.2.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2 := by
  have hh : ∀ i j k l : Vertex, [i,j,k,l].Pairwise (· ≠ ·) →
    let q := orderedTet (i,j,k,l)
    q.1 < q.2.1 ∧ q.2.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2 := by decide +kernel
  exact hh a b c d h

/-- Increasing-index minors suffice to establish general position for arbitrary distinct labels. -/
theorem generic_volume_ne (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ) (h : GenericLift p z)
    (a b c d : Vertex) (hd : [a,b,c,d].Pairwise (· ≠ ·)) : volume p z a b c d ≠ 0 := by
  obtain ⟨h₁,h₂,h₃⟩ := orderedTet_strict a b c d hd
  have ht : tetVolume p z (orderedTet (a,b,c,d)) ≠ 0 := h _ _ _ _ h₁ h₂ h₃
  unfold orderedTet at ht
  rw [compareLeft_ne,compareMiddle_ne,compareLeft_ne,compareRight_ne,compareMiddle_ne,compareLeft_ne] at ht
  exact ht

/-- The strict sign certificate excludes all common points of the closed convex edge and
triangle whenever its five complementary minors are nonzero. -/
theorem separation_excludes_intersection (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ)
    (a b c d e : Vertex)
    (h₀ : volume p z b c d e ≠ 0) (h₁ : volume p z a c d e ≠ 0)
    (h₂ : volume p z a b d e ≠ 0) (h₃ : volume p z a b c e ≠ 0)
    (h₄ : volume p z a b c d ≠ 0) (hsep : isSeparated p z ((a,b),(c,d,e))) :
    let q (i : Vertex) : Point3 := ((p i).1,(p i).2,z i)
    ∀ s t u v w : ℝ, 0 ≤ s → 0 ≤ t → 0 ≤ u → 0 ≤ v → 0 ≤ w →
      s+t=1 → u+v+w=1 → s • q a+t • q b ≠ u • q c+v • q d+w • q e := by
  simp only [isSeparated,separates,volume_eq_affineBracket] at h₀ h₁ h₂ h₃ h₄ hsep
  dsimp only
  intro s t u v w hs ht hu hv hw hed hfa heq
  obtain ⟨h01,h23,h34,h24⟩ := intersection_forces_signs _ _ _ _ _ h₀ h₁ h₂ h₃ h₄
    s t u v w hs ht hu hv hw hed hfa heq
  rcases hsep with h | h | h | h
  · exact (not_lt_of_ge h01.le) h
  · exact (not_lt_of_ge h23.le) h
  · exact (not_lt_of_ge h34.le) h
  · exact (not_lt_of_ge h24.le) h

/-- Genericity and the strict sign certificate suffice whenever the edge and face have
five distinct vertices. -/
theorem generic_separation_excludes_intersection (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ)
    (a b c d e : Vertex) (hg : GenericLift p z)
    (hd : [a,b,c,d,e].Pairwise (· ≠ ·)) (hsep : isSeparated p z ((a,b),(c,d,e))) :
    let q (i : Vertex) : Point3 := ((p i).1,(p i).2,z i)
    ∀ s t u v w : ℝ, 0 ≤ s → 0 ≤ t → 0 ≤ u → 0 ≤ v → 0 ≤ w →
      s+t=1 → u+v+w=1 → s • q a+t • q b ≠ u • q c+v • q d+w • q e := by
  apply separation_excludes_intersection p z a b c d e _ _ _ _ _ hsep
  all_goals
    apply generic_volume_ne p z hg
    simp [List.pairwise_cons] at hd ⊢
    tauto

/-- Barycentric coordinates in a closed triangle. -/
private theorem triangle_weights (a b c x : Point3)
    (h : x ∈ convexHull ℝ (Set.range (![a,b,c] : Fin 3 → Point3))) :
    ∃ u v w : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u+v+w=1 ∧ u • a+v • b+w • c=x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at h
  obtain ⟨s,f,hf,hs,hx⟩ := h
  let weights (i : Fin 3) : ℝ := if i ∈ s then f i else 0
  have hnonneg (i : Fin 3) : 0 ≤ weights i := by
    by_cases hi : i ∈ s <;> simp [weights,hi,hf]
  have hsum : ∑ i, weights i = 1 := by
    rw [← Finset.sum_subset (Finset.subset_univ s) (by intro i _ hi; simp [weights,hi])]
    rw [← hs]
    apply Finset.sum_congr rfl
    intro i hi
    simp [weights,hi]
  have hcombo : ∑ i, weights i • (![a,b,c] : Fin 3 → Point3) i = x := by
    rw [← Finset.sum_subset (Finset.subset_univ s) (by intro i _ hi; simp [weights,hi])]
    rw [Finset.affineCombination_eq_linear_combination s _ _ hs] at hx
    rw [← hx]
    apply Finset.sum_congr rfl
    intro i hi
    simp [weights,hi]
  refine ⟨weights 0,weights 1,weights 2,hnonneg _,hnonneg _,hnonneg _,?_,?_⟩
  · simpa [Fin.sum_univ_succ,add_assoc] using hsum
  · simpa [Fin.sum_univ_succ,add_assoc] using hcombo

/-- The certificate gives disjoint closed convex hulls for the edge and the triangle. -/
theorem separated_segment_disjoint_triangle (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ)
    (a b c d e : Vertex) (hg : GenericLift p z)
    (hd : [a,b,c,d,e].Pairwise (· ≠ ·)) (hsep : isSeparated p z ((a,b),(c,d,e))) :
    let q (i : Vertex) : Point3 := ((p i).1,(p i).2,z i)
    Disjoint (segment ℝ (q a) (q b))
      (convexHull ℝ (Set.range (![q c,q d,q e] : Fin 3 → Point3))) := by
  dsimp only
  rw [Set.disjoint_left]
  intro x hseg htri
  obtain ⟨s,t,hs,ht,hst,he⟩ := hseg
  obtain ⟨u,v,w,hu,hv,hw,huvw,hf⟩ := triangle_weights _ _ _ _ htri
  exact generic_separation_excludes_intersection p z a b c d e hg hd hsep
    s t u v w hs ht hu hv hw hst huvw (he.trans hf.symm)

/-- Apply the convex separation result to the disjoint pairs of the flipped Type 6 face list. -/
theorem type6_disjoint_edge_face (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ)
    (a b c d e : Vertex) (h : ((a,b),(c,d,e)) ∈ type6DisjointPairs)
    (hg : GenericLift p z) (hs : isSeparated p z ((a,b),(c,d,e))) :
    let q (i : Vertex) : Point3 := ((p i).1,(p i).2,z i)
    Disjoint (segment ℝ (q a) (q b))
      (convexHull ℝ (Set.range (![q c,q d,q e] : Fin 3 → Point3))) := by
  have hc : type6DisjointPairs.all (fun ((a,b),c,d,e) =>
      decide ([a,b,c,d,e].Pairwise (· ≠ ·))) = true := by decide +kernel
  exact separated_segment_disjoint_triangle p z a b c d e hg
    (of_decide_eq_true ((List.all_eq_true.mp hc) _ h)) hs

end OrigamiTorus
