module

public import OrigamiTorus.EightVertex.Type5.Square
import Mathlib.Tactic

/-! Area bounds for each of the three coherent leaf polygons of a sharp Type 5 core.
In the coordinates used here, a vertex represents $4U(p · A, p · B)$, with
$U=1/|B|²$. The squared lengths of A, B and B-A are 1, 1/U and 1/U. -/

public section

namespace OrigamiTorus.Type5.SharpCore

/-- The four free intrinsic vertices, with vertex 1 at the origin. -/
structure Core where
  p2 : Plane ℝ
  p3 : Plane ℝ
  p4 : Plane ℝ
  p5 : Plane ℝ

def point (p : Core) (i : Vertex) : Plane ℝ :=
  ![(0,0), (0,0), p.p2, p.p3, p.p4, p.p5, (0,0), (0,0)] i

def period (u : ℝ) (i j : Vertex) : Plane ℝ :=
  let (m,n) := squareShift i j
  ((4*m+2*n : ℤ)*u, (2*m : ℤ)*u+(4*n : ℤ))

/-- The nine edges on the anchors and roots. -/
def edges : Fin 9 → Vertex × Vertex :=
  ![(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,5),(4,5)]

/-- The two strict Voronoi inequalities for each of A, B and B-A. -/
def margin (u : ℝ) (p : Core) (i : Fin 9) (k : Fin 6) : ℝ :=
  let (v,w) := edges i
  let d := point p w - point p v + period u v w
  ![2*u+d.1, 2*u-d.1, 2+d.2, 2-d.2, 2+(d.2-d.1), 2-(d.2-d.1)] k

def ShortestCore (u : ℝ) (p : Core) : Prop := ∀ i k, 0 < margin u p i k

def anchorArea (p : Core) : ℝ := cross p.p5 p.p2

/-- Signed double area of the polygon of the five coherent neighbor lifts. -/
def starArea (u : ℝ) (p : Core) (j : Vertex) : ℝ :=
  let side (i k : Vertex) := cross (point p i-period u i j) (point p k-period u k j)
  (faces.map fun (a,b,c) =>
    if a = j then side b c else if b = j then side c a else if c = j then side a b else 0).sum

private def target (u : ℝ) (p : Core) : Fin 8 → ℝ :=
  ![anchorArea p, 4*u-anchorArea p, starArea u p 0-4*u, 20*u-starArea u p 0,
    starArea u p 6-4*u, 20*u-starArea u p 6, starArea u p 7-4*u, 20*u-starArea u p 7]

private def factor (u : ℝ) (p : Core) (l r : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 1 else if i = 1 then u else if i = 2 then 1-u else if i = 57 then l
  else if i = 58 then r else margin u p ⟨((i-3)/6)%9, by omega⟩ ⟨(i-3)%6, by omega⟩

private theorem factor_nonneg {u l r : ℝ} {p : Core} (hu : 0 < u) (hu1 : u ≤ 1)
    (hs : ShortestCore u p) (hl : 0 ≤ l) (hr : 0 ≤ r) (i : ℕ) :
    0 ≤ factor u p l r i := by
  unfold factor
  split_ifs
  · exact zero_le_one
  · exact hu.le
  · exact sub_nonneg.mpr hu1
  · exact hl
  · exact hr
  · exact (hs _ _).le

private theorem factor_pos {u l r : ℝ} {p : Core} (hu : 0 < u) (hs : ShortestCore u p)
    {i : ℕ} (hi : i ≠ 2 ∧ i < 57) : 0 < factor u p l r i := by
  unfold factor
  split_ifs <;> first | exact zero_lt_one | exact hu | exact hs _ _ | omega

private abbrev Term := ℕ × ℕ × ℕ

private def term (s : ℕ → ℝ) (t : Term) : ℝ := (t.1 : ℝ)*s t.2.1*s t.2.2

private structure Identity where
  goal : Fin 8
  denominator : ℕ
  first : Term
  rest : List Term

-- The first product is strictly positive throughout its case. The other
-- products use normalized shortest-edge margins and the two case inequalities.
private def identities : Fin 11 → Identity :=
  ![
    ⟨0, 1, (1,10,12), [(1,10,29),(1,12,46),(1,29,46),(1,18,57),(1,54,57)]⟩,
    ⟨0, 1, (1,20,34), [(1,20,52),(1,34,37),(1,37,52),(1,31,57),(1,49,57)]⟩,
    ⟨1, 1, (1,7,34), [(1,7,52),(1,21,31),(1,21,49),(1,39,44)]⟩,
    ⟨2, 1, (1,4,18), [(1,10,23),(1,21,36),(1,29,51),(1,47,57),(2,2,27),(2,29,57)]⟩,
    ⟨2, 2, (1,20,27), [(1,20,39),(1,20,45),(2,5,21),(2,10,23),(2,21,29),(4,1,29),
      (2,44,57),(4,2,39),(4,2,58)]⟩,
    ⟨2, 2, (1,20,40), [(1,29,33),(1,29,34),(2,5,21),(2,15,23),(2,21,29),(2,21,44),
      (2,44,46),(3,20,39),(2,5,58),(2,39,58),(4,2,39)]⟩,
    ⟨3, 28, (2,6,34), [(4,16,56),(4,18,52),(4,21,47),(4,21,51),(4,33,56),(4,34,53),
      (4,39,51),(5,22,49),(8,4,54),(8,16,47),(8,44,52),(12,18,34),
      (12,21,54),(12,51,54),(14,5,15),(14,5,39),(14,10,11),(14,10,41),
      (14,29,46),(16,30,34),(16,39,47),(18,25,46),(20,42,52),(23,21,49),
      (24,12,52),(24,23,46)]⟩,
    ⟨4, 1, (1,3,49), [(1,5,34),(1,7,46),(1,21,54),(1,23,39),(1,34,41),(2,2,46)]⟩,
    ⟨5, 6, (1,10,32), [(2,9,54),(2,10,44),(2,22,54),(2,30,39),(2,39,41),(2,39,46),
      (3,9,31),(4,10,50),(4,39,49),(4,46,54),(6,5,15),(6,9,18),
      (6,21,29),(6,21,44),(6,41,52)]⟩,
    ⟨6, 1, (1,4,54), [(1,5,52),(1,7,10),(1,10,26),(1,21,44),(1,39,49),(2,2,52)]⟩,
    ⟨7, 2, (1,23,34), [(1,24,34),(2,4,20),(2,7,27),(2,7,34),(2,8,46),(2,21,26),
      (2,25,39),(2,28,49),(2,31,45)]⟩]

private def leftFactor (p : Core) : Fin 11 → ℝ :=
  ![p.p2.1, -p.p2.1, 0, p.p4.1, -p.p4.1, -p.p4.1, 0, 0, 0, 0, 0]

private def rightFactor (p : Core) : Fin 11 → ℝ :=
  ![0, 0, 0, 0, p.p3.1+p.p4.1, -(p.p3.1+p.p4.1), 0, 0, 0, 0, 0]

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem polynomial_identity (u : ℝ) (p : Core) (c : Fin 11) :
    let d := identities c
    let s := factor u p (leftFactor p c) (rightFactor p c)
    (d.denominator : ℝ)*target u p d.goal = term s d.first + (d.rest.map (term s)).sum := by
  fin_cases c <;>
    norm_num [identities, target, anchorArea, starArea, faces, point, period, margin, edges,
      cross, squareShift, positiveShift, term, factor, leftFactor, rightFactor,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring

private theorem choice_of_case (p : Core) (t : Fin 8) :
    ∃ c : Fin 11, (identities c).goal = t ∧ 0 ≤ leftFactor p c ∧ 0 ≤ rightFactor p c := by
  fin_cases t
  · by_cases h : 0 ≤ p.p2.1
    · exact ⟨0,rfl,h,le_rfl⟩
    · exact ⟨1,rfl,neg_nonneg.mpr (le_of_not_ge h),le_rfl⟩
  · exact ⟨2,rfl,le_rfl,le_rfl⟩
  · by_cases h : 0 ≤ p.p4.1
    · exact ⟨3,rfl,h,le_rfl⟩
    · have hn := neg_nonneg.mpr (le_of_not_ge h)
      by_cases h' : 0 ≤ p.p3.1+p.p4.1
      · exact ⟨4,rfl,hn,h'⟩
      · exact ⟨5,rfl,hn,neg_nonneg.mpr (le_of_not_ge h')⟩
  · exact ⟨6,rfl,le_rfl,le_rfl⟩
  · exact ⟨7,rfl,le_rfl,le_rfl⟩
  · exact ⟨8,rfl,le_rfl,le_rfl⟩
  · exact ⟨9,rfl,le_rfl,le_rfl⟩
  · exact ⟨10,rfl,le_rfl,le_rfl⟩

private theorem positive_target {u : ℝ} {p : Core} (hu : 0 < u) (hu1 : u ≤ 1)
    (hs : ShortestCore u p) (t : Fin 8) : 0 < target u p t := by
  obtain ⟨c,rfl,hl,hr⟩ := choice_of_case p t
  let d := identities c
  let s := factor u p (leftFactor p c) (rightFactor p c)
  have good : ∀ k, 0 ≤ s k := factor_nonneg hu hu1 hs hl hr
  have hfirst : 0 < d.first.1 ∧ (d.first.2.1 ≠ 2 ∧ d.first.2.1 < 57) ∧
      (d.first.2.2 ≠ 2 ∧ d.first.2.2 < 57) := by
    change 0 < (identities c).first.1 ∧ _; fin_cases c <;> decide
  have hpos : 0 < term s d.first :=
    mul_pos (mul_pos (by exact_mod_cast hfirst.1) (factor_pos hu hs hfirst.2.1))
      (factor_pos hu hs hfirst.2.2)
  have hrest : 0 ≤ (d.rest.map (term s)).sum := by
    apply List.sum_nonneg
    intro r hr
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hr
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (good _)) (good _)
  have hp := add_pos_of_pos_of_nonneg hpos hrest
  rw [← polynomial_identity u p c] at hp
  exact pos_of_mul_pos_right hp (Nat.cast_nonneg _)

/-- All four oriented double areas are positive under the nine strict core
edge comparisons, uniformly up to and including the hexagonal metric. -/
theorem area_bounds {u : ℝ} {p : Core} (hu : 0 < u) (hu1 : u ≤ 1) (hs : ShortestCore u p) :
    0 < anchorArea p ∧ anchorArea p < 4*u ∧
    (∀ j ∈ leaves, 4*u < starArea u p j ∧ starArea u p j < 20*u) := by
  have h := positive_target hu hu1 hs
  refine ⟨h 0, sub_pos.mp (h 1), ?_⟩
  intro j hj
  simp [leaves] at hj
  rcases hj with rfl | rfl | rfl
  · exact ⟨sub_pos.mp (h 2), sub_pos.mp (h 3)⟩
  · exact ⟨sub_pos.mp (h 4), sub_pos.mp (h 5)⟩
  · exact ⟨sub_pos.mp (h 6), sub_pos.mp (h 7)⟩

end OrigamiTorus.Type5.SharpCore
