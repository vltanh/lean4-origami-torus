module

public import OrigamiTorus.WindingAutomorphisms
import Mathlib.Tactic

/-! Equivalence of finite winding markings under relabeling and lattice
symmetry, including the hexagonal endpoint. -/

@[expose] public section

namespace OrigamiTorus.Winding

def mulPeriodMatrix (M N : PeriodMatrix) : PeriodMatrix :=
  (mapPeriod N M.1,mapPeriod N M.2)

def periodIdentity : PeriodMatrix := ((1,0),(0,1))

def periodNegIdentity : PeriodMatrix := ((-1,0),(0,-1))

def periodReflection : PeriodMatrix := ((-1,0),(-1,1))

def periodOtherReflection : PeriodMatrix := ((1,0),(1,-1))

inductive Region where
  | interior
  | ray
  | hexagonal
  deriving DecidableEq

def Region.sharp : Region → Bool
  | .interior => false
  | _ => true

def Region.metricCondition (r : Region) (x y : ℝ) : Prop :=
  match r with
  | .interior => True
  | .ray => x = 1/2
  | .hexagonal => x = 1/2 ∧ y^2 = 3/4

def hexDot (u v : Period) : ℤ :=
  2*u.1*v.1 + u.1*v.2 + u.2*v.1 + 2*u.2*v.2

def targetSymmetries : Region → Finset PeriodMatrix
  | .interior => {periodIdentity,periodNegIdentity}
  | .ray => {periodIdentity,periodNegIdentity,periodReflection,periodOtherReflection}
  | .hexagonal => ((allowed true).product (allowed true)).filter fun M =>
      (periodDet M).natAbs = 1 ∧ hexDot M.1 M.1 = 2 ∧
        hexDot M.1 M.2 = 1 ∧ hexDot M.2 M.2 = 2

theorem hexagonal_symmetry_count : (targetSymmetries .hexagonal).card = 12 := by
  decide +kernel

def metricSq (x y : ℝ) (u : ℝ × ℝ) : ℝ := (u.1+x*u.2)^2+y^2*u.2^2

def mapPeriodReal (M : PeriodMatrix) (u : ℝ × ℝ) : ℝ × ℝ :=
  (u.1*M.1.1+u.2*M.2.1,u.1*M.1.2+u.2*M.2.2)

private theorem hexagonal_symmetry_metric {M : PeriodMatrix}
    (h₁ : hexDot M.1 M.1 = 2) (h₂ : hexDot M.1 M.2 = 1) (h₃ : hexDot M.2 M.2 = 2)
    {y : ℝ} (hy : y^2 = 3/4) (u : ℝ × ℝ) :
    metricSq (1/2) y (mapPeriodReal M u) = metricSq (1/2) y u := by
  have hc₁ : (hexDot M.1 M.1 : ℝ) = 2 := by exact_mod_cast h₁
  have hc₂ : (hexDot M.1 M.2 : ℝ) = 1 := by exact_mod_cast h₂
  have hc₃ : (hexDot M.2 M.2 : ℝ) = 2 := by exact_mod_cast h₃
  simp only [hexDot,Int.cast_add,Int.cast_mul,Int.cast_ofNat] at hc₁ hc₂ hc₃
  simp only [metricSq,mapPeriodReal,hy]
  linear_combination (norm := ring) u.1^2/2*hc₁+u.1*u.2*hc₂+u.2^2/2*hc₃

/-- Each listed matrix is unimodular and extends to a Euclidean isometry
in lattice coordinates for the indicated region. -/
theorem targetSymmetry_metric {r : Region} {M : PeriodMatrix} (hM : M ∈ targetSymmetries r)
    {x y : ℝ} (hxy : r.metricCondition x y) (u : ℝ × ℝ) :
    (periodDet M).natAbs = 1 ∧ metricSq x y (mapPeriodReal M u) = metricSq x y u := by
  cases r with
  | interior =>
    simp only [targetSymmetries,Finset.mem_insert,Finset.mem_singleton] at hM
    rcases hM with rfl | rfl
    · exact ⟨by decide +kernel,by norm_num [metricSq,mapPeriodReal,periodIdentity]⟩
    · refine ⟨by decide +kernel,?_⟩
      norm_num [metricSq,mapPeriodReal,periodNegIdentity]
      ring
  | ray =>
    change x = 1/2 at hxy
    subst x
    simp only [targetSymmetries,Finset.mem_insert,Finset.mem_singleton] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel,by norm_num [metricSq,mapPeriodReal,periodIdentity]⟩
    · refine ⟨by decide +kernel,?_⟩
      norm_num [metricSq,mapPeriodReal,periodNegIdentity]
      ring
    · refine ⟨by decide +kernel,?_⟩
      norm_num [metricSq,mapPeriodReal,periodReflection]
      ring
    · refine ⟨by decide +kernel,?_⟩
      norm_num [metricSq,mapPeriodReal,periodOtherReflection]
      ring
  | hexagonal =>
    obtain ⟨rfl,hy⟩ := hxy
    obtain ⟨_,hd,h₁,h₂,h₃⟩ := Finset.mem_filter.mp hM
    exact ⟨hd,hexagonal_symmetry_metric h₁ h₂ h₃ hy u⟩

namespace Triangulation

/-- The rows of the marking after relabeling the basis cycles. -/
theorem automorphism_marking {k : Triangulation} {p : Equiv.Perm Vertex}
    (hp : k.IsAutomorphism p) {K : EdgeCochain} (hK : k.IsCocycle K) (ht : k.IsTreeNormalized K) :
    (cyclePeriod K (mapTriangle p k.basisCycles.1),cyclePeriod K (mapTriangle p k.basisCycles.2)) =
      mulPeriodMatrix (k.automorphismAction p) (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2) := by
  have he (f : Triangle) (hf : f ∈ k.threeCycles) :
      ∀ e ∈ faceEdges (mapTriangle p f), e ∈ k.edges := by
    rcases f with ⟨a,b,c⟩
    intro e hm
    simp only [mapTriangle,faceEdges,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact (automorphism_preserves_edge hp a b).mpr (edges_of_threeCycle hf _ (by simp [faceEdges]))
    · exact (automorphism_preserves_edge hp b c).mpr (edges_of_threeCycle hf _ (by simp [faceEdges]))
    · exact (automorphism_preserves_edge hp c a).mpr (edges_of_threeCycle hf _ (by simp [faceEdges]))
  exact Prod.ext (cycle_eq_mapPeriod_of_edges hK ht (he _ k.basis_threeCycles.1))
    (cycle_eq_mapPeriod_of_edges hK ht (he _ k.basis_threeCycles.2))

def orbit (k : Triangulation) (r : Region) (M : PeriodMatrix) : Finset PeriodMatrix :=
  k.actionTable.biUnion fun A => (targetSymmetries r).image fun B =>
    mulPeriodMatrix (mulPeriodMatrix A M) B

/-- Representatives in the original marking basis. The interior column
uses the central inversion, and the sharp ray adds the two reflections. -/
def representatives : Triangulation → Region → List PeriodMatrix
  | .type4, .interior => [((-1,-1),(-1,0)),((-1,-1),(0,-1)),((-1,0),(-1,1)),
      ((-1,0),(0,-1)),((-1,0),(0,1)),((-1,1),(0,1))]
  | .type5, .interior => [((-1,-1),(-1,0)),((-1,0),(-1,1))]
  | .type7, .interior => [((-1,-1),(-1,0)),((-1,-1),(0,-1)),((-1,-1),(0,1)),
      ((-1,-1),(1,0)),((-1,0),(-1,1)),((-1,0),(0,-1)),((-1,0),(0,1)),
      ((-1,0),(1,-1)),((-1,1),(0,-1)),((-1,1),(0,1))]
  | .type4, .ray => [((-1,0),(-1,1)),((-1,1),(0,1))]
  | .type5, .ray => [((-1,0),(-1,1))]
  | .type7, .ray => [((-1,0),(-1,1)),((-1,0),(0,1)),((-1,1),(0,-1)),((-1,1),(0,1))]
  | .type4, .hexagonal | .type5, .hexagonal => [((-1,0),(-1,1))]
  | .type7, .hexagonal => [((-1,0),(-1,1)),((-1,0),(0,1))]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
/-- The representative table partitions the candidate matrices into exactly
the displayed symmetry classes. -/
theorem orbit_partition (k : Triangulation) (r : Region) :
    let reps := k.representatives r
    reps.Pairwise (fun M N => Disjoint (k.orbit r M) (k.orbit r N)) ∧
    reps.toFinset.biUnion (k.orbit r) = k.candidates r.sharp ∧
    ∀ M ∈ reps, M ∈ k.orbit r M := by
  cases k <;> cases r <;> decide +kernel

theorem representative_count (k : Triangulation) (r : Region) :
    (k.representatives r).length =
      match k, r with
      | .type4, .interior => 6
      | .type5, .interior | .type4, .ray | .type7, .hexagonal => 2
      | .type7, .interior => 10
      | .type5, .ray | .type4, .hexagonal | .type5, .hexagonal => 1
      | .type7, .ray => 4 := by
  cases k <;> cases r <;> decide +kernel

/-- Every candidate is a relabeling and lattice isometry of a listed
representative. The relabeling is a permutation of the actual Lutz face list. -/
theorem exists_orbit_representative {k : Triangulation} {r : Region} {M : PeriodMatrix}
    (hM : M ∈ k.candidates r.sharp) :
    ∃ N ∈ k.representatives r, ∃ p : Equiv.Perm Vertex, k.IsAutomorphism p ∧
      ∃ B ∈ targetSymmetries r, M = mulPeriodMatrix (mulPeriodMatrix (k.automorphismAction p) N) B := by
  rw [← (orbit_partition k r).2.1] at hM
  obtain ⟨N,hN,h⟩ := Finset.mem_biUnion.mp hM
  obtain ⟨A,hA,h⟩ := Finset.mem_biUnion.mp h
  obtain ⟨B,hB,hEq⟩ := Finset.mem_image.mp h
  rw [← (automorphism_table k).1] at hA
  obtain ⟨p,hp,rfl⟩ := (mem_automorphismActions k A).mp hA
  exact ⟨N,List.mem_toFinset.mp hN,p,hp,B,hB,hEq.symm⟩

end Triangulation
end OrigamiTorus.Winding
