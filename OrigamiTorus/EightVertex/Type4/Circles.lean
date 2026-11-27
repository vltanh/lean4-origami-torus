module

public import OrigamiTorus.EightVertex.Type4.Strips
import Mathlib.Tactic

/-! Exact concyclicities underlying the Type 4 cone-angle argument. -/

@[expose] public section

namespace OrigamiTorus.Type4

open Type5 (Plane)

/-- The first five vertices lie on a common circle in physical coordinates `(X,sqrt(w)*Y)`. -/
theorem first_circle (x w c H : ℝ) (v : Vertex) (hv : v ∈ ([0,4,5,6,7] : List Vertex)) :
    let a := H*x
    let D := H-1+a
    let Q := D^2+H^2*w
    let M := a^2-a+H^2*w
    let P := polynomialPoints x w c H 1 v
    H*(P.1^2+w*P.2^2-Q*P.1) = Q*M*P.2 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl <;>
    norm_num [polynomialPoints] <;> ring_nf <;> exact Or.inr True.intro

set_option maxRecDepth 20000 in
/-- Four vertices and the mirror of vertex 1 lie on a second circle, in the same scaling. -/
theorem second_circle (x w c H : ℝ) (hc : 1-c ≠ 0) (v : Vertex)
    (hv : v ∈ ([0,4,1,3] : List Vertex)) :
    let p := polynomialPoints x w c H 1
    let a := H*x
    let D := H-1+a
    let Q := D^2+H^2*w
    let p' := (Q-(p 1).1,(p 1).2)
    let M := p'.1^2+w*p'.2^2-Q*p'.1
    let P := p v
    p'.2*(P.1^2+w*P.2^2-Q*P.1) = M*P.2 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;>
    norm_num [polynomialPoints] <;> field_simp [hc] <;> ring_nf <;> exact Or.inr True.intro

def negativeBlocks : Vertex → List Vertex × List Vertex :=
  ![([1,5,2],[3,6,7]),([3,7],[0,4]),([4],[0]),([4,0],[6,1]),
    ([3,2],[1,5]),([7,6],[0,4]),([0,3],[5,7]),([6,0],[5,1])]

def rayProduct (w : ℝ) (p : Vertex → Plane ℝ) (v : Vertex) (ends : List Vertex) : Plane ℝ :=
  ends.foldl (fun acc j => Type7.multiplyComplex w acc (p j-p v)) (1,0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
/-- The exact algebraic identity behind the Type 4 negative-block angle sums.
The two products of edge directions have zero cross product at each vertex. -/
theorem negative_blocks_collinear (x w c H : ℝ) (hc : 1-c ≠ 0) (v : Vertex) :
    let p := polynomialPoints x w c H 1
    let blocks := negativeBlocks v
    Type5.cross (rayProduct w p v blocks.1) (rayProduct w p v blocks.2) = 0 := by
  fin_cases v <;>
    norm_num [negativeBlocks,rayProduct,polynomialPoints,Type7.multiplyComplex,Type5.cross] <;>
    (try field_simp [hc]) <;> ring

end OrigamiTorus.Type4
