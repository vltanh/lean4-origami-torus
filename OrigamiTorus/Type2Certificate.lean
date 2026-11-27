module

public import OrigamiTorus.Defs
import OrigamiTorus.ReverseUnitPropagation

/-!
The Type 2 resolution certificate. Each premise is checked in its original
Plücker, circuit, or mixed-side group. Each subsequent line checks only its
displayed predecessor clauses, avoiding a single large kernel reduction.
-/

namespace OrigamiTorus.Type2

private theorem pluckerAt_mem {s q : List Nat} {c : SignClause}
    (hs : s ∈ choose 2 vertices) (hq : q ∈ choose 4 (vertices.filter fun v => !s.contains v))
    (hc : c ∈ pluckerAt s q) : c ∈ signClauses := by
  simp only [signClauses, List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨s, hs, List.mem_flatMap.mpr ⟨q, hq, hc⟩⟩)))

private theorem circuitAt_mem {q : List Nat} {c : SignClause}
    (hq : q ∈ choose 5 vertices) (hc : c ∈ circuitAt q) : c ∈ signClauses := by
  simp only [signClauses, List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨q, hq, hc⟩))

private theorem mixedAt_mem {v : Nat} {c : SignClause}
    (hv : v ∈ ([0,1,2] : List Nat)) (hc : c ∈ mixedAt v) : c ∈ signClauses := by
  simp only [signClauses, List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨v, hv, hc⟩)

set_option maxRecDepth 10000

variable (a : Nat → Bool)
variable (assignment : ∀ c ∈ signClauses, ∃ l ∈ c, a l.1 = l.2)

include assignment in
private theorem h0 : RUP.trueClause a (([1] : List Int).map RUP.decode) :=
  assignment _ (List.mem_append_left _ (List.mem_cons_self))

include assignment in
private theorem g0 (c) (hc : c ∈ pluckerAt [0, 2] [3, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h1 : RUP.trueClause a (([16, 24, 17, -22, 19, 20] : List Int).map RUP.decode) :=
  g0 a assignment _ (by decide +kernel)

include assignment in
private theorem g1 (c) (hc : c ∈ pluckerAt [0, 2] [4, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h2 : RUP.trueClause a (([20, 25, -21, 24, 22, 23] : List Int).map RUP.decode) :=
  g1 a assignment _ (by decide +kernel)

include assignment in
private theorem g2 (c) (hc : c ∈ pluckerAt [0, 4] [2, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h3 : RUP.trueClause a (([20, 34, 21, -33, -22, -32] : List Int).map RUP.decode) :=
  g2 a assignment _ (by decide +kernel)

include assignment in
private theorem h4 : RUP.trueClause a (([20, 34, -21, 33, -22, -32] : List Int).map RUP.decode) :=
  g2 a assignment _ (by decide +kernel)

include assignment in
private theorem g3 (c) (hc : c ∈ pluckerAt [0, 6] [2, 3, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h5 : RUP.trueClause a (([18, -35, 23, 31, 25, -29] : List Int).map RUP.decode) :=
  g3 a assignment _ (by decide +kernel)

include assignment in
private theorem h6 : RUP.trueClause a (([-18, -35, 23, -31, 25, 29] : List Int).map RUP.decode) :=
  g3 a assignment _ (by decide +kernel)

include assignment in
private theorem g4 (c) (hc : c ∈ pluckerAt [0, 6] [2, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h7 : RUP.trueClause a (([21, -35, -23, -34, 25, -32] : List Int).map RUP.decode) :=
  g4 a assignment _ (by decide +kernel)

include assignment in
private theorem h8 : RUP.trueClause a (([21, 35, -23, 34, -25, -32] : List Int).map RUP.decode) :=
  g4 a assignment _ (by decide +kernel)

include assignment in
private theorem h9 : RUP.trueClause a (([-21, -35, 23, -34, 25, 32] : List Int).map RUP.decode) :=
  g4 a assignment _ (by decide +kernel)

include assignment in
private theorem h10 : RUP.trueClause a (([-21, 35, 23, 34, -25, 32] : List Int).map RUP.decode) :=
  g4 a assignment _ (by decide +kernel)

include assignment in
private theorem g5 (c) (hc : c ∈ pluckerAt [0, 7] [2, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h11 : RUP.trueClause a (([22, 35, -24, 34, -25, -33] : List Int).map RUP.decode) :=
  g5 a assignment _ (by decide +kernel)

include assignment in
private theorem h12 : RUP.trueClause a (([22, -35, -24, -34, 25, -33] : List Int).map RUP.decode) :=
  g5 a assignment _ (by decide +kernel)

include assignment in
private theorem g6 (c) (hc : c ∈ pluckerAt [0, 7] [3, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h13 : RUP.trueClause a (([-28, 35, 30, 34, -31, 33] : List Int).map RUP.decode) :=
  g6 a assignment _ (by decide +kernel)

include assignment in
private theorem g7 (c) (hc : c ∈ pluckerAt [1, 2] [3, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h14 : RUP.trueClause a (([36, 43, 37, -41, -38, -40] : List Int).map RUP.decode) :=
  g7 a assignment _ (by decide +kernel)

include assignment in
private theorem h15 : RUP.trueClause a (([-36, -43, 37, -41, -38, -40] : List Int).map RUP.decode) :=
  g7 a assignment _ (by decide +kernel)

include assignment in
private theorem g8 (c) (hc : c ∈ pluckerAt [1, 2] [3, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h16 : RUP.trueClause a (([36, -44, 37, 42, 39, -40] : List Int).map RUP.decode) :=
  g8 a assignment _ (by decide +kernel)

include assignment in
private theorem h17 : RUP.trueClause a (([-36, 44, -37, -42, -39, 40] : List Int).map RUP.decode) :=
  g8 a assignment _ (by decide +kernel)

include assignment in
private theorem g9 (c) (hc : c ∈ pluckerAt [1, 2] [3, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h18 : RUP.trueClause a (([36, 45, 38, -42, -39, -41] : List Int).map RUP.decode) :=
  g9 a assignment _ (by decide +kernel)

include assignment in
private theorem h19 : RUP.trueClause a (([-36, 45, 38, 42, -39, 41] : List Int).map RUP.decode) :=
  g9 a assignment _ (by decide +kernel)

include assignment in
private theorem g10 (c) (hc : c ∈ pluckerAt [1, 2] [3, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h20 : RUP.trueClause a (([37, -45, -38, -44, 39, -43] : List Int).map RUP.decode) :=
  g10 a assignment _ (by decide +kernel)

include assignment in
private theorem g11 (c) (hc : c ∈ pluckerAt [1, 3] [2, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h21 : RUP.trueClause a (([-36, -49, -37, 47, 38, 46] : List Int).map RUP.decode) :=
  g11 a assignment _ (by decide +kernel)

include assignment in
private theorem g12 (c) (hc : c ∈ pluckerAt [1, 3] [2, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h22 : RUP.trueClause a (([-36, -50, -37, 48, 39, 46] : List Int).map RUP.decode) :=
  g12 a assignment _ (by decide +kernel)

include assignment in
private theorem h23 : RUP.trueClause a (([36, -50, 37, 48, 39, -46] : List Int).map RUP.decode) :=
  g12 a assignment _ (by decide +kernel)

include assignment in
private theorem h24 : RUP.trueClause a (([36, -50, -37, -48, 39, -46] : List Int).map RUP.decode) :=
  g12 a assignment _ (by decide +kernel)

include assignment in
private theorem g13 (c) (hc : c ∈ pluckerAt [1, 3] [2, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h25 : RUP.trueClause a (([-36, -51, -38, 48, -39, -47] : List Int).map RUP.decode) :=
  g13 a assignment _ (by decide +kernel)

include assignment in
private theorem g14 (c) (hc : c ∈ pluckerAt [1, 3] [2, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h26 : RUP.trueClause a (([-37, 51, 38, 50, 39, -49] : List Int).map RUP.decode) :=
  g14 a assignment _ (by decide +kernel)

include assignment in
private theorem h27 : RUP.trueClause a (([37, -51, -38, -50, -39, 49] : List Int).map RUP.decode) :=
  g14 a assignment _ (by decide +kernel)

include assignment in
private theorem g15 (c) (hc : c ∈ pluckerAt [1, 3] [4, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h28 : RUP.trueClause a (([46, 51, -47, 50, -48, -49] : List Int).map RUP.decode) :=
  g15 a assignment _ (by decide +kernel)

include assignment in
private theorem h29 : RUP.trueClause a (([46, 51, 47, -50, -48, -49] : List Int).map RUP.decode) :=
  g15 a assignment _ (by decide +kernel)

include assignment in
private theorem h30 : RUP.trueClause a (([-46, -51, 47, -50, 48, 49] : List Int).map RUP.decode) :=
  g15 a assignment _ (by decide +kernel)

include assignment in
private theorem g16 (c) (hc : c ∈ pluckerAt [1, 4] [2, 3, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h31 : RUP.trueClause a (([36, 53, -40, 48, 42, 46] : List Int).map RUP.decode) :=
  g16 a assignment _ (by decide +kernel)

include assignment in
private theorem h32 : RUP.trueClause a (([-36, 53, -40, -48, -42, 46] : List Int).map RUP.decode) :=
  g16 a assignment _ (by decide +kernel)

include assignment in
private theorem g17 (c) (hc : c ∈ pluckerAt [1, 5] [2, 3, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h33 : RUP.trueClause a (([37, -55, 43, 50, -44, 49] : List Int).map RUP.decode) :=
  g17 a assignment _ (by decide +kernel)

include assignment in
private theorem g18 (c) (hc : c ∈ pluckerAt [1, 5] [2, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h34 : RUP.trueClause a (([40, -55, -43, -53, -44, 52] : List Int).map RUP.decode) :=
  g18 a assignment _ (by decide +kernel)

include assignment in
private theorem h35 : RUP.trueClause a (([-40, -55, -43, 53, -44, -52] : List Int).map RUP.decode) :=
  g18 a assignment _ (by decide +kernel)

include assignment in
private theorem g19 (c) (hc : c ∈ pluckerAt [1, 5] [3, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h36 : RUP.trueClause a (([46, 55, -49, 53, -50, -52] : List Int).map RUP.decode) :=
  g19 a assignment _ (by decide +kernel)

include assignment in
private theorem h37 : RUP.trueClause a (([-46, -55, 49, -53, -50, -52] : List Int).map RUP.decode) :=
  g19 a assignment _ (by decide +kernel)

include assignment in
private theorem g20 (c) (hc : c ∈ pluckerAt [1, 6] [2, 3, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h38 : RUP.trueClause a (([38, -55, 43, 51, 45, -49] : List Int).map RUP.decode) :=
  g20 a assignment _ (by decide +kernel)

include assignment in
private theorem h39 : RUP.trueClause a (([-38, -55, 43, -51, 45, 49] : List Int).map RUP.decode) :=
  g20 a assignment _ (by decide +kernel)

include assignment in
private theorem g21 (c) (hc : c ∈ pluckerAt [1, 6] [2, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h40 : RUP.trueClause a (([41, -55, -43, -54, -45, 52] : List Int).map RUP.decode) :=
  g21 a assignment _ (by decide +kernel)

include assignment in
private theorem g22 (c) (hc : c ∈ pluckerAt [1, 7] [0, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h41 : RUP.trueClause a (([-12, -55, -14, 54, 15, 53] : List Int).map RUP.decode) :=
  g22 a assignment _ (by decide +kernel)

include assignment in
private theorem g23 (c) (hc : c ∈ pluckerAt [1, 7] [2, 3, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h42 : RUP.trueClause a (([-39, 54, 42, 51, -45, 48] : List Int).map RUP.decode) :=
  g23 a assignment _ (by decide +kernel)

include assignment in
private theorem h43 : RUP.trueClause a (([-39, -54, -42, 51, -45, -48] : List Int).map RUP.decode) :=
  g23 a assignment _ (by decide +kernel)

include assignment in
private theorem g24 (c) (hc : c ∈ pluckerAt [1, 7] [2, 3, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h44 : RUP.trueClause a (([39, 55, -44, 51, 45, 50] : List Int).map RUP.decode) :=
  g24 a assignment _ (by decide +kernel)

include assignment in
private theorem h45 : RUP.trueClause a (([-39, -55, 44, -51, -45, -50] : List Int).map RUP.decode) :=
  g24 a assignment _ (by decide +kernel)

include assignment in
private theorem g25 (c) (hc : c ∈ pluckerAt [1, 7] [3, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h46 : RUP.trueClause a (([48, 55, -50, 54, -51, -53] : List Int).map RUP.decode) :=
  g25 a assignment _ (by decide +kernel)

include assignment in
private theorem g26 (c) (hc : c ∈ pluckerAt [2, 3] [0, 1, 4, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h47 : RUP.trueClause a (([-1, 58, 16, 39, -19, 36] : List Int).map RUP.decode) :=
  g26 a assignment _ (by decide +kernel)

include assignment in
private theorem g27 (c) (hc : c ∈ pluckerAt [2, 3] [0, 1, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h48 : RUP.trueClause a (([-1, -61, -18, 39, -19, -38] : List Int).map RUP.decode) :=
  g27 a assignment _ (by decide +kernel)

include assignment in
private theorem h49 : RUP.trueClause a (([-1, -61, 18, -39, -19, -38] : List Int).map RUP.decode) :=
  g27 a assignment _ (by decide +kernel)

include assignment in
private theorem g28 (c) (hc : c ∈ pluckerAt [2, 3] [0, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h50 : RUP.trueClause a (([-16, 59, 17, 57, 18, -56] : List Int).map RUP.decode) :=
  g28 a assignment _ (by decide +kernel)

include assignment in
private theorem g29 (c) (hc : c ∈ pluckerAt [2, 3] [0, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h51 : RUP.trueClause a (([-17, -61, 18, -60, 19, 59] : List Int).map RUP.decode) :=
  g29 a assignment _ (by decide +kernel)

include assignment in
private theorem g30 (c) (hc : c ∈ pluckerAt [2, 3] [1, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h52 : RUP.trueClause a (([36, 59, -37, 57, 38, 56] : List Int).map RUP.decode) :=
  g30 a assignment _ (by decide +kernel)

include assignment in
private theorem h53 : RUP.trueClause a (([36, 59, 37, -57, -38, -56] : List Int).map RUP.decode) :=
  g30 a assignment _ (by decide +kernel)

include assignment in
private theorem h54 : RUP.trueClause a (([36, -59, -37, -57, 38, -56] : List Int).map RUP.decode) :=
  g30 a assignment _ (by decide +kernel)

include assignment in
private theorem h55 : RUP.trueClause a (([-36, -59, 37, -57, -38, -56] : List Int).map RUP.decode) :=
  g30 a assignment _ (by decide +kernel)

include assignment in
private theorem g31 (c) (hc : c ∈ pluckerAt [2, 3] [1, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h56 : RUP.trueClause a (([36, -60, -37, -58, 39, -56] : List Int).map RUP.decode) :=
  g31 a assignment _ (by decide +kernel)

include assignment in
private theorem h57 : RUP.trueClause a (([36, -60, 37, 58, 39, -56] : List Int).map RUP.decode) :=
  g31 a assignment _ (by decide +kernel)

include assignment in
private theorem g32 (c) (hc : c ∈ pluckerAt [2, 3] [1, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h58 : RUP.trueClause a (([36, -61, 38, 58, 39, -57] : List Int).map RUP.decode) :=
  g32 a assignment _ (by decide +kernel)

include assignment in
private theorem h59 : RUP.trueClause a (([36, -61, 38, 58, -39, 57] : List Int).map RUP.decode) :=
  g32 a assignment _ (by decide +kernel)

include assignment in
private theorem h60 : RUP.trueClause a (([-36, -61, -38, 58, -39, -57] : List Int).map RUP.decode) :=
  g32 a assignment _ (by decide +kernel)

include assignment in
private theorem g33 (c) (hc : c ∈ pluckerAt [2, 3] [1, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h61 : RUP.trueClause a (([37, 61, -38, 60, -39, -59] : List Int).map RUP.decode) :=
  g33 a assignment _ (by decide +kernel)

include assignment in
private theorem h62 : RUP.trueClause a (([37, -61, -38, -60, 39, -59] : List Int).map RUP.decode) :=
  g33 a assignment _ (by decide +kernel)

include assignment in
private theorem h63 : RUP.trueClause a (([37, -61, -38, -60, -39, 59] : List Int).map RUP.decode) :=
  g33 a assignment _ (by decide +kernel)

include assignment in
private theorem h64 : RUP.trueClause a (([-37, 61, 38, 60, 39, -59] : List Int).map RUP.decode) :=
  g33 a assignment _ (by decide +kernel)

include assignment in
private theorem h65 : RUP.trueClause a (([-37, -61, 38, -60, -39, -59] : List Int).map RUP.decode) :=
  g33 a assignment _ (by decide +kernel)

include assignment in
private theorem g34 (c) (hc : c ∈ pluckerAt [2, 3] [4, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h66 : RUP.trueClause a (([56, 61, -57, 60, 58, 59] : List Int).map RUP.decode) :=
  g34 a assignment _ (by decide +kernel)

include assignment in
private theorem h67 : RUP.trueClause a (([56, 61, -57, 60, -58, -59] : List Int).map RUP.decode) :=
  g34 a assignment _ (by decide +kernel)

include assignment in
private theorem h68 : RUP.trueClause a (([-56, 61, 57, 60, -58, 59] : List Int).map RUP.decode) :=
  g34 a assignment _ (by decide +kernel)

include assignment in
private theorem h69 : RUP.trueClause a (([-56, -61, 57, -60, 58, 59] : List Int).map RUP.decode) :=
  g34 a assignment _ (by decide +kernel)

include assignment in
private theorem g35 (c) (hc : c ∈ pluckerAt [2, 4] [0, 3, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h70 : RUP.trueClause a (([16, 64, 21, -58, -22, -57] : List Int).map RUP.decode) :=
  g35 a assignment _ (by decide +kernel)

include assignment in
private theorem g36 (c) (hc : c ∈ pluckerAt [2, 4] [0, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h71 : RUP.trueClause a (([20, -64, -21, -63, 22, -62] : List Int).map RUP.decode) :=
  g36 a assignment _ (by decide +kernel)

include assignment in
private theorem h72 : RUP.trueClause a (([-20, 64, 21, 63, -22, 62] : List Int).map RUP.decode) :=
  g36 a assignment _ (by decide +kernel)

include assignment in
private theorem h73 : RUP.trueClause a (([-20, -64, -21, 63, 22, 62] : List Int).map RUP.decode) :=
  g36 a assignment _ (by decide +kernel)

include assignment in
private theorem g37 (c) (hc : c ∈ pluckerAt [2, 4] [1, 3, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h74 : RUP.trueClause a (([-36, -62, 40, -57, -41, -56] : List Int).map RUP.decode) :=
  g37 a assignment _ (by decide +kernel)

include assignment in
private theorem g38 (c) (hc : c ∈ pluckerAt [2, 4] [1, 3, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h75 : RUP.trueClause a (([-36, 63, -40, -58, -42, 56] : List Int).map RUP.decode) :=
  g38 a assignment _ (by decide +kernel)

include assignment in
private theorem h76 : RUP.trueClause a (([-36, -63, -40, 58, -42, -56] : List Int).map RUP.decode) :=
  g38 a assignment _ (by decide +kernel)

include assignment in
private theorem h77 : RUP.trueClause a (([36, -63, 40, 58, 42, -56] : List Int).map RUP.decode) :=
  g38 a assignment _ (by decide +kernel)

include assignment in
private theorem g39 (c) (hc : c ∈ pluckerAt [2, 4] [1, 3, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h78 : RUP.trueClause a (([-36, 64, -41, -58, -42, 57] : List Int).map RUP.decode) :=
  g39 a assignment _ (by decide +kernel)

include assignment in
private theorem h79 : RUP.trueClause a (([-36, 64, 41, 58, 42, -57] : List Int).map RUP.decode) :=
  g39 a assignment _ (by decide +kernel)

include assignment in
private theorem h80 : RUP.trueClause a (([36, 64, -41, 58, -42, -57] : List Int).map RUP.decode) :=
  g39 a assignment _ (by decide +kernel)

include assignment in
private theorem h81 : RUP.trueClause a (([36, -64, -41, -58, 42, -57] : List Int).map RUP.decode) :=
  g39 a assignment _ (by decide +kernel)

include assignment in
private theorem h82 : RUP.trueClause a (([36, -64, 41, 58, 42, -57] : List Int).map RUP.decode) :=
  g39 a assignment _ (by decide +kernel)

include assignment in
private theorem g40 (c) (hc : c ∈ pluckerAt [2, 4] [1, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h83 : RUP.trueClause a (([40, -64, -41, -63, 42, -62] : List Int).map RUP.decode) :=
  g40 a assignment _ (by decide +kernel)

include assignment in
private theorem g41 (c) (hc : c ∈ pluckerAt [2, 4] [3, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h84 : RUP.trueClause a (([-56, -64, 57, -63, -58, -62] : List Int).map RUP.decode) :=
  g41 a assignment _ (by decide +kernel)

include assignment in
private theorem h85 : RUP.trueClause a (([56, 64, -57, 63, 58, 62] : List Int).map RUP.decode) :=
  g41 a assignment _ (by decide +kernel)

include assignment in
private theorem h86 : RUP.trueClause a (([56, -64, -57, -63, 58, -62] : List Int).map RUP.decode) :=
  g41 a assignment _ (by decide +kernel)

include assignment in
private theorem g42 (c) (hc : c ∈ pluckerAt [2, 5] [0, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h87 : RUP.trueClause a (([-20, 65, 23, 63, -24, 62] : List Int).map RUP.decode) :=
  g42 a assignment _ (by decide +kernel)

include assignment in
private theorem h88 : RUP.trueClause a (([-20, -65, -23, 63, 24, 62] : List Int).map RUP.decode) :=
  g42 a assignment _ (by decide +kernel)

include assignment in
private theorem h89 : RUP.trueClause a (([-20, -65, -23, 63, -24, -62] : List Int).map RUP.decode) :=
  g42 a assignment _ (by decide +kernel)

include assignment in
private theorem h90 : RUP.trueClause a (([20, 65, 23, -63, 24, 62] : List Int).map RUP.decode) :=
  g42 a assignment _ (by decide +kernel)

include assignment in
private theorem h91 : RUP.trueClause a (([20, 65, 23, -63, -24, -62] : List Int).map RUP.decode) :=
  g42 a assignment _ (by decide +kernel)

include assignment in
private theorem h92 : RUP.trueClause a (([20, -65, -23, -63, 24, -62] : List Int).map RUP.decode) :=
  g42 a assignment _ (by decide +kernel)

include assignment in
private theorem h93 : RUP.trueClause a (([20, -65, 23, 63, 24, -62] : List Int).map RUP.decode) :=
  g42 a assignment _ (by decide +kernel)

include assignment in
private theorem g43 (c) (hc : c ∈ pluckerAt [2, 5] [1, 3, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h94 : RUP.trueClause a (([-37, 62, 40, 59, -43, 56] : List Int).map RUP.decode) :=
  g43 a assignment _ (by decide +kernel)

include assignment in
private theorem h95 : RUP.trueClause a (([37, -62, 40, 59, 43, -56] : List Int).map RUP.decode) :=
  g43 a assignment _ (by decide +kernel)

include assignment in
private theorem h96 : RUP.trueClause a (([37, -62, -40, -59, 43, -56] : List Int).map RUP.decode) :=
  g43 a assignment _ (by decide +kernel)

include assignment in
private theorem g44 (c) (hc : c ∈ pluckerAt [2, 5] [1, 3, 4, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h97 : RUP.trueClause a (([-37, 63, -40, -60, -44, 56] : List Int).map RUP.decode) :=
  g44 a assignment _ (by decide +kernel)

include assignment in
private theorem h98 : RUP.trueClause a (([37, -63, -40, -60, 44, -56] : List Int).map RUP.decode) :=
  g44 a assignment _ (by decide +kernel)

include assignment in
private theorem g45 (c) (hc : c ∈ pluckerAt [2, 5] [1, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h99 : RUP.trueClause a (([-40, -65, 43, -63, -44, -62] : List Int).map RUP.decode) :=
  g45 a assignment _ (by decide +kernel)

include assignment in
private theorem g46 (c) (hc : c ∈ pluckerAt [2, 5] [3, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h100 : RUP.trueClause a (([56, 65, 59, -63, 60, 62] : List Int).map RUP.decode) :=
  g46 a assignment _ (by decide +kernel)

include assignment in
private theorem h101 : RUP.trueClause a (([56, 65, -59, 63, 60, 62] : List Int).map RUP.decode) :=
  g46 a assignment _ (by decide +kernel)

include assignment in
private theorem h102 : RUP.trueClause a (([56, -65, 59, 63, -60, 62] : List Int).map RUP.decode) :=
  g46 a assignment _ (by decide +kernel)

include assignment in
private theorem h103 : RUP.trueClause a (([56, -65, -59, -63, 60, -62] : List Int).map RUP.decode) :=
  g46 a assignment _ (by decide +kernel)

include assignment in
private theorem h104 : RUP.trueClause a (([-56, 65, 59, 63, -60, 62] : List Int).map RUP.decode) :=
  g46 a assignment _ (by decide +kernel)

include assignment in
private theorem h105 : RUP.trueClause a (([-56, 65, -59, -63, 60, -62] : List Int).map RUP.decode) :=
  g46 a assignment _ (by decide +kernel)

include assignment in
private theorem h106 : RUP.trueClause a (([-56, -65, 59, -63, -60, -62] : List Int).map RUP.decode) :=
  g46 a assignment _ (by decide +kernel)

include assignment in
private theorem g47 (c) (hc : c ∈ pluckerAt [2, 6] [0, 3, 4, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h107 : RUP.trueClause a (([18, -64, -21, -61, -25, 57] : List Int).map RUP.decode) :=
  g47 a assignment _ (by decide +kernel)

include assignment in
private theorem g48 (c) (hc : c ∈ pluckerAt [2, 6] [0, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h108 : RUP.trueClause a (([21, -65, 23, 64, 25, -62] : List Int).map RUP.decode) :=
  g48 a assignment _ (by decide +kernel)

include assignment in
private theorem g49 (c) (hc : c ∈ pluckerAt [2, 6] [1, 3, 4, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h109 : RUP.trueClause a (([-38, -62, -41, 59, -43, -57] : List Int).map RUP.decode) :=
  g49 a assignment _ (by decide +kernel)

include assignment in
private theorem h110 : RUP.trueClause a (([38, -62, -41, -59, 43, -57] : List Int).map RUP.decode) :=
  g49 a assignment _ (by decide +kernel)

include assignment in
private theorem g50 (c) (hc : c ∈ pluckerAt [2, 6] [1, 3, 4, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h111 : RUP.trueClause a (([-38, -64, 41, -61, -45, -57] : List Int).map RUP.decode) :=
  g50 a assignment _ (by decide +kernel)

include assignment in
private theorem h112 : RUP.trueClause a (([38, -64, -41, -61, 45, -57] : List Int).map RUP.decode) :=
  g50 a assignment _ (by decide +kernel)

include assignment in
private theorem g51 (c) (hc : c ∈ pluckerAt [2, 6] [1, 3, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h113 : RUP.trueClause a (([-38, -65, 43, -61, -45, -59] : List Int).map RUP.decode) :=
  g51 a assignment _ (by decide +kernel)

include assignment in
private theorem h114 : RUP.trueClause a (([-38, 65, 43, 61, 45, -59] : List Int).map RUP.decode) :=
  g51 a assignment _ (by decide +kernel)

include assignment in
private theorem h115 : RUP.trueClause a (([-38, 65, -43, -61, -45, 59] : List Int).map RUP.decode) :=
  g51 a assignment _ (by decide +kernel)

include assignment in
private theorem h116 : RUP.trueClause a (([38, -65, -43, -61, 45, -59] : List Int).map RUP.decode) :=
  g51 a assignment _ (by decide +kernel)

include assignment in
private theorem h117 : RUP.trueClause a (([38, -65, -43, -61, -45, 59] : List Int).map RUP.decode) :=
  g51 a assignment _ (by decide +kernel)

include assignment in
private theorem h118 : RUP.trueClause a (([38, 65, -43, 61, 45, 59] : List Int).map RUP.decode) :=
  g51 a assignment _ (by decide +kernel)

include assignment in
private theorem h119 : RUP.trueClause a (([38, 65, -43, 61, -45, -59] : List Int).map RUP.decode) :=
  g51 a assignment _ (by decide +kernel)

include assignment in
private theorem g52 (c) (hc : c ∈ pluckerAt [2, 6] [1, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h120 : RUP.trueClause a (([-41, -65, 43, -64, -45, -62] : List Int).map RUP.decode) :=
  g52 a assignment _ (by decide +kernel)

include assignment in
private theorem h121 : RUP.trueClause a (([41, -65, -43, -64, -45, 62] : List Int).map RUP.decode) :=
  g52 a assignment _ (by decide +kernel)

include assignment in
private theorem g53 (c) (hc : c ∈ pluckerAt [2, 6] [3, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h122 : RUP.trueClause a (([57, -65, -59, -64, -61, 62] : List Int).map RUP.decode) :=
  g53 a assignment _ (by decide +kernel)

include assignment in
private theorem h123 : RUP.trueClause a (([57, -65, -59, -64, 61, -62] : List Int).map RUP.decode) :=
  g53 a assignment _ (by decide +kernel)

include assignment in
private theorem h124 : RUP.trueClause a (([57, 65, -59, 64, 61, 62] : List Int).map RUP.decode) :=
  g53 a assignment _ (by decide +kernel)

include assignment in
private theorem h125 : RUP.trueClause a (([57, 65, 59, -64, 61, 62] : List Int).map RUP.decode) :=
  g53 a assignment _ (by decide +kernel)

include assignment in
private theorem h126 : RUP.trueClause a (([-57, -65, 59, -64, -61, -62] : List Int).map RUP.decode) :=
  g53 a assignment _ (by decide +kernel)

include assignment in
private theorem h127 : RUP.trueClause a (([-57, 65, 59, 64, -61, 62] : List Int).map RUP.decode) :=
  g53 a assignment _ (by decide +kernel)

include assignment in
private theorem h128 : RUP.trueClause a (([-57, 65, 59, 64, 61, -62] : List Int).map RUP.decode) :=
  g53 a assignment _ (by decide +kernel)

include assignment in
private theorem g54 (c) (hc : c ∈ pluckerAt [2, 7] [0, 3, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h129 : RUP.trueClause a (([-19, 64, -22, -61, 25, -58] : List Int).map RUP.decode) :=
  g54 a assignment _ (by decide +kernel)

include assignment in
private theorem g55 (c) (hc : c ∈ pluckerAt [2, 7] [0, 3, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h130 : RUP.trueClause a (([-19, -65, 24, -61, -25, -60] : List Int).map RUP.decode) :=
  g55 a assignment _ (by decide +kernel)

include assignment in
private theorem h131 : RUP.trueClause a (([19, -65, -24, -61, 25, -60] : List Int).map RUP.decode) :=
  g55 a assignment _ (by decide +kernel)

include assignment in
private theorem g56 (c) (hc : c ∈ pluckerAt [2, 7] [1, 3, 4, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h132 : RUP.trueClause a (([39, -63, 42, 60, 44, -58] : List Int).map RUP.decode) :=
  g56 a assignment _ (by decide +kernel)

include assignment in
private theorem g57 (c) (hc : c ∈ pluckerAt [2, 7] [1, 3, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h133 : RUP.trueClause a (([-39, -64, 42, -61, -45, -58] : List Int).map RUP.decode) :=
  g57 a assignment _ (by decide +kernel)

include assignment in
private theorem h134 : RUP.trueClause a (([-39, -64, 42, -61, 45, 58] : List Int).map RUP.decode) :=
  g57 a assignment _ (by decide +kernel)

include assignment in
private theorem h135 : RUP.trueClause a (([-39, -64, -42, 61, 45, 58] : List Int).map RUP.decode) :=
  g57 a assignment _ (by decide +kernel)

include assignment in
private theorem h136 : RUP.trueClause a (([39, -64, 42, 61, -45, 58] : List Int).map RUP.decode) :=
  g57 a assignment _ (by decide +kernel)

include assignment in
private theorem h137 : RUP.trueClause a (([39, -64, -42, -61, -45, 58] : List Int).map RUP.decode) :=
  g57 a assignment _ (by decide +kernel)

include assignment in
private theorem g58 (c) (hc : c ∈ pluckerAt [2, 7] [1, 3, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h138 : RUP.trueClause a (([39, -65, -44, -61, 45, -60] : List Int).map RUP.decode) :=
  g58 a assignment _ (by decide +kernel)

include assignment in
private theorem g59 (c) (hc : c ∈ pluckerAt [2, 7] [3, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h139 : RUP.trueClause a (([58, 65, -60, 64, 61, 63] : List Int).map RUP.decode) :=
  g59 a assignment _ (by decide +kernel)

include assignment in
private theorem h140 : RUP.trueClause a (([-58, 65, 60, 64, 61, -63] : List Int).map RUP.decode) :=
  g59 a assignment _ (by decide +kernel)

include assignment in
private theorem h141 : RUP.trueClause a (([-58, 65, 60, 64, -61, 63] : List Int).map RUP.decode) :=
  g59 a assignment _ (by decide +kernel)

include assignment in
private theorem h142 : RUP.trueClause a (([-58, -65, 60, -64, -61, -63] : List Int).map RUP.decode) :=
  g59 a assignment _ (by decide +kernel)

include assignment in
private theorem g60 (c) (hc : c ∈ pluckerAt [3, 4] [1, 2, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h143 : RUP.trueClause a (([36, 66, -46, 57, 47, 56] : List Int).map RUP.decode) :=
  g60 a assignment _ (by decide +kernel)

include assignment in
private theorem h144 : RUP.trueClause a (([36, -66, -46, -57, -47, 56] : List Int).map RUP.decode) :=
  g60 a assignment _ (by decide +kernel)

include assignment in
private theorem h145 : RUP.trueClause a (([-36, 66, -46, -57, 47, -56] : List Int).map RUP.decode) :=
  g60 a assignment _ (by decide +kernel)

include assignment in
private theorem h146 : RUP.trueClause a (([-36, -66, -46, 57, 47, 56] : List Int).map RUP.decode) :=
  g60 a assignment _ (by decide +kernel)

include assignment in
private theorem g61 (c) (hc : c ∈ pluckerAt [3, 4] [1, 2, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h147 : RUP.trueClause a (([36, 67, -46, 58, -48, -56] : List Int).map RUP.decode) :=
  g61 a assignment _ (by decide +kernel)

include assignment in
private theorem h148 : RUP.trueClause a (([-36, -67, 46, -58, 48, 56] : List Int).map RUP.decode) :=
  g61 a assignment _ (by decide +kernel)

include assignment in
private theorem g62 (c) (hc : c ∈ pluckerAt [3, 4] [1, 2, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h149 : RUP.trueClause a (([36, 68, 47, -58, -48, -57] : List Int).map RUP.decode) :=
  g62 a assignment _ (by decide +kernel)

include assignment in
private theorem h150 : RUP.trueClause a (([36, -68, -47, -58, -48, 57] : List Int).map RUP.decode) :=
  g62 a assignment _ (by decide +kernel)

include assignment in
private theorem g63 (c) (hc : c ∈ pluckerAt [3, 4] [1, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h151 : RUP.trueClause a (([46, 68, -47, 67, -48, -66] : List Int).map RUP.decode) :=
  g63 a assignment _ (by decide +kernel)

include assignment in
private theorem h152 : RUP.trueClause a (([46, -68, -47, -67, 48, -66] : List Int).map RUP.decode) :=
  g63 a assignment _ (by decide +kernel)

include assignment in
private theorem h153 : RUP.trueClause a (([46, -68, -47, -67, -48, 66] : List Int).map RUP.decode) :=
  g63 a assignment _ (by decide +kernel)

include assignment in
private theorem h154 : RUP.trueClause a (([46, -68, 47, 67, -48, 66] : List Int).map RUP.decode) :=
  g63 a assignment _ (by decide +kernel)

include assignment in
private theorem h155 : RUP.trueClause a (([-46, 68, -47, -67, 48, -66] : List Int).map RUP.decode) :=
  g63 a assignment _ (by decide +kernel)

include assignment in
private theorem h156 : RUP.trueClause a (([-46, -68, 47, -67, 48, 66] : List Int).map RUP.decode) :=
  g63 a assignment _ (by decide +kernel)

include assignment in
private theorem h157 : RUP.trueClause a (([-46, -68, 47, -67, -48, -66] : List Int).map RUP.decode) :=
  g63 a assignment _ (by decide +kernel)

include assignment in
private theorem g64 (c) (hc : c ∈ pluckerAt [3, 4] [2, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h158 : RUP.trueClause a (([-56, -68, 57, -67, 58, 66] : List Int).map RUP.decode) :=
  g64 a assignment _ (by decide +kernel)

include assignment in
private theorem g65 (c) (hc : c ∈ pluckerAt [3, 5] [1, 2, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h159 : RUP.trueClause a (([37, -66, 46, 59, 49, -56] : List Int).map RUP.decode) :=
  g65 a assignment _ (by decide +kernel)

include assignment in
private theorem h160 : RUP.trueClause a (([37, -66, -46, -59, 49, -56] : List Int).map RUP.decode) :=
  g65 a assignment _ (by decide +kernel)

include assignment in
private theorem h161 : RUP.trueClause a (([37, 66, 46, -59, -49, -56] : List Int).map RUP.decode) :=
  g65 a assignment _ (by decide +kernel)

include assignment in
private theorem h162 : RUP.trueClause a (([-37, -66, 46, -59, 49, 56] : List Int).map RUP.decode) :=
  g65 a assignment _ (by decide +kernel)

include assignment in
private theorem h163 : RUP.trueClause a (([-37, -66, 46, -59, -49, -56] : List Int).map RUP.decode) :=
  g65 a assignment _ (by decide +kernel)

include assignment in
private theorem h164 : RUP.trueClause a (([-37, -66, -46, 59, 49, 56] : List Int).map RUP.decode) :=
  g65 a assignment _ (by decide +kernel)

include assignment in
private theorem h165 : RUP.trueClause a (([-37, 66, 46, 59, 49, -56] : List Int).map RUP.decode) :=
  g65 a assignment _ (by decide +kernel)

include assignment in
private theorem h166 : RUP.trueClause a (([-37, 66, 46, 59, -49, 56] : List Int).map RUP.decode) :=
  g65 a assignment _ (by decide +kernel)

include assignment in
private theorem h167 : RUP.trueClause a (([-37, 66, -46, -59, -49, 56] : List Int).map RUP.decode) :=
  g65 a assignment _ (by decide +kernel)

include assignment in
private theorem g66 (c) (hc : c ∈ pluckerAt [3, 5] [1, 2, 4, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h168 : RUP.trueClause a (([37, -67, -46, -60, 50, -56] : List Int).map RUP.decode) :=
  g66 a assignment _ (by decide +kernel)

include assignment in
private theorem h169 : RUP.trueClause a (([37, 67, 46, -60, -50, -56] : List Int).map RUP.decode) :=
  g66 a assignment _ (by decide +kernel)

include assignment in
private theorem h170 : RUP.trueClause a (([-37, -67, 46, -60, 50, 56] : List Int).map RUP.decode) :=
  g66 a assignment _ (by decide +kernel)

include assignment in
private theorem h171 : RUP.trueClause a (([-37, 67, -46, -60, 50, -56] : List Int).map RUP.decode) :=
  g66 a assignment _ (by decide +kernel)

include assignment in
private theorem g67 (c) (hc : c ∈ pluckerAt [3, 5] [1, 2, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h172 : RUP.trueClause a (([37, -69, -49, -60, -50, 59] : List Int).map RUP.decode) :=
  g67 a assignment _ (by decide +kernel)

include assignment in
private theorem h173 : RUP.trueClause a (([37, -69, 49, 60, -50, 59] : List Int).map RUP.decode) :=
  g67 a assignment _ (by decide +kernel)

include assignment in
private theorem h174 : RUP.trueClause a (([-37, 69, 49, 60, 50, -59] : List Int).map RUP.decode) :=
  g67 a assignment _ (by decide +kernel)

include assignment in
private theorem h175 : RUP.trueClause a (([-37, -69, 49, -60, 50, 59] : List Int).map RUP.decode) :=
  g67 a assignment _ (by decide +kernel)

include assignment in
private theorem h176 : RUP.trueClause a (([-37, -69, 49, -60, -50, -59] : List Int).map RUP.decode) :=
  g67 a assignment _ (by decide +kernel)

include assignment in
private theorem g68 (c) (hc : c ∈ pluckerAt [3, 5] [1, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h177 : RUP.trueClause a (([-46, 69, -49, -67, 50, -66] : List Int).map RUP.decode) :=
  g68 a assignment _ (by decide +kernel)

include assignment in
private theorem h178 : RUP.trueClause a (([-46, 69, 49, 67, -50, 66] : List Int).map RUP.decode) :=
  g68 a assignment _ (by decide +kernel)

include assignment in
private theorem h179 : RUP.trueClause a (([-46, -69, 49, -67, 50, 66] : List Int).map RUP.decode) :=
  g68 a assignment _ (by decide +kernel)

include assignment in
private theorem h180 : RUP.trueClause a (([-46, -69, 49, -67, -50, -66] : List Int).map RUP.decode) :=
  g68 a assignment _ (by decide +kernel)

include assignment in
private theorem h181 : RUP.trueClause a (([46, -69, -49, -67, 50, -66] : List Int).map RUP.decode) :=
  g68 a assignment _ (by decide +kernel)

include assignment in
private theorem h182 : RUP.trueClause a (([46, -69, -49, -67, -50, 66] : List Int).map RUP.decode) :=
  g68 a assignment _ (by decide +kernel)

include assignment in
private theorem h183 : RUP.trueClause a (([46, -69, 49, 67, 50, -66] : List Int).map RUP.decode) :=
  g68 a assignment _ (by decide +kernel)

include assignment in
private theorem g69 (c) (hc : c ∈ pluckerAt [3, 5] [2, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h184 : RUP.trueClause a (([-56, -69, 59, -67, 60, 66] : List Int).map RUP.decode) :=
  g69 a assignment _ (by decide +kernel)

include assignment in
private theorem h185 : RUP.trueClause a (([-56, -69, 59, -67, -60, -66] : List Int).map RUP.decode) :=
  g69 a assignment _ (by decide +kernel)

include assignment in
private theorem h186 : RUP.trueClause a (([56, 69, 59, -67, 60, 66] : List Int).map RUP.decode) :=
  g69 a assignment _ (by decide +kernel)

include assignment in
private theorem h187 : RUP.trueClause a (([56, -69, 59, 67, 60, -66] : List Int).map RUP.decode) :=
  g69 a assignment _ (by decide +kernel)

include assignment in
private theorem g70 (c) (hc : c ∈ pluckerAt [3, 6] [1, 2, 4, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h188 : RUP.trueClause a (([38, 66, 47, -59, 49, 57] : List Int).map RUP.decode) :=
  g70 a assignment _ (by decide +kernel)

include assignment in
private theorem h189 : RUP.trueClause a (([38, -66, -47, -59, 49, -57] : List Int).map RUP.decode) :=
  g70 a assignment _ (by decide +kernel)

include assignment in
private theorem h190 : RUP.trueClause a (([-38, 66, 47, 59, -49, 57] : List Int).map RUP.decode) :=
  g70 a assignment _ (by decide +kernel)

include assignment in
private theorem h191 : RUP.trueClause a (([-38, -66, -47, 59, 49, 57] : List Int).map RUP.decode) :=
  g70 a assignment _ (by decide +kernel)

include assignment in
private theorem g71 (c) (hc : c ∈ pluckerAt [3, 6] [1, 2, 4, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h192 : RUP.trueClause a (([38, 68, -47, 61, -51, -57] : List Int).map RUP.decode) :=
  g71 a assignment _ (by decide +kernel)

include assignment in
private theorem h193 : RUP.trueClause a (([-38, -68, 47, -61, 51, 57] : List Int).map RUP.decode) :=
  g71 a assignment _ (by decide +kernel)

include assignment in
private theorem h194 : RUP.trueClause a (([-38, 68, 47, 61, 51, -57] : List Int).map RUP.decode) :=
  g71 a assignment _ (by decide +kernel)

include assignment in
private theorem h195 : RUP.trueClause a (([-38, 68, -47, -61, 51, -57] : List Int).map RUP.decode) :=
  g71 a assignment _ (by decide +kernel)

include assignment in
private theorem g72 (c) (hc : c ∈ pluckerAt [3, 6] [1, 2, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h196 : RUP.trueClause a (([38, -69, 49, 61, -51, 59] : List Int).map RUP.decode) :=
  g72 a assignment _ (by decide +kernel)

include assignment in
private theorem h197 : RUP.trueClause a (([-38, -69, 49, -61, 51, 59] : List Int).map RUP.decode) :=
  g72 a assignment _ (by decide +kernel)

include assignment in
private theorem h198 : RUP.trueClause a (([-38, 69, -49, -61, 51, -59] : List Int).map RUP.decode) :=
  g72 a assignment _ (by decide +kernel)

include assignment in
private theorem h199 : RUP.trueClause a (([-38, 69, -49, -61, -51, 59] : List Int).map RUP.decode) :=
  g72 a assignment _ (by decide +kernel)

include assignment in
private theorem g73 (c) (hc : c ∈ pluckerAt [3, 6] [1, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h200 : RUP.trueClause a (([-47, -69, -49, 68, 51, 66] : List Int).map RUP.decode) :=
  g73 a assignment _ (by decide +kernel)

include assignment in
private theorem h201 : RUP.trueClause a (([-47, -69, -49, 68, -51, -66] : List Int).map RUP.decode) :=
  g73 a assignment _ (by decide +kernel)

include assignment in
private theorem h202 : RUP.trueClause a (([-47, 69, -49, -68, 51, -66] : List Int).map RUP.decode) :=
  g73 a assignment _ (by decide +kernel)

include assignment in
private theorem h203 : RUP.trueClause a (([47, -69, -49, -68, -51, 66] : List Int).map RUP.decode) :=
  g73 a assignment _ (by decide +kernel)

include assignment in
private theorem h204 : RUP.trueClause a (([47, 69, 49, -68, 51, 66] : List Int).map RUP.decode) :=
  g73 a assignment _ (by decide +kernel)

include assignment in
private theorem h205 : RUP.trueClause a (([47, 69, 49, -68, -51, -66] : List Int).map RUP.decode) :=
  g73 a assignment _ (by decide +kernel)

include assignment in
private theorem g74 (c) (hc : c ∈ pluckerAt [3, 6] [2, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h206 : RUP.trueClause a (([-57, -69, 59, -68, -61, -66] : List Int).map RUP.decode) :=
  g74 a assignment _ (by decide +kernel)

include assignment in
private theorem h207 : RUP.trueClause a (([-57, 69, -59, -68, 61, -66] : List Int).map RUP.decode) :=
  g74 a assignment _ (by decide +kernel)

include assignment in
private theorem h208 : RUP.trueClause a (([57, -69, -59, -68, -61, 66] : List Int).map RUP.decode) :=
  g74 a assignment _ (by decide +kernel)

include assignment in
private theorem h209 : RUP.trueClause a (([57, 69, 59, -68, 61, 66] : List Int).map RUP.decode) :=
  g74 a assignment _ (by decide +kernel)

include assignment in
private theorem g75 (c) (hc : c ∈ pluckerAt [3, 7] [0, 2, 4, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h210 : RUP.trueClause a (([-19, -67, 28, -60, -30, -58] : List Int).map RUP.decode) :=
  g75 a assignment _ (by decide +kernel)

include assignment in
private theorem g76 (c) (hc : c ∈ pluckerAt [3, 7] [0, 2, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h211 : RUP.trueClause a (([-19, -69, 30, -61, -31, -60] : List Int).map RUP.decode) :=
  g76 a assignment _ (by decide +kernel)

include assignment in
private theorem g77 (c) (hc : c ∈ pluckerAt [3, 7] [1, 2, 4, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h212 : RUP.trueClause a (([-39, 67, -48, -60, -50, 58] : List Int).map RUP.decode) :=
  g77 a assignment _ (by decide +kernel)

include assignment in
private theorem g78 (c) (hc : c ∈ pluckerAt [3, 7] [1, 2, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h213 : RUP.trueClause a (([39, 68, 48, -61, 51, 58] : List Int).map RUP.decode) :=
  g78 a assignment _ (by decide +kernel)

include assignment in
private theorem h214 : RUP.trueClause a (([39, -68, 48, 61, 51, -58] : List Int).map RUP.decode) :=
  g78 a assignment _ (by decide +kernel)

include assignment in
private theorem h215 : RUP.trueClause a (([-39, 68, -48, -61, -51, 58] : List Int).map RUP.decode) :=
  g78 a assignment _ (by decide +kernel)

include assignment in
private theorem h216 : RUP.trueClause a (([-39, -68, 48, -61, 51, 58] : List Int).map RUP.decode) :=
  g78 a assignment _ (by decide +kernel)

include assignment in
private theorem g79 (c) (hc : c ∈ pluckerAt [3, 7] [1, 2, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h217 : RUP.trueClause a (([39, 69, 50, -61, -51, -60] : List Int).map RUP.decode) :=
  g79 a assignment _ (by decide +kernel)

include assignment in
private theorem h218 : RUP.trueClause a (([39, -69, 50, 61, -51, 60] : List Int).map RUP.decode) :=
  g79 a assignment _ (by decide +kernel)

include assignment in
private theorem h219 : RUP.trueClause a (([-39, 69, 50, 61, -51, 60] : List Int).map RUP.decode) :=
  g79 a assignment _ (by decide +kernel)

include assignment in
private theorem h220 : RUP.trueClause a (([-39, -69, 50, -61, -51, -60] : List Int).map RUP.decode) :=
  g79 a assignment _ (by decide +kernel)

include assignment in
private theorem g80 (c) (hc : c ∈ pluckerAt [3, 7] [1, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h221 : RUP.trueClause a (([48, 69, 50, -68, -51, -67] : List Int).map RUP.decode) :=
  g80 a assignment _ (by decide +kernel)

include assignment in
private theorem g81 (c) (hc : c ∈ pluckerAt [3, 7] [2, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h222 : RUP.trueClause a (([58, 69, 60, -68, 61, 67] : List Int).map RUP.decode) :=
  g81 a assignment _ (by decide +kernel)

include assignment in
private theorem h223 : RUP.trueClause a (([58, -69, 60, 68, 61, -67] : List Int).map RUP.decode) :=
  g81 a assignment _ (by decide +kernel)

include assignment in
private theorem h224 : RUP.trueClause a (([58, -69, -60, -68, 61, -67] : List Int).map RUP.decode) :=
  g81 a assignment _ (by decide +kernel)

include assignment in
private theorem g82 (c) (hc : c ∈ pluckerAt [4, 5] [0, 1, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h225 : RUP.trueClause a (([10, -70, -32, -53, -33, 52] : List Int).map RUP.decode) :=
  g82 a assignment _ (by decide +kernel)

include assignment in
private theorem h226 : RUP.trueClause a (([-10, -70, 32, -53, 33, 52] : List Int).map RUP.decode) :=
  g82 a assignment _ (by decide +kernel)

include assignment in
private theorem g83 (c) (hc : c ∈ pluckerAt [4, 5] [0, 2, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h227 : RUP.trueClause a (([20, 70, -32, 63, -33, -62] : List Int).map RUP.decode) :=
  g83 a assignment _ (by decide +kernel)

include assignment in
private theorem h228 : RUP.trueClause a (([20, -70, -32, -63, -33, 62] : List Int).map RUP.decode) :=
  g83 a assignment _ (by decide +kernel)

include assignment in
private theorem h229 : RUP.trueClause a (([-20, 70, 32, 63, 33, -62] : List Int).map RUP.decode) :=
  g83 a assignment _ (by decide +kernel)

include assignment in
private theorem h230 : RUP.trueClause a (([-20, -70, 32, -63, 33, 62] : List Int).map RUP.decode) :=
  g83 a assignment _ (by decide +kernel)

include assignment in
private theorem g84 (c) (hc : c ∈ pluckerAt [4, 5] [1, 2, 3, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h231 : RUP.trueClause a (([40, 66, -46, 62, -52, -56] : List Int).map RUP.decode) :=
  g84 a assignment _ (by decide +kernel)

include assignment in
private theorem h232 : RUP.trueClause a (([40, -66, -46, -62, -52, 56] : List Int).map RUP.decode) :=
  g84 a assignment _ (by decide +kernel)

include assignment in
private theorem h233 : RUP.trueClause a (([40, -66, 46, 62, 52, -56] : List Int).map RUP.decode) :=
  g84 a assignment _ (by decide +kernel)

include assignment in
private theorem h234 : RUP.trueClause a (([40, -66, 46, 62, -52, 56] : List Int).map RUP.decode) :=
  g84 a assignment _ (by decide +kernel)

include assignment in
private theorem h235 : RUP.trueClause a (([-40, 66, -46, -62, 52, -56] : List Int).map RUP.decode) :=
  g84 a assignment _ (by decide +kernel)

include assignment in
private theorem h236 : RUP.trueClause a (([-40, 66, 46, 62, 52, -56] : List Int).map RUP.decode) :=
  g84 a assignment _ (by decide +kernel)

include assignment in
private theorem h237 : RUP.trueClause a (([-40, -66, 46, -62, 52, 56] : List Int).map RUP.decode) :=
  g84 a assignment _ (by decide +kernel)

include assignment in
private theorem h238 : RUP.trueClause a (([-40, -66, 46, -62, -52, -56] : List Int).map RUP.decode) :=
  g84 a assignment _ (by decide +kernel)

include assignment in
private theorem g85 (c) (hc : c ∈ pluckerAt [4, 5] [1, 2, 3, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h239 : RUP.trueClause a (([40, 67, 46, -63, -53, -56] : List Int).map RUP.decode) :=
  g85 a assignment _ (by decide +kernel)

include assignment in
private theorem h240 : RUP.trueClause a (([40, -67, -46, -63, -53, 56] : List Int).map RUP.decode) :=
  g85 a assignment _ (by decide +kernel)

include assignment in
private theorem g86 (c) (hc : c ∈ pluckerAt [4, 5] [1, 3, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h241 : RUP.trueClause a (([46, 70, 52, -67, -53, -66] : List Int).map RUP.decode) :=
  g86 a assignment _ (by decide +kernel)

include assignment in
private theorem h242 : RUP.trueClause a (([46, -70, -52, -67, 53, -66] : List Int).map RUP.decode) :=
  g86 a assignment _ (by decide +kernel)

include assignment in
private theorem h243 : RUP.trueClause a (([46, -70, 52, 67, 53, -66] : List Int).map RUP.decode) :=
  g86 a assignment _ (by decide +kernel)

include assignment in
private theorem h244 : RUP.trueClause a (([-46, 70, 52, 67, 53, -66] : List Int).map RUP.decode) :=
  g86 a assignment _ (by decide +kernel)

include assignment in
private theorem h245 : RUP.trueClause a (([-46, 70, 52, 67, -53, 66] : List Int).map RUP.decode) :=
  g86 a assignment _ (by decide +kernel)

include assignment in
private theorem g87 (c) (hc : c ∈ pluckerAt [4, 5] [2, 3, 6, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h246 : RUP.trueClause a (([-56, -70, 62, -67, 63, 66] : List Int).map RUP.decode) :=
  g87 a assignment _ (by decide +kernel)

include assignment in
private theorem g88 (c) (hc : c ∈ pluckerAt [4, 6] [0, 1, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h247 : RUP.trueClause a (([-11, -70, 32, -54, 34, 52] : List Int).map RUP.decode) :=
  g88 a assignment _ (by decide +kernel)

include assignment in
private theorem g89 (c) (hc : c ∈ pluckerAt [4, 6] [0, 2, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h248 : RUP.trueClause a (([21, -70, 32, 64, 34, -62] : List Int).map RUP.decode) :=
  g89 a assignment _ (by decide +kernel)

include assignment in
private theorem h249 : RUP.trueClause a (([21, 70, -32, 64, -34, -62] : List Int).map RUP.decode) :=
  g89 a assignment _ (by decide +kernel)

include assignment in
private theorem h250 : RUP.trueClause a (([-21, -70, 32, -64, 34, 62] : List Int).map RUP.decode) :=
  g89 a assignment _ (by decide +kernel)

include assignment in
private theorem h251 : RUP.trueClause a (([-21, 70, -32, -64, -34, 62] : List Int).map RUP.decode) :=
  g89 a assignment _ (by decide +kernel)

include assignment in
private theorem g90 (c) (hc : c ∈ pluckerAt [4, 6] [1, 2, 3, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h252 : RUP.trueClause a (([41, -66, -47, -62, 52, -57] : List Int).map RUP.decode) :=
  g90 a assignment _ (by decide +kernel)

include assignment in
private theorem h253 : RUP.trueClause a (([41, -66, 47, 62, -52, 57] : List Int).map RUP.decode) :=
  g90 a assignment _ (by decide +kernel)

include assignment in
private theorem h254 : RUP.trueClause a (([-41, -66, -47, 62, -52, -57] : List Int).map RUP.decode) :=
  g90 a assignment _ (by decide +kernel)

include assignment in
private theorem h255 : RUP.trueClause a (([-41, -66, -47, 62, 52, 57] : List Int).map RUP.decode) :=
  g90 a assignment _ (by decide +kernel)

include assignment in
private theorem h256 : RUP.trueClause a (([-41, 66, 47, 62, -52, 57] : List Int).map RUP.decode) :=
  g90 a assignment _ (by decide +kernel)

include assignment in
private theorem g91 (c) (hc : c ∈ pluckerAt [4, 6] [1, 2, 3, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h257 : RUP.trueClause a (([41, -68, 47, 64, -54, 57] : List Int).map RUP.decode) :=
  g91 a assignment _ (by decide +kernel)

include assignment in
private theorem g92 (c) (hc : c ∈ pluckerAt [4, 6] [1, 2, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h258 : RUP.trueClause a (([41, -70, 52, 64, 54, -62] : List Int).map RUP.decode) :=
  g92 a assignment _ (by decide +kernel)

include assignment in
private theorem h259 : RUP.trueClause a (([41, -70, -52, -64, 54, -62] : List Int).map RUP.decode) :=
  g92 a assignment _ (by decide +kernel)

include assignment in
private theorem h260 : RUP.trueClause a (([-41, -70, 52, -64, 54, 62] : List Int).map RUP.decode) :=
  g92 a assignment _ (by decide +kernel)

include assignment in
private theorem h261 : RUP.trueClause a (([-41, -70, 52, -64, -54, -62] : List Int).map RUP.decode) :=
  g92 a assignment _ (by decide +kernel)

include assignment in
private theorem g93 (c) (hc : c ∈ pluckerAt [4, 6] [1, 3, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h262 : RUP.trueClause a (([47, -70, 52, 68, 54, -66] : List Int).map RUP.decode) :=
  g93 a assignment _ (by decide +kernel)

include assignment in
private theorem h263 : RUP.trueClause a (([47, -70, -52, -68, -54, 66] : List Int).map RUP.decode) :=
  g93 a assignment _ (by decide +kernel)

include assignment in
private theorem h264 : RUP.trueClause a (([47, 70, 52, -68, 54, 66] : List Int).map RUP.decode) :=
  g93 a assignment _ (by decide +kernel)

include assignment in
private theorem h265 : RUP.trueClause a (([-47, -70, 52, -68, 54, 66] : List Int).map RUP.decode) :=
  g93 a assignment _ (by decide +kernel)

include assignment in
private theorem h266 : RUP.trueClause a (([-47, -70, -52, 68, -54, -66] : List Int).map RUP.decode) :=
  g93 a assignment _ (by decide +kernel)

include assignment in
private theorem h267 : RUP.trueClause a (([-47, 70, -52, -68, 54, -66] : List Int).map RUP.decode) :=
  g93 a assignment _ (by decide +kernel)

include assignment in
private theorem g94 (c) (hc : c ∈ pluckerAt [4, 6] [2, 3, 5, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h268 : RUP.trueClause a (([57, -70, 62, 68, 64, -66] : List Int).map RUP.decode) :=
  g94 a assignment _ (by decide +kernel)

include assignment in
private theorem h269 : RUP.trueClause a (([57, -70, -62, -68, -64, 66] : List Int).map RUP.decode) :=
  g94 a assignment _ (by decide +kernel)

include assignment in
private theorem h270 : RUP.trueClause a (([-57, -70, 62, -68, 64, 66] : List Int).map RUP.decode) :=
  g94 a assignment _ (by decide +kernel)

include assignment in
private theorem h271 : RUP.trueClause a (([-57, -70, -62, 68, 64, 66] : List Int).map RUP.decode) :=
  g94 a assignment _ (by decide +kernel)

include assignment in
private theorem h272 : RUP.trueClause a (([-57, -70, -62, 68, -64, -66] : List Int).map RUP.decode) :=
  g94 a assignment _ (by decide +kernel)

include assignment in
private theorem h273 : RUP.trueClause a (([-57, 70, 62, 68, 64, -66] : List Int).map RUP.decode) :=
  g94 a assignment _ (by decide +kernel)

include assignment in
private theorem g95 (c) (hc : c ∈ pluckerAt [4, 7] [0, 1, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h274 : RUP.trueClause a (([12, -70, -33, -54, 34, -53] : List Int).map RUP.decode) :=
  g95 a assignment _ (by decide +kernel)

include assignment in
private theorem h275 : RUP.trueClause a (([-12, -70, -33, 54, 34, 53] : List Int).map RUP.decode) :=
  g95 a assignment _ (by decide +kernel)

include assignment in
private theorem g96 (c) (hc : c ∈ pluckerAt [4, 7] [0, 2, 3, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h276 : RUP.trueClause a (([-22, 68, -28, -64, -34, 58] : List Int).map RUP.decode) :=
  g96 a assignment _ (by decide +kernel)

include assignment in
private theorem h277 : RUP.trueClause a (([-22, 68, 28, 64, 34, -58] : List Int).map RUP.decode) :=
  g96 a assignment _ (by decide +kernel)

include assignment in
private theorem g97 (c) (hc : c ∈ pluckerAt [4, 7] [0, 2, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h278 : RUP.trueClause a (([22, 70, 33, -64, -34, -63] : List Int).map RUP.decode) :=
  g97 a assignment _ (by decide +kernel)

include assignment in
private theorem h279 : RUP.trueClause a (([22, -70, 33, 64, 34, -63] : List Int).map RUP.decode) :=
  g97 a assignment _ (by decide +kernel)

include assignment in
private theorem h280 : RUP.trueClause a (([22, -70, -33, -64, 34, -63] : List Int).map RUP.decode) :=
  g97 a assignment _ (by decide +kernel)

include assignment in
private theorem h281 : RUP.trueClause a (([-22, 70, 33, 64, -34, 63] : List Int).map RUP.decode) :=
  g97 a assignment _ (by decide +kernel)

include assignment in
private theorem h282 : RUP.trueClause a (([-22, -70, -33, 64, 34, 63] : List Int).map RUP.decode) :=
  g97 a assignment _ (by decide +kernel)

include assignment in
private theorem g98 (c) (hc : c ∈ pluckerAt [4, 7] [0, 3, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h283 : RUP.trueClause a (([28, -70, -33, -68, 34, -67] : List Int).map RUP.decode) :=
  g98 a assignment _ (by decide +kernel)

include assignment in
private theorem g99 (c) (hc : c ∈ pluckerAt [4, 7] [1, 2, 3, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h284 : RUP.trueClause a (([42, -67, -48, -63, -53, 58] : List Int).map RUP.decode) :=
  g99 a assignment _ (by decide +kernel)

include assignment in
private theorem h285 : RUP.trueClause a (([42, -67, 48, 63, 53, -58] : List Int).map RUP.decode) :=
  g99 a assignment _ (by decide +kernel)

include assignment in
private theorem h286 : RUP.trueClause a (([42, 67, -48, 63, 53, 58] : List Int).map RUP.decode) :=
  g99 a assignment _ (by decide +kernel)

include assignment in
private theorem h287 : RUP.trueClause a (([42, 67, 48, -63, 53, 58] : List Int).map RUP.decode) :=
  g99 a assignment _ (by decide +kernel)

include assignment in
private theorem h288 : RUP.trueClause a (([-42, 67, -48, -63, -53, 58] : List Int).map RUP.decode) :=
  g99 a assignment _ (by decide +kernel)

include assignment in
private theorem g100 (c) (hc : c ∈ pluckerAt [4, 7] [1, 2, 3, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h289 : RUP.trueClause a (([-42, -68, 48, -64, -54, -58] : List Int).map RUP.decode) :=
  g100 a assignment _ (by decide +kernel)

include assignment in
private theorem h290 : RUP.trueClause a (([-42, 68, 48, 64, 54, -58] : List Int).map RUP.decode) :=
  g100 a assignment _ (by decide +kernel)

include assignment in
private theorem g101 (c) (hc : c ∈ pluckerAt [4, 7] [1, 2, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h291 : RUP.trueClause a (([-42, -70, -53, 64, 54, 63] : List Int).map RUP.decode) :=
  g101 a assignment _ (by decide +kernel)

include assignment in
private theorem g102 (c) (hc : c ∈ pluckerAt [4, 7] [1, 3, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h292 : RUP.trueClause a (([48, 70, 53, -68, 54, 67] : List Int).map RUP.decode) :=
  g102 a assignment _ (by decide +kernel)

include assignment in
private theorem h293 : RUP.trueClause a (([-48, 70, -53, -68, -54, 67] : List Int).map RUP.decode) :=
  g102 a assignment _ (by decide +kernel)

include assignment in
private theorem h294 : RUP.trueClause a (([-48, -70, 53, -68, -54, -67] : List Int).map RUP.decode) :=
  g102 a assignment _ (by decide +kernel)

include assignment in
private theorem h295 : RUP.trueClause a (([-48, -70, -53, 68, 54, 67] : List Int).map RUP.decode) :=
  g102 a assignment _ (by decide +kernel)

include assignment in
private theorem g103 (c) (hc : c ∈ pluckerAt [4, 7] [2, 3, 5, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h296 : RUP.trueClause a (([58, 70, -63, 68, -64, -67] : List Int).map RUP.decode) :=
  g103 a assignment _ (by decide +kernel)

include assignment in
private theorem h297 : RUP.trueClause a (([-58, 70, 63, 68, 64, -67] : List Int).map RUP.decode) :=
  g103 a assignment _ (by decide +kernel)

include assignment in
private theorem h298 : RUP.trueClause a (([-58, -70, -63, 68, 64, 67] : List Int).map RUP.decode) :=
  g103 a assignment _ (by decide +kernel)

include assignment in
private theorem g104 (c) (hc : c ∈ pluckerAt [5, 6] [0, 2, 4, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h299 : RUP.trueClause a (([23, 70, -32, 65, 35, 62] : List Int).map RUP.decode) :=
  g104 a assignment _ (by decide +kernel)

include assignment in
private theorem h300 : RUP.trueClause a (([23, -70, 32, 65, -35, 62] : List Int).map RUP.decode) :=
  g104 a assignment _ (by decide +kernel)

include assignment in
private theorem h301 : RUP.trueClause a (([-23, 70, -32, -65, 35, -62] : List Int).map RUP.decode) :=
  g104 a assignment _ (by decide +kernel)

include assignment in
private theorem h302 : RUP.trueClause a (([-23, -70, 32, -65, -35, -62] : List Int).map RUP.decode) :=
  g104 a assignment _ (by decide +kernel)

include assignment in
private theorem g105 (c) (hc : c ∈ pluckerAt [5, 6] [1, 2, 3, 4]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h303 : RUP.trueClause a (([43, -66, -49, -62, 52, -59] : List Int).map RUP.decode) :=
  g105 a assignment _ (by decide +kernel)

include assignment in
private theorem h304 : RUP.trueClause a (([43, -66, 49, 62, -52, 59] : List Int).map RUP.decode) :=
  g105 a assignment _ (by decide +kernel)

include assignment in
private theorem h305 : RUP.trueClause a (([-43, 66, 49, 62, -52, 59] : List Int).map RUP.decode) :=
  g105 a assignment _ (by decide +kernel)

include assignment in
private theorem h306 : RUP.trueClause a (([-43, -66, 49, -62, -52, -59] : List Int).map RUP.decode) :=
  g105 a assignment _ (by decide +kernel)

include assignment in
private theorem g106 (c) (hc : c ∈ pluckerAt [5, 6] [1, 2, 3, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h307 : RUP.trueClause a (([43, -69, -49, -65, 55, -59] : List Int).map RUP.decode) :=
  g106 a assignment _ (by decide +kernel)

include assignment in
private theorem h308 : RUP.trueClause a (([43, -69, -49, -65, -55, 59] : List Int).map RUP.decode) :=
  g106 a assignment _ (by decide +kernel)

include assignment in
private theorem h309 : RUP.trueClause a (([43, -69, 49, 65, -55, 59] : List Int).map RUP.decode) :=
  g106 a assignment _ (by decide +kernel)

include assignment in
private theorem h310 : RUP.trueClause a (([-43, -69, 49, -65, 55, 59] : List Int).map RUP.decode) :=
  g106 a assignment _ (by decide +kernel)

include assignment in
private theorem g107 (c) (hc : c ∈ pluckerAt [5, 6] [1, 2, 4, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h311 : RUP.trueClause a (([43, 70, 52, -65, 55, 62] : List Int).map RUP.decode) :=
  g107 a assignment _ (by decide +kernel)

include assignment in
private theorem h312 : RUP.trueClause a (([43, -70, -52, -65, -55, 62] : List Int).map RUP.decode) :=
  g107 a assignment _ (by decide +kernel)

include assignment in
private theorem h313 : RUP.trueClause a (([43, -70, 52, 65, 55, -62] : List Int).map RUP.decode) :=
  g107 a assignment _ (by decide +kernel)

include assignment in
private theorem h314 : RUP.trueClause a (([43, -70, 52, 65, -55, 62] : List Int).map RUP.decode) :=
  g107 a assignment _ (by decide +kernel)

include assignment in
private theorem h315 : RUP.trueClause a (([-43, 70, -52, -65, -55, 62] : List Int).map RUP.decode) :=
  g107 a assignment _ (by decide +kernel)

include assignment in
private theorem h316 : RUP.trueClause a (([-43, -70, -52, 65, -55, -62] : List Int).map RUP.decode) :=
  g107 a assignment _ (by decide +kernel)

include assignment in
private theorem h317 : RUP.trueClause a (([-43, -70, 52, -65, 55, 62] : List Int).map RUP.decode) :=
  g107 a assignment _ (by decide +kernel)

include assignment in
private theorem g108 (c) (hc : c ∈ pluckerAt [5, 6] [1, 3, 4, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h318 : RUP.trueClause a (([49, 70, -52, 69, -55, -66] : List Int).map RUP.decode) :=
  g108 a assignment _ (by decide +kernel)

include assignment in
private theorem h319 : RUP.trueClause a (([49, 70, 52, -69, 55, 66] : List Int).map RUP.decode) :=
  g108 a assignment _ (by decide +kernel)

include assignment in
private theorem h320 : RUP.trueClause a (([49, -70, -52, -69, 55, -66] : List Int).map RUP.decode) :=
  g108 a assignment _ (by decide +kernel)

include assignment in
private theorem h321 : RUP.trueClause a (([49, -70, -52, -69, -55, 66] : List Int).map RUP.decode) :=
  g108 a assignment _ (by decide +kernel)

include assignment in
private theorem h322 : RUP.trueClause a (([49, -70, 52, 69, 55, -66] : List Int).map RUP.decode) :=
  g108 a assignment _ (by decide +kernel)

include assignment in
private theorem h323 : RUP.trueClause a (([-49, 70, -52, -69, -55, 66] : List Int).map RUP.decode) :=
  g108 a assignment _ (by decide +kernel)

include assignment in
private theorem h324 : RUP.trueClause a (([-49, 70, 52, 69, 55, -66] : List Int).map RUP.decode) :=
  g108 a assignment _ (by decide +kernel)

include assignment in
private theorem h325 : RUP.trueClause a (([-49, -70, -52, 69, -55, -66] : List Int).map RUP.decode) :=
  g108 a assignment _ (by decide +kernel)

include assignment in
private theorem h326 : RUP.trueClause a (([-49, -70, 52, -69, 55, 66] : List Int).map RUP.decode) :=
  g108 a assignment _ (by decide +kernel)

include assignment in
private theorem h327 : RUP.trueClause a (([-49, -70, 52, -69, -55, -66] : List Int).map RUP.decode) :=
  g108 a assignment _ (by decide +kernel)

include assignment in
private theorem g109 (c) (hc : c ∈ pluckerAt [5, 6] [2, 3, 4, 7]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h328 : RUP.trueClause a (([59, 70, 62, -69, 65, 66] : List Int).map RUP.decode) :=
  g109 a assignment _ (by decide +kernel)

include assignment in
private theorem h329 : RUP.trueClause a (([59, 70, 62, -69, -65, -66] : List Int).map RUP.decode) :=
  g109 a assignment _ (by decide +kernel)

include assignment in
private theorem h330 : RUP.trueClause a (([59, -70, 62, 69, 65, -66] : List Int).map RUP.decode) :=
  g109 a assignment _ (by decide +kernel)

include assignment in
private theorem h331 : RUP.trueClause a (([-59, -70, -62, 69, 65, 66] : List Int).map RUP.decode) :=
  g109 a assignment _ (by decide +kernel)

include assignment in
private theorem g110 (c) (hc : c ∈ pluckerAt [5, 7] [0, 1, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h332 : RUP.trueClause a (([14, -70, -33, -55, -35, 53] : List Int).map RUP.decode) :=
  g110 a assignment _ (by decide +kernel)

include assignment in
private theorem g111 (c) (hc : c ∈ pluckerAt [5, 7] [0, 2, 3, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h333 : RUP.trueClause a (([-24, -69, 30, -65, -35, -60] : List Int).map RUP.decode) :=
  g111 a assignment _ (by decide +kernel)

include assignment in
private theorem g112 (c) (hc : c ∈ pluckerAt [5, 7] [0, 2, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h334 : RUP.trueClause a (([24, -70, -33, -65, -35, 63] : List Int).map RUP.decode) :=
  g112 a assignment _ (by decide +kernel)

include assignment in
private theorem h335 : RUP.trueClause a (([24, -70, -33, -65, 35, -63] : List Int).map RUP.decode) :=
  g112 a assignment _ (by decide +kernel)

include assignment in
private theorem h336 : RUP.trueClause a (([24, 70, 33, -65, 35, 63] : List Int).map RUP.decode) :=
  g112 a assignment _ (by decide +kernel)

include assignment in
private theorem h337 : RUP.trueClause a (([-24, -70, -33, 65, -35, -63] : List Int).map RUP.decode) :=
  g112 a assignment _ (by decide +kernel)

include assignment in
private theorem h338 : RUP.trueClause a (([-24, -70, 33, -65, -35, -63] : List Int).map RUP.decode) :=
  g112 a assignment _ (by decide +kernel)

include assignment in
private theorem h339 : RUP.trueClause a (([-24, 70, 33, 65, 35, -63] : List Int).map RUP.decode) :=
  g112 a assignment _ (by decide +kernel)

include assignment in
private theorem g113 (c) (hc : c ∈ pluckerAt [5, 7] [0, 3, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h340 : RUP.trueClause a (([30, -70, -33, -69, -35, 67] : List Int).map RUP.decode) :=
  g113 a assignment _ (by decide +kernel)

include assignment in
private theorem h341 : RUP.trueClause a (([30, -70, -33, -69, 35, -67] : List Int).map RUP.decode) :=
  g113 a assignment _ (by decide +kernel)

include assignment in
private theorem g114 (c) (hc : c ∈ pluckerAt [5, 7] [1, 2, 3, 4]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h342 : RUP.trueClause a (([44, 67, 50, -63, -53, -60] : List Int).map RUP.decode) :=
  g114 a assignment _ (by decide +kernel)

include assignment in
private theorem g115 (c) (hc : c ∈ pluckerAt [5, 7] [1, 2, 3, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h343 : RUP.trueClause a (([44, -69, -50, -65, 55, -60] : List Int).map RUP.decode) :=
  g115 a assignment _ (by decide +kernel)

include assignment in
private theorem h344 : RUP.trueClause a (([44, -69, 50, 65, -55, 60] : List Int).map RUP.decode) :=
  g115 a assignment _ (by decide +kernel)

include assignment in
private theorem h345 : RUP.trueClause a (([44, 69, 50, -65, -55, -60] : List Int).map RUP.decode) :=
  g115 a assignment _ (by decide +kernel)

include assignment in
private theorem h346 : RUP.trueClause a (([44, 69, 50, -65, 55, 60] : List Int).map RUP.decode) :=
  g115 a assignment _ (by decide +kernel)

include assignment in
private theorem h347 : RUP.trueClause a (([-44, -69, 50, -65, -55, -60] : List Int).map RUP.decode) :=
  g115 a assignment _ (by decide +kernel)

include assignment in
private theorem h348 : RUP.trueClause a (([-44, 69, 50, 65, -55, 60] : List Int).map RUP.decode) :=
  g115 a assignment _ (by decide +kernel)

include assignment in
private theorem g116 (c) (hc : c ∈ pluckerAt [5, 7] [1, 2, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h349 : RUP.trueClause a (([44, -70, 53, 65, -55, 63] : List Int).map RUP.decode) :=
  g116 a assignment _ (by decide +kernel)

include assignment in
private theorem h350 : RUP.trueClause a (([44, 70, 53, -65, 55, 63] : List Int).map RUP.decode) :=
  g116 a assignment _ (by decide +kernel)

include assignment in
private theorem g117 (c) (hc : c ∈ pluckerAt [5, 7] [1, 3, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h351 : RUP.trueClause a (([50, -70, -53, -69, -55, 67] : List Int).map RUP.decode) :=
  g117 a assignment _ (by decide +kernel)

include assignment in
private theorem h352 : RUP.trueClause a (([50, -70, 53, 69, 55, -67] : List Int).map RUP.decode) :=
  g117 a assignment _ (by decide +kernel)

include assignment in
private theorem h353 : RUP.trueClause a (([50, 70, -53, 69, 55, 67] : List Int).map RUP.decode) :=
  g117 a assignment _ (by decide +kernel)

include assignment in
private theorem h354 : RUP.trueClause a (([50, 70, 53, -69, 55, 67] : List Int).map RUP.decode) :=
  g117 a assignment _ (by decide +kernel)

include assignment in
private theorem h355 : RUP.trueClause a (([-50, 70, -53, -69, -55, 67] : List Int).map RUP.decode) :=
  g117 a assignment _ (by decide +kernel)

include assignment in
private theorem h356 : RUP.trueClause a (([-50, 70, 53, 69, -55, 67] : List Int).map RUP.decode) :=
  g117 a assignment _ (by decide +kernel)

include assignment in
private theorem g118 (c) (hc : c ∈ pluckerAt [5, 7] [2, 3, 4, 6]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h357 : RUP.trueClause a (([-60, -70, 63, -69, 65, 67] : List Int).map RUP.decode) :=
  g118 a assignment _ (by decide +kernel)

include assignment in
private theorem g119 (c) (hc : c ∈ pluckerAt [6, 7] [0, 1, 4, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h358 : RUP.trueClause a (([15, -70, -34, -55, -35, 54] : List Int).map RUP.decode) :=
  g119 a assignment _ (by decide +kernel)

include assignment in
private theorem h359 : RUP.trueClause a (([-15, -70, 34, -55, 35, 54] : List Int).map RUP.decode) :=
  g119 a assignment _ (by decide +kernel)

include assignment in
private theorem g120 (c) (hc : c ∈ pluckerAt [6, 7] [0, 2, 4, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h360 : RUP.trueClause a (([25, 70, -34, 65, -35, -64] : List Int).map RUP.decode) :=
  g120 a assignment _ (by decide +kernel)

include assignment in
private theorem h361 : RUP.trueClause a (([25, -70, -34, -65, -35, 64] : List Int).map RUP.decode) :=
  g120 a assignment _ (by decide +kernel)

include assignment in
private theorem h362 : RUP.trueClause a (([-25, 70, 34, 65, 35, -64] : List Int).map RUP.decode) :=
  g120 a assignment _ (by decide +kernel)

include assignment in
private theorem h363 : RUP.trueClause a (([-25, 70, 34, 65, -35, 64] : List Int).map RUP.decode) :=
  g120 a assignment _ (by decide +kernel)

include assignment in
private theorem h364 : RUP.trueClause a (([-25, -70, 34, -65, 35, 64] : List Int).map RUP.decode) :=
  g120 a assignment _ (by decide +kernel)

include assignment in
private theorem g121 (c) (hc : c ∈ pluckerAt [6, 7] [0, 3, 4, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h365 : RUP.trueClause a (([31, 70, 34, -69, 35, 68] : List Int).map RUP.decode) :=
  g121 a assignment _ (by decide +kernel)

include assignment in
private theorem h366 : RUP.trueClause a (([31, -70, -34, -69, -35, 68] : List Int).map RUP.decode) :=
  g121 a assignment _ (by decide +kernel)

include assignment in
private theorem g122 (c) (hc : c ∈ pluckerAt [6, 7] [1, 2, 3, 4]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h367 : RUP.trueClause a (([45, 68, 51, -64, -54, -61] : List Int).map RUP.decode) :=
  g122 a assignment _ (by decide +kernel)

include assignment in
private theorem h368 : RUP.trueClause a (([45, -68, -51, -64, 54, -61] : List Int).map RUP.decode) :=
  g122 a assignment _ (by decide +kernel)

include assignment in
private theorem h369 : RUP.trueClause a (([-45, 68, 51, 64, 54, -61] : List Int).map RUP.decode) :=
  g122 a assignment _ (by decide +kernel)

include assignment in
private theorem g123 (c) (hc : c ∈ pluckerAt [6, 7] [1, 2, 3, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h370 : RUP.trueClause a (([45, 69, -51, 65, -55, -61] : List Int).map RUP.decode) :=
  g123 a assignment _ (by decide +kernel)

include assignment in
private theorem h371 : RUP.trueClause a (([45, -69, -51, -65, -55, 61] : List Int).map RUP.decode) :=
  g123 a assignment _ (by decide +kernel)

include assignment in
private theorem h372 : RUP.trueClause a (([-45, 69, -51, -65, -55, 61] : List Int).map RUP.decode) :=
  g123 a assignment _ (by decide +kernel)

include assignment in
private theorem h373 : RUP.trueClause a (([-45, -69, 51, -65, 55, 61] : List Int).map RUP.decode) :=
  g123 a assignment _ (by decide +kernel)

include assignment in
private theorem h374 : RUP.trueClause a (([-45, -69, 51, -65, -55, -61] : List Int).map RUP.decode) :=
  g123 a assignment _ (by decide +kernel)

include assignment in
private theorem g124 (c) (hc : c ∈ pluckerAt [6, 7] [1, 2, 4, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h375 : RUP.trueClause a (([45, 70, -54, 65, 55, 64] : List Int).map RUP.decode) :=
  g124 a assignment _ (by decide +kernel)

include assignment in
private theorem h376 : RUP.trueClause a (([-45, 70, -54, -65, 55, -64] : List Int).map RUP.decode) :=
  g124 a assignment _ (by decide +kernel)

include assignment in
private theorem h377 : RUP.trueClause a (([-45, -70, 54, -65, -55, -64] : List Int).map RUP.decode) :=
  g124 a assignment _ (by decide +kernel)

include assignment in
private theorem g125 (c) (hc : c ∈ pluckerAt [6, 7] [1, 3, 4, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h378 : RUP.trueClause a (([51, -70, 54, 69, 55, -68] : List Int).map RUP.decode) :=
  g125 a assignment _ (by decide +kernel)

include assignment in
private theorem h379 : RUP.trueClause a (([-51, 70, -54, -69, 55, -68] : List Int).map RUP.decode) :=
  g125 a assignment _ (by decide +kernel)

include assignment in
private theorem h380 : RUP.trueClause a (([-51, -70, -54, 69, -55, -68] : List Int).map RUP.decode) :=
  g125 a assignment _ (by decide +kernel)

include assignment in
private theorem h381 : RUP.trueClause a (([-51, -70, 54, -69, -55, -68] : List Int).map RUP.decode) :=
  g125 a assignment _ (by decide +kernel)

include assignment in
private theorem g126 (c) (hc : c ∈ pluckerAt [6, 7] [2, 3, 4, 5]) : RUP.trueClause a c :=
  assignment c (pluckerAt_mem (by decide +kernel) (by decide +kernel) hc)

include assignment in
private theorem h382 : RUP.trueClause a (([61, 70, -64, 69, -65, -68] : List Int).map RUP.decode) :=
  g126 a assignment _ (by decide +kernel)

include assignment in
private theorem h383 : RUP.trueClause a (([61, 70, 64, -69, 65, 68] : List Int).map RUP.decode) :=
  g126 a assignment _ (by decide +kernel)

include assignment in
private theorem h384 : RUP.trueClause a (([-61, 70, -64, -69, -65, 68] : List Int).map RUP.decode) :=
  g126 a assignment _ (by decide +kernel)

include assignment in
private theorem h385 : RUP.trueClause a (([-61, -70, 64, -69, 65, 68] : List Int).map RUP.decode) :=
  g126 a assignment _ (by decide +kernel)

include assignment in
private theorem g127 (c) (hc : c ∈ circuitAt [0, 1, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h386 : RUP.trueClause a (([52, 32, -13, 11, 10] : List Int).map RUP.decode) :=
  g127 a assignment _ (by decide +kernel)

include assignment in
private theorem h387 : RUP.trueClause a (([52, 32, 13, 11, 10] : List Int).map RUP.decode) :=
  g127 a assignment _ (by decide +kernel)

include assignment in
private theorem g128 (c) (hc : c ∈ circuitAt [0, 1, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h388 : RUP.trueClause a (([-53, -33, 14, -12, -10] : List Int).map RUP.decode) :=
  g128 a assignment _ (by decide +kernel)

include assignment in
private theorem h389 : RUP.trueClause a (([-53, -33, -14, -12, -10] : List Int).map RUP.decode) :=
  g128 a assignment _ (by decide +kernel)

include assignment in
private theorem g129 (c) (hc : c ∈ circuitAt [0, 1, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h390 : RUP.trueClause a (([54, 34, 15, 12, -11] : List Int).map RUP.decode) :=
  g129 a assignment _ (by decide +kernel)

include assignment in
private theorem h391 : RUP.trueClause a (([54, 34, 15, 12, 11] : List Int).map RUP.decode) :=
  g129 a assignment _ (by decide +kernel)

include assignment in
private theorem g130 (c) (hc : c ∈ circuitAt [0, 1, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h392 : RUP.trueClause a (([-55, -35, -15, -14, 13] : List Int).map RUP.decode) :=
  g130 a assignment _ (by decide +kernel)

include assignment in
private theorem h393 : RUP.trueClause a (([-55, -35, -15, -14, -13] : List Int).map RUP.decode) :=
  g130 a assignment _ (by decide +kernel)

include assignment in
private theorem g131 (c) (hc : c ∈ circuitAt [0, 2, 3, 4, 6]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h394 : RUP.trueClause a (([-57, -27, 21, -18, -16] : List Int).map RUP.decode) :=
  g131 a assignment _ (by decide +kernel)

include assignment in
private theorem g132 (c) (hc : c ∈ circuitAt [0, 2, 3, 4, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h395 : RUP.trueClause a (([58, 28, -22, -19, -16] : List Int).map RUP.decode) :=
  g132 a assignment _ (by decide +kernel)

include assignment in
private theorem g133 (c) (hc : c ∈ circuitAt [0, 2, 3, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h396 : RUP.trueClause a (([-61, -31, 25, 19, 18] : List Int).map RUP.decode) :=
  g133 a assignment _ (by decide +kernel)

include assignment in
private theorem g134 (c) (hc : c ∈ circuitAt [0, 2, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h397 : RUP.trueClause a (([-62, -32, -23, -21, 20] : List Int).map RUP.decode) :=
  g134 a assignment _ (by decide +kernel)

include assignment in
private theorem h398 : RUP.trueClause a (([62, 32, -23, 21, 20] : List Int).map RUP.decode) :=
  g134 a assignment _ (by decide +kernel)

include assignment in
private theorem h399 : RUP.trueClause a (([-62, -32, 23, -21, -20] : List Int).map RUP.decode) :=
  g134 a assignment _ (by decide +kernel)

include assignment in
private theorem h400 : RUP.trueClause a (([-62, -32, 23, 21, -20] : List Int).map RUP.decode) :=
  g134 a assignment _ (by decide +kernel)

include assignment in
private theorem h401 : RUP.trueClause a (([62, 32, -23, -21, 20] : List Int).map RUP.decode) :=
  g134 a assignment _ (by decide +kernel)

include assignment in
private theorem h402 : RUP.trueClause a (([-62, -32, -23, -21, -20] : List Int).map RUP.decode) :=
  g134 a assignment _ (by decide +kernel)

include assignment in
private theorem h403 : RUP.trueClause a (([62, 32, 23, 21, 20] : List Int).map RUP.decode) :=
  g134 a assignment _ (by decide +kernel)

include assignment in
private theorem g135 (c) (hc : c ∈ circuitAt [0, 2, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h404 : RUP.trueClause a (([63, 33, -24, 22, 20] : List Int).map RUP.decode) :=
  g135 a assignment _ (by decide +kernel)

include assignment in
private theorem h405 : RUP.trueClause a (([-63, -33, 24, -22, -20] : List Int).map RUP.decode) :=
  g135 a assignment _ (by decide +kernel)

include assignment in
private theorem h406 : RUP.trueClause a (([-63, -33, 24, 22, -20] : List Int).map RUP.decode) :=
  g135 a assignment _ (by decide +kernel)

include assignment in
private theorem h407 : RUP.trueClause a (([63, 33, -24, -22, 20] : List Int).map RUP.decode) :=
  g135 a assignment _ (by decide +kernel)

include assignment in
private theorem h408 : RUP.trueClause a (([-63, -33, -24, -22, -20] : List Int).map RUP.decode) :=
  g135 a assignment _ (by decide +kernel)

include assignment in
private theorem h409 : RUP.trueClause a (([63, 33, 24, 22, 20] : List Int).map RUP.decode) :=
  g135 a assignment _ (by decide +kernel)

include assignment in
private theorem g136 (c) (hc : c ∈ circuitAt [0, 2, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h410 : RUP.trueClause a (([64, 34, 25, 22, -21] : List Int).map RUP.decode) :=
  g136 a assignment _ (by decide +kernel)

include assignment in
private theorem h411 : RUP.trueClause a (([-64, -34, -25, -22, 21] : List Int).map RUP.decode) :=
  g136 a assignment _ (by decide +kernel)

include assignment in
private theorem h412 : RUP.trueClause a (([-64, -34, -25, -22, -21] : List Int).map RUP.decode) :=
  g136 a assignment _ (by decide +kernel)

include assignment in
private theorem h413 : RUP.trueClause a (([64, 34, 25, 22, 21] : List Int).map RUP.decode) :=
  g136 a assignment _ (by decide +kernel)

include assignment in
private theorem h414 : RUP.trueClause a (([-64, -34, -25, 22, 21] : List Int).map RUP.decode) :=
  g136 a assignment _ (by decide +kernel)

include assignment in
private theorem h415 : RUP.trueClause a (([64, 34, 25, -22, -21] : List Int).map RUP.decode) :=
  g136 a assignment _ (by decide +kernel)

include assignment in
private theorem g137 (c) (hc : c ∈ circuitAt [0, 2, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h416 : RUP.trueClause a (([65, 35, 25, 24, -23] : List Int).map RUP.decode) :=
  g137 a assignment _ (by decide +kernel)

include assignment in
private theorem h417 : RUP.trueClause a (([-65, -35, -25, -24, 23] : List Int).map RUP.decode) :=
  g137 a assignment _ (by decide +kernel)

include assignment in
private theorem h418 : RUP.trueClause a (([65, 35, -25, 24, 23] : List Int).map RUP.decode) :=
  g137 a assignment _ (by decide +kernel)

include assignment in
private theorem h419 : RUP.trueClause a (([-65, -35, 25, -24, -23] : List Int).map RUP.decode) :=
  g137 a assignment _ (by decide +kernel)

include assignment in
private theorem h420 : RUP.trueClause a (([-65, -35, -25, -24, -23] : List Int).map RUP.decode) :=
  g137 a assignment _ (by decide +kernel)

include assignment in
private theorem h421 : RUP.trueClause a (([65, 35, 25, 24, 23] : List Int).map RUP.decode) :=
  g137 a assignment _ (by decide +kernel)

include assignment in
private theorem h422 : RUP.trueClause a (([-65, -35, -25, 24, 23] : List Int).map RUP.decode) :=
  g137 a assignment _ (by decide +kernel)

include assignment in
private theorem h423 : RUP.trueClause a (([65, 35, 25, -24, -23] : List Int).map RUP.decode) :=
  g137 a assignment _ (by decide +kernel)

include assignment in
private theorem g138 (c) (hc : c ∈ circuitAt [0, 3, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h424 : RUP.trueClause a (([-66, -32, 29, 27, -26] : List Int).map RUP.decode) :=
  g138 a assignment _ (by decide +kernel)

include assignment in
private theorem g139 (c) (hc : c ∈ circuitAt [0, 3, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h425 : RUP.trueClause a (([-67, -33, -30, -28, 26] : List Int).map RUP.decode) :=
  g139 a assignment _ (by decide +kernel)

include assignment in
private theorem h426 : RUP.trueClause a (([67, 33, -30, -28, 26] : List Int).map RUP.decode) :=
  g139 a assignment _ (by decide +kernel)

include assignment in
private theorem h427 : RUP.trueClause a (([-67, -33, -30, -28, -26] : List Int).map RUP.decode) :=
  g139 a assignment _ (by decide +kernel)

include assignment in
private theorem g140 (c) (hc : c ∈ circuitAt [0, 3, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h428 : RUP.trueClause a (([-69, -35, 31, 30, 29] : List Int).map RUP.decode) :=
  g140 a assignment _ (by decide +kernel)

include assignment in
private theorem h429 : RUP.trueClause a (([-69, -35, -31, -30, -29] : List Int).map RUP.decode) :=
  g140 a assignment _ (by decide +kernel)

include assignment in
private theorem h430 : RUP.trueClause a (([-69, 35, -31, -30, -29] : List Int).map RUP.decode) :=
  g140 a assignment _ (by decide +kernel)

include assignment in
private theorem g141 (c) (hc : c ∈ circuitAt [0, 4, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h431 : RUP.trueClause a (([70, -35, 34, -33, 32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h432 : RUP.trueClause a (([-70, 35, -34, 33, -32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h433 : RUP.trueClause a (([-70, -35, -34, -33, -32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h434 : RUP.trueClause a (([70, 35, 34, 33, 32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h435 : RUP.trueClause a (([-70, -35, -34, 33, 32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h436 : RUP.trueClause a (([70, 35, 34, -33, -32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h437 : RUP.trueClause a (([-70, 35, 34, -33, -32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h438 : RUP.trueClause a (([70, -35, -34, 33, 32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h439 : RUP.trueClause a (([-70, 35, 34, 33, 32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h440 : RUP.trueClause a (([70, -35, -34, -33, -32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h441 : RUP.trueClause a (([70, 35, -34, 33, -32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h442 : RUP.trueClause a (([-70, -35, 34, -33, 32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h443 : RUP.trueClause a (([-70, -35, -34, 33, -32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h444 : RUP.trueClause a (([70, 35, 34, -33, 32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h445 : RUP.trueClause a (([-70, 35, 34, 33, -32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h446 : RUP.trueClause a (([70, -35, -34, -33, 32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h447 : RUP.trueClause a (([-70, 35, -34, -33, -32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h448 : RUP.trueClause a (([70, -35, 34, 33, 32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h449 : RUP.trueClause a (([-70, 35, -34, 33, 32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem h450 : RUP.trueClause a (([70, -35, 34, -33, -32] : List Int).map RUP.decode) :=
  g141 a assignment _ (by decide +kernel)

include assignment in
private theorem g142 (c) (hc : c ∈ circuitAt [1, 2, 3, 4, 5]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h451 : RUP.trueClause a (([-56, 46, -40, 37, -36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h452 : RUP.trueClause a (([56, 46, 40, 37, -36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h453 : RUP.trueClause a (([-56, -46, -40, -37, 36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h454 : RUP.trueClause a (([56, 46, -40, 37, 36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h455 : RUP.trueClause a (([-56, -46, 40, -37, -36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h456 : RUP.trueClause a (([-56, -46, 40, 37, -36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h457 : RUP.trueClause a (([56, 46, -40, -37, 36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h458 : RUP.trueClause a (([-56, -46, -40, -37, -36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h459 : RUP.trueClause a (([56, 46, 40, 37, 36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h460 : RUP.trueClause a (([-56, 46, 40, 37, -36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h461 : RUP.trueClause a (([56, -46, -40, -37, 36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h462 : RUP.trueClause a (([-56, 46, -40, -37, -36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h463 : RUP.trueClause a (([56, -46, 40, 37, 36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem h464 : RUP.trueClause a (([-56, 46, -40, 37, 36] : List Int).map RUP.decode) :=
  g142 a assignment _ (by decide +kernel)

include assignment in
private theorem g143 (c) (hc : c ∈ circuitAt [1, 2, 3, 4, 6]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h465 : RUP.trueClause a (([57, 47, -41, 38, 36] : List Int).map RUP.decode) :=
  g143 a assignment _ (by decide +kernel)

include assignment in
private theorem h466 : RUP.trueClause a (([-57, -47, 41, -38, -36] : List Int).map RUP.decode) :=
  g143 a assignment _ (by decide +kernel)

include assignment in
private theorem h467 : RUP.trueClause a (([57, 47, 41, 38, 36] : List Int).map RUP.decode) :=
  g143 a assignment _ (by decide +kernel)

include assignment in
private theorem h468 : RUP.trueClause a (([-57, 47, 41, 38, -36] : List Int).map RUP.decode) :=
  g143 a assignment _ (by decide +kernel)

include assignment in
private theorem h469 : RUP.trueClause a (([-57, 47, -41, -38, -36] : List Int).map RUP.decode) :=
  g143 a assignment _ (by decide +kernel)

include assignment in
private theorem h470 : RUP.trueClause a (([57, -47, 41, -38, -36] : List Int).map RUP.decode) :=
  g143 a assignment _ (by decide +kernel)

include assignment in
private theorem g144 (c) (hc : c ∈ circuitAt [1, 2, 3, 4, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h471 : RUP.trueClause a (([58, -48, 42, -39, 36] : List Int).map RUP.decode) :=
  g144 a assignment _ (by decide +kernel)

include assignment in
private theorem h472 : RUP.trueClause a (([58, 48, -42, -39, -36] : List Int).map RUP.decode) :=
  g144 a assignment _ (by decide +kernel)

include assignment in
private theorem h473 : RUP.trueClause a (([58, 48, -42, 39, 36] : List Int).map RUP.decode) :=
  g144 a assignment _ (by decide +kernel)

include assignment in
private theorem h474 : RUP.trueClause a (([-58, -48, 42, -39, -36] : List Int).map RUP.decode) :=
  g144 a assignment _ (by decide +kernel)

include assignment in
private theorem h475 : RUP.trueClause a (([-58, -48, 42, 39, -36] : List Int).map RUP.decode) :=
  g144 a assignment _ (by decide +kernel)

include assignment in
private theorem h476 : RUP.trueClause a (([58, 48, -42, -39, 36] : List Int).map RUP.decode) :=
  g144 a assignment _ (by decide +kernel)

include assignment in
private theorem h477 : RUP.trueClause a (([58, -48, -42, -39, 36] : List Int).map RUP.decode) :=
  g144 a assignment _ (by decide +kernel)

include assignment in
private theorem h478 : RUP.trueClause a (([58, -48, 42, 39, 36] : List Int).map RUP.decode) :=
  g144 a assignment _ (by decide +kernel)

include assignment in
private theorem h479 : RUP.trueClause a (([58, -48, 42, -39, -36] : List Int).map RUP.decode) :=
  g144 a assignment _ (by decide +kernel)

include assignment in
private theorem g145 (c) (hc : c ∈ circuitAt [1, 2, 3, 5, 6]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h480 : RUP.trueClause a (([-59, 49, -43, 38, -37] : List Int).map RUP.decode) :=
  g145 a assignment _ (by decide +kernel)

include assignment in
private theorem h481 : RUP.trueClause a (([59, 49, 43, 38, -37] : List Int).map RUP.decode) :=
  g145 a assignment _ (by decide +kernel)

include assignment in
private theorem h482 : RUP.trueClause a (([-59, -49, -43, -38, 37] : List Int).map RUP.decode) :=
  g145 a assignment _ (by decide +kernel)

include assignment in
private theorem h483 : RUP.trueClause a (([-59, -49, -43, -38, -37] : List Int).map RUP.decode) :=
  g145 a assignment _ (by decide +kernel)

include assignment in
private theorem h484 : RUP.trueClause a (([59, 49, 43, 38, 37] : List Int).map RUP.decode) :=
  g145 a assignment _ (by decide +kernel)

include assignment in
private theorem h485 : RUP.trueClause a (([-59, -49, -43, 38, 37] : List Int).map RUP.decode) :=
  g145 a assignment _ (by decide +kernel)

include assignment in
private theorem h486 : RUP.trueClause a (([59, 49, 43, -38, -37] : List Int).map RUP.decode) :=
  g145 a assignment _ (by decide +kernel)

include assignment in
private theorem h487 : RUP.trueClause a (([-59, 49, 43, 38, -37] : List Int).map RUP.decode) :=
  g145 a assignment _ (by decide +kernel)

include assignment in
private theorem h488 : RUP.trueClause a (([-59, 49, -43, -38, -37] : List Int).map RUP.decode) :=
  g145 a assignment _ (by decide +kernel)

include assignment in
private theorem h489 : RUP.trueClause a (([-59, 49, -43, 38, 37] : List Int).map RUP.decode) :=
  g145 a assignment _ (by decide +kernel)

include assignment in
private theorem g146 (c) (hc : c ∈ circuitAt [1, 2, 3, 5, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h490 : RUP.trueClause a (([60, 50, -44, -39, -37] : List Int).map RUP.decode) :=
  g146 a assignment _ (by decide +kernel)

include assignment in
private theorem h491 : RUP.trueClause a (([-60, -50, 44, 39, 37] : List Int).map RUP.decode) :=
  g146 a assignment _ (by decide +kernel)

include assignment in
private theorem h492 : RUP.trueClause a (([-60, -50, -44, 39, 37] : List Int).map RUP.decode) :=
  g146 a assignment _ (by decide +kernel)

include assignment in
private theorem h493 : RUP.trueClause a (([-60, 50, -44, -39, -37] : List Int).map RUP.decode) :=
  g146 a assignment _ (by decide +kernel)

include assignment in
private theorem g147 (c) (hc : c ∈ circuitAt [1, 2, 3, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h494 : RUP.trueClause a (([-61, 51, -45, 39, -38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem h495 : RUP.trueClause a (([61, 51, 45, 39, -38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem h496 : RUP.trueClause a (([-61, -51, -45, -39, 38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem h497 : RUP.trueClause a (([61, 51, -45, -39, -38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem h498 : RUP.trueClause a (([-61, -51, 45, 39, 38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem h499 : RUP.trueClause a (([-61, -51, 45, 39, -38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem h500 : RUP.trueClause a (([-61, -51, -45, 39, 38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem h501 : RUP.trueClause a (([61, 51, 45, -39, -38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem h502 : RUP.trueClause a (([-61, 51, 45, 39, -38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem h503 : RUP.trueClause a (([-61, 51, -45, -39, -38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem h504 : RUP.trueClause a (([61, -51, 45, 39, 38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem h505 : RUP.trueClause a (([-61, 51, -45, 39, 38] : List Int).map RUP.decode) :=
  g147 a assignment _ (by decide +kernel)

include assignment in
private theorem g148 (c) (hc : c ∈ circuitAt [1, 2, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h506 : RUP.trueClause a (([62, 52, 43, 41, -40] : List Int).map RUP.decode) :=
  g148 a assignment _ (by decide +kernel)

include assignment in
private theorem h507 : RUP.trueClause a (([62, 52, -43, 41, 40] : List Int).map RUP.decode) :=
  g148 a assignment _ (by decide +kernel)

include assignment in
private theorem h508 : RUP.trueClause a (([-62, -52, 43, -41, -40] : List Int).map RUP.decode) :=
  g148 a assignment _ (by decide +kernel)

include assignment in
private theorem h509 : RUP.trueClause a (([-62, 52, -43, -41, -40] : List Int).map RUP.decode) :=
  g148 a assignment _ (by decide +kernel)

include assignment in
private theorem g149 (c) (hc : c ∈ circuitAt [1, 2, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h510 : RUP.trueClause a (([63, 53, -44, 42, 40] : List Int).map RUP.decode) :=
  g149 a assignment _ (by decide +kernel)

include assignment in
private theorem h511 : RUP.trueClause a (([-63, -53, 44, -42, -40] : List Int).map RUP.decode) :=
  g149 a assignment _ (by decide +kernel)

include assignment in
private theorem h512 : RUP.trueClause a (([-63, -53, -44, -42, -40] : List Int).map RUP.decode) :=
  g149 a assignment _ (by decide +kernel)

include assignment in
private theorem h513 : RUP.trueClause a (([-63, 53, 44, 42, -40] : List Int).map RUP.decode) :=
  g149 a assignment _ (by decide +kernel)

include assignment in
private theorem g150 (c) (hc : c ∈ circuitAt [1, 2, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h514 : RUP.trueClause a (([64, -54, 45, -42, 41] : List Int).map RUP.decode) :=
  g150 a assignment _ (by decide +kernel)

include assignment in
private theorem h515 : RUP.trueClause a (([-64, 54, -45, 42, -41] : List Int).map RUP.decode) :=
  g150 a assignment _ (by decide +kernel)

include assignment in
private theorem h516 : RUP.trueClause a (([64, 54, 45, 42, -41] : List Int).map RUP.decode) :=
  g150 a assignment _ (by decide +kernel)

include assignment in
private theorem h517 : RUP.trueClause a (([-64, -54, -45, -42, 41] : List Int).map RUP.decode) :=
  g150 a assignment _ (by decide +kernel)

include assignment in
private theorem h518 : RUP.trueClause a (([-64, -54, 45, 42, -41] : List Int).map RUP.decode) :=
  g150 a assignment _ (by decide +kernel)

include assignment in
private theorem h519 : RUP.trueClause a (([64, 54, -45, -42, 41] : List Int).map RUP.decode) :=
  g150 a assignment _ (by decide +kernel)

include assignment in
private theorem h520 : RUP.trueClause a (([-64, -54, -45, -42, -41] : List Int).map RUP.decode) :=
  g150 a assignment _ (by decide +kernel)

include assignment in
private theorem h521 : RUP.trueClause a (([64, -54, -45, -42, 41] : List Int).map RUP.decode) :=
  g150 a assignment _ (by decide +kernel)

include assignment in
private theorem g151 (c) (hc : c ∈ circuitAt [1, 2, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h522 : RUP.trueClause a (([65, 55, 45, 44, -43] : List Int).map RUP.decode) :=
  g151 a assignment _ (by decide +kernel)

include assignment in
private theorem h523 : RUP.trueClause a (([-65, -55, -45, -44, 43] : List Int).map RUP.decode) :=
  g151 a assignment _ (by decide +kernel)

include assignment in
private theorem h524 : RUP.trueClause a (([65, 55, -45, 44, 43] : List Int).map RUP.decode) :=
  g151 a assignment _ (by decide +kernel)

include assignment in
private theorem h525 : RUP.trueClause a (([-65, -55, 45, -44, -43] : List Int).map RUP.decode) :=
  g151 a assignment _ (by decide +kernel)

include assignment in
private theorem h526 : RUP.trueClause a (([-65, -55, 45, 44, -43] : List Int).map RUP.decode) :=
  g151 a assignment _ (by decide +kernel)

include assignment in
private theorem h527 : RUP.trueClause a (([65, -55, 45, 44, 43] : List Int).map RUP.decode) :=
  g151 a assignment _ (by decide +kernel)

include assignment in
private theorem h528 : RUP.trueClause a (([65, -55, 45, -44, -43] : List Int).map RUP.decode) :=
  g151 a assignment _ (by decide +kernel)

include assignment in
private theorem g152 (c) (hc : c ∈ circuitAt [1, 3, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h529 : RUP.trueClause a (([66, -52, 49, -47, 46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h530 : RUP.trueClause a (([-66, 52, -49, 47, -46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h531 : RUP.trueClause a (([66, 52, -49, -47, -46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h532 : RUP.trueClause a (([-66, -52, 49, 47, 46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h533 : RUP.trueClause a (([-66, -52, -49, 47, 46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h534 : RUP.trueClause a (([66, 52, 49, -47, -46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h535 : RUP.trueClause a (([-66, 52, 49, -47, -46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h536 : RUP.trueClause a (([66, -52, -49, 47, 46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h537 : RUP.trueClause a (([-66, 52, 49, 47, 46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h538 : RUP.trueClause a (([66, -52, -49, -47, -46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h539 : RUP.trueClause a (([66, 52, -49, 47, -46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h540 : RUP.trueClause a (([-66, -52, 49, -47, 46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h541 : RUP.trueClause a (([-66, -52, -49, 47, -46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h542 : RUP.trueClause a (([66, 52, 49, -47, 46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h543 : RUP.trueClause a (([-66, 52, 49, 47, -46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h544 : RUP.trueClause a (([66, -52, -49, -47, 46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h545 : RUP.trueClause a (([-66, 52, -49, -47, -46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h546 : RUP.trueClause a (([66, -52, 49, 47, 46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h547 : RUP.trueClause a (([-66, 52, -49, 47, 46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem h548 : RUP.trueClause a (([66, -52, 49, -47, -46] : List Int).map RUP.decode) :=
  g152 a assignment _ (by decide +kernel)

include assignment in
private theorem g153 (c) (hc : c ∈ circuitAt [1, 3, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h549 : RUP.trueClause a (([67, 53, 50, 48, -46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h550 : RUP.trueClause a (([-67, -53, -50, -48, 46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h551 : RUP.trueClause a (([-67, -53, -50, -48, -46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h552 : RUP.trueClause a (([67, 53, 50, 48, 46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h553 : RUP.trueClause a (([-67, -53, -50, 48, 46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h554 : RUP.trueClause a (([67, 53, 50, -48, -46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h555 : RUP.trueClause a (([-67, 53, 50, 48, 46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h556 : RUP.trueClause a (([67, 53, -50, 48, -46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h557 : RUP.trueClause a (([-67, -53, 50, -48, 46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h558 : RUP.trueClause a (([67, 53, 50, -48, 46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h559 : RUP.trueClause a (([-67, 53, 50, 48, -46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h560 : RUP.trueClause a (([67, -53, -50, -48, 46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h561 : RUP.trueClause a (([-67, 53, -50, -48, -46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem h562 : RUP.trueClause a (([-67, 53, -50, 48, 46] : List Int).map RUP.decode) :=
  g153 a assignment _ (by decide +kernel)

include assignment in
private theorem g154 (c) (hc : c ∈ circuitAt [1, 3, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h563 : RUP.trueClause a (([68, 54, -51, 48, 47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem h564 : RUP.trueClause a (([-68, -54, 51, -48, -47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem h565 : RUP.trueClause a (([-68, -54, 51, 48, -47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem h566 : RUP.trueClause a (([-68, -54, -51, -48, -47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem h567 : RUP.trueClause a (([-68, 54, 51, 48, 47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem h568 : RUP.trueClause a (([68, 54, -51, 48, -47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem h569 : RUP.trueClause a (([-68, -54, 51, -48, 47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem h570 : RUP.trueClause a (([-68, -54, -51, 48, -47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem h571 : RUP.trueClause a (([-68, 54, 51, 48, -47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem h572 : RUP.trueClause a (([68, -54, -51, -48, 47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem h573 : RUP.trueClause a (([-68, 54, -51, -48, -47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem h574 : RUP.trueClause a (([68, -54, 51, -48, -47] : List Int).map RUP.decode) :=
  g154 a assignment _ (by decide +kernel)

include assignment in
private theorem g155 (c) (hc : c ∈ circuitAt [1, 3, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h575 : RUP.trueClause a (([69, -55, 51, -50, 49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h576 : RUP.trueClause a (([-69, 55, -51, 50, -49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h577 : RUP.trueClause a (([69, 55, -51, -50, -49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h578 : RUP.trueClause a (([-69, -55, 51, 50, 49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h579 : RUP.trueClause a (([-69, -55, 51, 50, -49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h580 : RUP.trueClause a (([69, 55, -51, -50, 49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h581 : RUP.trueClause a (([-69, 55, 51, 50, 49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h582 : RUP.trueClause a (([69, -55, -51, -50, -49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h583 : RUP.trueClause a (([-69, 55, -51, -50, 49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h584 : RUP.trueClause a (([69, -55, 51, 50, -49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h585 : RUP.trueClause a (([69, 55, -51, 50, -49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h586 : RUP.trueClause a (([-69, -55, 51, -50, 49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h587 : RUP.trueClause a (([-69, -55, -51, 50, -49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h588 : RUP.trueClause a (([69, 55, 51, -50, 49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h589 : RUP.trueClause a (([-69, 55, 51, 50, -49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h590 : RUP.trueClause a (([69, -55, -51, -50, 49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h591 : RUP.trueClause a (([69, -55, 51, 50, 49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h592 : RUP.trueClause a (([-69, 55, -51, 50, 49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem h593 : RUP.trueClause a (([69, -55, 51, -50, -49] : List Int).map RUP.decode) :=
  g155 a assignment _ (by decide +kernel)

include assignment in
private theorem g156 (c) (hc : c ∈ circuitAt [1, 4, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h594 : RUP.trueClause a (([70, -55, 54, -53, 52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h595 : RUP.trueClause a (([-70, 55, -54, 53, -52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h596 : RUP.trueClause a (([-70, -55, 54, 53, -52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h597 : RUP.trueClause a (([70, 55, -54, -53, 52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h598 : RUP.trueClause a (([-70, 55, 54, -53, -52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h599 : RUP.trueClause a (([70, -55, -54, 53, 52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h600 : RUP.trueClause a (([-70, 55, -54, -53, 52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h601 : RUP.trueClause a (([70, -55, 54, 53, -52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h602 : RUP.trueClause a (([-70, -55, 54, -53, 52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h603 : RUP.trueClause a (([-70, -55, -54, 53, -52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h604 : RUP.trueClause a (([70, 55, 54, -53, 52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h605 : RUP.trueClause a (([-70, 55, 54, 53, -52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h606 : RUP.trueClause a (([70, -55, -54, -53, 52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h607 : RUP.trueClause a (([-70, 55, -54, -53, -52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h608 : RUP.trueClause a (([70, -55, 54, 53, 52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h609 : RUP.trueClause a (([-70, 55, -54, 53, 52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem h610 : RUP.trueClause a (([70, -55, 54, -53, -52] : List Int).map RUP.decode) :=
  g156 a assignment _ (by decide +kernel)

include assignment in
private theorem g157 (c) (hc : c ∈ circuitAt [2, 3, 4, 5, 6]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h611 : RUP.trueClause a (([-66, 62, -59, 57, -56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h612 : RUP.trueClause a (([66, 62, -59, -57, -56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h613 : RUP.trueClause a (([-66, -62, 59, 57, 56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h614 : RUP.trueClause a (([-66, -62, 59, 57, -56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h615 : RUP.trueClause a (([66, 62, -59, -57, 56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h616 : RUP.trueClause a (([-66, -62, -59, 57, 56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h617 : RUP.trueClause a (([66, 62, 59, -57, -56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h618 : RUP.trueClause a (([-66, 62, -59, -57, 56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h619 : RUP.trueClause a (([66, -62, 59, 57, -56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h620 : RUP.trueClause a (([66, 62, -59, 57, -56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h621 : RUP.trueClause a (([-66, -62, -59, 57, -56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h622 : RUP.trueClause a (([66, 62, 59, -57, 56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h623 : RUP.trueClause a (([-66, 62, 59, 57, -56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h624 : RUP.trueClause a (([66, -62, -59, -57, 56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h625 : RUP.trueClause a (([-66, 62, -59, -57, -56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h626 : RUP.trueClause a (([66, -62, 59, 57, 56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem h627 : RUP.trueClause a (([-66, 62, -59, 57, 56] : List Int).map RUP.decode) :=
  g157 a assignment _ (by decide +kernel)

include assignment in
private theorem g158 (c) (hc : c ∈ circuitAt [2, 3, 4, 5, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h628 : RUP.trueClause a (([67, -63, 60, -58, 56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h629 : RUP.trueClause a (([67, 63, 60, 58, -56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h630 : RUP.trueClause a (([-67, -63, -60, -58, 56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h631 : RUP.trueClause a (([-67, -63, -60, 58, 56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h632 : RUP.trueClause a (([67, 63, 60, -58, -56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h633 : RUP.trueClause a (([-67, 63, 60, -58, -56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h634 : RUP.trueClause a (([67, -63, -60, 58, 56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h635 : RUP.trueClause a (([-67, 63, -60, -58, 56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h636 : RUP.trueClause a (([67, -63, 60, 58, -56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h637 : RUP.trueClause a (([-67, -63, 60, -58, 56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h638 : RUP.trueClause a (([67, 63, 60, -58, 56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h639 : RUP.trueClause a (([-67, 63, 60, 58, -56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h640 : RUP.trueClause a (([67, -63, -60, -58, 56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h641 : RUP.trueClause a (([-67, 63, -60, -58, -56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem h642 : RUP.trueClause a (([-67, 63, -60, 58, 56] : List Int).map RUP.decode) :=
  g158 a assignment _ (by decide +kernel)

include assignment in
private theorem g159 (c) (hc : c ∈ circuitAt [2, 3, 4, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h643 : RUP.trueClause a (([68, -64, 61, -58, 57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h644 : RUP.trueClause a (([-68, 64, -61, 58, -57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h645 : RUP.trueClause a (([68, 64, -61, 58, 57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h646 : RUP.trueClause a (([-68, -64, 61, -58, -57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h647 : RUP.trueClause a (([-68, -64, 61, 58, -57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h648 : RUP.trueClause a (([68, 64, -61, -58, 57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h649 : RUP.trueClause a (([-68, 64, 61, -58, -57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h650 : RUP.trueClause a (([68, -64, -61, 58, 57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h651 : RUP.trueClause a (([-68, 64, -61, -58, 57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h652 : RUP.trueClause a (([68, -64, 61, 58, -57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h653 : RUP.trueClause a (([68, 64, -61, 58, -57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h654 : RUP.trueClause a (([-68, -64, 61, -58, 57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h655 : RUP.trueClause a (([-68, -64, -61, 58, -57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h656 : RUP.trueClause a (([68, 64, 61, -58, 57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h657 : RUP.trueClause a (([-68, 64, 61, 58, -57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h658 : RUP.trueClause a (([68, -64, -61, -58, 57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h659 : RUP.trueClause a (([-68, 64, -61, -58, -57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h660 : RUP.trueClause a (([68, -64, 61, 58, 57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h661 : RUP.trueClause a (([-68, 64, -61, 58, 57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem h662 : RUP.trueClause a (([68, -64, 61, -58, -57] : List Int).map RUP.decode) :=
  g159 a assignment _ (by decide +kernel)

include assignment in
private theorem g160 (c) (hc : c ∈ circuitAt [2, 3, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h663 : RUP.trueClause a (([69, -65, 61, -60, 59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h664 : RUP.trueClause a (([-69, 65, -61, 60, -59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h665 : RUP.trueClause a (([69, 65, -61, -60, -59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h666 : RUP.trueClause a (([-69, -65, 61, 60, 59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h667 : RUP.trueClause a (([-69, -65, 61, 60, -59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h668 : RUP.trueClause a (([69, 65, -61, -60, 59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h669 : RUP.trueClause a (([-69, -65, -61, 60, 59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h670 : RUP.trueClause a (([69, 65, 61, -60, -59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h671 : RUP.trueClause a (([-69, 65, 61, -60, -59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h672 : RUP.trueClause a (([69, -65, -61, 60, 59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h673 : RUP.trueClause a (([69, 65, -61, 60, -59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h674 : RUP.trueClause a (([-69, -65, 61, -60, 59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h675 : RUP.trueClause a (([-69, -65, -61, 60, -59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h676 : RUP.trueClause a (([69, 65, 61, -60, 59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h677 : RUP.trueClause a (([-69, 65, 61, 60, -59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h678 : RUP.trueClause a (([69, -65, -61, -60, 59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h679 : RUP.trueClause a (([-69, 65, -61, -60, -59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h680 : RUP.trueClause a (([69, -65, 61, 60, 59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h681 : RUP.trueClause a (([-69, 65, -61, 60, 59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem h682 : RUP.trueClause a (([69, -65, 61, -60, -59] : List Int).map RUP.decode) :=
  g160 a assignment _ (by decide +kernel)

include assignment in
private theorem g161 (c) (hc : c ∈ circuitAt [2, 4, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h683 : RUP.trueClause a (([70, -65, 64, -63, 62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h684 : RUP.trueClause a (([-70, 65, -64, 63, -62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h685 : RUP.trueClause a (([-70, -65, 64, 63, -62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h686 : RUP.trueClause a (([70, 65, -64, -63, 62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h687 : RUP.trueClause a (([-70, -65, -64, 63, 62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h688 : RUP.trueClause a (([70, 65, 64, -63, -62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h689 : RUP.trueClause a (([-70, 65, -64, -63, 62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h690 : RUP.trueClause a (([70, -65, 64, 63, -62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h691 : RUP.trueClause a (([70, 65, -64, 63, -62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h692 : RUP.trueClause a (([-70, -65, 64, -63, 62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h693 : RUP.trueClause a (([-70, -65, -64, 63, -62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h694 : RUP.trueClause a (([70, 65, 64, -63, 62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h695 : RUP.trueClause a (([-70, 65, 64, 63, -62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h696 : RUP.trueClause a (([70, -65, -64, -63, 62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h697 : RUP.trueClause a (([-70, 65, -64, -63, -62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h698 : RUP.trueClause a (([70, -65, 64, 63, 62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h699 : RUP.trueClause a (([-70, 65, -64, 63, 62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem h700 : RUP.trueClause a (([70, -65, 64, -63, -62] : List Int).map RUP.decode) :=
  g161 a assignment _ (by decide +kernel)

include assignment in
private theorem g162 (c) (hc : c ∈ circuitAt [3, 4, 5, 6, 7]) : RUP.trueClause a c :=
  assignment c (circuitAt_mem (by decide +kernel) hc)

include assignment in
private theorem h701 : RUP.trueClause a (([-70, -69, -68, -67, -66] : List Int).map RUP.decode) :=
  g162 a assignment _ (by decide +kernel)

include assignment in
private theorem h702 : RUP.trueClause a (([70, 69, 68, 67, 66] : List Int).map RUP.decode) :=
  g162 a assignment _ (by decide +kernel)

include assignment in
private theorem h703 : RUP.trueClause a (([-70, 69, 68, 67, 66] : List Int).map RUP.decode) :=
  g162 a assignment _ (by decide +kernel)

include assignment in
private theorem h704 : RUP.trueClause a (([70, -69, -68, -67, -66] : List Int).map RUP.decode) :=
  g162 a assignment _ (by decide +kernel)

include assignment in
private theorem h705 : RUP.trueClause a (([-70, -69, 68, -67, 66] : List Int).map RUP.decode) :=
  g162 a assignment _ (by decide +kernel)

include assignment in
private theorem h706 : RUP.trueClause a (([70, 69, 68, -67, 66] : List Int).map RUP.decode) :=
  g162 a assignment _ (by decide +kernel)

include assignment in
private theorem h707 : RUP.trueClause a (([-70, 69, 68, 67, -66] : List Int).map RUP.decode) :=
  g162 a assignment _ (by decide +kernel)

include assignment in
private theorem h708 : RUP.trueClause a (([70, -69, 68, 67, 66] : List Int).map RUP.decode) :=
  g162 a assignment _ (by decide +kernel)

include assignment in
private theorem h709 : RUP.trueClause a (([70, -69, 68, -67, -66] : List Int).map RUP.decode) :=
  g162 a assignment _ (by decide +kernel)

include assignment in
private theorem g163 (c) (hc : c ∈ mixedAt 0) : RUP.trueClause a c :=
  assignment c (mixedAt_mem (by decide +kernel) hc)

include assignment in
private theorem h710 : RUP.trueClause a (([-71, -32, 34] : List Int).map RUP.decode) :=
  g163 a assignment _ (by decide +kernel)

include assignment in
private theorem h711 : RUP.trueClause a (([-71, 32, -34] : List Int).map RUP.decode) :=
  g163 a assignment _ (by decide +kernel)

include assignment in
private theorem h712 : RUP.trueClause a (([-72, -33, -34] : List Int).map RUP.decode) :=
  g163 a assignment _ (by decide +kernel)

include assignment in
private theorem h713 : RUP.trueClause a (([-72, 33, 34] : List Int).map RUP.decode) :=
  g163 a assignment _ (by decide +kernel)

include assignment in
private theorem h714 : RUP.trueClause a (([-73, 32, 35] : List Int).map RUP.decode) :=
  g163 a assignment _ (by decide +kernel)

include assignment in
private theorem h715 : RUP.trueClause a (([-73, -32, -35] : List Int).map RUP.decode) :=
  g163 a assignment _ (by decide +kernel)

include assignment in
private theorem h716 : RUP.trueClause a (([-74, 33, -35] : List Int).map RUP.decode) :=
  g163 a assignment _ (by decide +kernel)

include assignment in
private theorem h717 : RUP.trueClause a (([-74, -33, 35] : List Int).map RUP.decode) :=
  g163 a assignment _ (by decide +kernel)

include assignment in
private theorem h718 : RUP.trueClause a (([71, 72, 73, 74] : List Int).map RUP.decode) :=
  g163 a assignment _ (by decide +kernel)

include assignment in
private theorem g164 (c) (hc : c ∈ mixedAt 1) : RUP.trueClause a c :=
  assignment c (mixedAt_mem (by decide +kernel) hc)

include assignment in
private theorem h719 : RUP.trueClause a (([-75, -46, 49, 50] : List Int).map RUP.decode) :=
  g164 a assignment _ (by decide +kernel)

include assignment in
private theorem h720 : RUP.trueClause a (([-75, 46, -49, -50] : List Int).map RUP.decode) :=
  g164 a assignment _ (by decide +kernel)

include assignment in
private theorem h721 : RUP.trueClause a (([-76, -47, -49, 51] : List Int).map RUP.decode) :=
  g164 a assignment _ (by decide +kernel)

include assignment in
private theorem h722 : RUP.trueClause a (([-76, 47, 49, -51] : List Int).map RUP.decode) :=
  g164 a assignment _ (by decide +kernel)

include assignment in
private theorem h723 : RUP.trueClause a (([-77, 46, 52, 53] : List Int).map RUP.decode) :=
  g164 a assignment _ (by decide +kernel)

include assignment in
private theorem h724 : RUP.trueClause a (([-77, -46, -52, -53] : List Int).map RUP.decode) :=
  g164 a assignment _ (by decide +kernel)

include assignment in
private theorem h725 : RUP.trueClause a (([-78, 48, -53, -54] : List Int).map RUP.decode) :=
  g164 a assignment _ (by decide +kernel)

include assignment in
private theorem h726 : RUP.trueClause a (([-78, -48, 53, 54] : List Int).map RUP.decode) :=
  g164 a assignment _ (by decide +kernel)

include assignment in
private theorem h727 : RUP.trueClause a (([-79, 51, 54, 55] : List Int).map RUP.decode) :=
  g164 a assignment _ (by decide +kernel)

include assignment in
private theorem h728 : RUP.trueClause a (([-79, -51, -54, -55] : List Int).map RUP.decode) :=
  g164 a assignment _ (by decide +kernel)

include assignment in
private theorem h729 : RUP.trueClause a (([75, 76, 77, 78, 79] : List Int).map RUP.decode) :=
  g164 a assignment _ (by decide +kernel)

include assignment in
private theorem g165 (c) (hc : c ∈ mixedAt 2) : RUP.trueClause a c :=
  assignment c (mixedAt_mem (by decide +kernel) hc)

include assignment in
private theorem h730 : RUP.trueClause a (([-80, 56, 57, 58] : List Int).map RUP.decode) :=
  g165 a assignment _ (by decide +kernel)

include assignment in
private theorem h731 : RUP.trueClause a (([-80, -56, -57, -58] : List Int).map RUP.decode) :=
  g165 a assignment _ (by decide +kernel)

include assignment in
private theorem h732 : RUP.trueClause a (([-81, -58, -60, -61] : List Int).map RUP.decode) :=
  g165 a assignment _ (by decide +kernel)

include assignment in
private theorem h733 : RUP.trueClause a (([-81, 58, 60, 61] : List Int).map RUP.decode) :=
  g165 a assignment _ (by decide +kernel)

include assignment in
private theorem h734 : RUP.trueClause a (([-82, 56, 62, 63] : List Int).map RUP.decode) :=
  g165 a assignment _ (by decide +kernel)

include assignment in
private theorem h735 : RUP.trueClause a (([-82, -56, -62, -63] : List Int).map RUP.decode) :=
  g165 a assignment _ (by decide +kernel)

include assignment in
private theorem h736 : RUP.trueClause a (([-83, 59, 62, 65] : List Int).map RUP.decode) :=
  g165 a assignment _ (by decide +kernel)

include assignment in
private theorem h737 : RUP.trueClause a (([-83, -59, -62, -65] : List Int).map RUP.decode) :=
  g165 a assignment _ (by decide +kernel)

include assignment in
private theorem h738 : RUP.trueClause a (([-84, 61, 64, 65] : List Int).map RUP.decode) :=
  g165 a assignment _ (by decide +kernel)

include assignment in
private theorem h739 : RUP.trueClause a (([-84, -61, -64, -65] : List Int).map RUP.decode) :=
  g165 a assignment _ (by decide +kernel)

include assignment in
private theorem h740 : RUP.trueClause a (([80, 81, 82, 83, 84] : List Int).map RUP.decode) :=
  g165 a assignment _ (by decide +kernel)

include assignment in
private theorem h741 : RUP.trueClause a (([-61, 18, -39, -19, -38] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[1], [-1, -61, 18, -39, -19, -38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h0 a assignment
  · exact h49 a assignment

include assignment in
private theorem h742 : RUP.trueClause a (([-61, -18, 39, -19, -38] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[1], [-1, -61, -18, 39, -19, -38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h0 a assignment
  · exact h48 a assignment

include assignment in
private theorem h743 : RUP.trueClause a (([58, 16, 39, -19, 36] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[1], [-1, 58, 16, 39, -19, 36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h0 a assignment
  · exact h47 a assignment

include assignment in
private theorem h744 : RUP.trueClause a (([60, 61, -69, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-69, -65, 61, 60, 59], [-69, -65, 61, 60, -59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h666 a assignment
  · exact h667 a assignment

include assignment in
private theorem h745 : RUP.trueClause a (([-58, 61, -68, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-68, -64, 61, -58, -57], [-68, -64, 61, -58, 57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h646 a assignment
  · exact h654 a assignment

include assignment in
private theorem h746 : RUP.trueClause a (([58, -61, -68, 64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-68, 64, -61, 58, 57], [-68, 64, -61, 58, -57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h661 a assignment
  · exact h644 a assignment

include assignment in
private theorem h747 : RUP.trueClause a (([63, 65, -70, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, 65, -64, 63, 62], [-70, 65, -64, 63, -62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h699 a assignment
  · exact h684 a assignment

include assignment in
private theorem h748 : RUP.trueClause a (([-63, 65, -70, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, 65, -64, -63, 62], [-70, 65, -64, -63, -62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h689 a assignment
  · exact h697 a assignment

include assignment in
private theorem h749 : RUP.trueClause a (([65, -64, -70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[63, 65, -70, -64], [-63, 65, -70, -64]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h747 a assignment
  · exact h748 a assignment

include assignment in
private theorem h750 : RUP.trueClause a (([-58, -61, -68, 64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-68, 64, -61, -58, 57], [-68, 64, -61, -58, -57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h651 a assignment
  · exact h659 a assignment

include assignment in
private theorem h751 : RUP.trueClause a (([-61, 64, -68] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[58, -61, -68, 64], [-58, -61, -68, 64]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h746 a assignment
  · exact h750 a assignment

include assignment in
private theorem h752 : RUP.trueClause a (([60, -61, -69, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-69, -65, -61, 60, -59], [-69, -65, -61, 60, 59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h675 a assignment
  · exact h669 a assignment

include assignment in
private theorem h753 : RUP.trueClause a (([58, -61, 68, 64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[68, 64, -61, 58, -57], [68, 64, -61, 58, 57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h653 a assignment
  · exact h645 a assignment

include assignment in
private theorem h754 : RUP.trueClause a (([-60, 61, 69, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[69, -65, 61, -60, 59], [69, -65, 61, -60, -59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h663 a assignment
  · exact h682 a assignment

include assignment in
private theorem h755 : RUP.trueClause a (([-58, 61, 68, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[68, -64, 61, -58, 57], [68, -64, 61, -58, -57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h643 a assignment
  · exact h662 a assignment

include assignment in
private theorem h756 : RUP.trueClause a (([65, 69, 61, -60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[69, 65, 61, -60, 59], [69, 65, 61, -60, -59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h676 a assignment
  · exact h670 a assignment

include assignment in
private theorem h757 : RUP.trueClause a (([58, 61, 68, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[68, -64, 61, 58, -57], [68, -64, 61, 58, 57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h652 a assignment
  · exact h660 a assignment

include assignment in
private theorem h758 : RUP.trueClause a (([68, 61, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-58, 61, 68, -64], [58, 61, 68, -64]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h755 a assignment
  · exact h757 a assignment

include assignment in
private theorem h759 : RUP.trueClause a (([-63, -58, 56, 60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[67, -63, 60, -58, 56], [-67, -63, 60, -58, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h628 a assignment
  · exact h637 a assignment

include assignment in
private theorem h760 : RUP.trueClause a (([-60, 65, 69, -61] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[69, 65, -61, -60, -59], [69, 65, -61, -60, 59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h665 a assignment
  · exact h668 a assignment

include assignment in
private theorem h761 : RUP.trueClause a (([62, -65, 70, 64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, -65, 64, -63, 62], [70, -65, 64, 63, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h683 a assignment
  · exact h698 a assignment

include assignment in
private theorem h762 : RUP.trueClause a (([-58, 60, -56, 63] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[67, 63, 60, -58, -56], [-67, 63, 60, -58, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h632 a assignment
  · exact h633 a assignment

include assignment in
private theorem h763 : RUP.trueClause a (([63, -62, 64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, -65, 64, 63, -62], [70, -65, 64, 63, -62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h685 a assignment
  · exact h690 a assignment

include assignment in
private theorem h764 : RUP.trueClause a (([-60, -58, 56, -63] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-67, -63, -60, -58, 56], [67, -63, -60, -58, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h630 a assignment
  · exact h640 a assignment

include assignment in
private theorem h765 : RUP.trueClause a (([-58, -63, 56] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-63, -58, 56, 60], [-60, -58, 56, -63]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h759 a assignment
  · exact h764 a assignment

include assignment in
private theorem h766 : RUP.trueClause a (([-60, -63, 56, 58] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-67, -63, -60, 58, 56], [67, -63, -60, 58, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h631 a assignment
  · exact h634 a assignment

include assignment in
private theorem h767 : RUP.trueClause a (([-60, 65, -59, 61] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-69, 65, 61, -60, -59], [65, 69, 61, -60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h671 a assignment
  · exact h756 a assignment

include assignment in
private theorem h768 : RUP.trueClause a (([-48, 51, -68, -54] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-68, -54, 51, -48, 47], [-68, -54, 51, -48, -47]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h569 a assignment
  · exact h564 a assignment

include assignment in
private theorem h769 : RUP.trueClause a (([48, 51, -68, 54] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-68, 54, 51, 48, -47], [-68, 54, 51, 48, 47]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h571 a assignment
  · exact h567 a assignment

include assignment in
private theorem h770 : RUP.trueClause a (([50, 51, 69, -55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[69, -55, 51, 50, -49], [69, -55, 51, 50, 49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h584 a assignment
  · exact h591 a assignment

include assignment in
private theorem h771 : RUP.trueClause a (([-50, -51, 69, -55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[69, -55, -51, -50, 49], [69, -55, -51, -50, -49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h590 a assignment
  · exact h582 a assignment

include assignment in
private theorem h772 : RUP.trueClause a (([-50, -51, 69, 55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[69, 55, -51, -50, 49], [69, 55, -51, -50, -49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h580 a assignment
  · exact h577 a assignment

include assignment in
private theorem h773 : RUP.trueClause a (([53, -54, -70, 55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, 55, -54, 53, -52], [-70, 55, -54, 53, 52]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h595 a assignment
  · exact h609 a assignment

include assignment in
private theorem h774 : RUP.trueClause a (([49, -47, 66, -46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[66, -52, 49, -47, -46], [66, 52, 49, -47, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h548 a assignment
  · exact h534 a assignment

include assignment in
private theorem h775 : RUP.trueClause a (([-43, 45, -65, -55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65, -55, 45, 44, -43], [-65, -55, 45, -44, -43]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h526 a assignment
  · exact h525 a assignment

include assignment in
private theorem h776 : RUP.trueClause a (([51, -50, 69, -55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[69, -55, 51, -50, -49], [69, -55, 51, -50, 49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h593 a assignment
  · exact h575 a assignment

include assignment in
private theorem h777 : RUP.trueClause a (([51, -55, 69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[50, 51, 69, -55], [51, -50, 69, -55]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h770 a assignment
  · exact h776 a assignment

include assignment in
private theorem h778 : RUP.trueClause a (([33, -32, -70, 35] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, 35, -34, 33, -32], [-70, 35, 34, 33, -32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h432 a assignment
  · exact h445 a assignment

include assignment in
private theorem h779 : RUP.trueClause a (([-15, -14, -55, -35] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-55, -35, -15, -14, -13], [-55, -35, -15, -14, 13]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h393 a assignment
  · exact h392 a assignment

include assignment in
private theorem h780 : RUP.trueClause a (([12, 34, 54, 15] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[54, 34, 15, 12, -11], [54, 34, 15, 12, 11]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h390 a assignment
  · exact h391 a assignment

include assignment in
private theorem h781 : RUP.trueClause a (([-35, -74, 54, 53, -55, -70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-74, 33, -35], [14, -70, -33, -55, -35, 53], [-15, -14, -55, -35], [15, -70, -34, -55, -35, 54], [-12, -55, -14, 54, 15, 53], [12, 34, 54, 15]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h716 a assignment
  · exact h332 a assignment
  · exact h779 a assignment
  · exact h358 a assignment
  · exact h41 a assignment
  · exact h780 a assignment

include assignment in
private theorem h782 : RUP.trueClause a (([33, 32, -70, 35] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, 35, -34, 33, 32], [-70, 35, 34, 33, 32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h449 a assignment
  · exact h439 a assignment

include assignment in
private theorem h783 : RUP.trueClause a (([33, 35, -70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[33, -32, -70, 35], [33, 32, -70, 35]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h778 a assignment
  · exact h782 a assignment

include assignment in
private theorem h784 : RUP.trueClause a (([-74, 54, -70, 53, -55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-35, -74, 54, 53, -55, -70], [-74, -33, 35], [33, 35, -70]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h781 a assignment
  · exact h717 a assignment
  · exact h783 a assignment

include assignment in
private theorem h785 : RUP.trueClause a (([34, 35, 54, 53, -55, -70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[33, 35, -70], [-15, -70, 34, -55, 35, 54], [-12, -70, -33, 54, 34, 53], [12, 34, 54, 15]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h783 a assignment
  · exact h359 a assignment
  · exact h275 a assignment
  · exact h780 a assignment

include assignment in
private theorem h786 : RUP.trueClause a (([32, 72, -34, 35, 74] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-73, 32, 35], [-71, 32, -34], [71, 72, 73, 74]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h714 a assignment
  · exact h711 a assignment
  · exact h718 a assignment

include assignment in
private theorem h787 : RUP.trueClause a (([35, 54, 53, -55, -70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-74, 54, -70, 53, -55], [33, 35, -70], [34, 35, 54, 53, -55, -70], [-72, -33, -34], [32, 72, -34, 35, 74], [-70, 35, -34, -33, -32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h784 a assignment
  · exact h783 a assignment
  · exact h785 a assignment
  · exact h712 a assignment
  · exact h786 a assignment
  · exact h447 a assignment

include assignment in
private theorem h788 : RUP.trueClause a (([-14, 54, 53, -55, -70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[35, 54, 53, -55, -70], [-15, -14, -55, -35], [15, -70, -34, -55, -35, 54], [-12, -55, -14, 54, 15, 53], [12, 34, 54, 15]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h787 a assignment
  · exact h779 a assignment
  · exact h358 a assignment
  · exact h41 a assignment
  · exact h780 a assignment

include assignment in
private theorem h789 : RUP.trueClause a (([-32, 72, 34, -35, 74] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-73, -32, -35], [-71, -32, 34], [71, 72, 73, 74]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h715 a assignment
  · exact h710 a assignment
  · exact h718 a assignment

include assignment in
private theorem h790 : RUP.trueClause a (([32, 10, 52, 11] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[52, 32, 13, 11, 10], [52, 32, -13, 11, 10]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h387 a assignment
  · exact h386 a assignment

include assignment in
private theorem h791 : RUP.trueClause a (([21, 20, 62, 32] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[62, 32, 23, 21, 20], [62, 32, -23, 21, 20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h403 a assignment
  · exact h398 a assignment

include assignment in
private theorem h792 : RUP.trueClause a (([34, 33, -35, 74, -63, -70, -64, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-72, 33, 34], [-32, 72, 34, -35, 74], [-20, -70, 32, -63, 33, 62], [-21, -70, 32, -64, 34, 62], [21, 20, 62, 32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h713 a assignment
  · exact h789 a assignment
  · exact h230 a assignment
  · exact h250 a assignment
  · exact h791 a assignment

include assignment in
private theorem h793 : RUP.trueClause a (([-34, 33, -70, -35] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, -35, -34, 33, -32], [-70, -35, -34, 33, 32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h443 a assignment
  · exact h435 a assignment

include assignment in
private theorem h794 : RUP.trueClause a (([33, -35, 62, 74, -63, -70, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[34, 33, -35, 74, -63, -70, -64, 62], [-34, 33, -70, -35]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h792 a assignment
  · exact h793 a assignment

include assignment in
private theorem h795 : RUP.trueClause a (([33, -35, -63, -70, -64, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-74, 33, -35], [33, -35, 62, 74, -63, -70, -64]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h716 a assignment
  · exact h794 a assignment

include assignment in
private theorem h796 : RUP.trueClause a (([-51, 55, -63, 56, -67, -70, 58, -68, 69, 60, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-50, -51, 69, 55], [48, 69, 50, -68, -51, -67], [50, -70, 53, 69, 55, -67], [44, 69, 50, -65, 55, 60], [42, -67, -48, -63, -53, 58], [-67, -53, 50, -48, 46], [-63, -53, -44, -42, -40], [40, -67, -46, -63, -53, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h772 a assignment
  · exact h221 a assignment
  · exact h352 a assignment
  · exact h346 a assignment
  · exact h284 a assignment
  · exact h557 a assignment
  · exact h512 a assignment
  · exact h240 a assignment

include assignment in
private theorem h797 : RUP.trueClause a (([-54, -53, -70, 55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, 55, -54, -53, 52], [-70, 55, -54, -53, -52]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h600 a assignment
  · exact h607 a assignment

include assignment in
private theorem h798 : RUP.trueClause a (([-54, 55, -70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[53, -54, -70, 55], [-54, -53, -70, 55]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h773 a assignment
  · exact h797 a assignment

include assignment in
private theorem h799 : RUP.trueClause a (([51, 55, -70, 69, -68] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[51, -70, 54, 69, 55, -68], [-54, 55, -70]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h378 a assignment
  · exact h798 a assignment

include assignment in
private theorem h800 : RUP.trueClause a (([55, -63, -65, 56, -67, -70, 58, -68, 69, 60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-51, 55, -63, 56, -67, -70, 58, -68, 69, 60, -65], [51, 55, -70, 69, -68]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h796 a assignment
  · exact h799 a assignment

include assignment in
private theorem h801 : RUP.trueClause a (([62, -56, -59, -57] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-66, 62, -59, -57, -56], [66, 62, -59, -57, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h625 a assignment
  · exact h612 a assignment

include assignment in
private theorem h802 : RUP.trueClause a (([53, 54, -55, -66, 67, -69, -70, 68] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, -55, 54, 53, -52], [47, -70, 52, 68, 54, -66], [-49, -70, 52, -69, -55, -66], [46, -70, 52, 67, 53, -66], [-66, 52, 49, -47, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h596 a assignment
  · exact h262 a assignment
  · exact h327 a assignment
  · exact h243 a assignment
  · exact h535 a assignment

include assignment in
private theorem h803 : RUP.trueClause a (([48, 54, 68, -51] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[68, 54, -51, 48, -47], [68, 54, -51, 48, 47]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h568 a assignment
  · exact h563 a assignment

include assignment in
private theorem h804 : RUP.trueClause a (([54, -51, -55, -66, 67, -69, -70, 68] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[53, 54, -55, -66, 67, -69, -70, 68], [-48, -70, -53, 68, 54, 67], [48, 54, 68, -51]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h802 a assignment
  · exact h295 a assignment
  · exact h803 a assignment

include assignment in
private theorem h805 : RUP.trueClause a (([-52, 46, -66, 47] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-66, -52, 49, 47, 46], [-66, -52, -49, 47, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h532 a assignment
  · exact h533 a assignment

include assignment in
private theorem h806 : RUP.trueClause a (([33, -35, 52, -53, -54, -70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-74, 33, -35], [-34, 33, -70, -35], [-72, 33, 34], [-32, 72, 34, -35, 74], [-10, -70, 32, -53, 33, 52], [-11, -70, 32, -54, 34, 52], [32, 10, 52, 11]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h716 a assignment
  · exact h793 a assignment
  · exact h713 a assignment
  · exact h789 a assignment
  · exact h226 a assignment
  · exact h247 a assignment
  · exact h790 a assignment

include assignment in
private theorem h807 : RUP.trueClause a (([-12, -10, -53, -33] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-53, -33, -14, -12, -10], [-53, -33, 14, -12, -10]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h389 a assignment
  · exact h388 a assignment

include assignment in
private theorem h808 : RUP.trueClause a (([34, -35, 52, -53, -54, -70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[33, -35, 52, -53, -54, -70], [-70, -35, 34, -33, 32], [12, -70, -33, -54, 34, -53], [10, -70, -32, -53, -33, 52], [-12, -10, -53, -33]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h806 a assignment
  · exact h442 a assignment
  · exact h274 a assignment
  · exact h225 a assignment
  · exact h807 a assignment

include assignment in
private theorem h809 : RUP.trueClause a (([-25, -24, -65, -35] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65, -35, -25, -24, -23], [-65, -35, -25, -24, 23]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h420 a assignment
  · exact h417 a assignment

include assignment in
private theorem h810 : RUP.trueClause a (([-34, 35, -70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[33, 35, -70], [-74, -33, 35], [-72, -33, -34], [-70, 35, -34, -33, -32], [32, 72, -34, 35, 74]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h783 a assignment
  · exact h717 a assignment
  · exact h712 a assignment
  · exact h447 a assignment
  · exact h786 a assignment

include assignment in
private theorem h811 : RUP.trueClause a (([22, 25, 64, 34] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[64, 34, 25, 22, 21], [64, 34, 25, 22, -21]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h413 a assignment
  · exact h410 a assignment

include assignment in
private theorem h812 : RUP.trueClause a (([35, 63, -70, 64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[33, 35, -70], [-34, 35, -70], [-25, -70, 34, -65, 35, 64], [-22, -70, -33, 64, 34, 63], [22, 25, 64, 34]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h783 a assignment
  · exact h810 a assignment
  · exact h364 a assignment
  · exact h282 a assignment
  · exact h811 a assignment

include assignment in
private theorem h813 : RUP.trueClause a (([25, 63, -70, 64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[35, 63, -70, 64, -65], [63, -62, 64, -65], [25, -70, -34, -65, -35, 64], [22, 25, 64, 34], [-22, -70, -33, 64, 34, 63], [64, 34, 25, -22, -21], [-74, 33, -35], [-72, 33, 34], [-20, 64, 21, 63, -22, 62], [-32, 72, 34, -35, 74], [21, 20, 62, 32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h812 a assignment
  · exact h763 a assignment
  · exact h361 a assignment
  · exact h811 a assignment
  · exact h282 a assignment
  · exact h415 a assignment
  · exact h716 a assignment
  · exact h713 a assignment
  · exact h72 a assignment
  · exact h789 a assignment
  · exact h791 a assignment

include assignment in
private theorem h814 : RUP.trueClause a (([70, 64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[62, -65, 70, 64], [63, -62, 64, -65], [70, -65, 64, -63, -62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h761 a assignment
  · exact h763 a assignment
  · exact h700 a assignment

include assignment in
private theorem h815 : RUP.trueClause a (([-63, 70, 65, 64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, 65, 64, -63, 62], [70, 65, 64, -63, -62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h694 a assignment
  · exact h688 a assignment

include assignment in
private theorem h816 : RUP.trueClause a (([22, 20, 63, 33] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[63, 33, -24, 22, 20], [63, 33, 24, 22, 20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h404 a assignment
  · exact h409 a assignment

include assignment in
private theorem h817 : RUP.trueClause a (([20, -21, -32, 33, 34, 63] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[20, 34, -21, 33, -22, -32], [22, 20, 63, 33]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h4 a assignment
  · exact h816 a assignment

include assignment in
private theorem h818 : RUP.trueClause a (([-20, -21, -62, -32] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-62, -32, -23, -21, -20], [-62, -32, 23, -21, -20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h402 a assignment
  · exact h399 a assignment

include assignment in
private theorem h819 : RUP.trueClause a (([-21, -32, 33, 34, -62, 63] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[20, -21, -32, 33, 34, 63], [-20, -21, -62, -32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h817 a assignment
  · exact h818 a assignment

include assignment in
private theorem h820 : RUP.trueClause a (([33, 35, 34, -25, -62, 63, 70, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, 35, 34, 33, 32], [-21, -32, 33, 34, -62, 63], [21, 35, -23, 34, -25, -32], [-62, -32, 23, 21, -20], [65, 35, -25, 24, 23], [22, 20, 63, 33], [63, 33, -24, -22, 20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h434 a assignment
  · exact h819 a assignment
  · exact h8 a assignment
  · exact h400 a assignment
  · exact h418 a assignment
  · exact h816 a assignment
  · exact h407 a assignment

include assignment in
private theorem h821 : RUP.trueClause a (([-33, 35, 70, 34] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, 35, 34, -33, -32], [70, 35, 34, -33, 32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h436 a assignment
  · exact h444 a assignment

include assignment in
private theorem h822 : RUP.trueClause a (([35, 34, 65, -25, -62, 63, 70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[33, 35, 34, -25, -62, 63, 70, 65], [-33, 35, 70, 34]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h820 a assignment
  · exact h821 a assignment

include assignment in
private theorem h823 : RUP.trueClause a (([34, -25, -62, 70, 64, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-63, 70, 65, 64], [-25, 70, 34, 65, -35, 64], [35, 34, 65, -25, -62, 63, 70]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h815 a assignment
  · exact h363 a assignment
  · exact h822 a assignment

include assignment in
private theorem h824 : RUP.trueClause a (([-33, 35, -34, -62, 63, 70, 64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-74, -33, 35], [-72, -33, -34], [32, 72, -34, 35, 74], [21, 70, -32, 64, -34, -62], [20, 70, -32, 63, -33, -62], [-20, -21, -62, -32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h717 a assignment
  · exact h712 a assignment
  · exact h786 a assignment
  · exact h249 a assignment
  · exact h227 a assignment
  · exact h818 a assignment

include assignment in
private theorem h825 : RUP.trueClause a (([35, -34, 64, -62, 63, 70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-33, 35, -34, -62, 63, 70, 64], [-22, 70, 33, 64, -34, 63], [70, 35, -34, 33, -32], [22, 20, 63, 33], [-20, 70, 32, 63, 33, -62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h824 a assignment
  · exact h281 a assignment
  · exact h441 a assignment
  · exact h816 a assignment
  · exact h229 a assignment

include assignment in
private theorem h826 : RUP.trueClause a (([33, -34, -62, 63, 70, 64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[35, -34, 64, -62, 63, 70], [-22, 70, 33, 64, -34, 63], [70, -35, -34, 33, 32], [22, 20, 63, 33], [21, 70, -32, 64, -34, -62], [-20, -21, -62, -32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h825 a assignment
  · exact h281 a assignment
  · exact h438 a assignment
  · exact h816 a assignment
  · exact h249 a assignment
  · exact h818 a assignment

include assignment in
private theorem h827 : RUP.trueClause a (([-33, -35, 70, -34] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, -35, -34, -33, 32], [70, -35, -34, -33, -32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h446 a assignment
  · exact h440 a assignment

include assignment in
private theorem h828 : RUP.trueClause a (([-34, 70, 64, -62, 63] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[35, -34, 64, -62, 63, 70], [33, -34, -62, 63, 70, 64], [-33, -35, 70, -34]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h825 a assignment
  · exact h826 a assignment
  · exact h827 a assignment

include assignment in
private theorem h829 : RUP.trueClause a (([-33, -35, 70, 34] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, -35, 34, -33, -32], [70, -35, 34, -33, 32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h450 a assignment
  · exact h431 a assignment

include assignment in
private theorem h830 : RUP.trueClause a (([-35, 34, 70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-33, -35, 70, 34], [-74, 33, -35], [-72, 33, 34], [70, -35, 34, 33, 32], [-32, 72, 34, -35, 74]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h829 a assignment
  · exact h716 a assignment
  · exact h713 a assignment
  · exact h448 a assignment
  · exact h789 a assignment

include assignment in
private theorem h831 : RUP.trueClause a (([70, -61, 64, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-61, 64, -68], [58, -61, 68, 64], [68, 64, -61, -58, 57], [-63, 70, 65, 64], [-58, 65, 60, 64, -61, 63], [-58, 70, 63, 68, 64, -67], [-60, 65, 69, -61], [70, -69, 68, 67, 66], [-57, 70, 62, 68, 64, -66], [-34, 70, 64, -62, 63], [34, -25, -62, 70, 64, 65], [22, 25, 64, 34], [-22, 68, 28, 64, 34, -58], [-19, 64, -22, -61, 25, -58], [64, 34, 25, -22, -21], [16, 64, 21, -58, -22, -57], [-35, 34, 70], [31, 70, 34, -69, 35, 68], [-33, 35, 70, 34], [-28, 35, 30, 34, -31, 33], [-61, -31, 25, 19, 18], [-69, 35, -31, -30, -29], [70, 35, 34, 33, 32], [67, 33, -30, -28, 26], [-57, -27, 21, -18, -16], [-66, -32, 29, 27, -26]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h751 a assignment
  · exact h753 a assignment
  · exact h648 a assignment
  · exact h815 a assignment
  · exact h141 a assignment
  · exact h297 a assignment
  · exact h760 a assignment
  · exact h708 a assignment
  · exact h273 a assignment
  · exact h828 a assignment
  · exact h823 a assignment
  · exact h811 a assignment
  · exact h277 a assignment
  · exact h129 a assignment
  · exact h415 a assignment
  · exact h70 a assignment
  · exact h830 a assignment
  · exact h365 a assignment
  · exact h821 a assignment
  · exact h13 a assignment
  · exact h396 a assignment
  · exact h430 a assignment
  · exact h434 a assignment
  · exact h426 a assignment
  · exact h394 a assignment
  · exact h424 a assignment

include assignment in
private theorem h832 : RUP.trueClause a (([24, 35, 65, 25] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[65, 35, 25, 24, 23], [65, 35, 25, 24, -23]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h421 a assignment
  · exact h416 a assignment

include assignment in
private theorem h833 : RUP.trueClause a (([34, -63, -64, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[65, -64, -70], [-35, 34, 70], [-25, 70, 34, 65, 35, -64], [-33, 35, 70, 34], [-24, 70, 33, 65, 35, -63], [24, 35, 65, 25]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h749 a assignment
  · exact h830 a assignment
  · exact h362 a assignment
  · exact h821 a assignment
  · exact h339 a assignment
  · exact h832 a assignment

include assignment in
private theorem h834 : RUP.trueClause a (([25, 35, -34, -63, -62, 70, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[24, 35, 65, 25], [-24, 70, 33, 65, 35, -63], [65, 35, 25, -24, -23], [-74, -33, 35], [-72, -33, -34], [20, 65, 23, -63, -24, -62], [32, 72, -34, 35, 74], [-20, -21, -62, -32], [-62, -32, 23, 21, -20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h832 a assignment
  · exact h339 a assignment
  · exact h423 a assignment
  · exact h717 a assignment
  · exact h712 a assignment
  · exact h91 a assignment
  · exact h786 a assignment
  · exact h818 a assignment
  · exact h400 a assignment

include assignment in
private theorem h835 : RUP.trueClause a (([-21, -23, -32, -62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-20, -21, -62, -32], [-62, -32, -23, -21, 20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h818 a assignment
  · exact h397 a assignment

include assignment in
private theorem h836 : RUP.trueClause a (([21, -25, -64, -34] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, -34, -25, 22, 21], [-64, -34, -25, -22, 21]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h414 a assignment
  · exact h411 a assignment

include assignment in
private theorem h837 : RUP.trueClause a (([35, -62, -64, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[65, -64, -70], [70, 65, -64, 63, -62], [34, -63, -64, 65], [25, 35, -34, -63, -62, 70, 65], [21, -25, -64, -34], [-64, -34, -25, -22, -21], [22, 70, 33, -64, -34, -63], [20, -64, -21, -63, 22, -62], [-74, -33, 35], [-72, -33, -34], [-20, -21, -62, -32], [32, 72, -34, 35, 74]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h749 a assignment
  · exact h691 a assignment
  · exact h833 a assignment
  · exact h834 a assignment
  · exact h836 a assignment
  · exact h412 a assignment
  · exact h278 a assignment
  · exact h71 a assignment
  · exact h717 a assignment
  · exact h712 a assignment
  · exact h818 a assignment
  · exact h786 a assignment

include assignment in
private theorem h838 : RUP.trueClause a (([-62, 65, 70, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, 65, -64, 63, -62], [34, -63, -64, 65], [35, -62, -64, 65], [-33, -35, 70, -34], [25, 70, -34, 65, -35, -64], [22, 70, 33, -64, -34, -63], [21, -25, -64, -34], [-64, -34, -25, -22, -21]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h691 a assignment
  · exact h833 a assignment
  · exact h837 a assignment
  · exact h827 a assignment
  · exact h360 a assignment
  · exact h278 a assignment
  · exact h836 a assignment
  · exact h412 a assignment

include assignment in
private theorem h839 : RUP.trueClause a (([57, -56, -59, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[66, 62, -59, 57, -56], [-66, 62, -59, 57, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h620 a assignment
  · exact h611 a assignment

include assignment in
private theorem h840 : RUP.trueClause a (([-56, -59, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[62, -56, -59, -57], [57, -56, -59, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h801 a assignment
  · exact h839 a assignment

include assignment in
private theorem h841 : RUP.trueClause a (([-61, -60, -59, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-69, 65, -61, -60, -59], [-60, 65, 69, -61]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h679 a assignment
  · exact h760 a assignment

include assignment in
private theorem h842 : RUP.trueClause a (([-60, 65, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-60, 65, -59, 61], [-61, -60, -59, 65]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h767 a assignment
  · exact h841 a assignment

include assignment in
private theorem h843 : RUP.trueClause a (([-61, 65, 60, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[69, 65, -61, 60, -59], [-69, 65, -61, 60, -59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h673 a assignment
  · exact h664 a assignment

include assignment in
private theorem h844 : RUP.trueClause a (([65, -59, 62, -84] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-56, -59, 62], [-60, 65, -59], [56, 65, -59, 63, 60, 62], [-61, 65, 60, -59], [-84, 61, 64, 65], [65, -64, -70], [70, 65, -64, -63, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h840 a assignment
  · exact h842 a assignment
  · exact h101 a assignment
  · exact h843 a assignment
  · exact h738 a assignment
  · exact h749 a assignment
  · exact h686 a assignment

include assignment in
private theorem h845 : RUP.trueClause a (([-64, 60, 61, -65, 56, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[60, 61, -69, -65], [68, 61, -64], [-58, 61, -68, -64], [61, 70, -64, 69, -65, -68], [58, 69, 60, -68, 61, 67], [-70, -65, -64, 63, 62], [55, -63, -65, 56, -67, -70, 58, -68, 69, 60], [51, -55, 69], [-51, -70, -54, 69, -55, -68], [-45, 69, -51, -65, -55, 61], [-43, 45, -65, -55], [43, -70, -52, -65, -55, 62], [-70, -55, 54, -53, 52], [-14, 54, 53, -55, -70], [35, 54, 53, -55, -70], [14, -70, -33, -55, -35, 53], [33, -35, -63, -70, -64, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h744 a assignment
  · exact h758 a assignment
  · exact h745 a assignment
  · exact h382 a assignment
  · exact h222 a assignment
  · exact h687 a assignment
  · exact h800 a assignment
  · exact h777 a assignment
  · exact h380 a assignment
  · exact h372 a assignment
  · exact h775 a assignment
  · exact h312 a assignment
  · exact h602 a assignment
  · exact h788 a assignment
  · exact h787 a assignment
  · exact h332 a assignment
  · exact h795 a assignment

include assignment in
private theorem h846 : RUP.trueClause a (([64, -70, -65, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, -65, 64, -63, 62], [35, 63, -70, 64, -65], [25, 63, -70, 64, -65], [-25, -24, -65, -35], [24, -70, -33, -65, -35, 63], [-65, -35, -25, 24, 23], [-74, 33, -35], [-34, 33, -70, -35], [-72, 33, 34], [-20, -65, -23, 63, 24, 62], [-32, 72, 34, -35, 74], [21, 20, 62, 32], [62, 32, -23, -21, 20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h692 a assignment
  · exact h812 a assignment
  · exact h813 a assignment
  · exact h809 a assignment
  · exact h334 a assignment
  · exact h422 a assignment
  · exact h716 a assignment
  · exact h793 a assignment
  · exact h713 a assignment
  · exact h88 a assignment
  · exact h789 a assignment
  · exact h791 a assignment
  · exact h401 a assignment

include assignment in
private theorem h847 : RUP.trueClause a (([64, -65, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, 64, -65], [64, -70, -65, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h814 a assignment
  · exact h846 a assignment

include assignment in
private theorem h848 : RUP.trueClause a (([53, 54, 52, 70, 66, 67, -69, -68] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[47, 70, 52, -68, 54, 66], [48, 70, 53, -68, 54, 67], [-78, -48, 53, 54], [70, -55, 54, 53, 52], [-68, 54, -51, -48, -47], [49, 70, 52, -69, 55, 66], [50, 70, 53, -69, 55, 67], [-79, 51, 54, 55], [66, 52, -49, -47, -46], [-75, 46, -49, -50], [-76, -47, -49, 51], [-77, 46, 52, 53], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h264 a assignment
  · exact h292 a assignment
  · exact h726 a assignment
  · exact h608 a assignment
  · exact h573 a assignment
  · exact h319 a assignment
  · exact h354 a assignment
  · exact h727 a assignment
  · exact h531 a assignment
  · exact h720 a assignment
  · exact h721 a assignment
  · exact h723 a assignment
  · exact h729 a assignment

include assignment in
private theorem h849 : RUP.trueClause a (([-53, 54, 70, 52] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, -55, 54, -53, 52], [70, 55, 54, -53, 52]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h594 a assignment
  · exact h604 a assignment

include assignment in
private theorem h850 : RUP.trueClause a (([54, 52, -68, 70, 66, 67, -69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[53, 54, 52, 70, 66, 67, -69, -68], [-53, 54, 70, 52]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h848 a assignment
  · exact h849 a assignment

include assignment in
private theorem h851 : RUP.trueClause a (([-53, 52, 70, -54] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, -55, -54, -53, 52], [70, 55, -54, -53, 52]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h606 a assignment
  · exact h597 a assignment

include assignment in
private theorem h852 : RUP.trueClause a (([46, 47, 66, -52] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[66, -52, 49, 47, 46], [66, -52, -49, 47, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h546 a assignment
  · exact h536 a assignment

include assignment in
private theorem h853 : RUP.trueClause a (([-43, -49, -59, 37] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59, -49, -43, -38, 37], [-59, -49, -43, 38, 37]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h482 a assignment
  · exact h485 a assignment

include assignment in
private theorem h854 : RUP.trueClause a (([50, 49, -69, 55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-69, 55, 51, 50, 49], [-69, 55, -51, 50, 49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h581 a assignment
  · exact h592 a assignment

include assignment in
private theorem h855 : RUP.trueClause a (([49, -47, 66, -52] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[66, -52, 49, -47, 46], [49, -47, 66, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h529 a assignment
  · exact h774 a assignment

include assignment in
private theorem h856 : RUP.trueClause a (([-49, -47, 66, -52] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[66, -52, -49, -47, -46], [66, -52, -49, -47, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h538 a assignment
  · exact h544 a assignment

include assignment in
private theorem h857 : RUP.trueClause a (([-47, -52, 66] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[49, -47, 66, -52], [-49, -47, 66, -52]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h855 a assignment
  · exact h856 a assignment

include assignment in
private theorem h858 : RUP.trueClause a (([-53, -55, -54, 49, -46, 47, -52, 70, 67, -69, -68] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-48, 70, -53, -68, -54, 67], [-78, 48, -53, -54], [-50, 70, -53, -69, -55, 67], [-77, -46, -52, -53], [-69, -55, 51, 50, 49], [-75, -46, 49, 50], [-79, -51, -54, -55], [-76, 47, 49, -51], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h293 a assignment
  · exact h725 a assignment
  · exact h355 a assignment
  · exact h724 a assignment
  · exact h578 a assignment
  · exact h719 a assignment
  · exact h728 a assignment
  · exact h722 a assignment
  · exact h729 a assignment

include assignment in
private theorem h859 : RUP.trueClause a (([-51, 53, 43, -55, 41, -54, -46, 67, 63, -69, 61, -64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[68, 61, -64], [-58, 61, -68, -64], [45, -69, -51, -65, -55, 61], [-64, -54, -45, -42, 41], [-65, -55, -45, -44, 43], [39, -64, 42, 61, -45, 58], [-39, -55, 44, -51, -45, -50], [42, 67, -48, 63, 53, 58], [67, 53, 50, 48, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h758 a assignment
  · exact h745 a assignment
  · exact h371 a assignment
  · exact h517 a assignment
  · exact h523 a assignment
  · exact h136 a assignment
  · exact h45 a assignment
  · exact h286 a assignment
  · exact h549 a assignment

include assignment in
private theorem h860 : RUP.trueClause a (([51, 49, -69, -55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-69, -55, 51, -50, 49], [-69, -55, 51, 50, 49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h586 a assignment
  · exact h578 a assignment

include assignment in
private theorem h861 : RUP.trueClause a (([-54, -46, 41, 47, -52, 43, 49, -55, 70, 67, 63, -69, 61, -64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[51, 49, -69, -55], [68, 61, -64], [-53, -55, -54, 49, -46, 47, -52, 70, 67, -69, -68], [-51, 53, 43, -55, 41, -54, -46, 67, 63, -69, 61, -64, -65]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h860 a assignment
  · exact h758 a assignment
  · exact h858 a assignment
  · exact h859 a assignment

include assignment in
private theorem h862 : RUP.trueClause a (([54, -52, 70, -55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, -55, 54, 53, -52], [70, -55, 54, -53, -52]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h601 a assignment
  · exact h610 a assignment

include assignment in
private theorem h863 : RUP.trueClause a (([-46, 41, -65, 47, -52, 43, 49, -55, 70, 67, 63, -69, 61, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-54, -46, 41, 47, -52, 43, 49, -55, 70, 67, 63, -69, 61, -64, -65], [54, -52, 70, -55]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h861 a assignment
  · exact h862 a assignment

include assignment in
private theorem h864 : RUP.trueClause a (([-52, 43, 49, -55, 66, 67, 63, -69, 61, -65, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[64, -65, 62], [-70, -65, -64, 63, 62], [68, 61, -64], [-58, 61, -68, -64], [-68, -64, 61, 58, -57], [-47, -52, 66], [-41, 66, 47, 62, -52, 57], [46, 47, 66, -52], [-46, 41, -65, 47, -52, 43, 49, -55, 70, 67, 63, -69, 61, -64]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h847 a assignment
  · exact h687 a assignment
  · exact h758 a assignment
  · exact h745 a assignment
  · exact h647 a assignment
  · exact h857 a assignment
  · exact h256 a assignment
  · exact h852 a assignment
  · exact h863 a assignment

include assignment in
private theorem h865 : RUP.trueClause a (([52, -55, 70, 66, 67, -69, -68] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[54, 52, -68, 70, 66, 67, -69], [-53, 52, 70, -54], [70, -55, -54, 53, 52]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h850 a assignment
  · exact h851 a assignment
  · exact h599 a assignment

include assignment in
private theorem h866 : RUP.trueClause a (([-55, 66, 67, 63, -69, 61, -65, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[64, -65, 62], [-70, -65, -64, 63, 62], [68, 61, -64], [52, -55, 70, 66, 67, -69, -68], [-49, 70, -52, -69, -55, 66], [-43, 70, -52, -65, -55, 62], [-52, 43, 49, -55, 66, 67, 63, -69, 61, -65, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h847 a assignment
  · exact h687 a assignment
  · exact h758 a assignment
  · exact h865 a assignment
  · exact h323 a assignment
  · exact h315 a assignment
  · exact h864 a assignment

include assignment in
private theorem h867 : RUP.trueClause a (([49, 47, 55, 66, 57, -60, 61, -65, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-60, 61, 69, -65], [50, 49, -69, 55], [38, 66, 47, -59, 49, 57], [44, -69, -50, -65, 55, -60], [-69, 55, -51, -50, 49], [-37, -69, 49, -60, -50, -59], [-60, -50, -44, 39, 37], [-45, -69, 51, -65, 55, 61], [61, 51, 45, -39, -38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h754 a assignment
  · exact h854 a assignment
  · exact h188 a assignment
  · exact h343 a assignment
  · exact h583 a assignment
  · exact h176 a assignment
  · exact h492 a assignment
  · exact h373 a assignment
  · exact h501 a assignment

include assignment in
private theorem h868 : RUP.trueClause a (([-52, 55, 66, 57, -60, 61, -65, 56, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-60, 61, 69, -65], [-47, -52, 66], [46, 47, 66, -52], [49, 47, 55, 66, 57, -60, 61, -65, -59], [43, -69, -49, -65, 55, -59], [-37, 66, -46, -59, -49, 56], [-43, -49, -59, 37]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h754 a assignment
  · exact h857 a assignment
  · exact h852 a assignment
  · exact h867 a assignment
  · exact h307 a assignment
  · exact h167 a assignment
  · exact h853 a assignment

include assignment in
private theorem h869 : RUP.trueClause a (([61, -65, -59, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[64, -65, 62], [-56, -59, 62], [68, 61, -64], [-64, 60, 61, -65, 56, 62], [-58, 61, -68, -64], [-68, -64, 61, 58, -57], [-60, 61, 69, -65], [-60, -63, 56, 58], [-67, 63, -60, 58, 56], [-66, 62, -59, 57, 56], [-70, -65, -64, 63, 62], [-55, 66, 67, 63, -69, 61, -65, 62], [-52, 55, 66, 57, -60, 61, -65, 56, -59], [54, 52, -68, 70, 66, 67, -69], [-53, 52, 70, -54], [43, 70, 52, -65, 55, 62], [49, 70, 52, -69, 55, 66], [-45, 70, -54, -65, 55, -64], [-51, 70, -54, -69, 55, -68], [-48, 51, -68, -54], [44, 70, 53, -65, 55, 63], [50, 70, 53, -69, 55, 67], [-43, -49, -59, 37], [-68, -54, 51, 48, -47], [67, 53, -50, 48, -46], [-37, 63, -40, -60, -44, 56], [-59, -49, -43, -38, -37], [63, 53, -44, 42, 40], [-36, -49, -37, 47, 38, 46], [58, 48, -42, 39, 36], [-39, -64, -42, 61, 45, 58]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h847 a assignment
  · exact h840 a assignment
  · exact h758 a assignment
  · exact h845 a assignment
  · exact h745 a assignment
  · exact h647 a assignment
  · exact h754 a assignment
  · exact h766 a assignment
  · exact h642 a assignment
  · exact h627 a assignment
  · exact h687 a assignment
  · exact h866 a assignment
  · exact h868 a assignment
  · exact h850 a assignment
  · exact h851 a assignment
  · exact h311 a assignment
  · exact h319 a assignment
  · exact h376 a assignment
  · exact h379 a assignment
  · exact h768 a assignment
  · exact h350 a assignment
  · exact h354 a assignment
  · exact h853 a assignment
  · exact h565 a assignment
  · exact h556 a assignment
  · exact h97 a assignment
  · exact h483 a assignment
  · exact h510 a assignment
  · exact h21 a assignment
  · exact h473 a assignment
  · exact h135 a assignment

include assignment in
private theorem h870 : RUP.trueClause a (([-59, 62, -84] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[65, -59, 62, -84], [64, -65, 62], [61, -65, -59, 62], [-84, -61, -64, -65]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h844 a assignment
  · exact h847 a assignment
  · exact h869 a assignment
  · exact h739 a assignment

include assignment in
private theorem h871 : RUP.trueClause a (([-69, 61, -65, 59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[60, 61, -69, -65], [-69, -65, 61, -60, 59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h744 a assignment
  · exact h674 a assignment

include assignment in
private theorem h872 : RUP.trueClause a (([61, 59, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-69, 61, -65, 59], [-60, 61, 69, -65], [69, -65, 61, 60, 59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h871 a assignment
  · exact h754 a assignment
  · exact h680 a assignment

include assignment in
private theorem h873 : RUP.trueClause a (([51, 36, 46, 38, -47, -49, -41, -43, 52, 55, -67, 64, -61, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, -61, 64, 65], [-54, 55, -70], [-61, 64, -68], [58, -61, 68, 64], [-45, 68, 51, 64, 54, -61], [-79, 51, 54, 55], [-76, -47, -49, 51], [64, 54, 45, 42, -41], [65, 55, 45, 44, -43], [36, 45, 38, -42, -39, -41], [-42, 68, 48, 64, 54, -58], [39, 55, -44, 51, 45, 50], [-67, -53, -50, -48, 46], [-78, -48, 53, 54], [-75, 46, -49, -50], [-77, 46, 52, 53], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h831 a assignment
  · exact h798 a assignment
  · exact h751 a assignment
  · exact h753 a assignment
  · exact h369 a assignment
  · exact h727 a assignment
  · exact h721 a assignment
  · exact h516 a assignment
  · exact h522 a assignment
  · exact h18 a assignment
  · exact h290 a assignment
  · exact h44 a assignment
  · exact h550 a assignment
  · exact h726 a assignment
  · exact h720 a assignment
  · exact h723 a assignment
  · exact h729 a assignment

include assignment in
private theorem h874 : RUP.trueClause a (([52, 55, 64, 59, -61, 65, -62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, -61, 64, 65], [-54, 55, -70], [-61, 64, -68], [58, -61, 68, 64], [68, 64, -61, -58, 57], [-57, -70, -62, 68, 64, 66], [-70, 65, 64, 63, -62], [-58, -70, -63, 68, 64, 67], [-58, -63, 56], [-61, -70, 64, -69, 65, 68], [43, -70, 52, 65, 55, -62], [41, -70, 52, 64, 54, -62], [49, -70, 52, 69, 55, -66], [47, -70, 52, 68, 54, -66], [-38, -62, -41, 59, -43, -57], [-62, 52, -43, -41, -40], [-66, 52, -49, -47, -46], [-36, -62, 40, -57, -41, -56], [51, 36, 46, 38, -47, -49, -41, -43, 52, 55, -67, 64, -61, 65], [-50, -51, 69, 55], [69, 55, -51, 50, -49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h831 a assignment
  · exact h798 a assignment
  · exact h751 a assignment
  · exact h753 a assignment
  · exact h648 a assignment
  · exact h271 a assignment
  · exact h695 a assignment
  · exact h298 a assignment
  · exact h765 a assignment
  · exact h385 a assignment
  · exact h313 a assignment
  · exact h258 a assignment
  · exact h322 a assignment
  · exact h262 a assignment
  · exact h109 a assignment
  · exact h509 a assignment
  · exact h545 a assignment
  · exact h74 a assignment
  · exact h873 a assignment
  · exact h772 a assignment
  · exact h585 a assignment

include assignment in
private theorem h875 : RUP.trueClause a (([-52, 54, -70, 55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, 55, 54, -53, -52], [-70, 55, 54, 53, -52]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h598 a assignment
  · exact h605 a assignment

include assignment in
private theorem h876 : RUP.trueClause a (([55, 64, 59, -61, 65, -62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, -61, 64, 65], [-54, 55, -70], [52, 55, 64, 59, -61, 65, -62], [-52, 54, -70, 55]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h831 a assignment
  · exact h798 a assignment
  · exact h874 a assignment
  · exact h875 a assignment

include assignment in
private theorem h877 : RUP.trueClause a (([38, -45, -61, -51] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-61, -51, -45, -39, 38], [-61, -51, -45, 39, 38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h496 a assignment
  · exact h500 a assignment

include assignment in
private theorem h878 : RUP.trueClause a (([-42, 41, 64, -45] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[64, 54, -45, -42, 41], [64, -54, -45, -42, 41]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h519 a assignment
  · exact h521 a assignment

include assignment in
private theorem h879 : RUP.trueClause a (([-52, -38, -45, -55, 60, -57, 69, -58, -70, 68, 64, 59, 65, -62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[51, -55, 69], [-50, -51, 69, -55], [-44, 69, 50, 65, -55, 60], [-57, -70, -62, 68, 64, 66], [-70, 65, 64, 63, -62], [-58, -63, 56], [-49, -70, -52, 69, -55, -66], [-43, -70, -52, 65, -55, -62], [59, 49, 43, -38, -37], [37, -62, 40, 59, 43, -56], [36, 59, 37, -57, -38, -56], [-62, -52, 43, -41, -40], [-57, -47, 41, -38, -36], [37, -66, 46, 59, 49, -56], [-76, 47, 49, -51], [-75, -46, 49, 50], [-42, 41, 64, -45], [39, -63, 42, 60, 44, -58], [-63, 53, 44, 42, -40], [-58, -48, 42, -39, -36], [-77, -46, -52, -53], [48, 54, 68, -51], [-79, -51, -54, -55], [-78, 48, -53, -54], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h777 a assignment
  · exact h771 a assignment
  · exact h348 a assignment
  · exact h271 a assignment
  · exact h695 a assignment
  · exact h765 a assignment
  · exact h325 a assignment
  · exact h316 a assignment
  · exact h486 a assignment
  · exact h95 a assignment
  · exact h53 a assignment
  · exact h508 a assignment
  · exact h466 a assignment
  · exact h159 a assignment
  · exact h722 a assignment
  · exact h719 a assignment
  · exact h878 a assignment
  · exact h132 a assignment
  · exact h513 a assignment
  · exact h474 a assignment
  · exact h724 a assignment
  · exact h803 a assignment
  · exact h728 a assignment
  · exact h725 a assignment
  · exact h729 a assignment

include assignment in
private theorem h880 : RUP.trueClause a (([-46, 49, -66, 52] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-66, 52, 49, -47, -46], [-66, 52, 49, 47, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h535 a assignment
  · exact h543 a assignment

include assignment in
private theorem h881 : RUP.trueClause a (([64, 59, -61, 65, -62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-61, 64, -68], [70, -61, 64, 65], [58, -61, 68, 64], [-61, -70, 64, -69, 65, 68], [-70, 65, 64, 63, -62], [68, 64, -61, -58, 57], [-58, -63, 56], [-60, 65, 69, -61], [-57, -70, -62, 68, 64, 66], [55, 64, 59, -61, 65, -62], [51, -55, 69], [45, 69, -51, 65, -55, -61], [38, -45, -61, -51], [-52, -38, -45, -55, 60, -57, 69, -58, -70, 68, 64, 59, 65, -62], [-38, 69, -49, -61, -51, 59], [-38, 65, -43, -61, -45, 59], [59, 49, 43, -38, -37], [37, -66, 46, 59, 49, -56], [-46, 49, -66, 52]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h751 a assignment
  · exact h831 a assignment
  · exact h753 a assignment
  · exact h385 a assignment
  · exact h695 a assignment
  · exact h648 a assignment
  · exact h765 a assignment
  · exact h760 a assignment
  · exact h271 a assignment
  · exact h876 a assignment
  · exact h777 a assignment
  · exact h370 a assignment
  · exact h877 a assignment
  · exact h879 a assignment
  · exact h199 a assignment
  · exact h115 a assignment
  · exact h486 a assignment
  · exact h159 a assignment
  · exact h880 a assignment

include assignment in
private theorem h882 : RUP.trueClause a (([-64, 65, -62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[65, -64, -70], [-62, 65, 70, -64]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h749 a assignment
  · exact h838 a assignment

include assignment in
private theorem h883 : RUP.trueClause a (([64, -61, -62, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[64, 59, -61, 65, -62], [-60, 65, -59], [-61, 65, 60, -59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h881 a assignment
  · exact h842 a assignment
  · exact h843 a assignment

include assignment in
private theorem h884 : RUP.trueClause a (([61, 65, -84] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-84, 61, 64, 65], [68, 61, -64], [-64, 65, -62], [-58, 61, -68, -64], [-68, -64, 61, 58, -57], [-59, 62, -84], [57, 65, 59, -64, 61, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h738 a assignment
  · exact h758 a assignment
  · exact h882 a assignment
  · exact h745 a assignment
  · exact h647 a assignment
  · exact h870 a assignment
  · exact h125 a assignment

include assignment in
private theorem h885 : RUP.trueClause a (([53, -46, 67, 50] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[67, 53, 50, 48, -46], [67, 53, 50, -48, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h549 a assignment
  · exact h554 a assignment

include assignment in
private theorem h886 : RUP.trueClause a (([-46, 49, 52, 67, 66, 69, 70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-46, 69, 49, 67, -50, 66], [-46, 70, 52, 67, -53, 66], [53, -46, 67, 50]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h178 a assignment
  · exact h245 a assignment
  · exact h885 a assignment

include assignment in
private theorem h887 : RUP.trueClause a (([49, 52, 67, 66, 69, -68, 70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-46, 49, 52, 67, 66, 69, 70], [66, 52, 49, -47, 46], [47, 70, 52, -68, 54, 66], [47, 69, 49, -68, 51, 66], [46, -68, 47, 67, -48, 66], [-53, 52, 70, -54], [70, -55, -54, 53, 52], [-50, -51, 69, 55], [67, 53, 50, 48, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h886 a assignment
  · exact h542 a assignment
  · exact h264 a assignment
  · exact h204 a assignment
  · exact h154 a assignment
  · exact h851 a assignment
  · exact h599 a assignment
  · exact h772 a assignment
  · exact h552 a assignment

include assignment in
private theorem h888 : RUP.trueClause a (([-35, -64, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65, -62], [65, -64, -70], [-35, 34, 70], [25, 70, -34, 65, -35, -64], [-33, -35, 70, -34], [21, -25, -64, -34], [70, -35, -34, 33, 32], [-21, 70, -32, -64, -34, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h882 a assignment
  · exact h749 a assignment
  · exact h830 a assignment
  · exact h360 a assignment
  · exact h827 a assignment
  · exact h836 a assignment
  · exact h438 a assignment
  · exact h251 a assignment

include assignment in
private theorem h889 : RUP.trueClause a (([-25, -64, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-35, -64, 65], [-64, 65, -62], [65, -64, -70], [70, 65, -64, -63, 62], [-25, 70, 34, 65, 35, -64], [21, -25, -64, -34], [-21, 70, -32, -64, -34, 62], [-64, -34, -25, -22, -21], [-20, -64, -21, 63, 22, 62], [22, 20, 63, 33], [-74, -33, 35], [-72, -33, -34], [32, 72, -34, 35, 74]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h888 a assignment
  · exact h882 a assignment
  · exact h749 a assignment
  · exact h686 a assignment
  · exact h362 a assignment
  · exact h836 a assignment
  · exact h251 a assignment
  · exact h412 a assignment
  · exact h73 a assignment
  · exact h816 a assignment
  · exact h717 a assignment
  · exact h712 a assignment
  · exact h786 a assignment

include assignment in
private theorem h890 : RUP.trueClause a (([-33, -34, 32, 35] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-74, -33, 35], [-72, -33, -34], [32, 72, -34, 35, 74]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h717 a assignment
  · exact h712 a assignment
  · exact h786 a assignment

include assignment in
private theorem h891 : RUP.trueClause a (([33, 20, -24, 63] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[22, 20, 63, 33], [63, 33, -24, -22, 20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h816 a assignment
  · exact h407 a assignment

include assignment in
private theorem h892 : RUP.trueClause a (([70, -64, 65, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, 65, -64, -63, 62], [-35, -64, 65], [-25, -64, 65], [24, 35, 65, 25], [65, 35, 25, -24, -23], [-20, 65, 23, 63, -24, 62], [23, 70, -32, 65, 35, 62], [33, 20, -24, 63], [-33, 35, 70, 34], [-33, -34, 32, 35]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h686 a assignment
  · exact h888 a assignment
  · exact h889 a assignment
  · exact h832 a assignment
  · exact h423 a assignment
  · exact h87 a assignment
  · exact h299 a assignment
  · exact h891 a assignment
  · exact h821 a assignment
  · exact h890 a assignment

include assignment in
private theorem h893 : RUP.trueClause a (([-64, 65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[65, -64, -70], [-64, 65, -62], [70, -64, 65, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h749 a assignment
  · exact h882 a assignment
  · exact h892 a assignment

include assignment in
private theorem h894 : RUP.trueClause a (([65, -84] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[61, 65, -84], [-64, 65], [-61, 64, -68], [64, -61, -62, 65], [58, -61, 68, 64], [-59, 62, -84], [68, 64, -61, -58, 57], [-57, 65, 59, 64, -61, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h884 a assignment
  · exact h893 a assignment
  · exact h751 a assignment
  · exact h883 a assignment
  · exact h753 a assignment
  · exact h870 a assignment
  · exact h648 a assignment
  · exact h127 a assignment

include assignment in
private theorem h895 : RUP.trueClause a (([35, 64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[64, -65, 62], [70, 64, -65], [33, 35, -70], [-34, 35, -70], [-70, 35, 34, -33, -32], [-25, -70, 34, -65, 35, 64], [21, -70, 32, 64, 34, -62], [22, 25, 64, 34], [64, 34, 25, -22, -21]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h847 a assignment
  · exact h814 a assignment
  · exact h783 a assignment
  · exact h810 a assignment
  · exact h437 a assignment
  · exact h364 a assignment
  · exact h248 a assignment
  · exact h811 a assignment
  · exact h415 a assignment

include assignment in
private theorem h896 : RUP.trueClause a (([25, -33, 34, 64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[35, 64, -65], [70, 64, -65], [-70, -35, 34, -33, 32], [64, -65, 62], [63, -62, 64, -65], [22, 25, 64, 34], [64, 34, 25, -22, -21], [21, -65, 23, 64, 25, -62], [20, 34, 21, -33, -22, -32], [-65, -35, 25, -24, -23], [-63, -33, 24, -22, -20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h895 a assignment
  · exact h814 a assignment
  · exact h442 a assignment
  · exact h847 a assignment
  · exact h763 a assignment
  · exact h811 a assignment
  · exact h415 a assignment
  · exact h108 a assignment
  · exact h3 a assignment
  · exact h419 a assignment
  · exact h405 a assignment

include assignment in
private theorem h897 : RUP.trueClause a (([-20, 24, -63, -33] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-63, -33, 24, -22, -20], [-63, -33, 24, 22, -20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h405 a assignment
  · exact h406 a assignment

include assignment in
private theorem h898 : RUP.trueClause a (([-33, 34, 64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[35, 64, -65], [64, -65, 62], [63, -62, 64, -65], [25, -33, 34, 64, -65], [-25, -24, -65, -35], [-65, -35, -25, 24, 23], [20, -65, -23, -63, 24, -62], [-20, 24, -63, -33]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h895 a assignment
  · exact h847 a assignment
  · exact h763 a assignment
  · exact h896 a assignment
  · exact h809 a assignment
  · exact h422 a assignment
  · exact h92 a assignment
  · exact h897 a assignment

include assignment in
private theorem h899 : RUP.trueClause a (([34, 64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[35, 64, -65], [64, -65, 62], [63, -62, 64, -65], [70, 64, -65], [-33, 34, 64, -65], [-74, 33, -35], [-24, -70, 33, -65, -35, -63], [22, -70, 33, 64, 34, -63], [-72, 33, 34], [-32, 72, 34, -35, 74], [-23, -70, 32, -65, -35, -62], [21, -70, 32, 64, 34, -62], [-65, -35, -25, 24, 23], [64, 34, 25, -22, -21]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h895 a assignment
  · exact h847 a assignment
  · exact h763 a assignment
  · exact h814 a assignment
  · exact h898 a assignment
  · exact h716 a assignment
  · exact h338 a assignment
  · exact h279 a assignment
  · exact h713 a assignment
  · exact h789 a assignment
  · exact h302 a assignment
  · exact h248 a assignment
  · exact h422 a assignment
  · exact h415 a assignment

include assignment in
private theorem h900 : RUP.trueClause a (([64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, 64, -65], [64, -65, 62], [35, 64, -65], [34, 64, -65], [-34, 33, -70, -35], [25, -70, -34, -65, -35, 64], [-70, -35, -34, -33, -32], [-25, -24, -65, -35], [-65, -35, -25, 24, 23], [-23, -70, 32, -65, -35, -62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h814 a assignment
  · exact h847 a assignment
  · exact h895 a assignment
  · exact h899 a assignment
  · exact h793 a assignment
  · exact h361 a assignment
  · exact h433 a assignment
  · exact h809 a assignment
  · exact h422 a assignment
  · exact h302 a assignment

include assignment in
private theorem h901 : RUP.trueClause a (([-64, -65, -84] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-84, -61, -64, -65], [68, 61, -64], [61, 59, -65], [-58, 61, -68, -64], [-59, 62, -84], [57, -65, -59, -64, 61, -62], [-68, -64, 61, 58, -57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h739 a assignment
  · exact h758 a assignment
  · exact h872 a assignment
  · exact h745 a assignment
  · exact h870 a assignment
  · exact h123 a assignment
  · exact h647 a assignment

include assignment in
private theorem h902 : RUP.trueClause a (([-84] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[65, -84], [64, -65], [-64, -65, -84]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h894 a assignment
  · exact h900 a assignment
  · exact h901 a assignment

include assignment in
private theorem h903 : RUP.trueClause a (([61, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [61, 59, -65], [68, 61, -64], [57, -65, -59, -64, 61, -62], [-58, 61, -68, -64], [-68, -64, 61, 58, -57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h758 a assignment
  · exact h123 a assignment
  · exact h745 a assignment
  · exact h647 a assignment

include assignment in
private theorem h904 : RUP.trueClause a (([-63, -58, -57, 83, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-84], [61, -62, -64], [-64, 65], [-58, -65, 60, -64, -61, -63], [-58, -63, 56], [-81, -58, -60, -61], [-82, -56, -62, -63], [-80, -56, -57, -58], [80, 81, 82, 83, 84]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h902 a assignment
  · exact h903 a assignment
  · exact h893 a assignment
  · exact h142 a assignment
  · exact h765 a assignment
  · exact h732 a assignment
  · exact h735 a assignment
  · exact h731 a assignment
  · exact h740 a assignment

include assignment in
private theorem h905 : RUP.trueClause a (([70, -35, -33] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-33, -35, 70, -34], [-35, 34, 70]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h827 a assignment
  · exact h830 a assignment

include assignment in
private theorem h906 : RUP.trueClause a (([-33, 70, 63, -62, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[70, -35, -33], [-33, 35, 70, 34], [-33, -34, 32, 35], [-23, 70, -32, -65, 35, -62], [20, 70, -32, 63, -33, -62], [-20, -21, -62, -32], [-62, -32, 23, 21, -20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h905 a assignment
  · exact h821 a assignment
  · exact h890 a assignment
  · exact h301 a assignment
  · exact h227 a assignment
  · exact h818 a assignment
  · exact h400 a assignment

include assignment in
private theorem h907 : RUP.trueClause a (([-24, 70, 63, -62, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-33, 70, 63, -62, -65], [33, 20, -24, 63], [-20, 70, 32, 63, 33, -62], [-20, -65, -23, 63, -24, -62], [-20, -21, -62, -32], [-62, -32, 23, 21, -20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h906 a assignment
  · exact h891 a assignment
  · exact h229 a assignment
  · exact h89 a assignment
  · exact h818 a assignment
  · exact h400 a assignment

include assignment in
private theorem h908 : RUP.trueClause a (([23, -32, 24, 63, -62, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[20, -65, 23, 63, 24, -62], [-20, -21, -62, -32], [-62, -32, 23, 21, -20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h93 a assignment
  · exact h818 a assignment
  · exact h400 a assignment

include assignment in
private theorem h909 : RUP.trueClause a (([63, -62, -64, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, -65, -64, 63, -62], [-33, 70, 63, -62, -65], [-24, 70, 63, -62, -65], [24, 70, 33, -65, 35, 63], [-35, 34, 70], [70, -35, -34, 33, 32], [23, -32, 24, 63, -62, -65], [-21, -23, -32, -62], [21, -25, -64, -34], [21, -35, -23, -34, 25, -32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h693 a assignment
  · exact h906 a assignment
  · exact h907 a assignment
  · exact h336 a assignment
  · exact h830 a assignment
  · exact h438 a assignment
  · exact h908 a assignment
  · exact h835 a assignment
  · exact h836 a assignment
  · exact h7 a assignment

include assignment in
private theorem h910 : RUP.trueClause a (([46, -36, -56, 37] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-56, 46, 40, 37, -36], [-56, 46, -40, 37, -36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h460 a assignment
  · exact h451 a assignment

include assignment in
private theorem h911 : RUP.trueClause a (([-36, 37, -60, -66, -56, -59, -63, -62, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[46, -36, -56, 37], [37, -66, -46, -59, 49, -56], [-56, -46, 40, 37, -36], [-43, -49, -59, 37], [-40, -65, 43, -63, -44, -62], [37, -63, -40, -60, 44, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h910 a assignment
  · exact h160 a assignment
  · exact h456 a assignment
  · exact h853 a assignment
  · exact h99 a assignment
  · exact h98 a assignment

include assignment in
private theorem h912 : RUP.trueClause a (([-46, 37, 38, 70, -57, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [63, -62, -64, -65], [-83, -59, -62, -65], [-63, -58, -57, 83, -62, -64], [56, -64, -57, -63, 58, -62], [61, -62, -64], [-68, -64, -61, 58, -57], [58, 70, -63, 68, -64, -67], [67, -63, 60, 58, -56], [-61, 70, -64, -69, -65, 68], [70, 69, 68, 67, 66], [-36, 37, -60, -66, -56, -59, -63, -62, -65], [36, -60, 37, 58, 39, -56], [37, -66, -46, -59, 49, -56], [36, 67, -46, 58, -48, -56], [-43, -49, -59, 37], [58, 48, -42, -39, 36], [38, -62, -41, -59, 43, -57], [36, -64, 41, 58, 42, -57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h909 a assignment
  · exact h737 a assignment
  · exact h904 a assignment
  · exact h86 a assignment
  · exact h903 a assignment
  · exact h655 a assignment
  · exact h296 a assignment
  · exact h636 a assignment
  · exact h384 a assignment
  · exact h702 a assignment
  · exact h911 a assignment
  · exact h57 a assignment
  · exact h160 a assignment
  · exact h147 a assignment
  · exact h853 a assignment
  · exact h476 a assignment
  · exact h110 a assignment
  · exact h82 a assignment

include assignment in
private theorem h913 : RUP.trueClause a (([53, 46, 67, 50] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[67, 53, 50, -48, 46], [67, 53, 50, 48, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h558 a assignment
  · exact h552 a assignment

include assignment in
private theorem h914 : RUP.trueClause a (([37, 38, 70, -57, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [-83, -59, -62, -65], [63, -62, -64, -65], [-63, -58, -57, 83, -62, -64], [56, -64, -57, -63, 58, -62], [61, -62, -64], [-68, -64, -61, 58, -57], [58, 70, -63, 68, -64, -67], [67, -63, 60, 58, -56], [-61, 70, -64, -69, -65, 68], [70, 69, 68, 67, 66], [-36, 37, -60, -66, -56, -59, -63, -62, -65], [-46, 37, 38, 70, -57, -59, -62, -64], [37, 67, 46, -60, -50, -56], [-56, 46, -40, 37, 36], [40, 67, 46, -63, -53, -56], [53, 46, 67, 50]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h737 a assignment
  · exact h909 a assignment
  · exact h904 a assignment
  · exact h86 a assignment
  · exact h903 a assignment
  · exact h655 a assignment
  · exact h296 a assignment
  · exact h636 a assignment
  · exact h384 a assignment
  · exact h702 a assignment
  · exact h911 a assignment
  · exact h912 a assignment
  · exact h169 a assignment
  · exact h464 a assignment
  · exact h239 a assignment
  · exact h913 a assignment

include assignment in
private theorem h915 : RUP.trueClause a (([49, -37, -59, 38] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59, 49, -43, 38, -37], [-59, 49, 43, 38, -37]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h480 a assignment
  · exact h487 a assignment

include assignment in
private theorem h916 : RUP.trueClause a (([-46, -36, -56, -37] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-56, -46, 40, -37, -36], [-56, -46, -40, -37, -36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h455 a assignment
  · exact h458 a assignment

include assignment in
private theorem h917 : RUP.trueClause a (([38, 70, -57, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[61, -62, -64], [-64, 65], [-83, -59, -62, -65], [63, -62, -64, -65], [-63, -58, -57, 83, -62, -64], [-68, -64, -61, 58, -57], [-61, 70, -64, -69, -65, 68], [58, 70, -63, 68, -64, -67], [70, 69, 68, 67, 66], [56, -64, -57, -63, 58, -62], [37, 38, 70, -57, -59, -62, -64], [36, -59, -37, -57, 38, -56], [49, -37, -59, 38], [-37, -66, 46, -59, -49, -56], [-46, -36, -56, -37]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h903 a assignment
  · exact h893 a assignment
  · exact h737 a assignment
  · exact h909 a assignment
  · exact h904 a assignment
  · exact h655 a assignment
  · exact h384 a assignment
  · exact h296 a assignment
  · exact h702 a assignment
  · exact h86 a assignment
  · exact h914 a assignment
  · exact h54 a assignment
  · exact h915 a assignment
  · exact h163 a assignment
  · exact h916 a assignment

include assignment in
private theorem h918 : RUP.trueClause a (([80, 81, 82, 83] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-84], [80, 81, 82, 83, 84]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h902 a assignment
  · exact h740 a assignment

include assignment in
private theorem h919 : RUP.trueClause a (([-46, 39, -37, 67, -56, 58, -63] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[67, -63, 60, 58, -56], [-37, 67, -46, -60, 50, -56], [-46, -36, -56, -37], [36, -50, -37, -48, 39, -46], [-56, -46, -40, -37, 36], [58, 48, -42, 39, 36], [36, -63, 40, 58, 42, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h636 a assignment
  · exact h171 a assignment
  · exact h916 a assignment
  · exact h24 a assignment
  · exact h453 a assignment
  · exact h473 a assignment
  · exact h77 a assignment

include assignment in
private theorem h920 : RUP.trueClause a (([45, 39, -61, -38] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-61, -51, 45, 39, -38], [-61, 51, 45, 39, -38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h499 a assignment
  · exact h502 a assignment

include assignment in
private theorem h921 : RUP.trueClause a (([39, -37, -38, -66, 67, -56, 58, -59, -63, -61, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-46, 39, -37, 67, -56, 58, -63], [-37, -66, 46, -59, -49, -56], [-59, 49, -43, -38, -37], [-38, -65, 43, -61, -45, -59], [45, 39, -61, -38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h919 a assignment
  · exact h163 a assignment
  · exact h488 a assignment
  · exact h113 a assignment
  · exact h920 a assignment

include assignment in
private theorem h922 : RUP.trueClause a (([-42, 36, 58, -39] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[58, -48, -42, -39, 36], [58, 48, -42, -39, 36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h477 a assignment
  · exact h476 a assignment

include assignment in
private theorem h923 : RUP.trueClause a (([-37, 70, -57, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[38, 70, -57, -59, -62, -64], [61, -62, -64], [-64, 65], [-83, -59, -62, -65], [63, -62, -64, -65], [-63, -58, -57, 83, -62, -64], [-68, -64, -61, 58, -57], [-61, 70, -64, -69, -65, 68], [58, 70, -63, 68, -64, -67], [70, 69, 68, 67, 66], [56, -64, -57, -63, 58, -62], [39, -37, -38, -66, 67, -56, 58, -59, -63, -61, -65], [-36, -61, -38, 58, -39, -57], [-42, 36, 58, -39], [36, -64, 41, 58, 42, -57], [36, -63, 40, 58, 42, -56], [-39, -64, 42, -61, 45, 58], [58, -48, 42, -39, 36], [-56, -46, -40, -37, 36], [36, 53, -40, 48, 42, 46], [-64, 54, -45, 42, -41], [-40, -66, 46, -62, -52, -56], [-53, 52, 70, -54]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h917 a assignment
  · exact h903 a assignment
  · exact h893 a assignment
  · exact h737 a assignment
  · exact h909 a assignment
  · exact h904 a assignment
  · exact h655 a assignment
  · exact h384 a assignment
  · exact h296 a assignment
  · exact h702 a assignment
  · exact h86 a assignment
  · exact h921 a assignment
  · exact h60 a assignment
  · exact h922 a assignment
  · exact h82 a assignment
  · exact h77 a assignment
  · exact h134 a assignment
  · exact h471 a assignment
  · exact h453 a assignment
  · exact h31 a assignment
  · exact h515 a assignment
  · exact h238 a assignment
  · exact h851 a assignment

include assignment in
private theorem h924 : RUP.trueClause a (([70, -57, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [63, -62, -64, -65], [-83, -59, -62, -65], [-63, -58, -57, 83, -62, -64], [56, -64, -57, -63, 58, -62], [61, -62, -64], [-68, -64, -61, 58, -57], [58, 70, -63, 68, -64, -67], [-61, 70, -64, -69, -65, 68], [70, 69, 68, 67, 66], [67, -63, 60, 58, -56], [38, 70, -57, -59, -62, -64], [-37, 70, -57, -59, -62, -64], [37, -61, -38, -60, 39, -59], [-36, -59, 37, -57, -38, -56], [-42, 36, 58, -39], [36, -64, 41, 58, 42, -57], [36, -63, 40, 58, 42, -56], [36, 43, 37, -41, -38, -40], [-56, 46, -40, 37, 36], [-43, -49, -59, 37], [37, -66, -46, -59, 49, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h909 a assignment
  · exact h737 a assignment
  · exact h904 a assignment
  · exact h86 a assignment
  · exact h903 a assignment
  · exact h655 a assignment
  · exact h296 a assignment
  · exact h384 a assignment
  · exact h702 a assignment
  · exact h636 a assignment
  · exact h917 a assignment
  · exact h923 a assignment
  · exact h62 a assignment
  · exact h55 a assignment
  · exact h922 a assignment
  · exact h82 a assignment
  · exact h77 a assignment
  · exact h14 a assignment
  · exact h464 a assignment
  · exact h853 a assignment
  · exact h160 a assignment

include assignment in
private theorem h925 : RUP.trueClause a (([-39, -38, -57, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[61, -62, -64], [-64, 65], [-83, -59, -62, -65], [63, -62, -64, -65], [-63, -58, -57, 83, -62, -64], [-68, -64, -61, 58, -57], [70, -57, -59, -62, -64], [-57, -70, -62, 68, -64, -66], [56, -64, -57, -63, 58, -62], [-36, -61, -38, 58, -39, -57], [-42, 36, 58, -39], [36, -64, 41, 58, 42, -57], [36, -63, 40, 58, 42, -56], [-39, -64, 42, -61, 45, 58], [58, -48, 42, -39, 36], [-61, 51, -45, -39, -38], [-41, -65, 43, -64, -45, -62], [-64, 54, -45, 42, -41], [-62, 52, -43, -41, -40], [-54, 55, -70], [-70, -55, -54, 53, -52], [-78, 48, -53, -54], [-47, -52, 66], [-79, -51, -54, -55], [46, 47, 66, -52], [-56, -46, -40, -37, 36], [-77, -46, -52, -53], [-43, -49, -59, 37], [-46, -51, 47, -50, 48, 49], [-76, 47, 49, -51], [-75, -46, 49, 50], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h903 a assignment
  · exact h893 a assignment
  · exact h737 a assignment
  · exact h909 a assignment
  · exact h904 a assignment
  · exact h655 a assignment
  · exact h924 a assignment
  · exact h272 a assignment
  · exact h86 a assignment
  · exact h60 a assignment
  · exact h922 a assignment
  · exact h82 a assignment
  · exact h77 a assignment
  · exact h134 a assignment
  · exact h471 a assignment
  · exact h503 a assignment
  · exact h120 a assignment
  · exact h515 a assignment
  · exact h509 a assignment
  · exact h798 a assignment
  · exact h603 a assignment
  · exact h725 a assignment
  · exact h857 a assignment
  · exact h728 a assignment
  · exact h852 a assignment
  · exact h453 a assignment
  · exact h724 a assignment
  · exact h853 a assignment
  · exact h30 a assignment
  · exact h722 a assignment
  · exact h719 a assignment
  · exact h729 a assignment

include assignment in
private theorem h926 : RUP.trueClause a (([-38, -57, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[61, -62, -64], [-64, 65], [-83, -59, -62, -65], [63, -62, -64, -65], [-63, -58, -57, 83, -62, -64], [-68, -64, -61, 58, -57], [70, -57, -59, -62, -64], [-57, -70, -62, 68, -64, -66], [56, -64, -57, -63, 58, -62], [-39, -38, -57, -59, -62, -64], [45, 39, -61, -38], [-61, 51, -45, 39, -38], [39, -64, -42, -61, -45, 58], [-38, -65, 43, -61, -45, -59], [-38, -64, 41, -61, -45, -57], [-64, 54, -45, 42, -41], [40, -64, -41, -63, 42, -62], [-54, 55, -70], [-41, -70, 52, -64, -54, -62], [-70, -55, -54, 53, -52], [-79, -51, -54, -55], [-47, -52, 66], [46, 47, 66, -52], [-57, 47, -41, -38, -36], [68, -54, -51, -48, 47], [-56, -46, -40, -37, 36], [-77, -46, -52, -53], [36, -50, 37, 48, 39, -46], [-78, 48, -53, -54], [-43, -49, -59, 37], [-75, -46, 49, 50], [-76, 47, 49, -51], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h903 a assignment
  · exact h893 a assignment
  · exact h737 a assignment
  · exact h909 a assignment
  · exact h904 a assignment
  · exact h655 a assignment
  · exact h924 a assignment
  · exact h272 a assignment
  · exact h86 a assignment
  · exact h925 a assignment
  · exact h920 a assignment
  · exact h494 a assignment
  · exact h137 a assignment
  · exact h113 a assignment
  · exact h111 a assignment
  · exact h515 a assignment
  · exact h83 a assignment
  · exact h798 a assignment
  · exact h261 a assignment
  · exact h603 a assignment
  · exact h728 a assignment
  · exact h857 a assignment
  · exact h852 a assignment
  · exact h469 a assignment
  · exact h572 a assignment
  · exact h453 a assignment
  · exact h724 a assignment
  · exact h23 a assignment
  · exact h725 a assignment
  · exact h853 a assignment
  · exact h719 a assignment
  · exact h722 a assignment
  · exact h729 a assignment

include assignment in
private theorem h927 : RUP.trueClause a (([37, -36, 66, -56, -57, -62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[46, -36, -56, 37], [-36, 66, -46, -57, 47, -56], [-56, -46, 40, 37, -36], [-40, 66, -46, -62, 52, -56], [-47, -52, 66]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h910 a assignment
  · exact h145 a assignment
  · exact h456 a assignment
  · exact h235 a assignment
  · exact h857 a assignment

include assignment in
private theorem h928 : RUP.trueClause a (([-51, 39, 38, -61] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[38, -45, -61, -51], [-61, -51, 45, 39, 38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h877 a assignment
  · exact h498 a assignment

include assignment in
private theorem h929 : RUP.trueClause a (([53, 75, 79, 54, 76, -48, 52, 46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-78, -48, 53, 54], [-77, 46, 52, 53], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h726 a assignment
  · exact h723 a assignment
  · exact h729 a assignment

include assignment in
private theorem h930 : RUP.trueClause a (([39, -57, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-38, -57, -59, -62, -64], [61, -62, -64], [-64, 65], [-83, -59, -62, -65], [63, -62, -64, -65], [-63, -58, -57, 83, -62, -64], [-68, -64, -61, 58, -57], [70, -57, -59, -62, -64], [-57, -70, -62, 68, -64, -66], [56, -64, -57, -63, 58, -62], [36, -61, 38, 58, 39, -57], [37, -36, 66, -56, -57, -62], [49, -37, -59, 38], [-46, -36, -56, -37], [-36, -49, -37, 47, 38, 46], [-47, -52, 66], [-51, 39, 38, -61], [-47, -69, -49, 68, 51, 66], [39, 68, 48, -61, 51, 58], [-61, 51, -45, 39, 38], [-76, -47, -49, 51], [45, 68, 51, -64, -54, -61], [-37, 51, 38, 50, 39, -49], [-70, 69, 68, 67, 66], [51, -55, 69], [-79, 51, 54, 55], [-75, 46, -49, -50], [53, 75, 79, 54, 76, -48, 52, 46], [-67, -53, -50, -48, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h926 a assignment
  · exact h903 a assignment
  · exact h893 a assignment
  · exact h737 a assignment
  · exact h909 a assignment
  · exact h904 a assignment
  · exact h655 a assignment
  · exact h924 a assignment
  · exact h272 a assignment
  · exact h86 a assignment
  · exact h58 a assignment
  · exact h927 a assignment
  · exact h915 a assignment
  · exact h916 a assignment
  · exact h21 a assignment
  · exact h857 a assignment
  · exact h928 a assignment
  · exact h200 a assignment
  · exact h213 a assignment
  · exact h505 a assignment
  · exact h721 a assignment
  · exact h367 a assignment
  · exact h26 a assignment
  · exact h703 a assignment
  · exact h777 a assignment
  · exact h727 a assignment
  · exact h720 a assignment
  · exact h929 a assignment
  · exact h550 a assignment

include assignment in
private theorem h931 : RUP.trueClause a (([45, -48, -57, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [-83, -59, -62, -65], [63, -62, -64, -65], [-63, -58, -57, 83, -62, -64], [39, -57, -59, -62, -64], [61, -62, -64], [-68, -64, -61, 58, -57], [-39, 68, -48, -61, -51, 58], [-38, -57, -59, -62, -64], [70, -57, -59, -62, -64], [-57, -70, -62, 68, -64, -66], [56, -64, -57, -63, 58, -62], [-39, -64, 42, -61, 45, 58], [38, -65, -43, -61, 45, -59], [38, -64, -41, -61, 45, -57], [45, 68, 51, -64, -54, -61], [-42, 36, 58, -39], [-36, -63, -40, 58, -42, -56], [-57, 47, 41, 38, -36], [41, -70, -52, -64, 54, -62], [37, -36, 66, -56, -57, -62], [-36, 44, -37, -42, -39, 40], [-37, -61, 38, -60, -39, -59], [49, -37, -59, 38], [-46, -36, -56, -37], [60, 50, -44, -39, -37], [67, -63, 60, 58, -56], [38, -55, 43, 51, 45, -49], [-76, -47, -49, 51], [-75, 46, -49, -50], [-67, -53, -50, -48, 46], [-79, 51, 54, 55], [53, 75, 79, 54, 76, -48, 52, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h737 a assignment
  · exact h909 a assignment
  · exact h904 a assignment
  · exact h930 a assignment
  · exact h903 a assignment
  · exact h655 a assignment
  · exact h215 a assignment
  · exact h926 a assignment
  · exact h924 a assignment
  · exact h272 a assignment
  · exact h86 a assignment
  · exact h134 a assignment
  · exact h116 a assignment
  · exact h112 a assignment
  · exact h367 a assignment
  · exact h922 a assignment
  · exact h76 a assignment
  · exact h468 a assignment
  · exact h259 a assignment
  · exact h927 a assignment
  · exact h17 a assignment
  · exact h65 a assignment
  · exact h915 a assignment
  · exact h916 a assignment
  · exact h490 a assignment
  · exact h636 a assignment
  · exact h38 a assignment
  · exact h721 a assignment
  · exact h720 a assignment
  · exact h550 a assignment
  · exact h727 a assignment
  · exact h929 a assignment

include assignment in
private theorem h932 : RUP.trueClause a (([-37, -45, 51, -48, -39, 38, 66, -56, 58, -57, -59, -63, -61, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-37, -61, 38, -60, -39, -59], [36, -59, -37, -57, 38, -56], [49, -37, -59, 38], [-46, -36, -56, -37], [60, -61, -69, -65], [67, -63, 60, 58, -56], [58, -48, 42, -39, -36], [-36, -49, -37, 47, 38, 46], [46, 51, -47, 50, -48, -49], [-76, -47, -49, 51], [51, -55, 69], [-39, -54, -42, 51, -45, -48], [-47, -52, 66], [-75, 46, -49, -50], [-67, -53, -50, -48, 46], [-79, 51, 54, 55], [53, 75, 79, 54, 76, -48, 52, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h65 a assignment
  · exact h54 a assignment
  · exact h915 a assignment
  · exact h916 a assignment
  · exact h752 a assignment
  · exact h636 a assignment
  · exact h479 a assignment
  · exact h21 a assignment
  · exact h28 a assignment
  · exact h721 a assignment
  · exact h777 a assignment
  · exact h43 a assignment
  · exact h857 a assignment
  · exact h720 a assignment
  · exact h550 a assignment
  · exact h727 a assignment
  · exact h929 a assignment

include assignment in
private theorem h933 : RUP.trueClause a (([-48, -57, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[39, -57, -59, -62, -64], [-38, -57, -59, -62, -64], [61, -62, -64], [-64, 65], [-83, -59, -62, -65], [63, -62, -64, -65], [-63, -58, -57, 83, -62, -64], [-68, -64, -61, 58, -57], [70, -57, -59, -62, -64], [-57, -70, -62, 68, -64, -66], [56, -64, -57, -63, 58, -62], [-39, 68, -48, -61, -51, 58], [45, -48, -57, -59, -62, -64], [-37, -45, 51, -48, -39, 38, 66, -56, 58, -57, -59, -63, -61, -65], [37, -36, 66, -56, -57, -62], [-42, 36, 58, -39], [58, -48, 42, -39, 36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h930 a assignment
  · exact h926 a assignment
  · exact h903 a assignment
  · exact h893 a assignment
  · exact h737 a assignment
  · exact h909 a assignment
  · exact h904 a assignment
  · exact h655 a assignment
  · exact h924 a assignment
  · exact h272 a assignment
  · exact h86 a assignment
  · exact h215 a assignment
  · exact h931 a assignment
  · exact h932 a assignment
  · exact h927 a assignment
  · exact h922 a assignment
  · exact h471 a assignment

include assignment in
private theorem h934 : RUP.trueClause a (([-43, 37, -59, 38] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59, 49, -43, 38, 37], [-43, -49, -59, 37]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h489 a assignment
  · exact h853 a assignment

include assignment in
private theorem h935 : RUP.trueClause a (([37, -39, 38, 66, -56, 58, -57, -59, -63, -62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[37, -36, 66, -56, -57, -62], [-42, 36, 58, -39], [36, -63, 40, 58, 42, -56], [37, -62, -40, -59, 43, -56], [-43, 37, -59, 38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h927 a assignment
  · exact h922 a assignment
  · exact h77 a assignment
  · exact h96 a assignment
  · exact h934 a assignment

include assignment in
private theorem h936 : RUP.trueClause a (([-45, 42, 69, 48, -39, 38, -70, -61] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[38, -45, -61, -51], [51, -55, 69], [-39, 54, 42, 51, -45, 48], [-54, 55, -70]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h877 a assignment
  · exact h777 a assignment
  · exact h42 a assignment
  · exact h798 a assignment

include assignment in
private theorem h937 : RUP.trueClause a (([-57, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [-83, -59, -62, -65], [63, -62, -64, -65], [61, -62, -64], [-63, -58, -57, 83, -62, -64], [-68, -64, -61, 58, -57], [56, -64, -57, -63, 58, -62], [70, -57, -59, -62, -64], [-57, -70, -62, 68, -64, -66], [-38, -57, -59, -62, -64], [39, -57, -59, -62, -64], [-48, -57, -59, -62, -64], [37, -39, 38, 66, -56, 58, -57, -59, -63, -62], [-37, -61, 38, -60, -39, -59], [36, -59, -37, -57, 38, -56], [-46, -36, -56, -37], [60, -61, -69, -65], [58, 48, -42, -39, -36], [-56, 46, -40, -37, -36], [-36, -62, 40, -57, -41, -56], [-45, 42, 69, 48, -39, 38, -70, -61], [-36, 45, 38, 42, -39, 41]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h737 a assignment
  · exact h909 a assignment
  · exact h903 a assignment
  · exact h904 a assignment
  · exact h655 a assignment
  · exact h86 a assignment
  · exact h924 a assignment
  · exact h272 a assignment
  · exact h926 a assignment
  · exact h930 a assignment
  · exact h933 a assignment
  · exact h935 a assignment
  · exact h65 a assignment
  · exact h54 a assignment
  · exact h916 a assignment
  · exact h752 a assignment
  · exact h472 a assignment
  · exact h462 a assignment
  · exact h74 a assignment
  · exact h936 a assignment
  · exact h19 a assignment

include assignment in
private theorem h938 : RUP.trueClause a (([42, -36, -68, 58, -39, 38, -61, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-39, -64, 42, -61, 45, 58], [58, -48, 42, -39, -36], [38, -45, -61, -51], [-39, -68, 48, -61, 51, 58]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h134 a assignment
  · exact h479 a assignment
  · exact h877 a assignment
  · exact h216 a assignment

include assignment in
private theorem h939 : RUP.trueClause a (([-66, 57, -62, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-66, -62, -59, 57, 56], [-66, -62, -59, 57, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h616 a assignment
  · exact h621 a assignment

include assignment in
private theorem h940 : RUP.trueClause a (([50, 67, 53] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[53, -46, 67, 50], [53, 46, 67, 50]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h885 a assignment
  · exact h913 a assignment

include assignment in
private theorem h941 : RUP.trueClause a (([-56, 53, -48, -68, 58, -39, 66, 57, -63] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-56, -68, 57, -67, 58, 66], [67, -63, 60, 58, -56], [-39, 67, -48, -60, -50, 58], [50, 67, 53]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h158 a assignment
  · exact h636 a assignment
  · exact h212 a assignment
  · exact h940 a assignment

include assignment in
private theorem h942 : RUP.trueClause a (([56, 58, -59, -63, -62, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-60, -63, 56, 58], [56, -65, -59, -63, 60, -62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h766 a assignment
  · exact h103 a assignment

include assignment in
private theorem h943 : RUP.trueClause a (([58, -39, 38, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-57, -59, -62, -64], [-66, 57, -62, -59], [-64, 65], [63, -62, -64, -65], [61, -62, -64], [68, -64, -61, 58, 57], [36, -61, 38, 58, -39, 57], [42, -36, -68, 58, -39, 38, -61, -64], [58, 48, -42, -39, -36], [56, 58, -59, -63, -62, -65], [-56, -68, 57, -67, 58, 66], [-56, 53, -48, -68, 58, -39, 66, 57, -63], [-42, 67, -48, -63, -53, 58]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h937 a assignment
  · exact h939 a assignment
  · exact h893 a assignment
  · exact h909 a assignment
  · exact h903 a assignment
  · exact h650 a assignment
  · exact h59 a assignment
  · exact h938 a assignment
  · exact h472 a assignment
  · exact h942 a assignment
  · exact h158 a assignment
  · exact h941 a assignment
  · exact h288 a assignment

include assignment in
private theorem h944 : RUP.trueClause a (([-58, 57, -64, -63, -62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-56, -64, 57, -63, -58, -62], [-58, -63, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h84 a assignment
  · exact h765 a assignment

include assignment in
private theorem h945 : RUP.trueClause a (([-53, 44, 45, 51, 39, 38, 67, 70, 69, -56, -68, 58, 57, -63, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[51, -55, 69], [67, -63, 60, 58, -56], [50, 70, -53, 69, 55, 67], [-60, -50, 44, 39, 37], [-46, 39, -37, 67, -56, 58, -63], [40, 67, 46, -63, -53, -56], [67, -53, -50, -48, 46], [-63, -53, 44, -42, -40], [-56, 46, -40, -37, -36], [48, 51, -68, 54], [-64, -54, 45, 42, -41], [-68, -54, 51, 48, -47], [57, 47, 41, 38, 36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h777 a assignment
  · exact h636 a assignment
  · exact h353 a assignment
  · exact h491 a assignment
  · exact h919 a assignment
  · exact h239 a assignment
  · exact h560 a assignment
  · exact h511 a assignment
  · exact h462 a assignment
  · exact h769 a assignment
  · exact h518 a assignment
  · exact h565 a assignment
  · exact h467 a assignment

include assignment in
private theorem h946 : RUP.trueClause a (([48, 46, -37, 53, 39, 67, 58, -63] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[50, 67, 53], [-36, -50, -37, 48, 39, 46], [42, 67, 48, -63, 53, 58], [58, 48, -42, 39, 36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h940 a assignment
  · exact h22 a assignment
  · exact h287 a assignment
  · exact h473 a assignment

include assignment in
private theorem h947 : RUP.trueClause a (([38, -59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [63, -62, -64, -65], [-57, -59, -62, -64], [-58, 57, -64, -63, -62], [56, 58, -59, -63, -62, -65], [-66, 57, -62, -59], [61, -62, -64], [68, -64, -61, 58, 57], [-56, -68, 57, -67, 58, 66], [67, -63, 60, 58, -56], [57, -70, -62, -68, -64, 66], [57, -69, -59, -68, -61, 66], [58, -39, 38, -59, -62, -64], [-51, 39, 38, -61], [-61, 51, -45, 39, 38], [51, -55, 69], [39, -65, -44, -61, 45, -60], [-53, 44, 45, 51, 39, 38, 67, 70, 69, -56, -68, 58, 57, -63, -64], [50, 67, 53], [-60, -50, 44, 39, 37], [69, 55, 51, -50, 49], [-46, 39, -37, 67, -56, 58, -63], [46, 55, -49, 53, -50, -52], [-75, 46, -49, -50], [-77, 46, 52, 53], [48, 46, -37, 53, 39, 67, 58, -63], [-48, 51, -68, -54], [46, 51, 47, -50, -48, -49], [-78, -48, 53, 54], [-79, 51, 54, 55], [-76, -47, -49, 51], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h909 a assignment
  · exact h937 a assignment
  · exact h944 a assignment
  · exact h942 a assignment
  · exact h939 a assignment
  · exact h903 a assignment
  · exact h650 a assignment
  · exact h158 a assignment
  · exact h636 a assignment
  · exact h269 a assignment
  · exact h208 a assignment
  · exact h943 a assignment
  · exact h928 a assignment
  · exact h505 a assignment
  · exact h777 a assignment
  · exact h138 a assignment
  · exact h945 a assignment
  · exact h940 a assignment
  · exact h491 a assignment
  · exact h588 a assignment
  · exact h919 a assignment
  · exact h36 a assignment
  · exact h720 a assignment
  · exact h723 a assignment
  · exact h946 a assignment
  · exact h768 a assignment
  · exact h29 a assignment
  · exact h726 a assignment
  · exact h727 a assignment
  · exact h721 a assignment
  · exact h729 a assignment

include assignment in
private theorem h948 : RUP.trueClause a (([53, -38, 67, 70, 69, -59, -61] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[50, 67, 53], [-50, 70, 53, 69, -55, 67], [-50, -51, 69, 55], [-38, 69, -49, -61, 51, -59], [69, 55, 51, -50, 49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h940 a assignment
  · exact h356 a assignment
  · exact h772 a assignment
  · exact h198 a assignment
  · exact h588 a assignment

include assignment in
private theorem h949 : RUP.trueClause a (([51, -50, -38, 69, -59, -61] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-38, 69, -49, -61, 51, -59], [51, -55, 69], [69, 55, 51, -50, 49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h198 a assignment
  · exact h777 a assignment
  · exact h588 a assignment

include assignment in
private theorem h950 : RUP.trueClause a (([-51, -50, 69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-50, -51, 69, 55], [-50, -51, 69, -55]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h772 a assignment
  · exact h771 a assignment

include assignment in
private theorem h951 : RUP.trueClause a (([-50, -38, -61, 69, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[51, -50, -38, 69, -59, -61], [-51, -50, 69]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h949 a assignment
  · exact h950 a assignment

include assignment in
private theorem h952 : RUP.trueClause a (([49, 50, -53, 67, 70, 69, -68, 66] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[50, 70, -53, 69, 55, 67], [51, -55, 69], [49, 52, 67, 66, 69, -68, 70], [-47, -52, 66], [54, -52, 70, -55], [46, 47, 66, -52], [-76, 47, 49, -51], [-48, 70, -53, -68, -54, 67], [-79, -51, -54, -55], [-77, -46, -52, -53], [-75, -46, 49, 50], [75, 76, 77, 78, 79], [-78, 48, -53, -54]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h353 a assignment
  · exact h777 a assignment
  · exact h887 a assignment
  · exact h857 a assignment
  · exact h862 a assignment
  · exact h852 a assignment
  · exact h722 a assignment
  · exact h293 a assignment
  · exact h728 a assignment
  · exact h724 a assignment
  · exact h719 a assignment
  · exact h729 a assignment
  · exact h725 a assignment

include assignment in
private theorem h953 : RUP.trueClause a (([-59, -62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [63, -62, -64, -65], [61, -62, -64], [-57, -59, -62, -64], [-66, 57, -62, -59], [-58, 57, -64, -63, -62], [68, -64, -61, 58, 57], [56, 58, -59, -63, -62, -65], [57, -69, -59, -68, -61, 66], [57, -70, -62, -68, -64, 66], [-56, -68, 57, -67, 58, 66], [67, -63, 60, 58, -56], [38, -59, -62, -64], [53, -38, 67, 70, 69, -59, -61], [-50, -38, -61, 69, -59], [50, 70, -53, 69, 55, 67], [44, 69, 50, -65, -55, -60], [51, -55, 69], [39, 69, 50, -61, -51, -60], [-60, 50, -44, -39, -37], [49, 50, -53, 67, 70, 69, -68, 66], [-43, -49, -59, 37], [37, 66, 46, -59, -49, -56], [-38, -65, 43, -61, -45, -59], [-40, -65, 43, -63, -44, -62], [-39, -64, 42, -61, 45, 58], [-56, -46, 40, 37, -36], [-42, 36, 58, -39]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h909 a assignment
  · exact h903 a assignment
  · exact h937 a assignment
  · exact h939 a assignment
  · exact h944 a assignment
  · exact h650 a assignment
  · exact h942 a assignment
  · exact h208 a assignment
  · exact h269 a assignment
  · exact h158 a assignment
  · exact h636 a assignment
  · exact h947 a assignment
  · exact h948 a assignment
  · exact h951 a assignment
  · exact h353 a assignment
  · exact h345 a assignment
  · exact h777 a assignment
  · exact h217 a assignment
  · exact h493 a assignment
  · exact h952 a assignment
  · exact h853 a assignment
  · exact h161 a assignment
  · exact h113 a assignment
  · exact h99 a assignment
  · exact h134 a assignment
  · exact h456 a assignment
  · exact h922 a assignment

include assignment in
private theorem h954 : RUP.trueClause a (([69, 59, -65, -61] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[69, -65, -61, 60, 59], [69, -65, -61, -60, 59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h672 a assignment
  · exact h678 a assignment

include assignment in
private theorem h955 : RUP.trueClause a (([-62, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [61, -62, -64], [63, -62, -64, -65], [-59, -62, -64], [-57, -65, 59, -64, -61, -62], [-58, 57, -64, -63, -62], [69, 59, -65, -61], [60, -61, -69, -65], [-56, -65, 59, -63, -60, -62], [-60, -63, 56, 58]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h903 a assignment
  · exact h909 a assignment
  · exact h953 a assignment
  · exact h126 a assignment
  · exact h944 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h106 a assignment
  · exact h766 a assignment

include assignment in
private theorem h956 : RUP.trueClause a (([56, -60, 62, 59, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[56, -65, 59, 63, -60, 62], [-58, -63, 56], [-60, -63, 56, 58]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h102 a assignment
  · exact h765 a assignment
  · exact h766 a assignment

include assignment in
private theorem h957 : RUP.trueClause a (([33, -63, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [-62, -64], [70, -65, -64, -63, 62], [33, 35, -70], [33, -35, -63, -70, -64, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h955 a assignment
  · exact h696 a assignment
  · exact h783 a assignment
  · exact h795 a assignment

include assignment in
private theorem h958 : RUP.trueClause a (([24, 32, 19, 16, 17, 18, -63, 57, -61, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[33, -63, -64], [-62, -64], [-20, 24, -63, -33], [16, 24, 17, -22, 19, 20], [21, 20, 62, 32], [18, -64, -21, -61, -25, 57], [20, 25, -21, 24, 22, 23], [62, 32, -23, -21, 20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h957 a assignment
  · exact h955 a assignment
  · exact h897 a assignment
  · exact h1 a assignment
  · exact h791 a assignment
  · exact h107 a assignment
  · exact h2 a assignment
  · exact h401 a assignment

include assignment in
private theorem h959 : RUP.trueClause a (([-35, 19, 17, 18, -53, 52, -54, -63, 57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [-62, -64], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [56, -60, 62, 59, -65], [-16, 59, 17, 57, 18, -56], [33, -63, -64], [70, -65, -64, -63, 62], [34, -35, 52, -53, -54, -70], [-70, -35, -34, -33, -32], [24, 32, 19, 16, 17, 18, -63, 57, -61, -64], [-25, -24, -65, -35], [19, -65, -24, -61, 25, -60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h955 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h956 a assignment
  · exact h50 a assignment
  · exact h957 a assignment
  · exact h696 a assignment
  · exact h808 a assignment
  · exact h433 a assignment
  · exact h958 a assignment
  · exact h809 a assignment
  · exact h131 a assignment

include assignment in
private theorem h960 : RUP.trueClause a (([-30, -28, -67, -33] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-67, -33, -30, -28, 26], [-67, -33, -30, -28, -26]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h425 a assignment
  · exact h427 a assignment

include assignment in
private theorem h961 : RUP.trueClause a (([35, -67, -33, -70, -68, -69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-34, 35, -70], [30, -70, -33, -69, 35, -67], [28, -70, -33, -68, 34, -67], [-30, -28, -67, -33]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h810 a assignment
  · exact h341 a assignment
  · exact h283 a assignment
  · exact h960 a assignment

include assignment in
private theorem h962 : RUP.trueClause a (([-30, -19, -67, -33, -58, -60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-30, -28, -67, -33], [-19, -67, 28, -60, -30, -58]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h960 a assignment
  · exact h210 a assignment

include assignment in
private theorem h963 : RUP.trueClause a (([-19, 18, 32, -35, -67, -63, -58, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[33, -63, -64], [-64, 65], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [-62, -64], [-30, -19, -67, -33, -58, -60], [-24, -69, 30, -65, -35, -60], [-19, -69, 30, -61, -31, -60], [-20, 24, -63, -33], [-19, -65, 24, -61, -25, -60], [-69, -35, 31, 30, 29], [21, 20, 62, 32], [18, -35, 23, 31, 25, -29], [62, 32, -23, -21, 20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h957 a assignment
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h955 a assignment
  · exact h962 a assignment
  · exact h333 a assignment
  · exact h211 a assignment
  · exact h897 a assignment
  · exact h130 a assignment
  · exact h428 a assignment
  · exact h791 a assignment
  · exact h5 a assignment
  · exact h401 a assignment

include assignment in
private theorem h964 : RUP.trueClause a (([18, -67, -53, 52, -54, -63, 57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [-62, -64], [56, -60, 62, 59, -65], [-56, -61, 57, -60, 58, 59], [68, -64, -61, -58, 57], [70, -65, -64, -63, 62], [33, -63, -64], [35, -67, -33, -70, -68, -69], [34, -35, 52, -53, -54, -70], [-70, -35, -34, -33, -32], [-19, 18, 32, -35, -67, -63, -58, 59, -64], [-17, -61, 18, -60, 19, 59], [-35, 19, 17, 18, -53, 52, -54, -63, 57, 59, -64]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h955 a assignment
  · exact h956 a assignment
  · exact h69 a assignment
  · exact h658 a assignment
  · exact h696 a assignment
  · exact h957 a assignment
  · exact h961 a assignment
  · exact h808 a assignment
  · exact h433 a assignment
  · exact h963 a assignment
  · exact h51 a assignment
  · exact h959 a assignment

include assignment in
private theorem h965 : RUP.trueClause a (([24, -34, -35, -63, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[33, -63, -64], [-64, 65], [-62, -64], [70, -65, -64, -63, 62], [-70, -35, -34, -33, -32], [-20, 24, -63, -33], [21, 20, 62, 32], [62, 32, -23, -21, 20], [-21, -35, 23, -34, 25, 32], [-65, -35, -25, 24, 23]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h957 a assignment
  · exact h893 a assignment
  · exact h955 a assignment
  · exact h696 a assignment
  · exact h433 a assignment
  · exact h897 a assignment
  · exact h791 a assignment
  · exact h401 a assignment
  · exact h9 a assignment
  · exact h422 a assignment

include assignment in
private theorem h966 : RUP.trueClause a (([-53, -55, -51, 50, -63, 57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-62, -64], [-64, 65], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [56, -60, 62, 59, -65], [-66, 62, 59, 57, -56], [70, -65, -64, -63, 62], [-69, -55, -51, 50, -49], [49, -70, -52, -69, -55, 66], [-44, -69, 50, -65, -55, -60], [-39, -69, 50, -61, -51, -60], [-51, 39, 38, -61], [45, 39, -61, -38], [-45, -70, 54, -65, -55, -64], [33, -63, -64], [-56, -61, 57, -60, 58, 59], [68, -64, -61, -58, 57], [44, 67, 50, -63, -53, -60], [35, -67, -33, -70, -68, -69], [34, -35, 52, -53, -54, -70], [18, -67, -53, 52, -54, -63, 57, 59, -64], [-61, -18, 39, -19, -38], [24, -34, -35, -63, -64], [-25, -24, -65, -35], [19, -65, -24, -61, 25, -60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h955 a assignment
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h956 a assignment
  · exact h623 a assignment
  · exact h696 a assignment
  · exact h587 a assignment
  · exact h321 a assignment
  · exact h347 a assignment
  · exact h220 a assignment
  · exact h928 a assignment
  · exact h920 a assignment
  · exact h377 a assignment
  · exact h957 a assignment
  · exact h69 a assignment
  · exact h658 a assignment
  · exact h342 a assignment
  · exact h961 a assignment
  · exact h808 a assignment
  · exact h964 a assignment
  · exact h742 a assignment
  · exact h965 a assignment
  · exact h809 a assignment
  · exact h131 a assignment

include assignment in
private theorem h967 : RUP.trueClause a (([-55, -51, 50, -63, 57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [-39, -69, 50, -61, -51, -60], [-51, 39, 38, -61], [45, 39, -61, -38], [-62, -64], [70, -65, -64, -63, 62], [56, -60, 62, 59, -65], [-56, -61, 57, -60, 58, 59], [68, -64, -61, -58, 57], [-45, -70, 54, -65, -55, -64], [-69, -55, -51, 50, -49], [-37, -69, 49, -60, 50, 59], [-53, -55, -51, 50, -63, 57, 59, -64], [50, 67, 53], [-48, -70, 53, -68, -54, -67], [37, -67, -46, -60, 50, -56], [-67, 53, 50, 48, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h220 a assignment
  · exact h928 a assignment
  · exact h920 a assignment
  · exact h955 a assignment
  · exact h696 a assignment
  · exact h956 a assignment
  · exact h69 a assignment
  · exact h658 a assignment
  · exact h377 a assignment
  · exact h587 a assignment
  · exact h175 a assignment
  · exact h966 a assignment
  · exact h940 a assignment
  · exact h294 a assignment
  · exact h168 a assignment
  · exact h555 a assignment

include assignment in
private theorem h968 : RUP.trueClause a (([-51, 50, -63, 57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [61, 59, -65], [69, 59, -65, -61], [-55, -51, 50, -63, 57, 59, -64], [50, 49, -69, 55], [-69, 55, -51, 50, -49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h967 a assignment
  · exact h854 a assignment
  · exact h576 a assignment

include assignment in
private theorem h969 : RUP.trueClause a (([55, 51, 50, -69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[50, 49, -69, 55], [-69, 55, 51, 50, -49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h854 a assignment
  · exact h589 a assignment

include assignment in
private theorem h970 : RUP.trueClause a (([51, 50, -69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[55, 51, 50, -69], [51, 49, -69, -55], [-69, -55, 51, 50, -49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h969 a assignment
  · exact h860 a assignment
  · exact h579 a assignment

include assignment in
private theorem h971 : RUP.trueClause a (([50, -63, 57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [61, 59, -65], [69, 59, -65, -61], [-51, 50, -63, 57, 59, -64], [51, 50, -69]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h968 a assignment
  · exact h970 a assignment

include assignment in
private theorem h972 : RUP.trueClause a (([-55, 51, 59, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[61, 59, -65], [69, 59, -65, -61], [51, 49, -69, -55], [-45, -69, 51, -65, -55, -61], [43, -69, -49, -65, -55, 59], [-43, 45, -65, -55]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h860 a assignment
  · exact h374 a assignment
  · exact h308 a assignment
  · exact h775 a assignment

include assignment in
private theorem h973 : RUP.trueClause a (([43, 38, 59, 49] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[59, 49, 43, 38, 37], [59, 49, 43, 38, -37]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h484 a assignment
  · exact h481 a assignment

include assignment in
private theorem h974 : RUP.trueClause a (([51, -70, 57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [-62, -64], [56, -60, 62, 59, -65], [-56, -61, 57, -60, 58, 59], [68, -64, -61, -58, 57], [-66, 62, 59, 57, -56], [-55, 51, 59, -65], [-54, 55, -70], [-52, 54, -70, 55], [-47, -70, 52, -68, 54, 66], [-43, -70, 52, -65, 55, 62], [-49, -70, 52, -69, 55, 66], [-38, -68, 47, -61, 51, 57], [43, 38, 59, 49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h955 a assignment
  · exact h956 a assignment
  · exact h69 a assignment
  · exact h658 a assignment
  · exact h623 a assignment
  · exact h972 a assignment
  · exact h798 a assignment
  · exact h875 a assignment
  · exact h265 a assignment
  · exact h317 a assignment
  · exact h326 a assignment
  · exact h193 a assignment
  · exact h973 a assignment

include assignment in
private theorem h975 : RUP.trueClause a (([43, 49, -51, -50, 59, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[61, 59, -65], [69, 59, -65, -61], [-69, 55, -51, -50, 49], [60, -61, -69, -65], [43, 38, 59, 49], [59, 49, 43, -38, -37], [-38, -55, 43, -51, 45, 49], [37, -61, -38, -60, -39, 59], [-60, -50, 44, 39, 37], [-65, -55, -45, -44, 43]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h583 a assignment
  · exact h752 a assignment
  · exact h973 a assignment
  · exact h486 a assignment
  · exact h39 a assignment
  · exact h63 a assignment
  · exact h491 a assignment
  · exact h523 a assignment

include assignment in
private theorem h976 : RUP.trueClause a (([37, 39, -38, -45, -43, -50, -60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-60, -50, 44, 39, 37], [37, -45, -38, -44, 39, -43]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h491 a assignment
  · exact h20 a assignment

include assignment in
private theorem h977 : RUP.trueClause a (([49, -63, 57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [-62, -64], [70, -65, -64, -63, 62], [51, -70, 57, 59, -64], [50, -63, 57, 59, -64], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [56, -60, 62, 59, -65], [-56, -61, 57, -60, 58, 59], [68, -64, -61, -58, 57], [-66, 62, 59, 57, -56], [-69, 55, -51, -50, 49], [-51, -70, 54, -69, -55, -68], [49, -70, -52, -69, -55, 66], [43, 49, -51, -50, 59, -65], [-43, 45, -65, -55], [41, -55, -43, -54, -45, 52], [38, -65, -43, -61, -45, 59], [-64, -54, -45, -42, -41], [-39, -64, 42, -61, -45, -58], [37, 39, -38, -45, -43, -50, -60], [36, -60, -37, -58, 39, -56], [-37, 66, 46, 59, 49, -56], [-46, -36, -56, -37]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h955 a assignment
  · exact h696 a assignment
  · exact h974 a assignment
  · exact h971 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h956 a assignment
  · exact h69 a assignment
  · exact h658 a assignment
  · exact h623 a assignment
  · exact h583 a assignment
  · exact h381 a assignment
  · exact h321 a assignment
  · exact h975 a assignment
  · exact h775 a assignment
  · exact h40 a assignment
  · exact h117 a assignment
  · exact h520 a assignment
  · exact h133 a assignment
  · exact h976 a assignment
  · exact h56 a assignment
  · exact h165 a assignment
  · exact h916 a assignment

include assignment in
private theorem h978 : RUP.trueClause a (([-47, -54, -68, -51] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-68, -54, -51, 48, -47], [-68, -54, -51, -48, -47]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h570 a assignment
  · exact h566 a assignment

include assignment in
private theorem h979 : RUP.trueClause a (([-63, 57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [-62, -64], [56, -60, 62, 59, -65], [-56, -61, 57, -60, 58, 59], [68, -64, -61, -58, 57], [-66, 62, 59, 57, -56], [70, -65, -64, -63, 62], [51, -70, 57, 59, -64], [49, -63, 57, 59, -64], [47, -69, -49, -68, -51, 66], [-47, -52, 66], [-47, -70, 52, -68, 54, 66], [-47, -54, -68, -51]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h955 a assignment
  · exact h956 a assignment
  · exact h69 a assignment
  · exact h658 a assignment
  · exact h623 a assignment
  · exact h696 a assignment
  · exact h974 a assignment
  · exact h977 a assignment
  · exact h203 a assignment
  · exact h857 a assignment
  · exact h265 a assignment
  · exact h978 a assignment

include assignment in
private theorem h980 : RUP.trueClause a (([-54, -51, 57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [-62, -64], [56, -60, 62, 59, -65], [-56, -61, 57, -60, 58, 59], [-63, 57, 59, -64], [-67, 63, -60, -58, -56], [-70, -65, -64, 63, 62], [68, -64, -61, -58, 57], [-66, 62, 59, 57, -56], [-51, 70, -54, -69, 55, -68], [-47, -54, -68, -51], [52, -55, 70, 66, 67, -69, -68], [46, 47, 66, -52], [47, -69, -49, -68, -51, 66], [-43, 70, -52, -65, -55, 62], [-53, -55, -54, 49, -46, 47, -52, 70, 67, -69, -68], [43, 49, -51, -50, 59, -65], [50, 67, 53]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h955 a assignment
  · exact h956 a assignment
  · exact h69 a assignment
  · exact h979 a assignment
  · exact h641 a assignment
  · exact h687 a assignment
  · exact h658 a assignment
  · exact h623 a assignment
  · exact h379 a assignment
  · exact h978 a assignment
  · exact h865 a assignment
  · exact h852 a assignment
  · exact h203 a assignment
  · exact h315 a assignment
  · exact h858 a assignment
  · exact h975 a assignment
  · exact h940 a assignment

include assignment in
private theorem h981 : RUP.trueClause a (([49, -51, -69, 55] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-69, 55, -51, -50, 49], [50, 49, -69, 55]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h583 a assignment
  · exact h854 a assignment

include assignment in
private theorem h982 : RUP.trueClause a (([-51, 57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [-62, -64], [56, -60, 62, 59, -65], [-56, -61, 57, -60, 58, 59], [-63, 57, 59, -64], [-67, 63, -60, -58, -56], [-70, -65, -64, 63, 62], [68, -64, -61, -58, 57], [-66, 62, 59, 57, -56], [-54, -51, 57, 59, -64], [45, -68, -51, -64, 54, -61], [54, 52, -68, 70, 66, 67, -69], [38, -45, -61, -51], [-47, -52, 66], [54, -52, 70, -55], [-38, 66, 47, 59, -49, 57], [49, -51, -69, 55]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h955 a assignment
  · exact h956 a assignment
  · exact h69 a assignment
  · exact h979 a assignment
  · exact h641 a assignment
  · exact h687 a assignment
  · exact h658 a assignment
  · exact h623 a assignment
  · exact h980 a assignment
  · exact h368 a assignment
  · exact h850 a assignment
  · exact h877 a assignment
  · exact h857 a assignment
  · exact h862 a assignment
  · exact h190 a assignment
  · exact h981 a assignment

include assignment in
private theorem h983 : RUP.trueClause a (([49, 55, 51, 70, 66, -69, -61, 59, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[49, 70, 52, -69, 55, 66], [-38, -69, 49, -61, 51, 59], [-43, 66, 49, 62, -52, 59], [43, 38, 59, 49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h319 a assignment
  · exact h197 a assignment
  · exact h305 a assignment
  · exact h973 a assignment

include assignment in
private theorem h984 : RUP.trueClause a (([-52, -37, 66, -56, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-47, -52, 66], [46, 47, 66, -52], [40, 66, -46, 62, -52, -56], [-46, -36, -56, -37], [-56, -46, -40, -37, 36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h857 a assignment
  · exact h852 a assignment
  · exact h231 a assignment
  · exact h916 a assignment
  · exact h453 a assignment

include assignment in
private theorem h985 : RUP.trueClause a (([57, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [-62, -64], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [56, -60, 62, 59, -65], [-56, -61, 57, -60, 58, 59], [-66, 62, 59, 57, -56], [68, -64, -61, -58, 57], [-63, 57, 59, -64], [-70, -65, -64, 63, 62], [-67, 63, -60, -58, -56], [-51, 57, 59, -64], [51, 50, -69], [-55, 51, 59, -65], [44, -69, -50, -65, 55, -60], [49, 55, 51, 70, 66, -69, -61, 59, 62], [37, -69, -49, -60, -50, 59], [-52, -37, 66, -56, 62], [54, 52, -68, 70, 66, 67, -69], [-53, 52, 70, -54], [-48, 51, -68, -54], [-42, -68, 48, -64, -54, -58], [67, 53, -50, 48, -46], [63, 53, -44, 42, 40], [-40, 66, 46, 62, 52, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h955 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h956 a assignment
  · exact h69 a assignment
  · exact h623 a assignment
  · exact h658 a assignment
  · exact h979 a assignment
  · exact h687 a assignment
  · exact h641 a assignment
  · exact h982 a assignment
  · exact h970 a assignment
  · exact h972 a assignment
  · exact h343 a assignment
  · exact h983 a assignment
  · exact h172 a assignment
  · exact h984 a assignment
  · exact h850 a assignment
  · exact h851 a assignment
  · exact h768 a assignment
  · exact h289 a assignment
  · exact h556 a assignment
  · exact h510 a assignment
  · exact h236 a assignment

include assignment in
private theorem h986 : RUP.trueClause a (([52, -49, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[57, 59, -64], [-64, 65], [61, 59, -65], [69, 59, -65, -61], [-62, -64], [60, -61, -69, -65], [56, -60, 62, 59, -65], [66, 62, 59, -57, -56], [-57, -69, 59, -68, -61, -66], [59, 70, 62, -69, -65, -66], [-49, -70, 52, -69, -55, -66], [-43, -70, 52, -65, 55, 62], [-54, 55, -70], [-41, -70, 52, -64, 54, 62], [47, -70, 52, 68, 54, -66], [62, 52, 43, 41, -40], [-66, 52, -49, -47, -46], [40, -66, 46, 62, 52, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h985 a assignment
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h955 a assignment
  · exact h752 a assignment
  · exact h956 a assignment
  · exact h617 a assignment
  · exact h206 a assignment
  · exact h329 a assignment
  · exact h327 a assignment
  · exact h317 a assignment
  · exact h798 a assignment
  · exact h260 a assignment
  · exact h262 a assignment
  · exact h506 a assignment
  · exact h545 a assignment
  · exact h233 a assignment

include assignment in
private theorem h987 : RUP.trueClause a (([-47, -52, -49, 68, -70, -66, 59, -65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[61, 59, -65], [69, 59, -65, -61], [-47, -70, -52, 68, -54, -66], [-47, -69, -49, 68, -51, -66], [-52, 54, -70, 55], [-55, 51, 59, -65]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h266 a assignment
  · exact h201 a assignment
  · exact h875 a assignment
  · exact h972 a assignment

include assignment in
private theorem h988 : RUP.trueClause a (([-52, -49, -65, 68, -70, -66, 59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-47, -52, -49, 68, -70, -66, 59, -65], [-52, 46, -66, 47], [-66, -52, -49, 47, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h987 a assignment
  · exact h805 a assignment
  · exact h541 a assignment

include assignment in
private theorem h989 : RUP.trueClause a (([-49, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[57, 59, -64], [-64, 65], [61, 59, -65], [69, 59, -65, -61], [-62, -64], [60, -61, -69, -65], [56, -60, 62, 59, -65], [66, 62, 59, -57, -56], [-57, -69, 59, -68, -61, -66], [59, 70, 62, -69, -65, -66], [52, -49, 59, -64], [-52, -49, -65, 68, -70, -66, 59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h985 a assignment
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h955 a assignment
  · exact h752 a assignment
  · exact h956 a assignment
  · exact h617 a assignment
  · exact h206 a assignment
  · exact h329 a assignment
  · exact h986 a assignment
  · exact h988 a assignment

include assignment in
private theorem h990 : RUP.trueClause a (([-52, 49, 68, -70, 67, -66, -69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[49, -70, -52, -69, 55, -66], [51, 49, -69, -55], [54, -51, -55, -66, 67, -69, -70, 68], [-70, -55, -54, 53, -52], [-47, -70, -52, 68, -54, -66], [50, -70, -53, -69, -55, 67], [-46, -55, 49, -53, -50, -52], [-52, 46, -66, 47]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h320 a assignment
  · exact h860 a assignment
  · exact h804 a assignment
  · exact h603 a assignment
  · exact h266 a assignment
  · exact h351 a assignment
  · exact h37 a assignment
  · exact h805 a assignment

include assignment in
private theorem h991 : RUP.trueClause a (([35, -70, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [-62, -64], [-70, -65, -64, 63, 62], [33, -63, -64], [-34, 35, -70], [24, -70, -33, -65, 35, -63], [-70, 35, 34, -33, -32], [22, -70, -33, -64, 34, -63], [-21, -70, 32, -64, 34, 62], [-63, -33, -24, -22, -20], [21, 20, 62, 32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h955 a assignment
  · exact h687 a assignment
  · exact h957 a assignment
  · exact h810 a assignment
  · exact h335 a assignment
  · exact h437 a assignment
  · exact h280 a assignment
  · exact h250 a assignment
  · exact h408 a assignment
  · exact h791 a assignment

include assignment in
private theorem h992 : RUP.trueClause a (([-55, 59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [-62, -64], [56, -60, 62, 59, -65], [57, 59, -64], [66, 62, 59, -57, -56], [-56, -69, 59, -67, -60, -66], [59, 70, 62, -69, -65, -66], [-70, -65, -64, 63, 62], [33, -63, -64], [35, -70, -64], [30, -70, -33, -69, -35, 67], [-49, 59, -64], [-57, -69, 59, -68, -61, -66], [-52, 49, 68, -70, 67, -66, -69], [-46, 49, -66, 52], [37, -66, 46, 59, 49, -56], [40, -66, 46, 62, 52, -56], [-56, 46, -40, -37, -36], [46, -70, 52, 67, 53, -66], [46, -69, 49, 67, 50, -66], [51, 49, -69, -55], [-70, -55, 54, -53, 52], [43, 49, -51, -50, 59, -65], [-43, 45, -65, -55], [38, -45, -61, -51], [41, -65, -43, -64, -45, 62], [-64, -54, -45, -42, -41], [36, -64, -41, -58, 42, -57], [34, -35, 52, -53, -54, -70], [31, -70, -34, -69, -35, 68], [24, -34, -35, -63, -64], [-69, -35, -31, -30, -29], [-25, -24, -65, -35], [-65, -35, 25, -24, -23], [22, -35, -24, -34, 25, -33], [19, -65, -24, -61, 25, -60], [-18, -35, 23, -31, 25, 29], [-22, 68, -28, -64, -34, 58], [-61, 18, -39, -19, -38], [58, 16, 39, -19, 36], [58, 28, -22, -19, -16]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h955 a assignment
  · exact h956 a assignment
  · exact h985 a assignment
  · exact h617 a assignment
  · exact h185 a assignment
  · exact h329 a assignment
  · exact h687 a assignment
  · exact h957 a assignment
  · exact h991 a assignment
  · exact h340 a assignment
  · exact h989 a assignment
  · exact h206 a assignment
  · exact h990 a assignment
  · exact h880 a assignment
  · exact h159 a assignment
  · exact h233 a assignment
  · exact h462 a assignment
  · exact h243 a assignment
  · exact h183 a assignment
  · exact h860 a assignment
  · exact h602 a assignment
  · exact h975 a assignment
  · exact h775 a assignment
  · exact h877 a assignment
  · exact h121 a assignment
  · exact h520 a assignment
  · exact h81 a assignment
  · exact h808 a assignment
  · exact h366 a assignment
  · exact h965 a assignment
  · exact h429 a assignment
  · exact h809 a assignment
  · exact h419 a assignment
  · exact h12 a assignment
  · exact h131 a assignment
  · exact h6 a assignment
  · exact h276 a assignment
  · exact h741 a assignment
  · exact h743 a assignment
  · exact h395 a assignment

include assignment in
private theorem h993 : RUP.trueClause a (([59, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-62, -64], [-64, 65], [61, 59, -65], [69, 59, -65, -61], [60, -61, -69, -65], [56, -60, 62, 59, -65], [57, 59, -64], [66, 62, 59, -57, -56], [-56, -69, 59, -67, -60, -66], [59, 70, 62, -69, -65, -66], [-57, -69, 59, -68, -61, -66], [-49, 59, -64], [-52, 49, 68, -70, 67, -66, -69], [-46, 49, -66, 52], [46, -69, 49, 67, 50, -66], [46, -70, 52, 67, 53, -66], [-66, 52, 49, 47, 46], [46, 68, -47, 67, -48, -66], [-55, 59, -64], [-54, 55, -70], [48, 55, -50, 54, -51, -53], [-43, -69, 49, -65, 55, 59], [-38, 68, -47, -61, 51, -57], [43, 38, 59, 49]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h955 a assignment
  · exact h893 a assignment
  · exact h872 a assignment
  · exact h954 a assignment
  · exact h752 a assignment
  · exact h956 a assignment
  · exact h985 a assignment
  · exact h617 a assignment
  · exact h185 a assignment
  · exact h329 a assignment
  · exact h206 a assignment
  · exact h989 a assignment
  · exact h990 a assignment
  · exact h880 a assignment
  · exact h183 a assignment
  · exact h243 a assignment
  · exact h537 a assignment
  · exact h151 a assignment
  · exact h992 a assignment
  · exact h798 a assignment
  · exact h46 a assignment
  · exact h310 a assignment
  · exact h195 a assignment
  · exact h973 a assignment

include assignment in
private theorem h994 : RUP.trueClause a (([56, -57, -59, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[66, 62, -59, -57, 56], [-66, 62, -59, -57, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h615 a assignment
  · exact h618 a assignment

include assignment in
private theorem h995 : RUP.trueClause a (([-59, 62, -65, -61, -64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[57, -65, -59, -64, -61, 62], [-56, -59, 62], [56, -57, -59, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h122 a assignment
  · exact h840 a assignment
  · exact h994 a assignment

include assignment in
private theorem h996 : RUP.trueClause a (([-64] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64, 65], [-62, -64], [59, -64], [61, -65, -59, 62], [-59, 62, -65, -61, -64]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h893 a assignment
  · exact h955 a assignment
  · exact h993 a assignment
  · exact h869 a assignment
  · exact h995 a assignment

include assignment in
private theorem h997 : RUP.trueClause a (([-65] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [64, -65]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h996 a assignment
  · exact h900 a assignment

include assignment in
private theorem h998 : RUP.trueClause a (([62, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-65], [-60, 65, -59], [-61, 65, 60, -59], [-56, -59, 62], [57, 65, -59, 64, 61, 62], [56, -57, -59, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h842 a assignment
  · exact h843 a assignment
  · exact h840 a assignment
  · exact h124 a assignment
  · exact h994 a assignment

include assignment in
private theorem h999 : RUP.trueClause a (([40, 37, 56, 46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[56, 46, 40, 37, 36], [56, 46, 40, 37, -36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h459 a assignment
  · exact h452 a assignment

include assignment in
private theorem h1000 : RUP.trueClause a (([52, 49, -66, 56, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[62, -59], [-46, 49, -66, 52], [-37, -66, 46, -59, 49, 56], [-40, -66, 46, -62, 52, 56], [40, 37, 56, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h998 a assignment
  · exact h880 a assignment
  · exact h162 a assignment
  · exact h237 a assignment
  · exact h999 a assignment

include assignment in
private theorem h1001 : RUP.trueClause a (([46, -52, 49, -66] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-52, 46, -66, 47], [-66, -52, 49, -47, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h805 a assignment
  · exact h540 a assignment

include assignment in
private theorem h1002 : RUP.trueClause a (([-47, 49, 56, -57, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[62, -59], [66, -62, -59, -57, 56], [52, 49, -66, 56, -59], [-43, -66, 49, -62, -52, -59], [46, -52, 49, -66], [40, -66, -46, -62, -52, 56], [-62, -52, 43, -41, -40], [38, -66, -47, -59, 49, -57], [-57, -47, 41, -38, -36], [36, -66, -46, -57, -47, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h998 a assignment
  · exact h624 a assignment
  · exact h1000 a assignment
  · exact h306 a assignment
  · exact h1001 a assignment
  · exact h232 a assignment
  · exact h508 a assignment
  · exact h189 a assignment
  · exact h466 a assignment
  · exact h144 a assignment

include assignment in
private theorem h1003 : RUP.trueClause a (([-38, 36, 49, -63, 56, -57, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-65], [62, -59], [66, -62, -59, -57, 56], [52, 49, -66, 56, -59], [46, -52, 49, -66], [40, -66, -46, -62, -52, 56], [56, -46, -40, -37, 36], [-47, 49, 56, -57, -59], [-43, -66, 49, -62, -52, -59], [-62, -52, 43, -41, -40], [-60, 65, -59], [-61, 65, 60, -59], [-69, 65, 61, 60, -59], [-57, 69, -59, -68, 61, -66], [56, 61, -57, 60, -58, -59], [-38, 65, 43, 61, 45, -59], [-38, 68, 47, 61, 51, -57], [37, 61, -38, 60, -39, -59], [-42, 41, 64, -45], [-51, -50, 69], [-76, 47, 49, -51], [36, -44, 37, 42, 39, -40], [58, -48, 42, 39, 36], [-75, -46, 49, 50], [-63, 53, 44, 42, -40], [65, 55, -45, 44, 43], [48, 54, 68, -51], [-77, -46, -52, -53], [-79, -51, -54, -55], [-78, 48, -53, -54], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h998 a assignment
  · exact h624 a assignment
  · exact h1000 a assignment
  · exact h1001 a assignment
  · exact h232 a assignment
  · exact h461 a assignment
  · exact h1002 a assignment
  · exact h306 a assignment
  · exact h508 a assignment
  · exact h842 a assignment
  · exact h843 a assignment
  · exact h677 a assignment
  · exact h207 a assignment
  · exact h67 a assignment
  · exact h114 a assignment
  · exact h194 a assignment
  · exact h61 a assignment
  · exact h878 a assignment
  · exact h950 a assignment
  · exact h722 a assignment
  · exact h16 a assignment
  · exact h478 a assignment
  · exact h719 a assignment
  · exact h513 a assignment
  · exact h524 a assignment
  · exact h803 a assignment
  · exact h724 a assignment
  · exact h728 a assignment
  · exact h725 a assignment
  · exact h729 a assignment

include assignment in
private theorem h1004 : RUP.trueClause a (([-55, 38, 37, 36, 47, -40, -46, 43, -52, 49, -63, 68, 58, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-64], [62, -59], [-62, -52, 43, -41, -40], [-60, 65, -59], [-61, 65, 60, -59], [-69, 65, 61, 60, -59], [51, -55, 69], [-51, -50, 69], [-76, 47, 49, -51], [-39, 69, 50, 61, -51, 60], [-75, -46, 49, 50], [37, -55, 43, 50, -44, 49], [61, -51, 45, 39, 38], [-42, 41, 64, -45], [58, -48, 42, 39, 36], [-63, 53, 44, 42, -40], [48, 54, 68, -51], [-77, -46, -52, -53], [-79, -51, -54, -55], [-78, 48, -53, -54], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h996 a assignment
  · exact h998 a assignment
  · exact h508 a assignment
  · exact h842 a assignment
  · exact h843 a assignment
  · exact h677 a assignment
  · exact h777 a assignment
  · exact h950 a assignment
  · exact h722 a assignment
  · exact h219 a assignment
  · exact h719 a assignment
  · exact h33 a assignment
  · exact h504 a assignment
  · exact h878 a assignment
  · exact h478 a assignment
  · exact h513 a assignment
  · exact h803 a assignment
  · exact h724 a assignment
  · exact h728 a assignment
  · exact h725 a assignment
  · exact h729 a assignment

include assignment in
private theorem h1005 : RUP.trueClause a (([55, -52, -70] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-54, 55, -70], [-52, 54, -70, 55]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h798 a assignment
  · exact h875 a assignment

include assignment in
private theorem h1006 : RUP.trueClause a (([49, -70, 56, -57, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-64], [62, -59], [-70, 65, 64, 63, -62], [-60, 65, -59], [-61, 65, 60, -59], [-69, 65, 61, 60, -59], [66, -62, -59, -57, 56], [-57, 69, -59, -68, 61, -66], [56, 61, -57, 60, -58, -59], [52, 49, -66, 56, -59], [-43, -66, 49, -62, -52, -59], [46, -52, 49, -66], [40, -66, -46, -62, -52, 56], [-62, -52, 43, -41, -40], [-47, 49, 56, -57, -59], [55, -52, -70], [51, -55, 69], [-51, -50, 69], [-44, 69, 50, 65, -55, 60], [-37, 69, 49, 60, 50, -59], [65, -55, 45, 44, 43], [-42, 41, 64, -45], [-36, 64, 41, 58, 42, -57], [-38, 36, 49, -63, 56, -57, -59], [-55, 38, 37, 36, 47, -40, -46, 43, -52, 49, -63, 68, 58, -59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h996 a assignment
  · exact h998 a assignment
  · exact h695 a assignment
  · exact h842 a assignment
  · exact h843 a assignment
  · exact h677 a assignment
  · exact h624 a assignment
  · exact h207 a assignment
  · exact h67 a assignment
  · exact h1000 a assignment
  · exact h306 a assignment
  · exact h1001 a assignment
  · exact h232 a assignment
  · exact h508 a assignment
  · exact h1002 a assignment
  · exact h1005 a assignment
  · exact h777 a assignment
  · exact h950 a assignment
  · exact h348 a assignment
  · exact h174 a assignment
  · exact h527 a assignment
  · exact h878 a assignment
  · exact h79 a assignment
  · exact h1003 a assignment
  · exact h1004 a assignment

include assignment in
private theorem h1007 : RUP.trueClause a (([-46, -49, -70, 68, -66, 69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, 69, 68, 67, -66], [-46, 69, -49, -67, 50, -66], [-51, -50, 69], [51, -55, 69], [-54, 55, -70], [55, -52, -70], [47, -70, 52, 68, 54, -66], [-66, 52, -49, -47, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h707 a assignment
  · exact h177 a assignment
  · exact h950 a assignment
  · exact h777 a assignment
  · exact h798 a assignment
  · exact h1005 a assignment
  · exact h262 a assignment
  · exact h545 a assignment

include assignment in
private theorem h1008 : RUP.trueClause a (([52, -47, -70, 56, -57, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-64], [-60, 65, -59], [-61, 65, 60, -59], [-69, 65, 61, 60, -59], [62, -59], [66, -62, -59, -57, 56], [-57, 69, -59, -68, 61, -66], [49, -70, 56, -57, -59], [-46, -49, -70, 68, -66, 69], [-70, 69, 68, 67, -66], [56, 61, -57, 60, -58, -59], [43, -66, -49, -62, 52, -59], [41, -66, -47, -62, 52, -57], [-43, -49, -59, 37], [-59, -49, -43, -38, -37], [38, 68, -47, 61, -51, -57], [38, 65, -43, 61, -45, -59], [-37, 61, 38, 60, 39, -59], [51, -55, 69], [-76, -47, -49, 51], [65, 55, 45, 44, -43], [-54, 55, -70], [-79, 51, 54, 55], [60, 50, -44, -39, -37], [64, 54, 45, 42, -41], [-75, 46, -49, -50], [36, 64, -41, 58, -42, -57], [58, 48, -42, -39, -36], [-67, -53, -50, -48, 46], [53, 75, 79, 54, 76, -48, 52, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h996 a assignment
  · exact h842 a assignment
  · exact h843 a assignment
  · exact h677 a assignment
  · exact h998 a assignment
  · exact h624 a assignment
  · exact h207 a assignment
  · exact h1006 a assignment
  · exact h1007 a assignment
  · exact h707 a assignment
  · exact h67 a assignment
  · exact h303 a assignment
  · exact h252 a assignment
  · exact h853 a assignment
  · exact h483 a assignment
  · exact h192 a assignment
  · exact h119 a assignment
  · exact h64 a assignment
  · exact h777 a assignment
  · exact h721 a assignment
  · exact h522 a assignment
  · exact h798 a assignment
  · exact h727 a assignment
  · exact h490 a assignment
  · exact h516 a assignment
  · exact h720 a assignment
  · exact h80 a assignment
  · exact h472 a assignment
  · exact h550 a assignment
  · exact h929 a assignment

include assignment in
private theorem h1009 : RUP.trueClause a (([-52, -70, -66, 69, -49] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-49, -70, -52, 69, -55, -66], [55, -52, -70]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h325 a assignment
  · exact h1005 a assignment

include assignment in
private theorem h1010 : RUP.trueClause a (([-70, 56, -57, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-60, 65, -59], [-61, 65, 60, -59], [-69, 65, 61, 60, -59], [62, -59], [66, -62, -59, -57, 56], [-57, 69, -59, -68, 61, -66], [49, -70, 56, -57, -59], [-46, -49, -70, 68, -66, 69], [-52, -70, -66, 69, -49], [-66, 52, -49, 47, 46], [52, -47, -70, 56, -57, -59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h842 a assignment
  · exact h843 a assignment
  · exact h677 a assignment
  · exact h998 a assignment
  · exact h624 a assignment
  · exact h207 a assignment
  · exact h1006 a assignment
  · exact h1007 a assignment
  · exact h1009 a assignment
  · exact h547 a assignment
  · exact h1008 a assignment

include assignment in
private theorem h1011 : RUP.trueClause a (([70, 63, -62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-64], [-34, 70, 64, -62, 63], [34, -25, -62, 70, 64, 65], [-35, 34, 70], [22, 25, 64, 34], [24, 35, 65, 25], [-33, 35, 70, 34], [63, 33, -24, -22, 20], [64, 34, 25, -22, -21], [65, 35, 25, -24, -23], [70, 35, 34, 33, 32], [-62, -32, 23, 21, -20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h996 a assignment
  · exact h828 a assignment
  · exact h823 a assignment
  · exact h830 a assignment
  · exact h811 a assignment
  · exact h832 a assignment
  · exact h821 a assignment
  · exact h407 a assignment
  · exact h415 a assignment
  · exact h423 a assignment
  · exact h434 a assignment
  · exact h400 a assignment

include assignment in
private theorem h1012 : RUP.trueClause a (([70, -62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-65], [-63, 70, 65, 64], [70, 63, -62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h815 a assignment
  · exact h1011 a assignment

include assignment in
private theorem h1013 : RUP.trueClause a (([60, 61, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-64], [-69, 65, 61, 60, -59], [62, -59], [70, -62], [-70, 65, 64, 63, -62], [-59, -70, -62, 69, 65, 66], [-56, 65, -59, -63, 60, -62], [-66, 57, -62, -59], [-70, 56, -57, -59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h996 a assignment
  · exact h677 a assignment
  · exact h998 a assignment
  · exact h1012 a assignment
  · exact h695 a assignment
  · exact h331 a assignment
  · exact h105 a assignment
  · exact h939 a assignment
  · exact h1010 a assignment

include assignment in
private theorem h1014 : RUP.trueClause a (([60, -59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-61, 65, 60, -59], [60, 61, -59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h997 a assignment
  · exact h843 a assignment
  · exact h1013 a assignment

include assignment in
private theorem h1015 : RUP.trueClause a (([-59] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-60, 65, -59], [60, -59]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h997 a assignment
  · exact h842 a assignment
  · exact h1014 a assignment

include assignment in
private theorem h1016 : RUP.trueClause a (([56, -62, 57] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [66, -62, 59, 57, 56], [-66, -62, 59, 57, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h626 a assignment
  · exact h613 a assignment

include assignment in
private theorem h1017 : RUP.trueClause a (([-56, -62, 57] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [66, -62, 59, 57, -56], [-66, -62, 59, 57, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h619 a assignment
  · exact h614 a assignment

include assignment in
private theorem h1018 : RUP.trueClause a (([-62, 57] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[56, -62, 57], [-56, -62, 57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h1016 a assignment
  · exact h1017 a assignment

include assignment in
private theorem h1019 : RUP.trueClause a (([-62, 61] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-64], [-59], [-57, 65, 59, 64, 61, -62], [-62, 57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h996 a assignment
  · exact h1015 a assignment
  · exact h128 a assignment
  · exact h1018 a assignment

include assignment in
private theorem h1020 : RUP.trueClause a (([-22, -24, 32, 34, -33, 35, -63, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-63, -33, -24, -22, -20], [21, 20, 62, 32], [64, 34, 25, -22, -21], [62, 32, -23, -21, 20], [-21, 35, 23, 34, -25, 32]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h408 a assignment
  · exact h791 a assignment
  · exact h415 a assignment
  · exact h401 a assignment
  · exact h10 a assignment

include assignment in
private theorem h1021 : RUP.trueClause a (([22, -24, 35, 34, -33] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [22, 35, -24, 34, -25, -33], [22, 25, 64, 34]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h996 a assignment
  · exact h11 a assignment
  · exact h811 a assignment

include assignment in
private theorem h1022 : RUP.trueClause a (([-24, 32, 62, 34, -33, 35, -63] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-22, -24, 32, 34, -33, 35, -63, 62], [22, -24, 35, 34, -33]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h1020 a assignment
  · exact h1021 a assignment

include assignment in
private theorem h1023 : RUP.trueClause a (([32, 34, 62, -63, -33, 35] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-24, 32, 62, 34, -33, 35, -63], [-20, 24, -63, -33], [20, 65, 23, -63, 24, 62], [21, 20, 62, 32], [62, 32, -23, -21, 20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h1022 a assignment
  · exact h897 a assignment
  · exact h90 a assignment
  · exact h791 a assignment
  · exact h401 a assignment

include assignment in
private theorem h1024 : RUP.trueClause a (([35, -63, -70, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[33, 35, -70], [-34, 35, -70], [-70, 35, 34, -33, -32], [32, 34, 62, -63, -33, 35]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h783 a assignment
  · exact h810 a assignment
  · exact h437 a assignment
  · exact h1023 a assignment

include assignment in
private theorem h1025 : RUP.trueClause a (([-33, -63, -70, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [35, -63, -70, 62], [-24, -70, -33, 65, -35, -63], [-20, 24, -63, -33], [20, 65, 23, -63, 24, 62], [20, -70, -32, -63, -33, 62], [21, 20, 62, 32], [62, 32, -23, -21, 20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h1024 a assignment
  · exact h337 a assignment
  · exact h897 a assignment
  · exact h90 a assignment
  · exact h228 a assignment
  · exact h791 a assignment
  · exact h401 a assignment

include assignment in
private theorem h1026 : RUP.trueClause a (([-63, -70, 62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [35, -63, -70, 62], [-33, -63, -70, 62], [-34, 33, -70, -35], [-72, 33, 34], [-74, 33, -35], [-32, 72, 34, -35, 74], [-20, -70, 32, -63, 33, 62], [23, -70, 32, 65, -35, 62], [21, 20, 62, 32], [62, 32, -23, -21, 20]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h1024 a assignment
  · exact h1025 a assignment
  · exact h793 a assignment
  · exact h713 a assignment
  · exact h716 a assignment
  · exact h789 a assignment
  · exact h230 a assignment
  · exact h300 a assignment
  · exact h791 a assignment
  · exact h401 a assignment

include assignment in
private theorem h1027 : RUP.trueClause a (([-56, 57, -70, 61, 60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [-62, 61], [-63, -70, 62], [-56, 61, 57, 60, -58, 59], [-66, 62, 59, 57, -56], [67, 63, 60, 58, -56], [-56, -70, 62, -67, 63, 66]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h1019 a assignment
  · exact h1026 a assignment
  · exact h68 a assignment
  · exact h623 a assignment
  · exact h629 a assignment
  · exact h246 a assignment

include assignment in
private theorem h1028 : RUP.trueClause a (([58, 82, 56, 57, 61, 60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [-65], [-62, 61], [-83, 59, 62, 65], [-81, 58, 60, 61], [-80, 56, 57, 58], [80, 81, 82, 83]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h997 a assignment
  · exact h1019 a assignment
  · exact h736 a assignment
  · exact h733 a assignment
  · exact h730 a assignment
  · exact h918 a assignment

include assignment in
private theorem h1029 : RUP.trueClause a (([50, 39, 60, 61, -69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[39, -69, 50, 61, -51, 60], [51, 50, -69]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h218 a assignment
  · exact h970 a assignment

include assignment in
private theorem h1030 : RUP.trueClause a (([-46, 52, 66, -49] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[66, 52, -49, -47, -46], [66, 52, -49, 47, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h531 a assignment
  · exact h539 a assignment

include assignment in
private theorem h1031 : RUP.trueClause a (([-48, -50, -67, -46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-67, -53, -50, -48, -46], [-67, 53, -50, -48, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h551 a assignment
  · exact h561 a assignment

include assignment in
private theorem h1032 : RUP.trueClause a (([-46, 49, -68, -69, -67, 66] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[49, -47, 66, -46], [-46, -69, 49, -67, 50, 66], [-46, -68, 47, -67, 48, 66], [-48, -50, -67, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h774 a assignment
  · exact h179 a assignment
  · exact h156 a assignment
  · exact h1031 a assignment

include assignment in
private theorem h1033 : RUP.trueClause a (([37, 36, 56, 46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[40, 37, 56, 46], [56, 46, -40, 37, 36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h999 a assignment
  · exact h454 a assignment

include assignment in
private theorem h1034 : RUP.trueClause a (([66, -69, 61, 60, 48, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-59], [-62, 61], [59, 70, 62, -69, 65, 66], [-56, -69, 59, -67, 60, 66], [-63, -70, 62], [66, 62, 59, -57, 56], [-82, 56, 62, 63], [58, 82, 56, 57, 61, 60], [-36, -67, 46, -58, 48, 56], [37, 36, 56, 46], [-37, 66, 46, 59, -49, 56], [36, 59, -37, 57, 38, 56], [56, 46, -40, -37, 36], [59, 49, 43, -38, -37], [-37, 62, 40, 59, -43, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h1015 a assignment
  · exact h1019 a assignment
  · exact h328 a assignment
  · exact h184 a assignment
  · exact h1026 a assignment
  · exact h622 a assignment
  · exact h734 a assignment
  · exact h1028 a assignment
  · exact h148 a assignment
  · exact h1033 a assignment
  · exact h166 a assignment
  · exact h52 a assignment
  · exact h457 a assignment
  · exact h486 a assignment
  · exact h94 a assignment

include assignment in
private theorem h1035 : RUP.trueClause a (([53, 48, -67, 46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-67, 53, -50, 48, 46], [-67, 53, 50, 48, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h562 a assignment
  · exact h555 a assignment

include assignment in
private theorem h1036 : RUP.trueClause a (([-69, 61, 60, 48, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-59], [53, 48, -67, 46], [-67, -53, -50, 48, 46], [66, -69, 61, 60, 48, 46, -67], [50, 39, 60, 61, -69], [51, 50, -69], [46, -69, -49, -67, 50, -66], [38, -69, 49, 61, -51, 59], [49, -51, -69, 55], [46, -52, 49, -66], [43, -69, 49, 65, -55, 59], [44, -69, 50, 65, -55, 60], [-66, 52, 49, 47, 46], [60, 50, -44, -39, -37], [40, -55, -43, -53, -44, 52], [-36, -51, -38, 48, -39, -47], [37, -66, 46, 59, 49, -56], [56, 46, -40, 37, 36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h1015 a assignment
  · exact h1035 a assignment
  · exact h553 a assignment
  · exact h1034 a assignment
  · exact h1029 a assignment
  · exact h970 a assignment
  · exact h181 a assignment
  · exact h196 a assignment
  · exact h981 a assignment
  · exact h1001 a assignment
  · exact h309 a assignment
  · exact h344 a assignment
  · exact h537 a assignment
  · exact h490 a assignment
  · exact h34 a assignment
  · exact h25 a assignment
  · exact h159 a assignment
  · exact h454 a assignment

include assignment in
private theorem h1037 : RUP.trueClause a (([-62] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-64], [64, -61, -62, 65], [-62, 61]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h996 a assignment
  · exact h883 a assignment
  · exact h1019 a assignment

include assignment in
private theorem h1038 : RUP.trueClause a (([-66, 69, 60, 48, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-64], [-59], [-62], [53, 48, -67, 46], [59, -70, 62, 69, 65, -66], [-63, 70, 65, 64], [70, -61, 64, 65], [46, 70, 52, -67, -53, -66], [-52, 46, -66, 47], [46, -68, -47, -67, 48, -66], [-57, 70, 62, 68, 64, -66], [-58, 70, 63, 68, 64, -67], [-66, 62, 59, 57, -56], [58, 82, 56, 57, 61, 60], [-82, 56, 62, 63]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h996 a assignment
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h1035 a assignment
  · exact h330 a assignment
  · exact h815 a assignment
  · exact h831 a assignment
  · exact h241 a assignment
  · exact h805 a assignment
  · exact h152 a assignment
  · exact h273 a assignment
  · exact h297 a assignment
  · exact h623 a assignment
  · exact h1028 a assignment
  · exact h734 a assignment

include assignment in
private theorem h1039 : RUP.trueClause a (([61, 66, 69, 60, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-62], [-59], [56, 69, 59, -67, 60, 66], [66, 62, 59, -57, -56], [57, 69, 59, -68, 61, 66], [-56, 57, -70, 61, 60], [70, 69, 68, -67, 66]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1037 a assignment
  · exact h1015 a assignment
  · exact h186 a assignment
  · exact h617 a assignment
  · exact h209 a assignment
  · exact h1027 a assignment
  · exact h706 a assignment

include assignment in
private theorem h1040 : RUP.trueClause a (([66, 69, -67, 60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-62], [-59], [56, 69, 59, -67, 60, 66], [66, 62, 59, -57, -56], [61, 66, 69, 60, -67], [-61, 64, -68], [58, -61, 68, 64], [68, 64, -61, -58, 57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h1037 a assignment
  · exact h1015 a assignment
  · exact h186 a assignment
  · exact h617 a assignment
  · exact h1039 a assignment
  · exact h751 a assignment
  · exact h753 a assignment
  · exact h648 a assignment

include assignment in
private theorem h1041 : RUP.trueClause a (([69, 60, -67, 48, 46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-66, 69, 60, 48, 46, -67], [66, 69, -67, 60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h1038 a assignment
  · exact h1040 a assignment

include assignment in
private theorem h1042 : RUP.trueClause a (([60, 48, -67, 46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [-65], [69, 60, -67, 48, 46], [-69, 65, -61, 60, 59], [-69, 61, 60, 48, 46, -67]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h997 a assignment
  · exact h1041 a assignment
  · exact h681 a assignment
  · exact h1036 a assignment

include assignment in
private theorem h1043 : RUP.trueClause a (([66, 61, -69, -60, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [-62], [-65], [59, 70, 62, -69, 65, 66], [-70, -69, 68, -67, 66], [-63, -70, 62], [58, -69, -60, -68, 61, -67], [-56, 65, 59, 63, -60, 62], [-67, 63, -60, -58, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h997 a assignment
  · exact h328 a assignment
  · exact h705 a assignment
  · exact h1026 a assignment
  · exact h224 a assignment
  · exact h104 a assignment
  · exact h635 a assignment

include assignment in
private theorem h1044 : RUP.trueClause a (([61, -69, 48, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-59], [53, 48, -67, 46], [-67, -53, -50, 48, 46], [51, 50, -69], [60, 48, -67, 46], [66, 61, -69, -60, -67], [-56, -69, 59, -67, -60, -66], [46, -69, -49, -67, 50, -66], [-37, -67, 46, -60, 50, 56], [46, -52, 49, -66], [50, 49, -69, 55], [38, -69, 49, 61, -51, 59], [43, -69, 49, 65, -55, 59], [40, 37, 56, 46], [37, 36, 56, 46], [-66, 52, 49, 47, 46], [-38, -66, -47, 59, 49, 57], [-36, -43, 37, -41, -38, -40], [-57, -47, 41, -38, -36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h1015 a assignment
  · exact h1035 a assignment
  · exact h553 a assignment
  · exact h970 a assignment
  · exact h1042 a assignment
  · exact h1043 a assignment
  · exact h185 a assignment
  · exact h181 a assignment
  · exact h170 a assignment
  · exact h1001 a assignment
  · exact h854 a assignment
  · exact h196 a assignment
  · exact h309 a assignment
  · exact h999 a assignment
  · exact h1033 a assignment
  · exact h537 a assignment
  · exact h191 a assignment
  · exact h15 a assignment
  · exact h466 a assignment

include assignment in
private theorem h1045 : RUP.trueClause a (([-69, 48, -67, 46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-65], [61, -69, 48, 46, -67], [-61, 64, -68], [70, -61, 64, 65], [-61, -70, 64, -69, 65, 68]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h1044 a assignment
  · exact h751 a assignment
  · exact h831 a assignment
  · exact h385 a assignment

include assignment in
private theorem h1046 : RUP.trueClause a (([69, -60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [65, 69, 61, -60], [-60, 65, 69, -61]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h997 a assignment
  · exact h756 a assignment
  · exact h760 a assignment

include assignment in
private theorem h1047 : RUP.trueClause a (([48, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[60, 48, -67, 46], [-69, 48, -67, 46], [69, -60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h1042 a assignment
  · exact h1045 a assignment
  · exact h1046 a assignment

include assignment in
private theorem h1048 : RUP.trueClause a (([68, 69, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-64], [-59], [-62], [69, -60], [66, 69, -67, 60], [59, -70, 62, 69, 65, -66], [70, -61, 64, 65], [-63, 70, 65, 64], [-57, 70, 62, 68, 64, -66], [-58, 70, 63, 68, 64, -67], [-66, 62, 59, 57, -56], [58, 82, 56, 57, 61, 60], [-82, 56, 62, 63]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h996 a assignment
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h1046 a assignment
  · exact h1040 a assignment
  · exact h330 a assignment
  · exact h831 a assignment
  · exact h815 a assignment
  · exact h273 a assignment
  · exact h297 a assignment
  · exact h623 a assignment
  · exact h1028 a assignment
  · exact h734 a assignment

include assignment in
private theorem h1049 : RUP.trueClause a (([42, -36, -58, -48] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-58, -48, 42, -39, -36], [-58, -48, 42, 39, -36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h474 a assignment
  · exact h475 a assignment

include assignment in
private theorem h1050 : RUP.trueClause a (([52, -42, -36, -47, 57, 69, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-62], [-64], [-65], [-59], [69, -60], [66, 69, -67, 60], [59, -70, 62, 69, 65, -66], [70, -61, 64, 65], [46, 70, 52, -67, -53, -66], [-41, -66, -47, 62, 52, 57], [57, -47, 41, -38, -36], [-42, 41, 64, -45], [64, -54, 45, -42, 41], [38, 65, -43, 61, 45, 59], [70, -55, 54, 53, 52], [43, 38, 59, 49], [-49, 70, 52, 69, 55, -66]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1037 a assignment
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h1015 a assignment
  · exact h1046 a assignment
  · exact h1040 a assignment
  · exact h330 a assignment
  · exact h831 a assignment
  · exact h241 a assignment
  · exact h255 a assignment
  · exact h470 a assignment
  · exact h878 a assignment
  · exact h514 a assignment
  · exact h118 a assignment
  · exact h608 a assignment
  · exact h973 a assignment
  · exact h324 a assignment

include assignment in
private theorem h1051 : RUP.trueClause a (([-47, 57, 56, 69, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [-64], [-65], [-62], [69, -60], [66, 69, -67, 60], [59, -70, 62, 69, 65, -66], [70, -61, 64, 65], [-63, 70, 65, 64], [-82, 56, 62, 63], [58, 82, 56, 57, 61, 60], [68, 69, -67], [48, 46, -67], [36, -68, -47, -58, -48, 57], [42, -36, -58, -48], [-36, 63, -40, -58, -42, 56], [52, -42, -36, -47, 57, 69, 46, -67], [40, -66, 46, 62, -52, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h1037 a assignment
  · exact h1046 a assignment
  · exact h1040 a assignment
  · exact h330 a assignment
  · exact h831 a assignment
  · exact h815 a assignment
  · exact h734 a assignment
  · exact h1028 a assignment
  · exact h1048 a assignment
  · exact h1047 a assignment
  · exact h150 a assignment
  · exact h1049 a assignment
  · exact h75 a assignment
  · exact h1050 a assignment
  · exact h234 a assignment

include assignment in
private theorem h1052 : RUP.trueClause a (([47, 52, 46, -66] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-66, 52, -49, 47, 46], [-66, 52, 49, 47, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h547 a assignment
  · exact h537 a assignment

include assignment in
private theorem h1053 : RUP.trueClause a (([47, -66, 46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-52, 46, -66, 47], [47, 52, 46, -66]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h805 a assignment
  · exact h1052 a assignment

include assignment in
private theorem h1054 : RUP.trueClause a (([56, 69, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-62], [-65], [-59], [-64], [69, -60], [66, 69, -67, 60], [47, -66, 46], [68, 69, -67], [59, -70, 62, 69, 65, -66], [70, -61, 64, 65], [-47, 57, 56, 69, 46, -67], [56, 61, -57, 60, 58, 59], [-68, 64, 61, -58, -57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1037 a assignment
  · exact h997 a assignment
  · exact h1015 a assignment
  · exact h996 a assignment
  · exact h1046 a assignment
  · exact h1040 a assignment
  · exact h1053 a assignment
  · exact h1048 a assignment
  · exact h330 a assignment
  · exact h831 a assignment
  · exact h1051 a assignment
  · exact h66 a assignment
  · exact h649 a assignment

include assignment in
private theorem h1055 : RUP.trueClause a (([69, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [-62], [-64], [-65], [69, -60], [66, 69, -67, 60], [59, -70, 62, 69, 65, -66], [-63, 70, 65, 64], [56, 69, 46, -67], [-58, 60, -56, 63], [-67, 63, 60, 58, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h1046 a assignment
  · exact h1040 a assignment
  · exact h330 a assignment
  · exact h815 a assignment
  · exact h1054 a assignment
  · exact h762 a assignment
  · exact h639 a assignment

include assignment in
private theorem h1056 : RUP.trueClause a (([-56, 57, 60, -69, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-62], [-59], [-66, 62, 59, 57, -56], [-56, -69, 59, -67, 60, 66]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h1037 a assignment
  · exact h1015 a assignment
  · exact h623 a assignment
  · exact h184 a assignment

include assignment in
private theorem h1057 : RUP.trueClause a (([58, 60, -67, -69, 61] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-62], [-65], [-59], [-64], [58, -69, 60, 68, 61, -67], [-68, 64, 61, 58, -57], [-56, 57, 60, -69, -67], [56, 65, 59, -63, 60, 62], [-82, 56, 62, 63], [58, 82, 56, 57, 61, 60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1037 a assignment
  · exact h997 a assignment
  · exact h1015 a assignment
  · exact h996 a assignment
  · exact h223 a assignment
  · exact h657 a assignment
  · exact h1056 a assignment
  · exact h100 a assignment
  · exact h734 a assignment
  · exact h1028 a assignment

include assignment in
private theorem h1058 : RUP.trueClause a (([-36, 49, 52, 57, 56, 63, -58, -48, 46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-62], [-59], [42, -36, -58, -48], [-36, 64, -41, -58, -42, 57], [-36, 63, -40, -58, -42, 56], [40, 37, 56, 46], [62, 52, -43, 41, 40], [43, 38, 59, 49], [59, 49, 43, -38, -37]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h1037 a assignment
  · exact h1015 a assignment
  · exact h1049 a assignment
  · exact h78 a assignment
  · exact h75 a assignment
  · exact h999 a assignment
  · exact h507 a assignment
  · exact h973 a assignment
  · exact h486 a assignment

include assignment in
private theorem h1059 : RUP.trueClause a (([49, 52, 46, 57, 56, 63, -58, -48] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [-62], [-36, 49, 52, 57, 56, 63, -58, -48, 46], [37, 36, 56, 46], [56, 46, -40, -37, 36], [36, 59, -37, 57, 38, 56], [-37, 62, 40, 59, -43, 56], [59, 49, 43, -38, -37]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h1058 a assignment
  · exact h1033 a assignment
  · exact h457 a assignment
  · exact h52 a assignment
  · exact h94 a assignment
  · exact h486 a assignment

include assignment in
private theorem h1060 : RUP.trueClause a (([66, -68, 60, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-59], [-65], [69, 46, -67], [-69, 65, -61, 60, 59], [58, 60, -67, -69, 61], [-68, 64, 61, -58, -57], [-58, 65, 60, 64, 61, -63], [-58, 60, -56, 63], [48, 46, -67], [46, -68, -47, -67, -48, 66], [46, 47, 66, -52], [49, 52, 46, 57, 56, 63, -58, -48], [46, -69, -49, -67, -50, 66], [47, -69, -49, -68, -51, 66], [51, 50, -69]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h1015 a assignment
  · exact h997 a assignment
  · exact h1055 a assignment
  · exact h681 a assignment
  · exact h1057 a assignment
  · exact h649 a assignment
  · exact h140 a assignment
  · exact h762 a assignment
  · exact h1047 a assignment
  · exact h153 a assignment
  · exact h852 a assignment
  · exact h1059 a assignment
  · exact h182 a assignment
  · exact h203 a assignment
  · exact h970 a assignment

include assignment in
private theorem h1061 : RUP.trueClause a (([-66, -68, -69, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-70, -69, -68, -67, -66], [70, -69, -68, -67, -66]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h701 a assignment
  · exact h704 a assignment

include assignment in
private theorem h1062 : RUP.trueClause a (([-68, 60, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[69, 46, -67], [66, -68, 60, 46, -67], [-66, -68, -69, -67]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h1055 a assignment
  · exact h1060 a assignment
  · exact h1061 a assignment

include assignment in
private theorem h1063 : RUP.trueClause a (([-49, 52, 60, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-59], [-65], [69, 46, -67], [-68, 60, 46, -67], [-69, 65, -61, 60, 59], [61, 70, 64, -69, 65, 68], [-70, -69, 68, -67, 66], [47, -66, 46], [48, 46, -67], [46, -69, -49, -67, 50, -66], [-47, -69, -49, 68, -51, -66], [-49, -70, 52, -69, -55, -66], [-75, 46, -49, -50], [-67, -53, -50, -48, 46], [-76, -47, -49, 51], [68, -54, 51, -48, -47], [53, 75, 79, 54, 76, -48, 52, 46], [-79, 51, 54, 55]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h1015 a assignment
  · exact h997 a assignment
  · exact h1055 a assignment
  · exact h1062 a assignment
  · exact h681 a assignment
  · exact h383 a assignment
  · exact h705 a assignment
  · exact h1053 a assignment
  · exact h1047 a assignment
  · exact h181 a assignment
  · exact h201 a assignment
  · exact h327 a assignment
  · exact h720 a assignment
  · exact h550 a assignment
  · exact h721 a assignment
  · exact h574 a assignment
  · exact h929 a assignment
  · exact h727 a assignment

include assignment in
private theorem h1064 : RUP.trueClause a (([43, -37, 49] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [43, 38, 59, 49], [59, 49, 43, -38, -37]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h973 a assignment
  · exact h486 a assignment

include assignment in
private theorem h1065 : RUP.trueClause a (([-50, 49, 60, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-65], [-59], [-62], [69, 46, -67], [-69, 65, -61, 60, 59], [58, 60, -67, -69, 61], [-58, 65, 60, 64, 61, -63], [-58, 60, -56, 63], [48, 46, -67], [37, -69, 49, 60, -50, 59], [-67, -53, -50, -48, 46], [43, -37, 49], [-37, 62, 40, 59, -43, 56], [56, 46, -40, -37, 36], [-36, 53, -40, -48, -42, 46], [42, -36, -58, -48]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h1055 a assignment
  · exact h681 a assignment
  · exact h1057 a assignment
  · exact h140 a assignment
  · exact h762 a assignment
  · exact h1047 a assignment
  · exact h173 a assignment
  · exact h550 a assignment
  · exact h1064 a assignment
  · exact h94 a assignment
  · exact h457 a assignment
  · exact h32 a assignment
  · exact h1049 a assignment

include assignment in
private theorem h1066 : RUP.trueClause a (([52, 60, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-59], [-62], [-65], [69, 46, -67], [-68, 60, 46, -67], [-69, 65, -61, 60, 59], [61, 70, 64, -69, 65, 68], [-70, -69, 68, -67, 66], [47, -66, 46], [58, 60, -67, -69, 61], [68, 64, 61, -58, 57], [-58, 65, 60, 64, 61, -63], [-58, 60, -56, 63], [48, 46, -67], [-49, 52, 60, 46, -67], [-50, 49, 60, 46, -67], [-67, -53, 50, -48, 46], [51, 50, -69], [50, 39, 60, 61, -69], [50, 49, -69, 55], [38, -69, 49, 61, -51, 59], [44, -70, 53, 65, -55, 63], [43, -70, 52, 65, -55, 62], [60, 50, -44, -39, -37], [40, 37, 56, 46], [37, 36, 56, 46], [-36, -43, 37, -41, -38, -40], [-57, -47, 41, -38, -36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h997 a assignment
  · exact h1055 a assignment
  · exact h1062 a assignment
  · exact h681 a assignment
  · exact h383 a assignment
  · exact h705 a assignment
  · exact h1053 a assignment
  · exact h1057 a assignment
  · exact h656 a assignment
  · exact h140 a assignment
  · exact h762 a assignment
  · exact h1047 a assignment
  · exact h1063 a assignment
  · exact h1065 a assignment
  · exact h557 a assignment
  · exact h970 a assignment
  · exact h1029 a assignment
  · exact h854 a assignment
  · exact h196 a assignment
  · exact h349 a assignment
  · exact h314 a assignment
  · exact h490 a assignment
  · exact h999 a assignment
  · exact h1033 a assignment
  · exact h15 a assignment
  · exact h466 a assignment

include assignment in
private theorem h1067 : RUP.trueClause a (([60, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [-65], [-64], [69, 46, -67], [48, 46, -67], [-69, 65, -61, 60, 59], [-68, 60, 46, -67], [61, 70, 64, -69, 65, 68], [-70, -69, 68, -67, 66], [52, 60, 46, -67], [46, -52, 49, -66], [46, -70, -52, -67, 53, -66], [46, -69, -49, -67, 50, -66], [-67, -53, -50, -48, 46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h997 a assignment
  · exact h996 a assignment
  · exact h1055 a assignment
  · exact h1047 a assignment
  · exact h681 a assignment
  · exact h1062 a assignment
  · exact h383 a assignment
  · exact h705 a assignment
  · exact h1066 a assignment
  · exact h1001 a assignment
  · exact h242 a assignment
  · exact h181 a assignment
  · exact h550 a assignment

include assignment in
private theorem h1068 : RUP.trueClause a (([66, 46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-59], [-62], [-64], [60, 46, -67], [69, 46, -67], [59, 70, 62, -69, 65, 66], [66, 61, -69, -60, -67], [-70, -69, 68, -67, 66], [-61, 64, -68]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h996 a assignment
  · exact h1067 a assignment
  · exact h1055 a assignment
  · exact h328 a assignment
  · exact h1043 a assignment
  · exact h705 a assignment
  · exact h751 a assignment

include assignment in
private theorem h1069 : RUP.trueClause a (([-66, -60, -69, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-62], [-64], [-59], [-56, -69, 59, -67, -60, -66], [-66, -68, -69, -67], [70, -69, 68, -67, -66], [57, -70, 62, 68, 64, -66], [-63, -70, 62], [56, 64, -57, 63, 58, 62], [-67, 63, -60, -58, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1037 a assignment
  · exact h996 a assignment
  · exact h1015 a assignment
  · exact h185 a assignment
  · exact h1061 a assignment
  · exact h709 a assignment
  · exact h268 a assignment
  · exact h1026 a assignment
  · exact h85 a assignment
  · exact h635 a assignment

include assignment in
private theorem h1070 : RUP.trueClause a (([46, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[69, 46, -67], [60, 46, -67], [66, 46, -67], [-66, -60, -69, -67]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h1055 a assignment
  · exact h1067 a assignment
  · exact h1068 a assignment
  · exact h1069 a assignment

include assignment in
private theorem h1071 : RUP.trueClause a (([-47, -38, -52, 56, -57, -66, -46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-62], [36, -66, -46, -57, -47, 56], [-41, -66, -47, 62, -52, -57], [-57, -47, 41, -38, -36]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h1037 a assignment
  · exact h144 a assignment
  · exact h254 a assignment
  · exact h466 a assignment

include assignment in
private theorem h1072 : RUP.trueClause a (([-36, 76, 47, -45, -38, -51, 75, -55, -52, 63, -57, -58, 68, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [46, -67], [-57, 47, -41, -38, -36], [-42, 41, 64, -45], [42, -36, -58, -48], [42, -67, 48, 63, 53, -58], [48, 54, 68, -51], [-77, -46, -52, -53], [-79, -51, -54, -55], [-78, 48, -53, -54], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h1070 a assignment
  · exact h469 a assignment
  · exact h878 a assignment
  · exact h1049 a assignment
  · exact h285 a assignment
  · exact h803 a assignment
  · exact h724 a assignment
  · exact h728 a assignment
  · exact h725 a assignment
  · exact h729 a assignment

include assignment in
private theorem h1073 : RUP.trueClause a (([49, -69, -66, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-62], [-59], [-65], [-66, -60, -69, -67], [-69, 65, -61, 60, 59], [58, 60, -67, -69, 61], [-58, 65, 60, 64, 61, -63], [-58, 60, -56, 63], [-66, -68, -69, -67], [61, 70, 64, -69, 65, 68], [57, -70, 62, 68, 64, -66], [46, -67], [-46, 49, -66, 52], [-46, -69, 49, -67, -50, -66], [49, -70, -52, -69, 55, -66], [43, -66, 49, 62, -52, 59], [-75, -46, 49, 50], [51, 50, -69], [44, -69, 50, 65, -55, 60], [38, -69, 49, 61, -51, 59], [65, -55, 45, -44, -43], [-47, -38, -52, 56, -57, -66, -46], [-76, 47, 49, -51], [-36, 76, 47, -45, -38, -51, 75, -55, -52, 63, -57, -58, 68, -67], [36, 68, 47, -58, -48, -57], [-67, 53, 50, 48, -46], [48, 54, 68, -51], [-77, -46, -52, -53], [-79, -51, -54, -55], [-78, 48, -53, -54], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h1037 a assignment
  · exact h1015 a assignment
  · exact h997 a assignment
  · exact h1069 a assignment
  · exact h681 a assignment
  · exact h1057 a assignment
  · exact h140 a assignment
  · exact h762 a assignment
  · exact h1061 a assignment
  · exact h383 a assignment
  · exact h268 a assignment
  · exact h1070 a assignment
  · exact h880 a assignment
  · exact h180 a assignment
  · exact h320 a assignment
  · exact h304 a assignment
  · exact h719 a assignment
  · exact h970 a assignment
  · exact h344 a assignment
  · exact h196 a assignment
  · exact h528 a assignment
  · exact h1071 a assignment
  · exact h722 a assignment
  · exact h1072 a assignment
  · exact h149 a assignment
  · exact h559 a assignment
  · exact h803 a assignment
  · exact h724 a assignment
  · exact h728 a assignment
  · exact h725 a assignment
  · exact h729 a assignment

include assignment in
private theorem h1074 : RUP.trueClause a (([-47, -69, -66, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[49, -69, -66, -67], [-66, -68, -69, -67], [46, -67], [-46, 68, -47, -67, 48, -66], [-47, -69, -49, 68, -51, -66], [-48, -50, -67, -46], [51, 50, -69]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1073 a assignment
  · exact h1061 a assignment
  · exact h1070 a assignment
  · exact h155 a assignment
  · exact h201 a assignment
  · exact h1031 a assignment
  · exact h970 a assignment

include assignment in
private theorem h1075 : RUP.trueClause a (([47, -49, -66, -46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-66, -52, -49, 47, -46], [-66, 52, -49, 47, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h541 a assignment
  · exact h530 a assignment

include assignment in
private theorem h1076 : RUP.trueClause a (([-69, -66, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[46, -67], [49, -69, -66, -67], [-47, -69, -66, -67], [47, -49, -66, -46]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h1070 a assignment
  · exact h1073 a assignment
  · exact h1074 a assignment
  · exact h1075 a assignment

include assignment in
private theorem h1077 : RUP.trueClause a (([-49, -66, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-69, -66, -67], [68, 69, -67], [46, -67], [47, -49, -66, -46], [-46, 69, -49, -67, 50, -66], [-47, 69, -49, -68, 51, -66], [-51, -50, 69]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1076 a assignment
  · exact h1048 a assignment
  · exact h1070 a assignment
  · exact h1075 a assignment
  · exact h177 a assignment
  · exact h202 a assignment
  · exact h950 a assignment

include assignment in
private theorem h1078 : RUP.trueClause a (([-54, -47, -68] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-47, -54, -68, -51], [-48, 51, -68, -54], [-68, -54, 51, 48, -47]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h978 a assignment
  · exact h768 a assignment
  · exact h565 a assignment

include assignment in
private theorem h1079 : RUP.trueClause a (([-47, -66, 70, -68, -52] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-47, 70, -52, -68, 54, -66], [-54, -47, -68]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h267 a assignment
  · exact h1078 a assignment

include assignment in
private theorem h1080 : RUP.trueClause a (([-57, 56, -68, 60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [-64], [-61, 64, -68], [56, 61, -57, 60, 58, 59], [-68, 64, 61, -58, -57]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h996 a assignment
  · exact h751 a assignment
  · exact h66 a assignment
  · exact h649 a assignment

include assignment in
private theorem h1081 : RUP.trueClause a (([56, -45, 51, 48, 47, 63, -68, 60, -66, -46] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-62], [-64], [48, 51, -68, 54], [-61, 64, -68], [-82, 56, 62, 63], [-57, 56, -68, 60], [58, 82, 56, 57, 61, 60], [41, -68, 47, 64, -54, 57], [-36, -66, -46, 57, 47, 56], [39, -68, 48, 61, 51, -58], [57, 47, -41, 38, 36], [61, 51, -45, -39, -38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1037 a assignment
  · exact h996 a assignment
  · exact h769 a assignment
  · exact h751 a assignment
  · exact h734 a assignment
  · exact h1080 a assignment
  · exact h1028 a assignment
  · exact h257 a assignment
  · exact h146 a assignment
  · exact h214 a assignment
  · exact h465 a assignment
  · exact h497 a assignment

include assignment in
private theorem h1082 : RUP.trueClause a (([-66, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [-62], [-64], [-65], [46, -67], [-69, -66, -67], [69, -60], [68, 69, -67], [59, -70, 62, 69, 65, -66], [-63, 70, 65, 64], [-49, -66, -67], [-46, 49, -66, 52], [49, 70, -52, 69, -55, -66], [-47, -66, 70, -68, -52], [-46, -68, 47, -67, -48, -66], [47, 69, 49, -68, -51, -66], [48, 51, -68, 54], [45, 70, -54, 65, 55, 64], [56, -45, 51, 48, 47, 63, -68, 60, -66, -46], [-58, 60, -56, 63], [-67, 63, 60, 58, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h1070 a assignment
  · exact h1076 a assignment
  · exact h1046 a assignment
  · exact h1048 a assignment
  · exact h330 a assignment
  · exact h815 a assignment
  · exact h1077 a assignment
  · exact h880 a assignment
  · exact h318 a assignment
  · exact h1079 a assignment
  · exact h157 a assignment
  · exact h205 a assignment
  · exact h769 a assignment
  · exact h375 a assignment
  · exact h1081 a assignment
  · exact h762 a assignment
  · exact h639 a assignment

include assignment in
private theorem h1083 : RUP.trueClause a (([69, -67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-66, -67], [69, -60], [66, 69, -67, 60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h1082 a assignment
  · exact h1046 a assignment
  · exact h1040 a assignment

include assignment in
private theorem h1084 : RUP.trueClause a (([-67] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-59], [-62], [-64], [46, -67], [-66, -67], [69, -67], [59, 70, 62, -69, 65, 66], [-63, -70, 62], [-70, -69, 68, -67, 66], [-56, -70, 62, -67, 63, 66], [-61, 64, -68], [-57, -70, 62, -68, 64, 66], [-46, 49, -68, -69, -67, 66], [-82, 56, 62, 63], [66, 61, -69, -60, -67], [58, 82, 56, 57, 61, 60], [-46, 52, 66, -49], [55, -52, -70], [-47, -52, 66], [36, 66, -46, 57, 47, 56], [-46, -68, 47, -67, 48, 66], [47, -70, -52, -68, -54, 66], [42, -36, -58, -48], [-70, -55, 54, 53, -52], [-42, -70, -53, 64, 54, 63]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h996 a assignment
  · exact h1070 a assignment
  · exact h1082 a assignment
  · exact h1083 a assignment
  · exact h328 a assignment
  · exact h1026 a assignment
  · exact h705 a assignment
  · exact h246 a assignment
  · exact h751 a assignment
  · exact h270 a assignment
  · exact h1032 a assignment
  · exact h734 a assignment
  · exact h1043 a assignment
  · exact h1028 a assignment
  · exact h1030 a assignment
  · exact h1005 a assignment
  · exact h857 a assignment
  · exact h143 a assignment
  · exact h156 a assignment
  · exact h263 a assignment
  · exact h1049 a assignment
  · exact h596 a assignment
  · exact h291 a assignment

include assignment in
private theorem h1085 : RUP.trueClause a (([56, 63, 66, 61, 60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-59], [-62], [-67], [66, 62, 59, -57, 56], [-82, 56, 62, 63], [67, 63, 60, -58, 56], [58, 82, 56, 57, 61, 60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h1084 a assignment
  · exact h622 a assignment
  · exact h734 a assignment
  · exact h638 a assignment
  · exact h1028 a assignment

include assignment in
private theorem h1086 : RUP.trueClause a (([66, 60, -69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-65], [-59], [-62], [-69, 65, -61, 60, 59], [59, 70, 62, -69, 65, 66], [-63, -70, 62], [56, 63, 66, 61, 60], [66, 62, 59, -57, -56], [-56, 57, -70, 61, 60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h997 a assignment
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h681 a assignment
  · exact h328 a assignment
  · exact h1026 a assignment
  · exact h1085 a assignment
  · exact h617 a assignment
  · exact h1027 a assignment

include assignment in
private theorem h1087 : RUP.trueClause a (([63, 60, -56] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-67], [-58, 60, -56, 63], [67, 63, 60, 58, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h1084 a assignment
  · exact h762 a assignment
  · exact h629 a assignment

include assignment in
private theorem h1088 : RUP.trueClause a (([60, -69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-67], [-65], [-64], [-59], [-69, 65, -61, 60, 59], [66, 60, -69], [56, -69, 59, 67, 60, -66], [63, 60, -56], [-58, 65, 60, 64, 61, -63], [67, -63, 60, 58, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1084 a assignment
  · exact h997 a assignment
  · exact h996 a assignment
  · exact h1015 a assignment
  · exact h681 a assignment
  · exact h1086 a assignment
  · exact h187 a assignment
  · exact h1087 a assignment
  · exact h140 a assignment
  · exact h636 a assignment

include assignment in
private theorem h1089 : RUP.trueClause a (([-63] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-65], [-62], [-63, 70, 65, 64], [-63, -70, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h1037 a assignment
  · exact h815 a assignment
  · exact h1026 a assignment

include assignment in
private theorem h1090 : RUP.trueClause a (([-45, 55, 47, -69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-63], [-67], [-62], [-59], [-65], [60, -69], [-60, -70, 63, -69, 65, 67], [59, 70, 62, -69, 65, 66], [47, -66, 46], [47, -49, -66, -46], [50, 49, -69, 55], [49, -51, -69, 55], [-56, 65, 59, 63, -60, 62], [70, -61, 64, 65], [61, 70, 64, -69, 65, 68], [58, 65, -60, 64, 61, 63], [-68, 64, 61, -58, -57], [-36, -66, -46, 57, 47, 56], [-46, 49, -66, 52], [41, -66, 47, 62, -52, 57], [57, 47, -41, 38, 36], [43, -66, 49, 62, -52, 59], [-37, -66, -46, 59, 49, 56], [37, 39, -38, -45, -43, -50, -60], [61, 51, -45, -39, -38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h1089 a assignment
  · exact h1084 a assignment
  · exact h1037 a assignment
  · exact h1015 a assignment
  · exact h997 a assignment
  · exact h1088 a assignment
  · exact h357 a assignment
  · exact h328 a assignment
  · exact h1053 a assignment
  · exact h1075 a assignment
  · exact h854 a assignment
  · exact h981 a assignment
  · exact h104 a assignment
  · exact h831 a assignment
  · exact h383 a assignment
  · exact h139 a assignment
  · exact h649 a assignment
  · exact h146 a assignment
  · exact h880 a assignment
  · exact h253 a assignment
  · exact h465 a assignment
  · exact h304 a assignment
  · exact h164 a assignment
  · exact h976 a assignment
  · exact h497 a assignment

include assignment in
private theorem h1091 : RUP.trueClause a (([45, 51, 61, -38] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[61, 51, 45, 39, -38], [61, 51, 45, -39, -38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h495 a assignment
  · exact h501 a assignment

include assignment in
private theorem h1092 : RUP.trueClause a (([55, 47, -69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-64], [-67], [-63], [-65], [-62], [-59], [60, -69], [-56, 65, 59, 63, -60, 62], [-60, -70, 63, -69, 65, 67], [59, 70, 62, -69, 65, 66], [47, -66, 46], [70, -61, 64, 65], [61, 70, 64, -69, 65, 68], [58, 65, -60, 64, 61, 63], [-68, 64, 61, -58, -57], [-36, -66, -46, 57, 47, 56], [47, -49, -66, -46], [-46, 49, -66, 52], [41, -66, 47, 62, -52, 57], [57, 47, -41, 38, 36], [49, -51, -69, 55], [-45, 55, 47, -69], [45, 51, 61, -38]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h996 a assignment
  · exact h1084 a assignment
  · exact h1089 a assignment
  · exact h997 a assignment
  · exact h1037 a assignment
  · exact h1015 a assignment
  · exact h1088 a assignment
  · exact h104 a assignment
  · exact h357 a assignment
  · exact h328 a assignment
  · exact h1053 a assignment
  · exact h831 a assignment
  · exact h383 a assignment
  · exact h139 a assignment
  · exact h649 a assignment
  · exact h146 a assignment
  · exact h1075 a assignment
  · exact h880 a assignment
  · exact h253 a assignment
  · exact h465 a assignment
  · exact h981 a assignment
  · exact h1090 a assignment
  · exact h1091 a assignment

include assignment in
private theorem h1093 : RUP.trueClause a (([47, -69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-63], [-64], [-65], [-59], [-62], [-67], [60, -69], [-60, -70, 63, -69, 65, 67], [70, -61, 64, 65], [61, 70, 64, -69, 65, 68], [58, 65, -60, 64, 61, 63], [-68, 64, 61, -58, -57], [59, 70, 62, -69, 65, 66], [-56, 65, 59, 63, -60, 62], [47, -66, 46], [47, -49, -66, -46], [-36, -66, -46, 57, 47, 56], [-46, 49, -66, 52], [-37, -66, -46, 59, 49, 56], [56, -46, 40, 37, 36], [43, -66, 49, 62, -52, 59], [41, -66, 47, 62, -52, 57], [57, 47, -41, 38, 36], [55, 47, -69], [51, 49, -69, -55], [54, -52, 70, -55], [-53, -55, -54, 49, -46, 47, -52, 70, 67, -69, -68], [50, 67, 53], [-40, -55, -43, 53, -44, -52], [37, -51, -38, -50, -39, 49], [-60, -50, 44, 39, 37]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1089 a assignment
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h1015 a assignment
  · exact h1037 a assignment
  · exact h1084 a assignment
  · exact h1088 a assignment
  · exact h357 a assignment
  · exact h831 a assignment
  · exact h383 a assignment
  · exact h139 a assignment
  · exact h649 a assignment
  · exact h328 a assignment
  · exact h104 a assignment
  · exact h1053 a assignment
  · exact h1075 a assignment
  · exact h146 a assignment
  · exact h880 a assignment
  · exact h164 a assignment
  · exact h463 a assignment
  · exact h304 a assignment
  · exact h253 a assignment
  · exact h465 a assignment
  · exact h1092 a assignment
  · exact h860 a assignment
  · exact h862 a assignment
  · exact h858 a assignment
  · exact h940 a assignment
  · exact h35 a assignment
  · exact h27 a assignment
  · exact h491 a assignment

include assignment in
private theorem h1094 : RUP.trueClause a (([-69, -60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-63], [-67], [-64], [-65], [-62], [-59], [-60, -70, 63, -69, 65, 67], [-56, 65, 59, 63, -60, 62], [70, -61, 64, 65], [61, 70, 64, -69, 65, 68], [59, 70, 62, -69, 65, 66], [58, 65, -60, 64, 61, 63], [-68, 64, 61, -58, -57], [47, -69], [-47, -66, 70, -68, -52], [-54, -47, -68], [-53, 54, 70, 52], [70, -55, 54, 53, 52], [50, 67, 53], [-46, 70, 52, 67, 53, -66], [48, 70, 53, -68, 54, 67], [-77, 46, 52, 53], [-78, -48, 53, 54], [49, 52, 46, 57, 56, 63, -58, -48], [-68, 54, -51, -48, -47], [-75, 46, -49, -50], [-76, -47, -49, 51], [-79, 51, 54, 55], [75, 76, 77, 78, 79]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1089 a assignment
  · exact h1084 a assignment
  · exact h996 a assignment
  · exact h997 a assignment
  · exact h1037 a assignment
  · exact h1015 a assignment
  · exact h357 a assignment
  · exact h104 a assignment
  · exact h831 a assignment
  · exact h383 a assignment
  · exact h328 a assignment
  · exact h139 a assignment
  · exact h649 a assignment
  · exact h1093 a assignment
  · exact h1079 a assignment
  · exact h1078 a assignment
  · exact h849 a assignment
  · exact h608 a assignment
  · exact h940 a assignment
  · exact h244 a assignment
  · exact h292 a assignment
  · exact h723 a assignment
  · exact h726 a assignment
  · exact h1059 a assignment
  · exact h573 a assignment
  · exact h720 a assignment
  · exact h721 a assignment
  · exact h727 a assignment
  · exact h729 a assignment

include assignment in
private theorem h1095 : RUP.trueClause a (([-69] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[60, -69], [-69, -60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h1088 a assignment
  · exact h1094 a assignment

include assignment in
private theorem h1096 : RUP.trueClause a (([-60] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-69], [69, -60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h1095 a assignment
  · exact h1046 a assignment

include assignment in
private theorem h1097 : RUP.trueClause a (([-56] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-60], [-63], [63, 60, -56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h1096 a assignment
  · exact h1089 a assignment
  · exact h1087 a assignment

include assignment in
private theorem h1098 : RUP.trueClause a (([-82] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-56], [-63], [-62], [-82, 56, 62, 63]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h1097 a assignment
  · exact h1089 a assignment
  · exact h1037 a assignment
  · exact h734 a assignment

include assignment in
private theorem h1099 : RUP.trueClause a (([-58] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-56], [-60], [-67], [-63], [67, 63, 60, -58, 56]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h1097 a assignment
  · exact h1096 a assignment
  · exact h1084 a assignment
  · exact h1089 a assignment
  · exact h638 a assignment

include assignment in
private theorem h1100 : RUP.trueClause a (([-57] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-58], [-62], [-64], [-56], [-63], [56, 64, -57, 63, 58, 62]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1099 a assignment
  · exact h1037 a assignment
  · exact h996 a assignment
  · exact h1097 a assignment
  · exact h1089 a assignment
  · exact h85 a assignment

include assignment in
private theorem h1101 : RUP.trueClause a (([61] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[-57], [-56], [-82], [-58], [-60], [58, 82, 56, 57, 61, 60]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1100 a assignment
  · exact h1097 a assignment
  · exact h1098 a assignment
  · exact h1099 a assignment
  · exact h1096 a assignment
  · exact h1028 a assignment

include assignment in
private theorem h1102 : RUP.trueClause a (([-68] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[61], [-64], [-61, 64, -68]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h1101 a assignment
  · exact h996 a assignment
  · exact h751 a assignment

include assignment in
private theorem h1103 : RUP.trueClause a (([] : List Int).map RUP.decode) := by
  apply RUP.derive (premises := [[61], [-68], [-58], [-64], [58, -61, 68, 64]]) (by decide +kernel)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h1101 a assignment
  · exact h1102 a assignment
  · exact h1099 a assignment
  · exact h996 a assignment
  · exact h753 a assignment


/-- No assignment satisfies all of the Type 2 determinant-sign conditions. -/
public theorem type2_signsImpossible (signs : Nat → Bool) :
    ¬ ∀ c ∈ signClauses, ∃ l ∈ c, signs l.1 = l.2 := by
  intro valid
  obtain ⟨l, hl, _⟩ := h1103 signs valid
  exact List.not_mem_nil hl

end OrigamiTorus.Type2
