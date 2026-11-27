module

public import OrigamiTorus.EightVertex.Type1.Collapse
public import OrigamiTorus.EightVertex.Type2.CircuitSigns
public import OrigamiTorus.EightVertex.Type2.PluckerSigns
public import OrigamiTorus.Certificates.ReverseUnitPropagation

/-! Determinant-sign refutation for the collapsed seven-vertex triangulation. -/

@[expose] public section

namespace OrigamiTorus.Type1

open Type2 (SignClause sortVertices faceLabels circuitFor choose pluckerAt pluckerClausesFor)

def collapsedLabels : List (List Nat) :=
  collapsedFaces.map (fun f => sortVertices (faceLabels f))

def collapsedEdge (a b : Nat) : Bool :=
  (a != b) && decide (0 < a ∧ a < 8 ∧ 0 < b ∧ b < 8)

def activeLabels : List Nat := List.range' 1 7

def hullSignClauses : List SignClause :=
  ((choose 5 activeLabels).flatMap (circuitFor collapsedLabels collapsedEdge)) ++
    pluckerClausesFor activeLabels


private theorem circuit_mem {q : List Nat} {c : SignClause}
    (hq : q ∈ choose 5 activeLabels) (hc : c ∈ circuitFor collapsedLabels collapsedEdge q) :
    c ∈ hullSignClauses :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨q,hq,hc⟩)

private theorem plucker_mem {s q : List Nat} {c : SignClause}
    (hs : s ∈ choose 2 activeLabels) (hq : q ∈ choose 4 (activeLabels.filter fun v => !s.contains v))
    (hc : c ∈ pluckerAt s q) : c ∈ hullSignClauses :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨s,hs,List.mem_flatMap.mpr ⟨q,hq,hc⟩⟩)

set_option maxRecDepth 10000

open Type2.RUP in
private def checkedClause (row : List Int) : SignClause := row.map decode

variable (a : Nat → Bool) (assignment : ∀ c ∈ hullSignClauses, Type2.RUP.trueClause a c)

-- CaDiCaL's refutation, retaining only the clauses used to derive the empty clause.
-- Input clauses are checked against their circuit or Plücker group.

include assignment in
private theorem group0 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 2, 3, 4, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row2 : List Int := [56, -46, -40, 37, -36]
include assignment in
private theorem clause2 : Type2.RUP.trueClause a (checkedClause row2) :=
  group0 a assignment _ (by decide +kernel)

private def row3 : List Int := [-56, 46, 40, -37, 36]
include assignment in
private theorem clause3 : Type2.RUP.trueClause a (checkedClause row3) :=
  group0 a assignment _ (by decide +kernel)

private def row4 : List Int := [-56, -46, -40, -37, -36]
include assignment in
private theorem clause4 : Type2.RUP.trueClause a (checkedClause row4) :=
  group0 a assignment _ (by decide +kernel)

private def row5 : List Int := [56, 46, 40, 37, 36]
include assignment in
private theorem clause5 : Type2.RUP.trueClause a (checkedClause row5) :=
  group0 a assignment _ (by decide +kernel)

private def row6 : List Int := [-56, 46, 40, 37, 36]
include assignment in
private theorem clause6 : Type2.RUP.trueClause a (checkedClause row6) :=
  group0 a assignment _ (by decide +kernel)

private def row7 : List Int := [56, -46, -40, -37, -36]
include assignment in
private theorem clause7 : Type2.RUP.trueClause a (checkedClause row7) :=
  group0 a assignment _ (by decide +kernel)

private def row8 : List Int := [-56, 46, -40, -37, 36]
include assignment in
private theorem clause8 : Type2.RUP.trueClause a (checkedClause row8) :=
  group0 a assignment _ (by decide +kernel)

private def row9 : List Int := [56, -46, 40, 37, -36]
include assignment in
private theorem clause9 : Type2.RUP.trueClause a (checkedClause row9) :=
  group0 a assignment _ (by decide +kernel)

private def row12 : List Int := [-56, -46, -40, 37, -36]
include assignment in
private theorem clause12 : Type2.RUP.trueClause a (checkedClause row12) :=
  group0 a assignment _ (by decide +kernel)

private def row13 : List Int := [56, 46, 40, -37, 36]
include assignment in
private theorem clause13 : Type2.RUP.trueClause a (checkedClause row13) :=
  group0 a assignment _ (by decide +kernel)

private def row14 : List Int := [-56, 46, 40, 37, -36]
include assignment in
private theorem clause14 : Type2.RUP.trueClause a (checkedClause row14) :=
  group0 a assignment _ (by decide +kernel)

private def row15 : List Int := [56, -46, -40, -37, 36]
include assignment in
private theorem clause15 : Type2.RUP.trueClause a (checkedClause row15) :=
  group0 a assignment _ (by decide +kernel)

private def row18 : List Int := [-56, 46, -40, 37, 36]
include assignment in
private theorem clause18 : Type2.RUP.trueClause a (checkedClause row18) :=
  group0 a assignment _ (by decide +kernel)

private def row19 : List Int := [56, -46, 40, -37, -36]
include assignment in
private theorem clause19 : Type2.RUP.trueClause a (checkedClause row19) :=
  group0 a assignment _ (by decide +kernel)

include assignment in
private theorem group1 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 2, 3, 4, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row22 : List Int := [57, 47, -41, -38, -36]
include assignment in
private theorem clause22 : Type2.RUP.trueClause a (checkedClause row22) :=
  group1 a assignment _ (by decide +kernel)

private def row23 : List Int := [-57, -47, 41, 38, 36]
include assignment in
private theorem clause23 : Type2.RUP.trueClause a (checkedClause row23) :=
  group1 a assignment _ (by decide +kernel)

private def row24 : List Int := [-57, -47, 41, 38, -36]
include assignment in
private theorem clause24 : Type2.RUP.trueClause a (checkedClause row24) :=
  group1 a assignment _ (by decide +kernel)

private def row25 : List Int := [57, 47, -41, -38, 36]
include assignment in
private theorem clause25 : Type2.RUP.trueClause a (checkedClause row25) :=
  group1 a assignment _ (by decide +kernel)

private def row26 : List Int := [-57, 47, 41, 38, 36]
include assignment in
private theorem clause26 : Type2.RUP.trueClause a (checkedClause row26) :=
  group1 a assignment _ (by decide +kernel)

private def row27 : List Int := [57, -47, -41, -38, -36]
include assignment in
private theorem clause27 : Type2.RUP.trueClause a (checkedClause row27) :=
  group1 a assignment _ (by decide +kernel)

private def row28 : List Int := [-57, 47, -41, -38, 36]
include assignment in
private theorem clause28 : Type2.RUP.trueClause a (checkedClause row28) :=
  group1 a assignment _ (by decide +kernel)

private def row29 : List Int := [57, -47, 41, 38, -36]
include assignment in
private theorem clause29 : Type2.RUP.trueClause a (checkedClause row29) :=
  group1 a assignment _ (by decide +kernel)

private def row32 : List Int := [-57, -47, -41, 38, -36]
include assignment in
private theorem clause32 : Type2.RUP.trueClause a (checkedClause row32) :=
  group1 a assignment _ (by decide +kernel)

private def row34 : List Int := [-57, 47, 41, 38, -36]
include assignment in
private theorem clause34 : Type2.RUP.trueClause a (checkedClause row34) :=
  group1 a assignment _ (by decide +kernel)

private def row36 : List Int := [-57, 47, -41, -38, -36]
include assignment in
private theorem clause36 : Type2.RUP.trueClause a (checkedClause row36) :=
  group1 a assignment _ (by decide +kernel)

private def row37 : List Int := [57, -47, 41, 38, 36]
include assignment in
private theorem clause37 : Type2.RUP.trueClause a (checkedClause row37) :=
  group1 a assignment _ (by decide +kernel)

private def row38 : List Int := [-57, 47, -41, 38, 36]
include assignment in
private theorem clause38 : Type2.RUP.trueClause a (checkedClause row38) :=
  group1 a assignment _ (by decide +kernel)

private def row39 : List Int := [57, -47, 41, -38, -36]
include assignment in
private theorem clause39 : Type2.RUP.trueClause a (checkedClause row39) :=
  group1 a assignment _ (by decide +kernel)

include assignment in
private theorem group2 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 2, 3, 4, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row40 : List Int := [58, -48, 42, -39, 36]
include assignment in
private theorem clause40 : Type2.RUP.trueClause a (checkedClause row40) :=
  group2 a assignment _ (by decide +kernel)

private def row41 : List Int := [-58, 48, -42, 39, -36]
include assignment in
private theorem clause41 : Type2.RUP.trueClause a (checkedClause row41) :=
  group2 a assignment _ (by decide +kernel)

private def row42 : List Int := [58, -48, -42, 39, -36]
include assignment in
private theorem clause42 : Type2.RUP.trueClause a (checkedClause row42) :=
  group2 a assignment _ (by decide +kernel)

private def row43 : List Int := [-58, 48, 42, -39, 36]
include assignment in
private theorem clause43 : Type2.RUP.trueClause a (checkedClause row43) :=
  group2 a assignment _ (by decide +kernel)

private def row44 : List Int := [58, 48, 42, 39, -36]
include assignment in
private theorem clause44 : Type2.RUP.trueClause a (checkedClause row44) :=
  group2 a assignment _ (by decide +kernel)

private def row45 : List Int := [-58, -48, -42, -39, 36]
include assignment in
private theorem clause45 : Type2.RUP.trueClause a (checkedClause row45) :=
  group2 a assignment _ (by decide +kernel)

private def row46 : List Int := [-58, 48, 42, 39, 36]
include assignment in
private theorem clause46 : Type2.RUP.trueClause a (checkedClause row46) :=
  group2 a assignment _ (by decide +kernel)

private def row47 : List Int := [58, -48, -42, -39, -36]
include assignment in
private theorem clause47 : Type2.RUP.trueClause a (checkedClause row47) :=
  group2 a assignment _ (by decide +kernel)

private def row48 : List Int := [-58, 48, -42, -39, 36]
include assignment in
private theorem clause48 : Type2.RUP.trueClause a (checkedClause row48) :=
  group2 a assignment _ (by decide +kernel)

private def row49 : List Int := [58, -48, 42, 39, -36]
include assignment in
private theorem clause49 : Type2.RUP.trueClause a (checkedClause row49) :=
  group2 a assignment _ (by decide +kernel)

private def row50 : List Int := [58, 48, -42, 39, -36]
include assignment in
private theorem clause50 : Type2.RUP.trueClause a (checkedClause row50) :=
  group2 a assignment _ (by decide +kernel)

private def row51 : List Int := [-58, -48, 42, -39, 36]
include assignment in
private theorem clause51 : Type2.RUP.trueClause a (checkedClause row51) :=
  group2 a assignment _ (by decide +kernel)

private def row52 : List Int := [-58, -48, -42, 39, -36]
include assignment in
private theorem clause52 : Type2.RUP.trueClause a (checkedClause row52) :=
  group2 a assignment _ (by decide +kernel)

private def row54 : List Int := [-58, 48, 42, 39, -36]
include assignment in
private theorem clause54 : Type2.RUP.trueClause a (checkedClause row54) :=
  group2 a assignment _ (by decide +kernel)

private def row55 : List Int := [58, -48, -42, -39, 36]
include assignment in
private theorem clause55 : Type2.RUP.trueClause a (checkedClause row55) :=
  group2 a assignment _ (by decide +kernel)

private def row56 : List Int := [-58, 48, -42, -39, -36]
include assignment in
private theorem clause56 : Type2.RUP.trueClause a (checkedClause row56) :=
  group2 a assignment _ (by decide +kernel)

private def row57 : List Int := [58, -48, 42, 39, 36]
include assignment in
private theorem clause57 : Type2.RUP.trueClause a (checkedClause row57) :=
  group2 a assignment _ (by decide +kernel)

private def row58 : List Int := [-58, 48, -42, 39, 36]
include assignment in
private theorem clause58 : Type2.RUP.trueClause a (checkedClause row58) :=
  group2 a assignment _ (by decide +kernel)

private def row59 : List Int := [58, -48, 42, -39, -36]
include assignment in
private theorem clause59 : Type2.RUP.trueClause a (checkedClause row59) :=
  group2 a assignment _ (by decide +kernel)

include assignment in
private theorem group3 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 2, 3, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row61 : List Int := [-59, 49, -43, 38, -37]
include assignment in
private theorem clause61 : Type2.RUP.trueClause a (checkedClause row61) :=
  group3 a assignment _ (by decide +kernel)

private def row62 : List Int := [59, 49, 43, 38, -37]
include assignment in
private theorem clause62 : Type2.RUP.trueClause a (checkedClause row62) :=
  group3 a assignment _ (by decide +kernel)

private def row63 : List Int := [-59, -49, -43, -38, 37]
include assignment in
private theorem clause63 : Type2.RUP.trueClause a (checkedClause row63) :=
  group3 a assignment _ (by decide +kernel)

private def row64 : List Int := [59, 49, -43, -38, -37]
include assignment in
private theorem clause64 : Type2.RUP.trueClause a (checkedClause row64) :=
  group3 a assignment _ (by decide +kernel)

private def row65 : List Int := [-59, -49, 43, 38, 37]
include assignment in
private theorem clause65 : Type2.RUP.trueClause a (checkedClause row65) :=
  group3 a assignment _ (by decide +kernel)

private def row66 : List Int := [-59, -49, -43, 38, 37]
include assignment in
private theorem clause66 : Type2.RUP.trueClause a (checkedClause row66) :=
  group3 a assignment _ (by decide +kernel)

private def row67 : List Int := [59, 49, 43, -38, -37]
include assignment in
private theorem clause67 : Type2.RUP.trueClause a (checkedClause row67) :=
  group3 a assignment _ (by decide +kernel)

private def row68 : List Int := [-59, 49, -43, -38, 37]
include assignment in
private theorem clause68 : Type2.RUP.trueClause a (checkedClause row68) :=
  group3 a assignment _ (by decide +kernel)

private def row69 : List Int := [59, -49, 43, 38, -37]
include assignment in
private theorem clause69 : Type2.RUP.trueClause a (checkedClause row69) :=
  group3 a assignment _ (by decide +kernel)

private def row70 : List Int := [59, 49, -43, 38, -37]
include assignment in
private theorem clause70 : Type2.RUP.trueClause a (checkedClause row70) :=
  group3 a assignment _ (by decide +kernel)

private def row71 : List Int := [-59, -49, 43, -38, 37]
include assignment in
private theorem clause71 : Type2.RUP.trueClause a (checkedClause row71) :=
  group3 a assignment _ (by decide +kernel)

private def row72 : List Int := [-59, -49, -43, 38, -37]
include assignment in
private theorem clause72 : Type2.RUP.trueClause a (checkedClause row72) :=
  group3 a assignment _ (by decide +kernel)

private def row73 : List Int := [59, 49, 43, -38, 37]
include assignment in
private theorem clause73 : Type2.RUP.trueClause a (checkedClause row73) :=
  group3 a assignment _ (by decide +kernel)

private def row76 : List Int := [-59, 49, -43, -38, -37]
include assignment in
private theorem clause76 : Type2.RUP.trueClause a (checkedClause row76) :=
  group3 a assignment _ (by decide +kernel)

private def row77 : List Int := [59, -49, 43, 38, 37]
include assignment in
private theorem clause77 : Type2.RUP.trueClause a (checkedClause row77) :=
  group3 a assignment _ (by decide +kernel)

private def row78 : List Int := [-59, 49, -43, 38, 37]
include assignment in
private theorem clause78 : Type2.RUP.trueClause a (checkedClause row78) :=
  group3 a assignment _ (by decide +kernel)

private def row79 : List Int := [59, -49, 43, -38, -37]
include assignment in
private theorem clause79 : Type2.RUP.trueClause a (checkedClause row79) :=
  group3 a assignment _ (by decide +kernel)

include assignment in
private theorem group4 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 2, 3, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row82 : List Int := [60, 50, 44, 39, -37]
include assignment in
private theorem clause82 : Type2.RUP.trueClause a (checkedClause row82) :=
  group4 a assignment _ (by decide +kernel)

private def row83 : List Int := [-60, -50, -44, -39, 37]
include assignment in
private theorem clause83 : Type2.RUP.trueClause a (checkedClause row83) :=
  group4 a assignment _ (by decide +kernel)

private def row85 : List Int := [60, 50, -44, -39, 37]
include assignment in
private theorem clause85 : Type2.RUP.trueClause a (checkedClause row85) :=
  group4 a assignment _ (by decide +kernel)

private def row86 : List Int := [-60, -50, -44, 39, 37]
include assignment in
private theorem clause86 : Type2.RUP.trueClause a (checkedClause row86) :=
  group4 a assignment _ (by decide +kernel)

private def row87 : List Int := [60, 50, 44, -39, -37]
include assignment in
private theorem clause87 : Type2.RUP.trueClause a (checkedClause row87) :=
  group4 a assignment _ (by decide +kernel)

private def row88 : List Int := [-60, 50, -44, -39, 37]
include assignment in
private theorem clause88 : Type2.RUP.trueClause a (checkedClause row88) :=
  group4 a assignment _ (by decide +kernel)

private def row89 : List Int := [60, -50, 44, 39, -37]
include assignment in
private theorem clause89 : Type2.RUP.trueClause a (checkedClause row89) :=
  group4 a assignment _ (by decide +kernel)

private def row91 : List Int := [-60, -50, 44, -39, 37]
include assignment in
private theorem clause91 : Type2.RUP.trueClause a (checkedClause row91) :=
  group4 a assignment _ (by decide +kernel)

private def row93 : List Int := [60, 50, 44, -39, 37]
include assignment in
private theorem clause93 : Type2.RUP.trueClause a (checkedClause row93) :=
  group4 a assignment _ (by decide +kernel)

private def row96 : List Int := [-60, 50, -44, -39, -37]
include assignment in
private theorem clause96 : Type2.RUP.trueClause a (checkedClause row96) :=
  group4 a assignment _ (by decide +kernel)

private def row98 : List Int := [-60, 50, -44, 39, 37]
include assignment in
private theorem clause98 : Type2.RUP.trueClause a (checkedClause row98) :=
  group4 a assignment _ (by decide +kernel)

private def row99 : List Int := [60, -50, 44, -39, -37]
include assignment in
private theorem clause99 : Type2.RUP.trueClause a (checkedClause row99) :=
  group4 a assignment _ (by decide +kernel)

include assignment in
private theorem group5 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 2, 3, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row102 : List Int := [61, -51, -45, 39, -38]
include assignment in
private theorem clause102 : Type2.RUP.trueClause a (checkedClause row102) :=
  group5 a assignment _ (by decide +kernel)

private def row103 : List Int := [-61, 51, 45, -39, 38]
include assignment in
private theorem clause103 : Type2.RUP.trueClause a (checkedClause row103) :=
  group5 a assignment _ (by decide +kernel)

private def row104 : List Int := [61, 51, -45, 39, 38]
include assignment in
private theorem clause104 : Type2.RUP.trueClause a (checkedClause row104) :=
  group5 a assignment _ (by decide +kernel)

private def row106 : List Int := [-61, -51, 45, 39, -38]
include assignment in
private theorem clause106 : Type2.RUP.trueClause a (checkedClause row106) :=
  group5 a assignment _ (by decide +kernel)

private def row107 : List Int := [61, 51, -45, -39, 38]
include assignment in
private theorem clause107 : Type2.RUP.trueClause a (checkedClause row107) :=
  group5 a assignment _ (by decide +kernel)

private def row108 : List Int := [-61, 51, -45, -39, 38]
include assignment in
private theorem clause108 : Type2.RUP.trueClause a (checkedClause row108) :=
  group5 a assignment _ (by decide +kernel)

private def row109 : List Int := [61, -51, 45, 39, -38]
include assignment in
private theorem clause109 : Type2.RUP.trueClause a (checkedClause row109) :=
  group5 a assignment _ (by decide +kernel)

private def row110 : List Int := [61, 51, -45, 39, -38]
include assignment in
private theorem clause110 : Type2.RUP.trueClause a (checkedClause row110) :=
  group5 a assignment _ (by decide +kernel)

private def row111 : List Int := [-61, -51, 45, -39, 38]
include assignment in
private theorem clause111 : Type2.RUP.trueClause a (checkedClause row111) :=
  group5 a assignment _ (by decide +kernel)

private def row112 : List Int := [-61, -51, -45, 39, -38]
include assignment in
private theorem clause112 : Type2.RUP.trueClause a (checkedClause row112) :=
  group5 a assignment _ (by decide +kernel)

private def row113 : List Int := [61, 51, 45, -39, 38]
include assignment in
private theorem clause113 : Type2.RUP.trueClause a (checkedClause row113) :=
  group5 a assignment _ (by decide +kernel)

private def row117 : List Int := [61, -51, 45, 39, 38]
include assignment in
private theorem clause117 : Type2.RUP.trueClause a (checkedClause row117) :=
  group5 a assignment _ (by decide +kernel)

private def row119 : List Int := [61, -51, 45, -39, -38]
include assignment in
private theorem clause119 : Type2.RUP.trueClause a (checkedClause row119) :=
  group5 a assignment _ (by decide +kernel)

include assignment in
private theorem group6 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 2, 4, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row123 : List Int := [-62, 52, 43, -41, 40]
include assignment in
private theorem clause123 : Type2.RUP.trueClause a (checkedClause row123) :=
  group6 a assignment _ (by decide +kernel)

private def row124 : List Int := [62, 52, 43, 41, -40]
include assignment in
private theorem clause124 : Type2.RUP.trueClause a (checkedClause row124) :=
  group6 a assignment _ (by decide +kernel)

private def row125 : List Int := [-62, -52, -43, -41, 40]
include assignment in
private theorem clause125 : Type2.RUP.trueClause a (checkedClause row125) :=
  group6 a assignment _ (by decide +kernel)

private def row126 : List Int := [-62, -52, -43, -41, -40]
include assignment in
private theorem clause126 : Type2.RUP.trueClause a (checkedClause row126) :=
  group6 a assignment _ (by decide +kernel)

private def row127 : List Int := [62, 52, 43, 41, 40]
include assignment in
private theorem clause127 : Type2.RUP.trueClause a (checkedClause row127) :=
  group6 a assignment _ (by decide +kernel)

private def row128 : List Int := [-62, 52, -43, -41, 40]
include assignment in
private theorem clause128 : Type2.RUP.trueClause a (checkedClause row128) :=
  group6 a assignment _ (by decide +kernel)

private def row129 : List Int := [62, -52, 43, 41, -40]
include assignment in
private theorem clause129 : Type2.RUP.trueClause a (checkedClause row129) :=
  group6 a assignment _ (by decide +kernel)

private def row130 : List Int := [62, 52, -43, 41, -40]
include assignment in
private theorem clause130 : Type2.RUP.trueClause a (checkedClause row130) :=
  group6 a assignment _ (by decide +kernel)

private def row131 : List Int := [-62, -52, 43, -41, 40]
include assignment in
private theorem clause131 : Type2.RUP.trueClause a (checkedClause row131) :=
  group6 a assignment _ (by decide +kernel)

private def row132 : List Int := [-62, -52, -43, 41, -40]
include assignment in
private theorem clause132 : Type2.RUP.trueClause a (checkedClause row132) :=
  group6 a assignment _ (by decide +kernel)

private def row133 : List Int := [62, 52, 43, -41, 40]
include assignment in
private theorem clause133 : Type2.RUP.trueClause a (checkedClause row133) :=
  group6 a assignment _ (by decide +kernel)

private def row136 : List Int := [-62, 52, -43, -41, -40]
include assignment in
private theorem clause136 : Type2.RUP.trueClause a (checkedClause row136) :=
  group6 a assignment _ (by decide +kernel)

private def row138 : List Int := [-62, 52, -43, 41, 40]
include assignment in
private theorem clause138 : Type2.RUP.trueClause a (checkedClause row138) :=
  group6 a assignment _ (by decide +kernel)

private def row139 : List Int := [62, -52, 43, -41, -40]
include assignment in
private theorem clause139 : Type2.RUP.trueClause a (checkedClause row139) :=
  group6 a assignment _ (by decide +kernel)

include assignment in
private theorem group7 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 2, 4, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row142 : List Int := [63, 53, 44, 42, -40]
include assignment in
private theorem clause142 : Type2.RUP.trueClause a (checkedClause row142) :=
  group7 a assignment _ (by decide +kernel)

private def row145 : List Int := [-63, -53, 44, 42, 40]
include assignment in
private theorem clause145 : Type2.RUP.trueClause a (checkedClause row145) :=
  group7 a assignment _ (by decide +kernel)

private def row147 : List Int := [63, 53, -44, -42, 40]
include assignment in
private theorem clause147 : Type2.RUP.trueClause a (checkedClause row147) :=
  group7 a assignment _ (by decide +kernel)

private def row148 : List Int := [-63, 53, -44, -42, 40]
include assignment in
private theorem clause148 : Type2.RUP.trueClause a (checkedClause row148) :=
  group7 a assignment _ (by decide +kernel)

private def row150 : List Int := [63, 53, -44, 42, -40]
include assignment in
private theorem clause150 : Type2.RUP.trueClause a (checkedClause row150) :=
  group7 a assignment _ (by decide +kernel)

private def row151 : List Int := [-63, -53, 44, -42, 40]
include assignment in
private theorem clause151 : Type2.RUP.trueClause a (checkedClause row151) :=
  group7 a assignment _ (by decide +kernel)

private def row153 : List Int := [63, 53, 44, -42, 40]
include assignment in
private theorem clause153 : Type2.RUP.trueClause a (checkedClause row153) :=
  group7 a assignment _ (by decide +kernel)

private def row156 : List Int := [-63, 53, -44, -42, -40]
include assignment in
private theorem clause156 : Type2.RUP.trueClause a (checkedClause row156) :=
  group7 a assignment _ (by decide +kernel)

private def row158 : List Int := [-63, 53, -44, 42, 40]
include assignment in
private theorem clause158 : Type2.RUP.trueClause a (checkedClause row158) :=
  group7 a assignment _ (by decide +kernel)

include assignment in
private theorem group8 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 2, 4, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row162 : List Int := [64, 54, -45, -42, -41]
include assignment in
private theorem clause162 : Type2.RUP.trueClause a (checkedClause row162) :=
  group8 a assignment _ (by decide +kernel)

private def row165 : List Int := [64, 54, -45, -42, 41]
include assignment in
private theorem clause165 : Type2.RUP.trueClause a (checkedClause row165) :=
  group8 a assignment _ (by decide +kernel)

private def row166 : List Int := [-64, -54, -45, 42, 41]
include assignment in
private theorem clause166 : Type2.RUP.trueClause a (checkedClause row166) :=
  group8 a assignment _ (by decide +kernel)

private def row167 : List Int := [64, 54, 45, -42, -41]
include assignment in
private theorem clause167 : Type2.RUP.trueClause a (checkedClause row167) :=
  group8 a assignment _ (by decide +kernel)

private def row168 : List Int := [-64, 54, -45, -42, 41]
include assignment in
private theorem clause168 : Type2.RUP.trueClause a (checkedClause row168) :=
  group8 a assignment _ (by decide +kernel)

private def row169 : List Int := [64, -54, 45, 42, -41]
include assignment in
private theorem clause169 : Type2.RUP.trueClause a (checkedClause row169) :=
  group8 a assignment _ (by decide +kernel)

private def row173 : List Int := [64, 54, 45, -42, 41]
include assignment in
private theorem clause173 : Type2.RUP.trueClause a (checkedClause row173) :=
  group8 a assignment _ (by decide +kernel)

private def row176 : List Int := [-64, 54, -45, -42, -41]
include assignment in
private theorem clause176 : Type2.RUP.trueClause a (checkedClause row176) :=
  group8 a assignment _ (by decide +kernel)

private def row178 : List Int := [-64, 54, -45, 42, 41]
include assignment in
private theorem clause178 : Type2.RUP.trueClause a (checkedClause row178) :=
  group8 a assignment _ (by decide +kernel)

private def row179 : List Int := [64, -54, 45, -42, -41]
include assignment in
private theorem clause179 : Type2.RUP.trueClause a (checkedClause row179) :=
  group8 a assignment _ (by decide +kernel)

include assignment in
private theorem group9 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 2, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row182 : List Int := [65, 55, -45, -44, -43]
include assignment in
private theorem clause182 : Type2.RUP.trueClause a (checkedClause row182) :=
  group9 a assignment _ (by decide +kernel)

private def row184 : List Int := [65, 55, -45, 44, 43]
include assignment in
private theorem clause184 : Type2.RUP.trueClause a (checkedClause row184) :=
  group9 a assignment _ (by decide +kernel)

private def row185 : List Int := [-65, -55, 45, -44, -43]
include assignment in
private theorem clause185 : Type2.RUP.trueClause a (checkedClause row185) :=
  group9 a assignment _ (by decide +kernel)

private def row186 : List Int := [-65, -55, 45, 44, -43]
include assignment in
private theorem clause186 : Type2.RUP.trueClause a (checkedClause row186) :=
  group9 a assignment _ (by decide +kernel)

private def row187 : List Int := [65, 55, -45, -44, 43]
include assignment in
private theorem clause187 : Type2.RUP.trueClause a (checkedClause row187) :=
  group9 a assignment _ (by decide +kernel)

private def row188 : List Int := [-65, -55, -45, -44, -43]
include assignment in
private theorem clause188 : Type2.RUP.trueClause a (checkedClause row188) :=
  group9 a assignment _ (by decide +kernel)

private def row189 : List Int := [65, 55, 45, 44, 43]
include assignment in
private theorem clause189 : Type2.RUP.trueClause a (checkedClause row189) :=
  group9 a assignment _ (by decide +kernel)

private def row190 : List Int := [65, 55, -45, 44, -43]
include assignment in
private theorem clause190 : Type2.RUP.trueClause a (checkedClause row190) :=
  group9 a assignment _ (by decide +kernel)

private def row192 : List Int := [-65, -55, -45, 44, -43]
include assignment in
private theorem clause192 : Type2.RUP.trueClause a (checkedClause row192) :=
  group9 a assignment _ (by decide +kernel)

private def row193 : List Int := [65, 55, 45, -44, 43]
include assignment in
private theorem clause193 : Type2.RUP.trueClause a (checkedClause row193) :=
  group9 a assignment _ (by decide +kernel)

private def row197 : List Int := [65, -55, 45, 44, 43]
include assignment in
private theorem clause197 : Type2.RUP.trueClause a (checkedClause row197) :=
  group9 a assignment _ (by decide +kernel)

private def row199 : List Int := [65, -55, 45, -44, -43]
include assignment in
private theorem clause199 : Type2.RUP.trueClause a (checkedClause row199) :=
  group9 a assignment _ (by decide +kernel)

include assignment in
private theorem group10 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 3, 4, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row200 : List Int := [66, -52, 49, -47, 46]
include assignment in
private theorem clause200 : Type2.RUP.trueClause a (checkedClause row200) :=
  group10 a assignment _ (by decide +kernel)

private def row201 : List Int := [-66, 52, -49, 47, -46]
include assignment in
private theorem clause201 : Type2.RUP.trueClause a (checkedClause row201) :=
  group10 a assignment _ (by decide +kernel)

private def row202 : List Int := [66, -52, -49, 47, -46]
include assignment in
private theorem clause202 : Type2.RUP.trueClause a (checkedClause row202) :=
  group10 a assignment _ (by decide +kernel)

private def row203 : List Int := [-66, 52, 49, -47, 46]
include assignment in
private theorem clause203 : Type2.RUP.trueClause a (checkedClause row203) :=
  group10 a assignment _ (by decide +kernel)

private def row204 : List Int := [66, 52, -49, 47, 46]
include assignment in
private theorem clause204 : Type2.RUP.trueClause a (checkedClause row204) :=
  group10 a assignment _ (by decide +kernel)

private def row205 : List Int := [-66, -52, 49, -47, -46]
include assignment in
private theorem clause205 : Type2.RUP.trueClause a (checkedClause row205) :=
  group10 a assignment _ (by decide +kernel)

private def row206 : List Int := [-66, -52, -49, -47, -46]
include assignment in
private theorem clause206 : Type2.RUP.trueClause a (checkedClause row206) :=
  group10 a assignment _ (by decide +kernel)

private def row207 : List Int := [66, 52, 49, 47, 46]
include assignment in
private theorem clause207 : Type2.RUP.trueClause a (checkedClause row207) :=
  group10 a assignment _ (by decide +kernel)

private def row208 : List Int := [-66, 52, 49, 47, 46]
include assignment in
private theorem clause208 : Type2.RUP.trueClause a (checkedClause row208) :=
  group10 a assignment _ (by decide +kernel)

private def row209 : List Int := [66, -52, -49, -47, -46]
include assignment in
private theorem clause209 : Type2.RUP.trueClause a (checkedClause row209) :=
  group10 a assignment _ (by decide +kernel)

private def row210 : List Int := [66, 52, -49, 47, -46]
include assignment in
private theorem clause210 : Type2.RUP.trueClause a (checkedClause row210) :=
  group10 a assignment _ (by decide +kernel)

private def row211 : List Int := [-66, -52, 49, -47, 46]
include assignment in
private theorem clause211 : Type2.RUP.trueClause a (checkedClause row211) :=
  group10 a assignment _ (by decide +kernel)

private def row212 : List Int := [-66, -52, -49, 47, -46]
include assignment in
private theorem clause212 : Type2.RUP.trueClause a (checkedClause row212) :=
  group10 a assignment _ (by decide +kernel)

private def row213 : List Int := [66, 52, 49, -47, 46]
include assignment in
private theorem clause213 : Type2.RUP.trueClause a (checkedClause row213) :=
  group10 a assignment _ (by decide +kernel)

private def row214 : List Int := [-66, 52, 49, 47, -46]
include assignment in
private theorem clause214 : Type2.RUP.trueClause a (checkedClause row214) :=
  group10 a assignment _ (by decide +kernel)

private def row215 : List Int := [66, -52, -49, -47, 46]
include assignment in
private theorem clause215 : Type2.RUP.trueClause a (checkedClause row215) :=
  group10 a assignment _ (by decide +kernel)

private def row216 : List Int := [-66, 52, -49, -47, -46]
include assignment in
private theorem clause216 : Type2.RUP.trueClause a (checkedClause row216) :=
  group10 a assignment _ (by decide +kernel)

private def row217 : List Int := [66, -52, 49, 47, 46]
include assignment in
private theorem clause217 : Type2.RUP.trueClause a (checkedClause row217) :=
  group10 a assignment _ (by decide +kernel)

private def row219 : List Int := [66, -52, 49, -47, -46]
include assignment in
private theorem clause219 : Type2.RUP.trueClause a (checkedClause row219) :=
  group10 a assignment _ (by decide +kernel)

include assignment in
private theorem group11 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 3, 4, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row220 : List Int := [67, -53, 50, -48, 46]
include assignment in
private theorem clause220 : Type2.RUP.trueClause a (checkedClause row220) :=
  group11 a assignment _ (by decide +kernel)

private def row221 : List Int := [-67, 53, -50, 48, -46]
include assignment in
private theorem clause221 : Type2.RUP.trueClause a (checkedClause row221) :=
  group11 a assignment _ (by decide +kernel)

private def row222 : List Int := [67, 53, -50, -48, -46]
include assignment in
private theorem clause222 : Type2.RUP.trueClause a (checkedClause row222) :=
  group11 a assignment _ (by decide +kernel)

private def row223 : List Int := [-67, -53, 50, 48, 46]
include assignment in
private theorem clause223 : Type2.RUP.trueClause a (checkedClause row223) :=
  group11 a assignment _ (by decide +kernel)

private def row224 : List Int := [67, 53, -50, 48, 46]
include assignment in
private theorem clause224 : Type2.RUP.trueClause a (checkedClause row224) :=
  group11 a assignment _ (by decide +kernel)

private def row225 : List Int := [-67, -53, 50, -48, -46]
include assignment in
private theorem clause225 : Type2.RUP.trueClause a (checkedClause row225) :=
  group11 a assignment _ (by decide +kernel)

private def row226 : List Int := [-67, -53, 50, 48, -46]
include assignment in
private theorem clause226 : Type2.RUP.trueClause a (checkedClause row226) :=
  group11 a assignment _ (by decide +kernel)

private def row227 : List Int := [67, 53, -50, -48, 46]
include assignment in
private theorem clause227 : Type2.RUP.trueClause a (checkedClause row227) :=
  group11 a assignment _ (by decide +kernel)

private def row228 : List Int := [-67, 53, 50, 48, 46]
include assignment in
private theorem clause228 : Type2.RUP.trueClause a (checkedClause row228) :=
  group11 a assignment _ (by decide +kernel)

private def row229 : List Int := [67, -53, -50, -48, -46]
include assignment in
private theorem clause229 : Type2.RUP.trueClause a (checkedClause row229) :=
  group11 a assignment _ (by decide +kernel)

private def row231 : List Int := [-67, -53, 50, -48, 46]
include assignment in
private theorem clause231 : Type2.RUP.trueClause a (checkedClause row231) :=
  group11 a assignment _ (by decide +kernel)

private def row232 : List Int := [-67, -53, -50, 48, -46]
include assignment in
private theorem clause232 : Type2.RUP.trueClause a (checkedClause row232) :=
  group11 a assignment _ (by decide +kernel)

private def row233 : List Int := [67, 53, 50, -48, 46]
include assignment in
private theorem clause233 : Type2.RUP.trueClause a (checkedClause row233) :=
  group11 a assignment _ (by decide +kernel)

private def row234 : List Int := [-67, 53, 50, 48, -46]
include assignment in
private theorem clause234 : Type2.RUP.trueClause a (checkedClause row234) :=
  group11 a assignment _ (by decide +kernel)

private def row235 : List Int := [67, -53, -50, -48, 46]
include assignment in
private theorem clause235 : Type2.RUP.trueClause a (checkedClause row235) :=
  group11 a assignment _ (by decide +kernel)

private def row236 : List Int := [-67, 53, -50, -48, -46]
include assignment in
private theorem clause236 : Type2.RUP.trueClause a (checkedClause row236) :=
  group11 a assignment _ (by decide +kernel)

private def row237 : List Int := [67, -53, 50, 48, 46]
include assignment in
private theorem clause237 : Type2.RUP.trueClause a (checkedClause row237) :=
  group11 a assignment _ (by decide +kernel)

private def row238 : List Int := [-67, 53, -50, 48, 46]
include assignment in
private theorem clause238 : Type2.RUP.trueClause a (checkedClause row238) :=
  group11 a assignment _ (by decide +kernel)

private def row239 : List Int := [67, -53, 50, -48, -46]
include assignment in
private theorem clause239 : Type2.RUP.trueClause a (checkedClause row239) :=
  group11 a assignment _ (by decide +kernel)

include assignment in
private theorem group12 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 3, 4, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row240 : List Int := [68, -54, 51, -48, 47]
include assignment in
private theorem clause240 : Type2.RUP.trueClause a (checkedClause row240) :=
  group12 a assignment _ (by decide +kernel)

private def row242 : List Int := [68, 54, 51, 48, -47]
include assignment in
private theorem clause242 : Type2.RUP.trueClause a (checkedClause row242) :=
  group12 a assignment _ (by decide +kernel)

private def row243 : List Int := [-68, -54, -51, -48, 47]
include assignment in
private theorem clause243 : Type2.RUP.trueClause a (checkedClause row243) :=
  group12 a assignment _ (by decide +kernel)

private def row244 : List Int := [68, 54, -51, -48, -47]
include assignment in
private theorem clause244 : Type2.RUP.trueClause a (checkedClause row244) :=
  group12 a assignment _ (by decide +kernel)

private def row245 : List Int := [-68, -54, 51, 48, 47]
include assignment in
private theorem clause245 : Type2.RUP.trueClause a (checkedClause row245) :=
  group12 a assignment _ (by decide +kernel)

private def row246 : List Int := [-68, -54, 51, 48, -47]
include assignment in
private theorem clause246 : Type2.RUP.trueClause a (checkedClause row246) :=
  group12 a assignment _ (by decide +kernel)

private def row247 : List Int := [68, 54, -51, -48, 47]
include assignment in
private theorem clause247 : Type2.RUP.trueClause a (checkedClause row247) :=
  group12 a assignment _ (by decide +kernel)

private def row248 : List Int := [-68, -54, -51, 48, 47]
include assignment in
private theorem clause248 : Type2.RUP.trueClause a (checkedClause row248) :=
  group12 a assignment _ (by decide +kernel)

private def row249 : List Int := [68, 54, 51, -48, -47]
include assignment in
private theorem clause249 : Type2.RUP.trueClause a (checkedClause row249) :=
  group12 a assignment _ (by decide +kernel)

private def row250 : List Int := [68, 54, -51, 48, -47]
include assignment in
private theorem clause250 : Type2.RUP.trueClause a (checkedClause row250) :=
  group12 a assignment _ (by decide +kernel)

private def row251 : List Int := [-68, -54, 51, -48, 47]
include assignment in
private theorem clause251 : Type2.RUP.trueClause a (checkedClause row251) :=
  group12 a assignment _ (by decide +kernel)

private def row253 : List Int := [68, 54, 51, -48, 47]
include assignment in
private theorem clause253 : Type2.RUP.trueClause a (checkedClause row253) :=
  group12 a assignment _ (by decide +kernel)

private def row254 : List Int := [-68, 54, 51, 48, -47]
include assignment in
private theorem clause254 : Type2.RUP.trueClause a (checkedClause row254) :=
  group12 a assignment _ (by decide +kernel)

private def row255 : List Int := [68, -54, -51, -48, 47]
include assignment in
private theorem clause255 : Type2.RUP.trueClause a (checkedClause row255) :=
  group12 a assignment _ (by decide +kernel)

private def row257 : List Int := [68, -54, 51, 48, 47]
include assignment in
private theorem clause257 : Type2.RUP.trueClause a (checkedClause row257) :=
  group12 a assignment _ (by decide +kernel)

private def row258 : List Int := [-68, 54, -51, 48, 47]
include assignment in
private theorem clause258 : Type2.RUP.trueClause a (checkedClause row258) :=
  group12 a assignment _ (by decide +kernel)

private def row259 : List Int := [68, -54, 51, -48, -47]
include assignment in
private theorem clause259 : Type2.RUP.trueClause a (checkedClause row259) :=
  group12 a assignment _ (by decide +kernel)

include assignment in
private theorem group13 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 3, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row261 : List Int := [-69, 55, -51, 50, -49]
include assignment in
private theorem clause261 : Type2.RUP.trueClause a (checkedClause row261) :=
  group13 a assignment _ (by decide +kernel)

private def row262 : List Int := [69, 55, 51, 50, -49]
include assignment in
private theorem clause262 : Type2.RUP.trueClause a (checkedClause row262) :=
  group13 a assignment _ (by decide +kernel)

private def row263 : List Int := [-69, -55, -51, -50, 49]
include assignment in
private theorem clause263 : Type2.RUP.trueClause a (checkedClause row263) :=
  group13 a assignment _ (by decide +kernel)

private def row264 : List Int := [-69, -55, 51, 50, -49]
include assignment in
private theorem clause264 : Type2.RUP.trueClause a (checkedClause row264) :=
  group13 a assignment _ (by decide +kernel)

private def row265 : List Int := [69, 55, -51, -50, 49]
include assignment in
private theorem clause265 : Type2.RUP.trueClause a (checkedClause row265) :=
  group13 a assignment _ (by decide +kernel)

private def row266 : List Int := [-69, -55, -51, -50, -49]
include assignment in
private theorem clause266 : Type2.RUP.trueClause a (checkedClause row266) :=
  group13 a assignment _ (by decide +kernel)

private def row267 : List Int := [69, 55, 51, 50, 49]
include assignment in
private theorem clause267 : Type2.RUP.trueClause a (checkedClause row267) :=
  group13 a assignment _ (by decide +kernel)

private def row268 : List Int := [-69, 55, -51, -50, 49]
include assignment in
private theorem clause268 : Type2.RUP.trueClause a (checkedClause row268) :=
  group13 a assignment _ (by decide +kernel)

private def row269 : List Int := [69, -55, 51, 50, -49]
include assignment in
private theorem clause269 : Type2.RUP.trueClause a (checkedClause row269) :=
  group13 a assignment _ (by decide +kernel)

private def row271 : List Int := [-69, -55, 51, -50, 49]
include assignment in
private theorem clause271 : Type2.RUP.trueClause a (checkedClause row271) :=
  group13 a assignment _ (by decide +kernel)

private def row272 : List Int := [-69, -55, -51, 50, -49]
include assignment in
private theorem clause272 : Type2.RUP.trueClause a (checkedClause row272) :=
  group13 a assignment _ (by decide +kernel)

private def row273 : List Int := [69, 55, 51, -50, 49]
include assignment in
private theorem clause273 : Type2.RUP.trueClause a (checkedClause row273) :=
  group13 a assignment _ (by decide +kernel)

private def row274 : List Int := [-69, 55, 51, 50, -49]
include assignment in
private theorem clause274 : Type2.RUP.trueClause a (checkedClause row274) :=
  group13 a assignment _ (by decide +kernel)

private def row276 : List Int := [-69, 55, -51, -50, -49]
include assignment in
private theorem clause276 : Type2.RUP.trueClause a (checkedClause row276) :=
  group13 a assignment _ (by decide +kernel)

private def row277 : List Int := [69, -55, 51, 50, 49]
include assignment in
private theorem clause277 : Type2.RUP.trueClause a (checkedClause row277) :=
  group13 a assignment _ (by decide +kernel)

private def row278 : List Int := [-69, 55, -51, 50, 49]
include assignment in
private theorem clause278 : Type2.RUP.trueClause a (checkedClause row278) :=
  group13 a assignment _ (by decide +kernel)

private def row279 : List Int := [69, -55, 51, -50, -49]
include assignment in
private theorem clause279 : Type2.RUP.trueClause a (checkedClause row279) :=
  group13 a assignment _ (by decide +kernel)

include assignment in
private theorem group14 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [1, 4, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row281 : List Int := [-70, 55, -54, 53, -52]
include assignment in
private theorem clause281 : Type2.RUP.trueClause a (checkedClause row281) :=
  group14 a assignment _ (by decide +kernel)

private def row282 : List Int := [70, 55, -54, 53, 52]
include assignment in
private theorem clause282 : Type2.RUP.trueClause a (checkedClause row282) :=
  group14 a assignment _ (by decide +kernel)

private def row283 : List Int := [-70, -55, 54, -53, -52]
include assignment in
private theorem clause283 : Type2.RUP.trueClause a (checkedClause row283) :=
  group14 a assignment _ (by decide +kernel)

private def row284 : List Int := [-70, -55, 54, 53, -52]
include assignment in
private theorem clause284 : Type2.RUP.trueClause a (checkedClause row284) :=
  group14 a assignment _ (by decide +kernel)

private def row285 : List Int := [70, 55, -54, -53, 52]
include assignment in
private theorem clause285 : Type2.RUP.trueClause a (checkedClause row285) :=
  group14 a assignment _ (by decide +kernel)

private def row286 : List Int := [-70, -55, -54, -53, -52]
include assignment in
private theorem clause286 : Type2.RUP.trueClause a (checkedClause row286) :=
  group14 a assignment _ (by decide +kernel)

private def row287 : List Int := [70, 55, 54, 53, 52]
include assignment in
private theorem clause287 : Type2.RUP.trueClause a (checkedClause row287) :=
  group14 a assignment _ (by decide +kernel)

private def row288 : List Int := [-70, 55, 54, 53, 52]
include assignment in
private theorem clause288 : Type2.RUP.trueClause a (checkedClause row288) :=
  group14 a assignment _ (by decide +kernel)

private def row289 : List Int := [70, -55, -54, -53, -52]
include assignment in
private theorem clause289 : Type2.RUP.trueClause a (checkedClause row289) :=
  group14 a assignment _ (by decide +kernel)

private def row290 : List Int := [70, 55, -54, 53, -52]
include assignment in
private theorem clause290 : Type2.RUP.trueClause a (checkedClause row290) :=
  group14 a assignment _ (by decide +kernel)

private def row291 : List Int := [-70, -55, 54, -53, 52]
include assignment in
private theorem clause291 : Type2.RUP.trueClause a (checkedClause row291) :=
  group14 a assignment _ (by decide +kernel)

private def row292 : List Int := [-70, -55, -54, 53, -52]
include assignment in
private theorem clause292 : Type2.RUP.trueClause a (checkedClause row292) :=
  group14 a assignment _ (by decide +kernel)

private def row294 : List Int := [-70, 55, 54, 53, -52]
include assignment in
private theorem clause294 : Type2.RUP.trueClause a (checkedClause row294) :=
  group14 a assignment _ (by decide +kernel)

private def row295 : List Int := [70, -55, -54, -53, 52]
include assignment in
private theorem clause295 : Type2.RUP.trueClause a (checkedClause row295) :=
  group14 a assignment _ (by decide +kernel)

private def row297 : List Int := [70, -55, 54, 53, 52]
include assignment in
private theorem clause297 : Type2.RUP.trueClause a (checkedClause row297) :=
  group14 a assignment _ (by decide +kernel)

private def row298 : List Int := [-70, 55, -54, 53, 52]
include assignment in
private theorem clause298 : Type2.RUP.trueClause a (checkedClause row298) :=
  group14 a assignment _ (by decide +kernel)

private def row299 : List Int := [70, -55, 54, -53, -52]
include assignment in
private theorem clause299 : Type2.RUP.trueClause a (checkedClause row299) :=
  group14 a assignment _ (by decide +kernel)

include assignment in
private theorem group15 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [2, 3, 4, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row300 : List Int := [66, -62, 59, -57, 56]
include assignment in
private theorem clause300 : Type2.RUP.trueClause a (checkedClause row300) :=
  group15 a assignment _ (by decide +kernel)

private def row301 : List Int := [-66, 62, -59, 57, -56]
include assignment in
private theorem clause301 : Type2.RUP.trueClause a (checkedClause row301) :=
  group15 a assignment _ (by decide +kernel)

private def row302 : List Int := [66, -62, -59, 57, -56]
include assignment in
private theorem clause302 : Type2.RUP.trueClause a (checkedClause row302) :=
  group15 a assignment _ (by decide +kernel)

private def row303 : List Int := [-66, 62, 59, -57, 56]
include assignment in
private theorem clause303 : Type2.RUP.trueClause a (checkedClause row303) :=
  group15 a assignment _ (by decide +kernel)

private def row304 : List Int := [66, 62, -59, 57, 56]
include assignment in
private theorem clause304 : Type2.RUP.trueClause a (checkedClause row304) :=
  group15 a assignment _ (by decide +kernel)

private def row305 : List Int := [-66, -62, 59, -57, -56]
include assignment in
private theorem clause305 : Type2.RUP.trueClause a (checkedClause row305) :=
  group15 a assignment _ (by decide +kernel)

private def row306 : List Int := [-66, -62, 59, 57, -56]
include assignment in
private theorem clause306 : Type2.RUP.trueClause a (checkedClause row306) :=
  group15 a assignment _ (by decide +kernel)

private def row307 : List Int := [66, 62, -59, -57, 56]
include assignment in
private theorem clause307 : Type2.RUP.trueClause a (checkedClause row307) :=
  group15 a assignment _ (by decide +kernel)

private def row308 : List Int := [-66, 62, 59, -57, -56]
include assignment in
private theorem clause308 : Type2.RUP.trueClause a (checkedClause row308) :=
  group15 a assignment _ (by decide +kernel)

private def row309 : List Int := [66, -62, -59, 57, 56]
include assignment in
private theorem clause309 : Type2.RUP.trueClause a (checkedClause row309) :=
  group15 a assignment _ (by decide +kernel)

private def row310 : List Int := [66, 62, -59, 57, -56]
include assignment in
private theorem clause310 : Type2.RUP.trueClause a (checkedClause row310) :=
  group15 a assignment _ (by decide +kernel)

private def row311 : List Int := [-66, -62, 59, -57, 56]
include assignment in
private theorem clause311 : Type2.RUP.trueClause a (checkedClause row311) :=
  group15 a assignment _ (by decide +kernel)

private def row313 : List Int := [66, 62, 59, -57, 56]
include assignment in
private theorem clause313 : Type2.RUP.trueClause a (checkedClause row313) :=
  group15 a assignment _ (by decide +kernel)

private def row314 : List Int := [-66, 62, 59, 57, -56]
include assignment in
private theorem clause314 : Type2.RUP.trueClause a (checkedClause row314) :=
  group15 a assignment _ (by decide +kernel)

private def row315 : List Int := [66, -62, -59, -57, 56]
include assignment in
private theorem clause315 : Type2.RUP.trueClause a (checkedClause row315) :=
  group15 a assignment _ (by decide +kernel)

private def row316 : List Int := [-66, 62, -59, -57, -56]
include assignment in
private theorem clause316 : Type2.RUP.trueClause a (checkedClause row316) :=
  group15 a assignment _ (by decide +kernel)

private def row317 : List Int := [66, -62, 59, 57, 56]
include assignment in
private theorem clause317 : Type2.RUP.trueClause a (checkedClause row317) :=
  group15 a assignment _ (by decide +kernel)

private def row319 : List Int := [66, -62, 59, -57, -56]
include assignment in
private theorem clause319 : Type2.RUP.trueClause a (checkedClause row319) :=
  group15 a assignment _ (by decide +kernel)

include assignment in
private theorem group16 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [2, 3, 4, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row320 : List Int := [67, -63, 60, -58, 56]
include assignment in
private theorem clause320 : Type2.RUP.trueClause a (checkedClause row320) :=
  group16 a assignment _ (by decide +kernel)

private def row321 : List Int := [-67, 63, -60, 58, -56]
include assignment in
private theorem clause321 : Type2.RUP.trueClause a (checkedClause row321) :=
  group16 a assignment _ (by decide +kernel)

private def row322 : List Int := [67, 63, -60, -58, -56]
include assignment in
private theorem clause322 : Type2.RUP.trueClause a (checkedClause row322) :=
  group16 a assignment _ (by decide +kernel)

private def row323 : List Int := [-67, -63, 60, 58, 56]
include assignment in
private theorem clause323 : Type2.RUP.trueClause a (checkedClause row323) :=
  group16 a assignment _ (by decide +kernel)

private def row324 : List Int := [67, 63, -60, 58, 56]
include assignment in
private theorem clause324 : Type2.RUP.trueClause a (checkedClause row324) :=
  group16 a assignment _ (by decide +kernel)

private def row325 : List Int := [-67, -63, 60, -58, -56]
include assignment in
private theorem clause325 : Type2.RUP.trueClause a (checkedClause row325) :=
  group16 a assignment _ (by decide +kernel)

private def row326 : List Int := [-67, -63, 60, 58, -56]
include assignment in
private theorem clause326 : Type2.RUP.trueClause a (checkedClause row326) :=
  group16 a assignment _ (by decide +kernel)

private def row327 : List Int := [67, 63, -60, -58, 56]
include assignment in
private theorem clause327 : Type2.RUP.trueClause a (checkedClause row327) :=
  group16 a assignment _ (by decide +kernel)

private def row328 : List Int := [-67, -63, -60, -58, -56]
include assignment in
private theorem clause328 : Type2.RUP.trueClause a (checkedClause row328) :=
  group16 a assignment _ (by decide +kernel)

private def row329 : List Int := [67, 63, 60, 58, 56]
include assignment in
private theorem clause329 : Type2.RUP.trueClause a (checkedClause row329) :=
  group16 a assignment _ (by decide +kernel)

private def row330 : List Int := [67, 63, -60, 58, -56]
include assignment in
private theorem clause330 : Type2.RUP.trueClause a (checkedClause row330) :=
  group16 a assignment _ (by decide +kernel)

private def row331 : List Int := [-67, -63, 60, -58, 56]
include assignment in
private theorem clause331 : Type2.RUP.trueClause a (checkedClause row331) :=
  group16 a assignment _ (by decide +kernel)

private def row332 : List Int := [-67, -63, -60, 58, -56]
include assignment in
private theorem clause332 : Type2.RUP.trueClause a (checkedClause row332) :=
  group16 a assignment _ (by decide +kernel)

private def row333 : List Int := [67, 63, 60, -58, 56]
include assignment in
private theorem clause333 : Type2.RUP.trueClause a (checkedClause row333) :=
  group16 a assignment _ (by decide +kernel)

private def row334 : List Int := [-67, 63, 60, 58, -56]
include assignment in
private theorem clause334 : Type2.RUP.trueClause a (checkedClause row334) :=
  group16 a assignment _ (by decide +kernel)

private def row335 : List Int := [67, -63, -60, -58, 56]
include assignment in
private theorem clause335 : Type2.RUP.trueClause a (checkedClause row335) :=
  group16 a assignment _ (by decide +kernel)

private def row336 : List Int := [-67, 63, -60, -58, -56]
include assignment in
private theorem clause336 : Type2.RUP.trueClause a (checkedClause row336) :=
  group16 a assignment _ (by decide +kernel)

private def row337 : List Int := [67, -63, 60, 58, 56]
include assignment in
private theorem clause337 : Type2.RUP.trueClause a (checkedClause row337) :=
  group16 a assignment _ (by decide +kernel)

private def row338 : List Int := [-67, 63, -60, 58, 56]
include assignment in
private theorem clause338 : Type2.RUP.trueClause a (checkedClause row338) :=
  group16 a assignment _ (by decide +kernel)

include assignment in
private theorem group17 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [2, 3, 4, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row340 : List Int := [68, -64, 61, -58, 57]
include assignment in
private theorem clause340 : Type2.RUP.trueClause a (checkedClause row340) :=
  group17 a assignment _ (by decide +kernel)

private def row342 : List Int := [68, 64, 61, 58, -57]
include assignment in
private theorem clause342 : Type2.RUP.trueClause a (checkedClause row342) :=
  group17 a assignment _ (by decide +kernel)

private def row343 : List Int := [-68, -64, -61, -58, 57]
include assignment in
private theorem clause343 : Type2.RUP.trueClause a (checkedClause row343) :=
  group17 a assignment _ (by decide +kernel)

private def row345 : List Int := [-68, -64, 61, 58, 57]
include assignment in
private theorem clause345 : Type2.RUP.trueClause a (checkedClause row345) :=
  group17 a assignment _ (by decide +kernel)

private def row346 : List Int := [-68, -64, -61, -58, -57]
include assignment in
private theorem clause346 : Type2.RUP.trueClause a (checkedClause row346) :=
  group17 a assignment _ (by decide +kernel)

private def row347 : List Int := [68, 64, 61, 58, 57]
include assignment in
private theorem clause347 : Type2.RUP.trueClause a (checkedClause row347) :=
  group17 a assignment _ (by decide +kernel)

private def row348 : List Int := [-68, 64, 61, 58, 57]
include assignment in
private theorem clause348 : Type2.RUP.trueClause a (checkedClause row348) :=
  group17 a assignment _ (by decide +kernel)

private def row349 : List Int := [68, -64, -61, -58, -57]
include assignment in
private theorem clause349 : Type2.RUP.trueClause a (checkedClause row349) :=
  group17 a assignment _ (by decide +kernel)

private def row350 : List Int := [68, 64, -61, 58, -57]
include assignment in
private theorem clause350 : Type2.RUP.trueClause a (checkedClause row350) :=
  group17 a assignment _ (by decide +kernel)

private def row351 : List Int := [-68, -64, 61, -58, 57]
include assignment in
private theorem clause351 : Type2.RUP.trueClause a (checkedClause row351) :=
  group17 a assignment _ (by decide +kernel)

private def row353 : List Int := [68, 64, 61, -58, 57]
include assignment in
private theorem clause353 : Type2.RUP.trueClause a (checkedClause row353) :=
  group17 a assignment _ (by decide +kernel)

private def row354 : List Int := [-68, 64, 61, 58, -57]
include assignment in
private theorem clause354 : Type2.RUP.trueClause a (checkedClause row354) :=
  group17 a assignment _ (by decide +kernel)

private def row355 : List Int := [68, -64, -61, -58, 57]
include assignment in
private theorem clause355 : Type2.RUP.trueClause a (checkedClause row355) :=
  group17 a assignment _ (by decide +kernel)

private def row356 : List Int := [-68, 64, -61, -58, -57]
include assignment in
private theorem clause356 : Type2.RUP.trueClause a (checkedClause row356) :=
  group17 a assignment _ (by decide +kernel)

private def row357 : List Int := [68, -64, 61, 58, 57]
include assignment in
private theorem clause357 : Type2.RUP.trueClause a (checkedClause row357) :=
  group17 a assignment _ (by decide +kernel)

private def row358 : List Int := [-68, 64, -61, 58, 57]
include assignment in
private theorem clause358 : Type2.RUP.trueClause a (checkedClause row358) :=
  group17 a assignment _ (by decide +kernel)

private def row359 : List Int := [68, -64, 61, -58, -57]
include assignment in
private theorem clause359 : Type2.RUP.trueClause a (checkedClause row359) :=
  group17 a assignment _ (by decide +kernel)

include assignment in
private theorem group18 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [2, 3, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row361 : List Int := [-69, 65, -61, 60, -59]
include assignment in
private theorem clause361 : Type2.RUP.trueClause a (checkedClause row361) :=
  group18 a assignment _ (by decide +kernel)

private def row362 : List Int := [69, 65, 61, 60, -59]
include assignment in
private theorem clause362 : Type2.RUP.trueClause a (checkedClause row362) :=
  group18 a assignment _ (by decide +kernel)

private def row363 : List Int := [-69, -65, -61, -60, 59]
include assignment in
private theorem clause363 : Type2.RUP.trueClause a (checkedClause row363) :=
  group18 a assignment _ (by decide +kernel)

private def row364 : List Int := [-69, -65, -61, -60, -59]
include assignment in
private theorem clause364 : Type2.RUP.trueClause a (checkedClause row364) :=
  group18 a assignment _ (by decide +kernel)

private def row365 : List Int := [69, 65, 61, 60, 59]
include assignment in
private theorem clause365 : Type2.RUP.trueClause a (checkedClause row365) :=
  group18 a assignment _ (by decide +kernel)

private def row366 : List Int := [-69, -65, -61, 60, 59]
include assignment in
private theorem clause366 : Type2.RUP.trueClause a (checkedClause row366) :=
  group18 a assignment _ (by decide +kernel)

private def row367 : List Int := [69, 65, 61, -60, -59]
include assignment in
private theorem clause367 : Type2.RUP.trueClause a (checkedClause row367) :=
  group18 a assignment _ (by decide +kernel)

private def row368 : List Int := [-69, 65, 61, 60, 59]
include assignment in
private theorem clause368 : Type2.RUP.trueClause a (checkedClause row368) :=
  group18 a assignment _ (by decide +kernel)

private def row369 : List Int := [69, -65, -61, -60, -59]
include assignment in
private theorem clause369 : Type2.RUP.trueClause a (checkedClause row369) :=
  group18 a assignment _ (by decide +kernel)

private def row371 : List Int := [-69, -65, 61, -60, 59]
include assignment in
private theorem clause371 : Type2.RUP.trueClause a (checkedClause row371) :=
  group18 a assignment _ (by decide +kernel)

private def row372 : List Int := [-69, -65, -61, 60, -59]
include assignment in
private theorem clause372 : Type2.RUP.trueClause a (checkedClause row372) :=
  group18 a assignment _ (by decide +kernel)

private def row373 : List Int := [69, 65, 61, -60, 59]
include assignment in
private theorem clause373 : Type2.RUP.trueClause a (checkedClause row373) :=
  group18 a assignment _ (by decide +kernel)

private def row376 : List Int := [-69, 65, -61, -60, -59]
include assignment in
private theorem clause376 : Type2.RUP.trueClause a (checkedClause row376) :=
  group18 a assignment _ (by decide +kernel)

private def row377 : List Int := [69, -65, 61, 60, 59]
include assignment in
private theorem clause377 : Type2.RUP.trueClause a (checkedClause row377) :=
  group18 a assignment _ (by decide +kernel)

private def row378 : List Int := [-69, 65, -61, 60, 59]
include assignment in
private theorem clause378 : Type2.RUP.trueClause a (checkedClause row378) :=
  group18 a assignment _ (by decide +kernel)

private def row379 : List Int := [69, -65, 61, -60, -59]
include assignment in
private theorem clause379 : Type2.RUP.trueClause a (checkedClause row379) :=
  group18 a assignment _ (by decide +kernel)

include assignment in
private theorem group19 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [2, 4, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row381 : List Int := [-70, 65, -64, 63, -62]
include assignment in
private theorem clause381 : Type2.RUP.trueClause a (checkedClause row381) :=
  group19 a assignment _ (by decide +kernel)

private def row382 : List Int := [70, 65, -64, 63, 62]
include assignment in
private theorem clause382 : Type2.RUP.trueClause a (checkedClause row382) :=
  group19 a assignment _ (by decide +kernel)

private def row383 : List Int := [-70, -65, 64, -63, -62]
include assignment in
private theorem clause383 : Type2.RUP.trueClause a (checkedClause row383) :=
  group19 a assignment _ (by decide +kernel)

private def row384 : List Int := [-70, -65, -64, -63, -62]
include assignment in
private theorem clause384 : Type2.RUP.trueClause a (checkedClause row384) :=
  group19 a assignment _ (by decide +kernel)

private def row385 : List Int := [70, 65, 64, 63, 62]
include assignment in
private theorem clause385 : Type2.RUP.trueClause a (checkedClause row385) :=
  group19 a assignment _ (by decide +kernel)

private def row386 : List Int := [-70, -65, -64, 63, 62]
include assignment in
private theorem clause386 : Type2.RUP.trueClause a (checkedClause row386) :=
  group19 a assignment _ (by decide +kernel)

private def row387 : List Int := [70, 65, 64, -63, -62]
include assignment in
private theorem clause387 : Type2.RUP.trueClause a (checkedClause row387) :=
  group19 a assignment _ (by decide +kernel)

private def row388 : List Int := [-70, 65, 64, -63, -62]
include assignment in
private theorem clause388 : Type2.RUP.trueClause a (checkedClause row388) :=
  group19 a assignment _ (by decide +kernel)

private def row389 : List Int := [70, -65, -64, 63, 62]
include assignment in
private theorem clause389 : Type2.RUP.trueClause a (checkedClause row389) :=
  group19 a assignment _ (by decide +kernel)

private def row391 : List Int := [-70, -65, 64, -63, 62]
include assignment in
private theorem clause391 : Type2.RUP.trueClause a (checkedClause row391) :=
  group19 a assignment _ (by decide +kernel)

private def row392 : List Int := [-70, -65, -64, 63, -62]
include assignment in
private theorem clause392 : Type2.RUP.trueClause a (checkedClause row392) :=
  group19 a assignment _ (by decide +kernel)

private def row393 : List Int := [70, 65, 64, -63, 62]
include assignment in
private theorem clause393 : Type2.RUP.trueClause a (checkedClause row393) :=
  group19 a assignment _ (by decide +kernel)

private def row394 : List Int := [-70, 65, 64, 63, -62]
include assignment in
private theorem clause394 : Type2.RUP.trueClause a (checkedClause row394) :=
  group19 a assignment _ (by decide +kernel)

private def row396 : List Int := [-70, 65, -64, -63, -62]
include assignment in
private theorem clause396 : Type2.RUP.trueClause a (checkedClause row396) :=
  group19 a assignment _ (by decide +kernel)

private def row397 : List Int := [70, -65, 64, 63, 62]
include assignment in
private theorem clause397 : Type2.RUP.trueClause a (checkedClause row397) :=
  group19 a assignment _ (by decide +kernel)

private def row398 : List Int := [-70, 65, -64, 63, 62]
include assignment in
private theorem clause398 : Type2.RUP.trueClause a (checkedClause row398) :=
  group19 a assignment _ (by decide +kernel)

private def row399 : List Int := [70, -65, 64, -63, -62]
include assignment in
private theorem clause399 : Type2.RUP.trueClause a (checkedClause row399) :=
  group19 a assignment _ (by decide +kernel)

include assignment in
private theorem group20 (c : SignClause) (hc : c ∈ circuitFor collapsedLabels collapsedEdge [3, 4, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (circuit_mem (by decide +kernel) hc)

private def row400 : List Int := [70, -69, 68, -67, 66]
include assignment in
private theorem clause400 : Type2.RUP.trueClause a (checkedClause row400) :=
  group20 a assignment _ (by decide +kernel)

private def row401 : List Int := [-70, 69, -68, 67, -66]
include assignment in
private theorem clause401 : Type2.RUP.trueClause a (checkedClause row401) :=
  group20 a assignment _ (by decide +kernel)

private def row402 : List Int := [70, 69, -68, 67, 66]
include assignment in
private theorem clause402 : Type2.RUP.trueClause a (checkedClause row402) :=
  group20 a assignment _ (by decide +kernel)

private def row403 : List Int := [-70, -69, 68, -67, -66]
include assignment in
private theorem clause403 : Type2.RUP.trueClause a (checkedClause row403) :=
  group20 a assignment _ (by decide +kernel)

private def row404 : List Int := [-70, -69, 68, 67, -66]
include assignment in
private theorem clause404 : Type2.RUP.trueClause a (checkedClause row404) :=
  group20 a assignment _ (by decide +kernel)

private def row405 : List Int := [70, 69, -68, -67, 66]
include assignment in
private theorem clause405 : Type2.RUP.trueClause a (checkedClause row405) :=
  group20 a assignment _ (by decide +kernel)

private def row406 : List Int := [-70, 69, 68, -67, -66]
include assignment in
private theorem clause406 : Type2.RUP.trueClause a (checkedClause row406) :=
  group20 a assignment _ (by decide +kernel)

private def row407 : List Int := [70, -69, -68, 67, 66]
include assignment in
private theorem clause407 : Type2.RUP.trueClause a (checkedClause row407) :=
  group20 a assignment _ (by decide +kernel)

private def row408 : List Int := [-70, 69, -68, -67, 66]
include assignment in
private theorem clause408 : Type2.RUP.trueClause a (checkedClause row408) :=
  group20 a assignment _ (by decide +kernel)

private def row409 : List Int := [70, -69, 68, 67, -66]
include assignment in
private theorem clause409 : Type2.RUP.trueClause a (checkedClause row409) :=
  group20 a assignment _ (by decide +kernel)

private def row410 : List Int := [70, 69, -68, 67, -66]
include assignment in
private theorem clause410 : Type2.RUP.trueClause a (checkedClause row410) :=
  group20 a assignment _ (by decide +kernel)

private def row411 : List Int := [-70, -69, 68, -67, 66]
include assignment in
private theorem clause411 : Type2.RUP.trueClause a (checkedClause row411) :=
  group20 a assignment _ (by decide +kernel)

private def row412 : List Int := [-70, -69, -68, 67, -66]
include assignment in
private theorem clause412 : Type2.RUP.trueClause a (checkedClause row412) :=
  group20 a assignment _ (by decide +kernel)

private def row413 : List Int := [70, 69, 68, -67, 66]
include assignment in
private theorem clause413 : Type2.RUP.trueClause a (checkedClause row413) :=
  group20 a assignment _ (by decide +kernel)

private def row414 : List Int := [-70, 69, 68, 67, -66]
include assignment in
private theorem clause414 : Type2.RUP.trueClause a (checkedClause row414) :=
  group20 a assignment _ (by decide +kernel)

private def row415 : List Int := [70, -69, -68, -67, 66]
include assignment in
private theorem clause415 : Type2.RUP.trueClause a (checkedClause row415) :=
  group20 a assignment _ (by decide +kernel)

private def row416 : List Int := [-70, 69, -68, -67, -66]
include assignment in
private theorem clause416 : Type2.RUP.trueClause a (checkedClause row416) :=
  group20 a assignment _ (by decide +kernel)

private def row417 : List Int := [70, -69, 68, 67, 66]
include assignment in
private theorem clause417 : Type2.RUP.trueClause a (checkedClause row417) :=
  group20 a assignment _ (by decide +kernel)

private def row418 : List Int := [-70, 69, -68, 67, 66]
include assignment in
private theorem clause418 : Type2.RUP.trueClause a (checkedClause row418) :=
  group20 a assignment _ (by decide +kernel)

private def row419 : List Int := [70, -69, 68, -67, -66]
include assignment in
private theorem clause419 : Type2.RUP.trueClause a (checkedClause row419) :=
  group20 a assignment _ (by decide +kernel)

include assignment in
private theorem group21 (c : SignClause) (hc : c ∈ pluckerAt [1, 2] [3, 4, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row427 : List Int := [36, -43, 37, 41, -38, 40]
include assignment in
private theorem clause427 : Type2.RUP.trueClause a (checkedClause row427) :=
  group21 a assignment _ (by decide +kernel)

private def row434 : List Int := [-36, -43, 37, -41, 38, 40]
include assignment in
private theorem clause434 : Type2.RUP.trueClause a (checkedClause row434) :=
  group21 a assignment _ (by decide +kernel)

include assignment in
private theorem group23 (c : SignClause) (hc : c ∈ pluckerAt [1, 2] [3, 4, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row456 : List Int := [36, -45, -38, -42, 39, -41]
include assignment in
private theorem clause456 : Type2.RUP.trueClause a (checkedClause row456) :=
  group23 a assignment _ (by decide +kernel)

private def row467 : List Int := [-36, -45, 38, -42, -39, -41]
include assignment in
private theorem clause467 : Type2.RUP.trueClause a (checkedClause row467) :=
  group23 a assignment _ (by decide +kernel)

include assignment in
private theorem group24 (c : SignClause) (hc : c ∈ pluckerAt [1, 2] [3, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row468 : List Int := [37, 45, -38, 44, 39, 43]
include assignment in
private theorem clause468 : Type2.RUP.trueClause a (checkedClause row468) :=
  group24 a assignment _ (by decide +kernel)

private def row474 : List Int := [37, -45, 38, 44, 39, -43]
include assignment in
private theorem clause474 : Type2.RUP.trueClause a (checkedClause row474) :=
  group24 a assignment _ (by decide +kernel)

include assignment in
private theorem group26 (c : SignClause) (hc : c ∈ pluckerAt [1, 3] [2, 4, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row500 : List Int := [-36, 49, 37, 47, -38, 46]
include assignment in
private theorem clause500 : Type2.RUP.trueClause a (checkedClause row500) :=
  group26 a assignment _ (by decide +kernel)

private def row508 : List Int := [36, 49, 37, -47, -38, -46]
include assignment in
private theorem clause508 : Type2.RUP.trueClause a (checkedClause row508) :=
  group26 a assignment _ (by decide +kernel)

private def row514 : List Int := [36, -49, -37, -47, -38, 46]
include assignment in
private theorem clause514 : Type2.RUP.trueClause a (checkedClause row514) :=
  group26 a assignment _ (by decide +kernel)

include assignment in
private theorem group27 (c : SignClause) (hc : c ∈ pluckerAt [1, 3] [2, 4, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row517 : List Int := [-36, 50, 37, 48, 39, -46]
include assignment in
private theorem clause517 : Type2.RUP.trueClause a (checkedClause row517) :=
  group27 a assignment _ (by decide +kernel)

private def row521 : List Int := [-36, -50, 37, -48, 39, 46]
include assignment in
private theorem clause521 : Type2.RUP.trueClause a (checkedClause row521) :=
  group27 a assignment _ (by decide +kernel)

private def row522 : List Int := [-36, -50, -37, 48, -39, -46]
include assignment in
private theorem clause522 : Type2.RUP.trueClause a (checkedClause row522) :=
  group27 a assignment _ (by decide +kernel)

private def row525 : List Int := [36, 50, 37, -48, 39, 46]
include assignment in
private theorem clause525 : Type2.RUP.trueClause a (checkedClause row525) :=
  group27 a assignment _ (by decide +kernel)

private def row526 : List Int := [36, 50, -37, 48, -39, -46]
include assignment in
private theorem clause526 : Type2.RUP.trueClause a (checkedClause row526) :=
  group27 a assignment _ (by decide +kernel)

private def row529 : List Int := [36, -50, 37, 48, 39, -46]
include assignment in
private theorem clause529 : Type2.RUP.trueClause a (checkedClause row529) :=
  group27 a assignment _ (by decide +kernel)

include assignment in
private theorem group28 (c : SignClause) (hc : c ∈ pluckerAt [1, 3] [2, 4, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row535 : List Int := [-36, 51, -38, -48, 39, -47]
include assignment in
private theorem clause535 : Type2.RUP.trueClause a (checkedClause row535) :=
  group28 a assignment _ (by decide +kernel)

include assignment in
private theorem group29 (c : SignClause) (hc : c ∈ pluckerAt [1, 3] [2, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row551 : List Int := [-37, 51, -38, -50, 39, -49]
include assignment in
private theorem clause551 : Type2.RUP.trueClause a (checkedClause row551) :=
  group29 a assignment _ (by decide +kernel)

include assignment in
private theorem group30 (c : SignClause) (hc : c ∈ pluckerAt [1, 3] [4, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row566 : List Int := [46, 51, 47, -50, 48, 49]
include assignment in
private theorem clause566 : Type2.RUP.trueClause a (checkedClause row566) :=
  group30 a assignment _ (by decide +kernel)

private def row567 : List Int := [46, 51, 47, -50, -48, -49]
include assignment in
private theorem clause567 : Type2.RUP.trueClause a (checkedClause row567) :=
  group30 a assignment _ (by decide +kernel)

private def row571 : List Int := [46, -51, 47, 50, -48, 49]
include assignment in
private theorem clause571 : Type2.RUP.trueClause a (checkedClause row571) :=
  group30 a assignment _ (by decide +kernel)

private def row572 : List Int := [-46, 51, -47, -50, 48, -49]
include assignment in
private theorem clause572 : Type2.RUP.trueClause a (checkedClause row572) :=
  group30 a assignment _ (by decide +kernel)

private def row577 : List Int := [-46, -51, -47, 50, -48, -49]
include assignment in
private theorem clause577 : Type2.RUP.trueClause a (checkedClause row577) :=
  group30 a assignment _ (by decide +kernel)

include assignment in
private theorem group31 (c : SignClause) (hc : c ∈ pluckerAt [1, 4] [2, 3, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row580 : List Int := [36, 52, 40, -47, -41, -46]
include assignment in
private theorem clause580 : Type2.RUP.trueClause a (checkedClause row580) :=
  group31 a assignment _ (by decide +kernel)

private def row585 : List Int := [36, -52, 40, 47, 41, -46]
include assignment in
private theorem clause585 : Type2.RUP.trueClause a (checkedClause row585) :=
  group31 a assignment _ (by decide +kernel)

private def row586 : List Int := [36, -52, -40, -47, -41, 46]
include assignment in
private theorem clause586 : Type2.RUP.trueClause a (checkedClause row586) :=
  group31 a assignment _ (by decide +kernel)

private def row589 : List Int := [-36, 52, 40, 47, 41, -46]
include assignment in
private theorem clause589 : Type2.RUP.trueClause a (checkedClause row589) :=
  group31 a assignment _ (by decide +kernel)

private def row594 : List Int := [-36, -52, -40, 47, -41, -46]
include assignment in
private theorem clause594 : Type2.RUP.trueClause a (checkedClause row594) :=
  group31 a assignment _ (by decide +kernel)

include assignment in
private theorem group32 (c : SignClause) (hc : c ∈ pluckerAt [1, 4] [2, 3, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row598 : List Int := [36, 53, -40, 48, -42, -46]
include assignment in
private theorem clause598 : Type2.RUP.trueClause a (checkedClause row598) :=
  group32 a assignment _ (by decide +kernel)

private def row601 : List Int := [36, -53, 40, 48, 42, -46]
include assignment in
private theorem clause601 : Type2.RUP.trueClause a (checkedClause row601) :=
  group32 a assignment _ (by decide +kernel)

private def row611 : List Int := [-36, -53, -40, 48, 42, 46]
include assignment in
private theorem clause611 : Type2.RUP.trueClause a (checkedClause row611) :=
  group32 a assignment _ (by decide +kernel)

include assignment in
private theorem group34 (c : SignClause) (hc : c ∈ pluckerAt [1, 4] [2, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row639 : List Int := [40, 54, -41, 53, 42, 52]
include assignment in
private theorem clause639 : Type2.RUP.trueClause a (checkedClause row639) :=
  group34 a assignment _ (by decide +kernel)

include assignment in
private theorem group35 (c : SignClause) (hc : c ∈ pluckerAt [1, 4] [3, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row650 : List Int := [-46, -54, -47, 53, -48, -52]
include assignment in
private theorem clause650 : Type2.RUP.trueClause a (checkedClause row650) :=
  group35 a assignment _ (by decide +kernel)

private def row651 : List Int := [-46, -54, -47, 53, 48, 52]
include assignment in
private theorem clause651 : Type2.RUP.trueClause a (checkedClause row651) :=
  group35 a assignment _ (by decide +kernel)

private def row652 : List Int := [46, 54, 47, -53, -48, -52]
include assignment in
private theorem clause652 : Type2.RUP.trueClause a (checkedClause row652) :=
  group35 a assignment _ (by decide +kernel)

include assignment in
private theorem group36 (c : SignClause) (hc : c ∈ pluckerAt [1, 5] [2, 3, 4, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row660 : List Int := [37, -52, -40, -49, -43, 46]
include assignment in
private theorem clause660 : Type2.RUP.trueClause a (checkedClause row660) :=
  group36 a assignment _ (by decide +kernel)

private def row662 : List Int := [37, -52, 40, 49, -43, 46]
include assignment in
private theorem clause662 : Type2.RUP.trueClause a (checkedClause row662) :=
  group36 a assignment _ (by decide +kernel)

private def row664 : List Int := [37, 52, -40, 49, -43, -46]
include assignment in
private theorem clause664 : Type2.RUP.trueClause a (checkedClause row664) :=
  group36 a assignment _ (by decide +kernel)

private def row671 : List Int := [-37, -52, 40, -49, 43, 46]
include assignment in
private theorem clause671 : Type2.RUP.trueClause a (checkedClause row671) :=
  group36 a assignment _ (by decide +kernel)

private def row673 : List Int := [-37, 52, -40, -49, 43, -46]
include assignment in
private theorem clause673 : Type2.RUP.trueClause a (checkedClause row673) :=
  group36 a assignment _ (by decide +kernel)

include assignment in
private theorem group37 (c : SignClause) (hc : c ∈ pluckerAt [1, 5] [2, 3, 4, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row677 : List Int := [37, -53, -40, -50, 44, -46]
include assignment in
private theorem clause677 : Type2.RUP.trueClause a (checkedClause row677) :=
  group37 a assignment _ (by decide +kernel)

private def row679 : List Int := [37, -53, 40, 50, 44, -46]
include assignment in
private theorem clause679 : Type2.RUP.trueClause a (checkedClause row679) :=
  group37 a assignment _ (by decide +kernel)

private def row684 : List Int := [-37, -53, -40, 50, -44, -46]
include assignment in
private theorem clause684 : Type2.RUP.trueClause a (checkedClause row684) :=
  group37 a assignment _ (by decide +kernel)

private def row688 : List Int := [-37, 53, -40, -50, -44, 46]
include assignment in
private theorem clause688 : Type2.RUP.trueClause a (checkedClause row688) :=
  group37 a assignment _ (by decide +kernel)

private def row690 : List Int := [-37, 53, 40, 50, -44, 46]
include assignment in
private theorem clause690 : Type2.RUP.trueClause a (checkedClause row690) :=
  group37 a assignment _ (by decide +kernel)

include assignment in
private theorem group38 (c : SignClause) (hc : c ∈ pluckerAt [1, 5] [2, 3, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row703 : List Int := [-37, 55, -43, -50, 44, -49]
include assignment in
private theorem clause703 : Type2.RUP.trueClause a (checkedClause row703) :=
  group38 a assignment _ (by decide +kernel)

private def row706 : List Int := [-37, -55, -43, 50, -44, -49]
include assignment in
private theorem clause706 : Type2.RUP.trueClause a (checkedClause row706) :=
  group38 a assignment _ (by decide +kernel)

include assignment in
private theorem group39 (c : SignClause) (hc : c ∈ pluckerAt [1, 5] [2, 4, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row713 : List Int := [40, -55, 43, 53, 44, -52]
include assignment in
private theorem clause713 : Type2.RUP.trueClause a (checkedClause row713) :=
  group39 a assignment _ (by decide +kernel)

private def row714 : List Int := [40, -55, -43, -53, -44, 52]
include assignment in
private theorem clause714 : Type2.RUP.trueClause a (checkedClause row714) :=
  group39 a assignment _ (by decide +kernel)

include assignment in
private theorem group40 (c : SignClause) (hc : c ∈ pluckerAt [1, 5] [3, 4, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row729 : List Int := [46, -55, 49, 53, 50, -52]
include assignment in
private theorem clause729 : Type2.RUP.trueClause a (checkedClause row729) :=
  group40 a assignment _ (by decide +kernel)

private def row734 : List Int := [-46, 55, -49, -53, -50, 52]
include assignment in
private theorem clause734 : Type2.RUP.trueClause a (checkedClause row734) :=
  group40 a assignment _ (by decide +kernel)

include assignment in
private theorem group41 (c : SignClause) (hc : c ∈ pluckerAt [1, 6] [2, 3, 4, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row751 : List Int := [-38, 52, 41, 49, -43, 47]
include assignment in
private theorem clause751 : Type2.RUP.trueClause a (checkedClause row751) :=
  group41 a assignment _ (by decide +kernel)

include assignment in
private theorem group42 (c : SignClause) (hc : c ∈ pluckerAt [1, 6] [2, 3, 4, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row757 : List Int := [38, -54, -41, -51, 45, -47]
include assignment in
private theorem clause757 : Type2.RUP.trueClause a (checkedClause row757) :=
  group42 a assignment _ (by decide +kernel)

private def row760 : List Int := [38, 54, -41, 51, -45, -47]
include assignment in
private theorem clause760 : Type2.RUP.trueClause a (checkedClause row760) :=
  group42 a assignment _ (by decide +kernel)

include assignment in
private theorem group43 (c : SignClause) (hc : c ∈ pluckerAt [1, 6] [2, 3, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row777 : List Int := [38, 55, -43, 51, 45, 49]
include assignment in
private theorem clause777 : Type2.RUP.trueClause a (checkedClause row777) :=
  group43 a assignment _ (by decide +kernel)

private def row787 : List Int := [-38, 55, 43, 51, 45, -49]
include assignment in
private theorem clause787 : Type2.RUP.trueClause a (checkedClause row787) :=
  group43 a assignment _ (by decide +kernel)

include assignment in
private theorem group45 (c : SignClause) (hc : c ∈ pluckerAt [1, 6] [3, 4, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row806 : List Int := [47, -55, 49, 54, -51, 52]
include assignment in
private theorem clause806 : Type2.RUP.trueClause a (checkedClause row806) :=
  group45 a assignment _ (by decide +kernel)

private def row807 : List Int := [47, -55, 49, 54, 51, -52]
include assignment in
private theorem clause807 : Type2.RUP.trueClause a (checkedClause row807) :=
  group45 a assignment _ (by decide +kernel)

include assignment in
private theorem group46 (c : SignClause) (hc : c ∈ pluckerAt [1, 7] [2, 3, 4, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row828 : List Int := [-39, 53, -42, -50, 44, -48]
include assignment in
private theorem clause828 : Type2.RUP.trueClause a (checkedClause row828) :=
  group46 a assignment _ (by decide +kernel)

private def row835 : List Int := [-39, -53, 42, -50, -44, -48]
include assignment in
private theorem clause835 : Type2.RUP.trueClause a (checkedClause row835) :=
  group46 a assignment _ (by decide +kernel)

include assignment in
private theorem group50 (c : SignClause) (hc : c ∈ pluckerAt [1, 7] [3, 4, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row894 : List Int := [-48, 55, 50, 54, 51, -53]
include assignment in
private theorem clause894 : Type2.RUP.trueClause a (checkedClause row894) :=
  group50 a assignment _ (by decide +kernel)

private def row898 : List Int := [-48, -55, 50, -54, 51, 53]
include assignment in
private theorem clause898 : Type2.RUP.trueClause a (checkedClause row898) :=
  group50 a assignment _ (by decide +kernel)

include assignment in
private theorem group51 (c : SignClause) (hc : c ∈ pluckerAt [2, 3] [1, 4, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row910 : List Int := [-36, 59, 37, 57, 38, -56]
include assignment in
private theorem clause910 : Type2.RUP.trueClause a (checkedClause row910) :=
  group51 a assignment _ (by decide +kernel)

include assignment in
private theorem group52 (c : SignClause) (hc : c ∈ pluckerAt [2, 3] [1, 4, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row924 : List Int := [-36, 60, -37, -58, 39, -56]
include assignment in
private theorem clause924 : Type2.RUP.trueClause a (checkedClause row924) :=
  group52 a assignment _ (by decide +kernel)

private def row925 : List Int := [-36, 60, -37, -58, -39, 56]
include assignment in
private theorem clause925 : Type2.RUP.trueClause a (checkedClause row925) :=
  group52 a assignment _ (by decide +kernel)

include assignment in
private theorem group53 (c : SignClause) (hc : c ∈ pluckerAt [2, 3] [1, 4, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row933 : List Int := [36, 61, -38, 58, -39, -57]
include assignment in
private theorem clause933 : Type2.RUP.trueClause a (checkedClause row933) :=
  group53 a assignment _ (by decide +kernel)

private def row946 : List Int := [-36, -61, 38, -58, 39, 57]
include assignment in
private theorem clause946 : Type2.RUP.trueClause a (checkedClause row946) :=
  group53 a assignment _ (by decide +kernel)

include assignment in
private theorem group54 (c : SignClause) (hc : c ∈ pluckerAt [2, 3] [1, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row958 : List Int := [-37, 61, 38, 60, 39, -59]
include assignment in
private theorem clause958 : Type2.RUP.trueClause a (checkedClause row958) :=
  group54 a assignment _ (by decide +kernel)

private def row961 : List Int := [-37, -61, -38, 60, -39, -59]
include assignment in
private theorem clause961 : Type2.RUP.trueClause a (checkedClause row961) :=
  group54 a assignment _ (by decide +kernel)

include assignment in
private theorem group55 (c : SignClause) (hc : c ∈ pluckerAt [2, 3] [4, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row965 : List Int := [56, 61, -57, 60, -58, -59]
include assignment in
private theorem clause965 : Type2.RUP.trueClause a (checkedClause row965) :=
  group55 a assignment _ (by decide +kernel)

private def row966 : List Int := [56, 61, 57, -60, 58, 59]
include assignment in
private theorem clause966 : Type2.RUP.trueClause a (checkedClause row966) :=
  group55 a assignment _ (by decide +kernel)

private def row971 : List Int := [56, -61, 57, 60, -58, 59]
include assignment in
private theorem clause971 : Type2.RUP.trueClause a (checkedClause row971) :=
  group55 a assignment _ (by decide +kernel)

private def row972 : List Int := [-56, 61, -57, -60, 58, -59]
include assignment in
private theorem clause972 : Type2.RUP.trueClause a (checkedClause row972) :=
  group55 a assignment _ (by decide +kernel)

private def row978 : List Int := [-56, -61, 57, -60, 58, 59]
include assignment in
private theorem clause978 : Type2.RUP.trueClause a (checkedClause row978) :=
  group55 a assignment _ (by decide +kernel)

include assignment in
private theorem group56 (c : SignClause) (hc : c ∈ pluckerAt [2, 4] [1, 3, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row982 : List Int := [-36, 62, 40, 57, 41, -56]
include assignment in
private theorem clause982 : Type2.RUP.trueClause a (checkedClause row982) :=
  group56 a assignment _ (by decide +kernel)

include assignment in
private theorem group57 (c : SignClause) (hc : c ∈ pluckerAt [2, 4] [1, 3, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row996 : List Int := [-36, 63, -40, -58, 42, -56]
include assignment in
private theorem clause996 : Type2.RUP.trueClause a (checkedClause row996) :=
  group57 a assignment _ (by decide +kernel)

private def row998 : List Int := [-36, 63, 40, 58, 42, -56]
include assignment in
private theorem clause998 : Type2.RUP.trueClause a (checkedClause row998) :=
  group57 a assignment _ (by decide +kernel)

private def row1000 : List Int := [-36, -63, -40, 58, 42, 56]
include assignment in
private theorem clause1000 : Type2.RUP.trueClause a (checkedClause row1000) :=
  group57 a assignment _ (by decide +kernel)

private def row1006 : List Int := [36, 63, 40, -58, 42, 56]
include assignment in
private theorem clause1006 : Type2.RUP.trueClause a (checkedClause row1006) :=
  group57 a assignment _ (by decide +kernel)

include assignment in
private theorem group58 (c : SignClause) (hc : c ∈ pluckerAt [2, 4] [1, 3, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1013 : List Int := [-36, 64, -41, -58, -42, 57]
include assignment in
private theorem clause1013 : Type2.RUP.trueClause a (checkedClause row1013) :=
  group58 a assignment _ (by decide +kernel)

include assignment in
private theorem group60 (c : SignClause) (hc : c ∈ pluckerAt [2, 4] [3, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1044 : List Int := [-56, 64, 57, 63, -58, 62]
include assignment in
private theorem clause1044 : Type2.RUP.trueClause a (checkedClause row1044) :=
  group60 a assignment _ (by decide +kernel)

private def row1045 : List Int := [-56, 64, 57, 63, 58, -62]
include assignment in
private theorem clause1045 : Type2.RUP.trueClause a (checkedClause row1045) :=
  group60 a assignment _ (by decide +kernel)

private def row1049 : List Int := [-56, -64, 57, -63, 58, 62]
include assignment in
private theorem clause1049 : Type2.RUP.trueClause a (checkedClause row1049) :=
  group60 a assignment _ (by decide +kernel)

private def row1054 : List Int := [56, 64, -57, 63, -58, -62]
include assignment in
private theorem clause1054 : Type2.RUP.trueClause a (checkedClause row1054) :=
  group60 a assignment _ (by decide +kernel)

private def row1059 : List Int := [56, -64, -57, -63, 58, -62]
include assignment in
private theorem clause1059 : Type2.RUP.trueClause a (checkedClause row1059) :=
  group60 a assignment _ (by decide +kernel)

include assignment in
private theorem group61 (c : SignClause) (hc : c ∈ pluckerAt [2, 5] [1, 3, 4, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1061 : List Int := [-37, -62, 40, -59, -43, -56]
include assignment in
private theorem clause1061 : Type2.RUP.trueClause a (checkedClause row1061) :=
  group61 a assignment _ (by decide +kernel)

private def row1065 : List Int := [-37, 62, 40, 59, -43, 56]
include assignment in
private theorem clause1065 : Type2.RUP.trueClause a (checkedClause row1065) :=
  group61 a assignment _ (by decide +kernel)

private def row1069 : List Int := [37, -62, 40, 59, -43, 56]
include assignment in
private theorem clause1069 : Type2.RUP.trueClause a (checkedClause row1069) :=
  group61 a assignment _ (by decide +kernel)

private def row1075 : List Int := [37, 62, -40, 59, -43, -56]
include assignment in
private theorem clause1075 : Type2.RUP.trueClause a (checkedClause row1075) :=
  group61 a assignment _ (by decide +kernel)

include assignment in
private theorem group62 (c : SignClause) (hc : c ∈ pluckerAt [2, 5] [1, 3, 4, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1076 : List Int := [-37, -63, 40, -60, 44, 56]
include assignment in
private theorem clause1076 : Type2.RUP.trueClause a (checkedClause row1076) :=
  group62 a assignment _ (by decide +kernel)

private def row1086 : List Int := [37, -63, -40, -60, 44, -56]
include assignment in
private theorem clause1086 : Type2.RUP.trueClause a (checkedClause row1086) :=
  group62 a assignment _ (by decide +kernel)

private def row1087 : List Int := [37, -63, -40, -60, -44, 56]
include assignment in
private theorem clause1087 : Type2.RUP.trueClause a (checkedClause row1087) :=
  group62 a assignment _ (by decide +kernel)

private def row1090 : List Int := [37, 63, -40, 60, 44, 56]
include assignment in
private theorem clause1090 : Type2.RUP.trueClause a (checkedClause row1090) :=
  group62 a assignment _ (by decide +kernel)

include assignment in
private theorem group63 (c : SignClause) (hc : c ∈ pluckerAt [2, 5] [1, 3, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1092 : List Int := [-37, 65, -43, -60, 44, -59]
include assignment in
private theorem clause1092 : Type2.RUP.trueClause a (checkedClause row1092) :=
  group63 a assignment _ (by decide +kernel)

private def row1099 : List Int := [-37, -65, 43, -60, -44, -59]
include assignment in
private theorem clause1099 : Type2.RUP.trueClause a (checkedClause row1099) :=
  group63 a assignment _ (by decide +kernel)

private def row1100 : List Int := [37, 65, -43, 60, 44, 59]
include assignment in
private theorem clause1100 : Type2.RUP.trueClause a (checkedClause row1100) :=
  group63 a assignment _ (by decide +kernel)

private def row1107 : List Int := [37, -65, 43, 60, -44, 59]
include assignment in
private theorem clause1107 : Type2.RUP.trueClause a (checkedClause row1107) :=
  group63 a assignment _ (by decide +kernel)

include assignment in
private theorem group65 (c : SignClause) (hc : c ∈ pluckerAt [2, 5] [3, 4, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1124 : List Int := [56, 65, 59, -63, -60, -62]
include assignment in
private theorem clause1124 : Type2.RUP.trueClause a (checkedClause row1124) :=
  group65 a assignment _ (by decide +kernel)

private def row1132 : List Int := [-56, 65, 59, 63, -60, 62]
include assignment in
private theorem clause1132 : Type2.RUP.trueClause a (checkedClause row1132) :=
  group65 a assignment _ (by decide +kernel)

private def row1139 : List Int := [-56, -65, -59, 63, 60, 62]
include assignment in
private theorem clause1139 : Type2.RUP.trueClause a (checkedClause row1139) :=
  group65 a assignment _ (by decide +kernel)

include assignment in
private theorem group66 (c : SignClause) (hc : c ∈ pluckerAt [2, 6] [1, 3, 4, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1140 : List Int := [-38, 62, 41, 59, -43, 57]
include assignment in
private theorem clause1140 : Type2.RUP.trueClause a (checkedClause row1140) :=
  group66 a assignment _ (by decide +kernel)

private def row1143 : List Int := [-38, 62, -41, -59, 43, -57]
include assignment in
private theorem clause1143 : Type2.RUP.trueClause a (checkedClause row1143) :=
  group66 a assignment _ (by decide +kernel)

private def row1144 : List Int := [-38, -62, 41, -59, -43, -57]
include assignment in
private theorem clause1144 : Type2.RUP.trueClause a (checkedClause row1144) :=
  group66 a assignment _ (by decide +kernel)

include assignment in
private theorem group67 (c : SignClause) (hc : c ∈ pluckerAt [2, 6] [1, 3, 4, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1159 : List Int := [-38, -64, -41, 61, -45, -57]
include assignment in
private theorem clause1159 : Type2.RUP.trueClause a (checkedClause row1159) :=
  group67 a assignment _ (by decide +kernel)

private def row1160 : List Int := [-38, 64, 41, 61, 45, -57]
include assignment in
private theorem clause1160 : Type2.RUP.trueClause a (checkedClause row1160) :=
  group67 a assignment _ (by decide +kernel)

private def row1163 : List Int := [-38, 64, -41, -61, -45, 57]
include assignment in
private theorem clause1163 : Type2.RUP.trueClause a (checkedClause row1163) :=
  group67 a assignment _ (by decide +kernel)

private def row1171 : List Int := [38, 64, -41, 61, -45, -57]
include assignment in
private theorem clause1171 : Type2.RUP.trueClause a (checkedClause row1171) :=
  group67 a assignment _ (by decide +kernel)

include assignment in
private theorem group68 (c : SignClause) (hc : c ∈ pluckerAt [2, 6] [1, 3, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1173 : List Int := [-38, -65, 43, -61, -45, -59]
include assignment in
private theorem clause1173 : Type2.RUP.trueClause a (checkedClause row1173) :=
  group68 a assignment _ (by decide +kernel)

private def row1180 : List Int := [38, -65, 43, 61, 45, -59]
include assignment in
private theorem clause1180 : Type2.RUP.trueClause a (checkedClause row1180) :=
  group68 a assignment _ (by decide +kernel)

private def row1185 : List Int := [38, 65, 43, -61, -45, -59]
include assignment in
private theorem clause1185 : Type2.RUP.trueClause a (checkedClause row1185) :=
  group68 a assignment _ (by decide +kernel)

private def row1186 : List Int := [38, 65, -43, 61, 45, 59]
include assignment in
private theorem clause1186 : Type2.RUP.trueClause a (checkedClause row1186) :=
  group68 a assignment _ (by decide +kernel)

include assignment in
private theorem group69 (c : SignClause) (hc : c ∈ pluckerAt [2, 6] [1, 4, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1196 : List Int := [41, -65, 43, 64, 45, -62]
include assignment in
private theorem clause1196 : Type2.RUP.trueClause a (checkedClause row1196) :=
  group69 a assignment _ (by decide +kernel)

private def row1201 : List Int := [41, 65, 43, -64, -45, -62]
include assignment in
private theorem clause1201 : Type2.RUP.trueClause a (checkedClause row1201) :=
  group69 a assignment _ (by decide +kernel)

include assignment in
private theorem group70 (c : SignClause) (hc : c ∈ pluckerAt [2, 6] [3, 4, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1205 : List Int := [57, -65, -59, -64, 61, -62]
include assignment in
private theorem clause1205 : Type2.RUP.trueClause a (checkedClause row1205) :=
  group70 a assignment _ (by decide +kernel)

private def row1206 : List Int := [57, -65, 59, 64, -61, 62]
include assignment in
private theorem clause1206 : Type2.RUP.trueClause a (checkedClause row1206) :=
  group70 a assignment _ (by decide +kernel)

private def row1215 : List Int := [-57, -65, 59, -64, 61, 62]
include assignment in
private theorem clause1215 : Type2.RUP.trueClause a (checkedClause row1215) :=
  group70 a assignment _ (by decide +kernel)

private def row1217 : List Int := [-57, 65, -59, -64, 61, -62]
include assignment in
private theorem clause1217 : Type2.RUP.trueClause a (checkedClause row1217) :=
  group70 a assignment _ (by decide +kernel)

include assignment in
private theorem group71 (c : SignClause) (hc : c ∈ pluckerAt [2, 7] [1, 3, 4, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1220 : List Int := [-39, 63, 42, 60, -44, 58]
include assignment in
private theorem clause1220 : Type2.RUP.trueClause a (checkedClause row1220) :=
  group71 a assignment _ (by decide +kernel)

include assignment in
private theorem group72 (c : SignClause) (hc : c ∈ pluckerAt [2, 7] [1, 3, 4, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1237 : List Int := [-39, 64, 42, 61, 45, -58]
include assignment in
private theorem clause1237 : Type2.RUP.trueClause a (checkedClause row1237) :=
  group72 a assignment _ (by decide +kernel)

private def row1238 : List Int := [-39, 64, -42, -61, -45, 58]
include assignment in
private theorem clause1238 : Type2.RUP.trueClause a (checkedClause row1238) :=
  group72 a assignment _ (by decide +kernel)

private def row1244 : List Int := [39, 64, 42, -61, -45, -58]
include assignment in
private theorem clause1244 : Type2.RUP.trueClause a (checkedClause row1244) :=
  group72 a assignment _ (by decide +kernel)

include assignment in
private theorem group73 (c : SignClause) (hc : c ∈ pluckerAt [2, 7] [1, 3, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1254 : List Int := [-39, 65, -44, -61, -45, 60]
include assignment in
private theorem clause1254 : Type2.RUP.trueClause a (checkedClause row1254) :=
  group73 a assignment _ (by decide +kernel)

include assignment in
private theorem group75 (c : SignClause) (hc : c ∈ pluckerAt [2, 7] [3, 4, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1288 : List Int := [58, -65, -60, -64, 61, -63]
include assignment in
private theorem clause1288 : Type2.RUP.trueClause a (checkedClause row1288) :=
  group75 a assignment _ (by decide +kernel)

private def row1291 : List Int := [58, -65, 60, 64, -61, 63]
include assignment in
private theorem clause1291 : Type2.RUP.trueClause a (checkedClause row1291) :=
  group75 a assignment _ (by decide +kernel)

include assignment in
private theorem group76 (c : SignClause) (hc : c ∈ pluckerAt [3, 4] [1, 2, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1300 : List Int := [36, 66, -46, 57, 47, 56]
include assignment in
private theorem clause1300 : Type2.RUP.trueClause a (checkedClause row1300) :=
  group76 a assignment _ (by decide +kernel)

private def row1301 : List Int := [36, 66, -46, 57, -47, -56]
include assignment in
private theorem clause1301 : Type2.RUP.trueClause a (checkedClause row1301) :=
  group76 a assignment _ (by decide +kernel)

private def row1304 : List Int := [36, -66, -46, -57, 47, -56]
include assignment in
private theorem clause1304 : Type2.RUP.trueClause a (checkedClause row1304) :=
  group76 a assignment _ (by decide +kernel)

private def row1305 : List Int := [36, -66, -46, -57, -47, 56]
include assignment in
private theorem clause1305 : Type2.RUP.trueClause a (checkedClause row1305) :=
  group76 a assignment _ (by decide +kernel)

private def row1307 : List Int := [36, -66, 46, 57, -47, 56]
include assignment in
private theorem clause1307 : Type2.RUP.trueClause a (checkedClause row1307) :=
  group76 a assignment _ (by decide +kernel)

private def row1308 : List Int := [-36, 66, -46, -57, 47, -56]
include assignment in
private theorem clause1308 : Type2.RUP.trueClause a (checkedClause row1308) :=
  group76 a assignment _ (by decide +kernel)

private def row1314 : List Int := [-36, -66, 46, -57, 47, 56]
include assignment in
private theorem clause1314 : Type2.RUP.trueClause a (checkedClause row1314) :=
  group76 a assignment _ (by decide +kernel)

private def row1315 : List Int := [-36, -66, 46, -57, -47, -56]
include assignment in
private theorem clause1315 : Type2.RUP.trueClause a (checkedClause row1315) :=
  group76 a assignment _ (by decide +kernel)

include assignment in
private theorem group77 (c : SignClause) (hc : c ∈ pluckerAt [3, 4] [1, 2, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1316 : List Int := [36, 67, -46, 58, 48, 56]
include assignment in
private theorem clause1316 : Type2.RUP.trueClause a (checkedClause row1316) :=
  group77 a assignment _ (by decide +kernel)

private def row1321 : List Int := [36, -67, -46, -58, -48, 56]
include assignment in
private theorem clause1321 : Type2.RUP.trueClause a (checkedClause row1321) :=
  group77 a assignment _ (by decide +kernel)

private def row1324 : List Int := [-36, 67, -46, -58, 48, -56]
include assignment in
private theorem clause1324 : Type2.RUP.trueClause a (checkedClause row1324) :=
  group77 a assignment _ (by decide +kernel)

private def row1325 : List Int := [-36, 67, -46, -58, -48, 56]
include assignment in
private theorem clause1325 : Type2.RUP.trueClause a (checkedClause row1325) :=
  group77 a assignment _ (by decide +kernel)

private def row1326 : List Int := [-36, 67, 46, 58, 48, -56]
include assignment in
private theorem clause1326 : Type2.RUP.trueClause a (checkedClause row1326) :=
  group77 a assignment _ (by decide +kernel)

private def row1330 : List Int := [-36, -67, 46, -58, 48, 56]
include assignment in
private theorem clause1330 : Type2.RUP.trueClause a (checkedClause row1330) :=
  group77 a assignment _ (by decide +kernel)

private def row1331 : List Int := [-36, -67, 46, -58, -48, -56]
include assignment in
private theorem clause1331 : Type2.RUP.trueClause a (checkedClause row1331) :=
  group77 a assignment _ (by decide +kernel)

include assignment in
private theorem group78 (c : SignClause) (hc : c ∈ pluckerAt [3, 4] [1, 2, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1337 : List Int := [36, -68, -47, -58, -48, 57]
include assignment in
private theorem clause1337 : Type2.RUP.trueClause a (checkedClause row1337) :=
  group78 a assignment _ (by decide +kernel)

private def row1340 : List Int := [-36, 68, -47, -58, 48, -57]
include assignment in
private theorem clause1340 : Type2.RUP.trueClause a (checkedClause row1340) :=
  group78 a assignment _ (by decide +kernel)

private def row1341 : List Int := [-36, 68, -47, -58, -48, 57]
include assignment in
private theorem clause1341 : Type2.RUP.trueClause a (checkedClause row1341) :=
  group78 a assignment _ (by decide +kernel)

private def row1342 : List Int := [-36, 68, 47, 58, 48, -57]
include assignment in
private theorem clause1342 : Type2.RUP.trueClause a (checkedClause row1342) :=
  group78 a assignment _ (by decide +kernel)

private def row1347 : List Int := [-36, -68, 47, -58, -48, -57]
include assignment in
private theorem clause1347 : Type2.RUP.trueClause a (checkedClause row1347) :=
  group78 a assignment _ (by decide +kernel)

include assignment in
private theorem group79 (c : SignClause) (hc : c ∈ pluckerAt [3, 4] [1, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1348 : List Int := [46, 68, -47, 67, 48, 66]
include assignment in
private theorem clause1348 : Type2.RUP.trueClause a (checkedClause row1348) :=
  group79 a assignment _ (by decide +kernel)

private def row1349 : List Int := [46, 68, -47, 67, -48, -66]
include assignment in
private theorem clause1349 : Type2.RUP.trueClause a (checkedClause row1349) :=
  group79 a assignment _ (by decide +kernel)

private def row1350 : List Int := [46, 68, 47, -67, 48, 66]
include assignment in
private theorem clause1350 : Type2.RUP.trueClause a (checkedClause row1350) :=
  group79 a assignment _ (by decide +kernel)

private def row1352 : List Int := [46, -68, -47, -67, 48, -66]
include assignment in
private theorem clause1352 : Type2.RUP.trueClause a (checkedClause row1352) :=
  group79 a assignment _ (by decide +kernel)

private def row1357 : List Int := [-46, 68, -47, -67, -48, 66]
include assignment in
private theorem clause1357 : Type2.RUP.trueClause a (checkedClause row1357) :=
  group79 a assignment _ (by decide +kernel)

private def row1358 : List Int := [-46, 68, 47, 67, 48, -66]
include assignment in
private theorem clause1358 : Type2.RUP.trueClause a (checkedClause row1358) :=
  group79 a assignment _ (by decide +kernel)

private def row1359 : List Int := [-46, 68, 47, 67, -48, 66]
include assignment in
private theorem clause1359 : Type2.RUP.trueClause a (checkedClause row1359) :=
  group79 a assignment _ (by decide +kernel)

private def row1360 : List Int := [-46, -68, -47, 67, 48, 66]
include assignment in
private theorem clause1360 : Type2.RUP.trueClause a (checkedClause row1360) :=
  group79 a assignment _ (by decide +kernel)

include assignment in
private theorem group80 (c : SignClause) (hc : c ∈ pluckerAt [3, 4] [2, 5, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1364 : List Int := [56, 68, -57, 67, 58, 66]
include assignment in
private theorem clause1364 : Type2.RUP.trueClause a (checkedClause row1364) :=
  group80 a assignment _ (by decide +kernel)

private def row1365 : List Int := [56, 68, -57, 67, -58, -66]
include assignment in
private theorem clause1365 : Type2.RUP.trueClause a (checkedClause row1365) :=
  group80 a assignment _ (by decide +kernel)

private def row1366 : List Int := [56, 68, 57, -67, 58, 66]
include assignment in
private theorem clause1366 : Type2.RUP.trueClause a (checkedClause row1366) :=
  group80 a assignment _ (by decide +kernel)

private def row1367 : List Int := [56, 68, 57, -67, -58, -66]
include assignment in
private theorem clause1367 : Type2.RUP.trueClause a (checkedClause row1367) :=
  group80 a assignment _ (by decide +kernel)

private def row1368 : List Int := [56, -68, -57, -67, 58, -66]
include assignment in
private theorem clause1368 : Type2.RUP.trueClause a (checkedClause row1368) :=
  group80 a assignment _ (by decide +kernel)

private def row1373 : List Int := [-56, 68, -57, -67, -58, 66]
include assignment in
private theorem clause1373 : Type2.RUP.trueClause a (checkedClause row1373) :=
  group80 a assignment _ (by decide +kernel)

private def row1375 : List Int := [-56, 68, 57, 67, -58, 66]
include assignment in
private theorem clause1375 : Type2.RUP.trueClause a (checkedClause row1375) :=
  group80 a assignment _ (by decide +kernel)

private def row1376 : List Int := [-56, -68, -57, 67, 58, 66]
include assignment in
private theorem clause1376 : Type2.RUP.trueClause a (checkedClause row1376) :=
  group80 a assignment _ (by decide +kernel)

private def row1379 : List Int := [-56, -68, 57, -67, -58, -66]
include assignment in
private theorem clause1379 : Type2.RUP.trueClause a (checkedClause row1379) :=
  group80 a assignment _ (by decide +kernel)

include assignment in
private theorem group81 (c : SignClause) (hc : c ∈ pluckerAt [3, 5] [1, 2, 4, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1381 : List Int := [37, -66, 46, 59, -49, 56]
include assignment in
private theorem clause1381 : Type2.RUP.trueClause a (checkedClause row1381) :=
  group81 a assignment _ (by decide +kernel)

private def row1382 : List Int := [37, -66, -46, -59, 49, -56]
include assignment in
private theorem clause1382 : Type2.RUP.trueClause a (checkedClause row1382) :=
  group81 a assignment _ (by decide +kernel)

private def row1386 : List Int := [37, 66, -46, 59, 49, 56]
include assignment in
private theorem clause1386 : Type2.RUP.trueClause a (checkedClause row1386) :=
  group81 a assignment _ (by decide +kernel)

private def row1387 : List Int := [37, 66, -46, 59, -49, -56]
include assignment in
private theorem clause1387 : Type2.RUP.trueClause a (checkedClause row1387) :=
  group81 a assignment _ (by decide +kernel)

private def row1388 : List Int := [-37, -66, 46, -59, 49, 56]
include assignment in
private theorem clause1388 : Type2.RUP.trueClause a (checkedClause row1388) :=
  group81 a assignment _ (by decide +kernel)

private def row1393 : List Int := [-37, 66, 46, 59, -49, 56]
include assignment in
private theorem clause1393 : Type2.RUP.trueClause a (checkedClause row1393) :=
  group81 a assignment _ (by decide +kernel)

private def row1394 : List Int := [-37, 66, -46, -59, 49, -56]
include assignment in
private theorem clause1394 : Type2.RUP.trueClause a (checkedClause row1394) :=
  group81 a assignment _ (by decide +kernel)

private def row1395 : List Int := [-37, 66, -46, -59, -49, 56]
include assignment in
private theorem clause1395 : Type2.RUP.trueClause a (checkedClause row1395) :=
  group81 a assignment _ (by decide +kernel)

include assignment in
private theorem group82 (c : SignClause) (hc : c ∈ pluckerAt [3, 5] [1, 2, 4, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1397 : List Int := [37, -67, 46, 60, -50, 56]
include assignment in
private theorem clause1397 : Type2.RUP.trueClause a (checkedClause row1397) :=
  group82 a assignment _ (by decide +kernel)

private def row1399 : List Int := [37, -67, -46, -60, -50, 56]
include assignment in
private theorem clause1399 : Type2.RUP.trueClause a (checkedClause row1399) :=
  group82 a assignment _ (by decide +kernel)

private def row1400 : List Int := [37, 67, 46, -60, 50, 56]
include assignment in
private theorem clause1400 : Type2.RUP.trueClause a (checkedClause row1400) :=
  group82 a assignment _ (by decide +kernel)

private def row1403 : List Int := [37, 67, -46, 60, -50, -56]
include assignment in
private theorem clause1403 : Type2.RUP.trueClause a (checkedClause row1403) :=
  group82 a assignment _ (by decide +kernel)

private def row1407 : List Int := [-37, -67, -46, 60, -50, -56]
include assignment in
private theorem clause1407 : Type2.RUP.trueClause a (checkedClause row1407) :=
  group82 a assignment _ (by decide +kernel)

private def row1410 : List Int := [-37, 67, -46, -60, 50, -56]
include assignment in
private theorem clause1410 : Type2.RUP.trueClause a (checkedClause row1410) :=
  group82 a assignment _ (by decide +kernel)

include assignment in
private theorem group83 (c : SignClause) (hc : c ∈ pluckerAt [3, 5] [1, 2, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1418 : List Int := [37, -69, 49, 60, 50, -59]
include assignment in
private theorem clause1418 : Type2.RUP.trueClause a (checkedClause row1418) :=
  group83 a assignment _ (by decide +kernel)

private def row1419 : List Int := [37, -69, 49, 60, -50, 59]
include assignment in
private theorem clause1419 : Type2.RUP.trueClause a (checkedClause row1419) :=
  group83 a assignment _ (by decide +kernel)

private def row1427 : List Int := [-37, -69, 49, -60, -50, -59]
include assignment in
private theorem clause1427 : Type2.RUP.trueClause a (checkedClause row1427) :=
  group83 a assignment _ (by decide +kernel)

include assignment in
private theorem group84 (c : SignClause) (hc : c ∈ pluckerAt [3, 5] [1, 4, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1430 : List Int := [-46, 69, 49, 67, 50, -66]
include assignment in
private theorem clause1430 : Type2.RUP.trueClause a (checkedClause row1430) :=
  group84 a assignment _ (by decide +kernel)

private def row1431 : List Int := [-46, 69, 49, 67, -50, 66]
include assignment in
private theorem clause1431 : Type2.RUP.trueClause a (checkedClause row1431) :=
  group84 a assignment _ (by decide +kernel)

private def row1432 : List Int := [-46, -69, -49, 67, 50, 66]
include assignment in
private theorem clause1432 : Type2.RUP.trueClause a (checkedClause row1432) :=
  group84 a assignment _ (by decide +kernel)

private def row1433 : List Int := [-46, -69, -49, 67, -50, -66]
include assignment in
private theorem clause1433 : Type2.RUP.trueClause a (checkedClause row1433) :=
  group84 a assignment _ (by decide +kernel)

private def row1434 : List Int := [-46, -69, 49, -67, 50, 66]
include assignment in
private theorem clause1434 : Type2.RUP.trueClause a (checkedClause row1434) :=
  group84 a assignment _ (by decide +kernel)

private def row1435 : List Int := [-46, -69, 49, -67, -50, -66]
include assignment in
private theorem clause1435 : Type2.RUP.trueClause a (checkedClause row1435) :=
  group84 a assignment _ (by decide +kernel)

private def row1437 : List Int := [46, 69, -49, 67, -50, -66]
include assignment in
private theorem clause1437 : Type2.RUP.trueClause a (checkedClause row1437) :=
  group84 a assignment _ (by decide +kernel)

private def row1439 : List Int := [46, 69, 49, -67, -50, -66]
include assignment in
private theorem clause1439 : Type2.RUP.trueClause a (checkedClause row1439) :=
  group84 a assignment _ (by decide +kernel)

private def row1441 : List Int := [46, -69, -49, -67, -50, 66]
include assignment in
private theorem clause1441 : Type2.RUP.trueClause a (checkedClause row1441) :=
  group84 a assignment _ (by decide +kernel)

private def row1443 : List Int := [46, -69, 49, 67, -50, 66]
include assignment in
private theorem clause1443 : Type2.RUP.trueClause a (checkedClause row1443) :=
  group84 a assignment _ (by decide +kernel)

include assignment in
private theorem group85 (c : SignClause) (hc : c ∈ pluckerAt [3, 5] [2, 4, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1444 : List Int := [-56, 69, -59, -67, 60, -66]
include assignment in
private theorem clause1444 : Type2.RUP.trueClause a (checkedClause row1444) :=
  group85 a assignment _ (by decide +kernel)

private def row1447 : List Int := [-56, 69, 59, 67, -60, 66]
include assignment in
private theorem clause1447 : Type2.RUP.trueClause a (checkedClause row1447) :=
  group85 a assignment _ (by decide +kernel)

private def row1448 : List Int := [-56, -69, -59, 67, 60, 66]
include assignment in
private theorem clause1448 : Type2.RUP.trueClause a (checkedClause row1448) :=
  group85 a assignment _ (by decide +kernel)

private def row1453 : List Int := [56, 69, -59, 67, -60, -66]
include assignment in
private theorem clause1453 : Type2.RUP.trueClause a (checkedClause row1453) :=
  group85 a assignment _ (by decide +kernel)

private def row1455 : List Int := [56, 69, 59, -67, -60, -66]
include assignment in
private theorem clause1455 : Type2.RUP.trueClause a (checkedClause row1455) :=
  group85 a assignment _ (by decide +kernel)

private def row1456 : List Int := [56, -69, -59, -67, 60, -66]
include assignment in
private theorem clause1456 : Type2.RUP.trueClause a (checkedClause row1456) :=
  group85 a assignment _ (by decide +kernel)

private def row1459 : List Int := [56, -69, 59, 67, -60, 66]
include assignment in
private theorem clause1459 : Type2.RUP.trueClause a (checkedClause row1459) :=
  group85 a assignment _ (by decide +kernel)

include assignment in
private theorem group86 (c : SignClause) (hc : c ∈ pluckerAt [3, 6] [1, 2, 4, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1467 : List Int := [38, -66, -47, -59, 49, -57]
include assignment in
private theorem clause1467 : Type2.RUP.trueClause a (checkedClause row1467) :=
  group86 a assignment _ (by decide +kernel)

private def row1468 : List Int := [-38, 66, 47, 59, -49, 57]
include assignment in
private theorem clause1468 : Type2.RUP.trueClause a (checkedClause row1468) :=
  group86 a assignment _ (by decide +kernel)

private def row1472 : List Int := [-38, -66, 47, -59, -49, -57]
include assignment in
private theorem clause1472 : Type2.RUP.trueClause a (checkedClause row1472) :=
  group86 a assignment _ (by decide +kernel)

private def row1475 : List Int := [-38, -66, -47, 59, 49, 57]
include assignment in
private theorem clause1475 : Type2.RUP.trueClause a (checkedClause row1475) :=
  group86 a assignment _ (by decide +kernel)

include assignment in
private theorem group87 (c : SignClause) (hc : c ∈ pluckerAt [3, 6] [1, 2, 4, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1476 : List Int := [38, -68, 47, 61, 51, -57]
include assignment in
private theorem clause1476 : Type2.RUP.trueClause a (checkedClause row1476) :=
  group87 a assignment _ (by decide +kernel)

private def row1483 : List Int := [38, 68, -47, 61, -51, -57]
include assignment in
private theorem clause1483 : Type2.RUP.trueClause a (checkedClause row1483) :=
  group87 a assignment _ (by decide +kernel)

private def row1484 : List Int := [-38, -68, 47, -61, 51, 57]
include assignment in
private theorem clause1484 : Type2.RUP.trueClause a (checkedClause row1484) :=
  group87 a assignment _ (by decide +kernel)

private def row1486 : List Int := [-38, -68, -47, 61, 51, 57]
include assignment in
private theorem clause1486 : Type2.RUP.trueClause a (checkedClause row1486) :=
  group87 a assignment _ (by decide +kernel)

private def row1487 : List Int := [-38, -68, -47, 61, -51, -57]
include assignment in
private theorem clause1487 : Type2.RUP.trueClause a (checkedClause row1487) :=
  group87 a assignment _ (by decide +kernel)

include assignment in
private theorem group88 (c : SignClause) (hc : c ∈ pluckerAt [3, 6] [1, 2, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1492 : List Int := [38, -69, 49, 61, 51, -59]
include assignment in
private theorem clause1492 : Type2.RUP.trueClause a (checkedClause row1492) :=
  group88 a assignment _ (by decide +kernel)

private def row1496 : List Int := [38, 69, 49, -61, 51, 59]
include assignment in
private theorem clause1496 : Type2.RUP.trueClause a (checkedClause row1496) :=
  group88 a assignment _ (by decide +kernel)

private def row1500 : List Int := [-38, -69, 49, -61, 51, 59]
include assignment in
private theorem clause1500 : Type2.RUP.trueClause a (checkedClause row1500) :=
  group88 a assignment _ (by decide +kernel)

private def row1502 : List Int := [-38, -69, -49, 61, 51, 59]
include assignment in
private theorem clause1502 : Type2.RUP.trueClause a (checkedClause row1502) :=
  group88 a assignment _ (by decide +kernel)

private def row1506 : List Int := [-38, 69, -49, -61, 51, -59]
include assignment in
private theorem clause1506 : Type2.RUP.trueClause a (checkedClause row1506) :=
  group88 a assignment _ (by decide +kernel)

include assignment in
private theorem group89 (c : SignClause) (hc : c ∈ pluckerAt [3, 6] [1, 4, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1508 : List Int := [-47, -69, 49, -68, 51, 66]
include assignment in
private theorem clause1508 : Type2.RUP.trueClause a (checkedClause row1508) :=
  group89 a assignment _ (by decide +kernel)

private def row1509 : List Int := [-47, -69, 49, -68, -51, -66]
include assignment in
private theorem clause1509 : Type2.RUP.trueClause a (checkedClause row1509) :=
  group89 a assignment _ (by decide +kernel)

private def row1513 : List Int := [-47, 69, 49, 68, -51, 66]
include assignment in
private theorem clause1513 : Type2.RUP.trueClause a (checkedClause row1513) :=
  group89 a assignment _ (by decide +kernel)

private def row1518 : List Int := [47, -69, -49, -68, 51, -66]
include assignment in
private theorem clause1518 : Type2.RUP.trueClause a (checkedClause row1518) :=
  group89 a assignment _ (by decide +kernel)

private def row1523 : List Int := [47, 69, -49, 68, -51, -66]
include assignment in
private theorem clause1523 : Type2.RUP.trueClause a (checkedClause row1523) :=
  group89 a assignment _ (by decide +kernel)

include assignment in
private theorem group90 (c : SignClause) (hc : c ∈ pluckerAt [3, 6] [2, 4, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1524 : List Int := [-57, -69, 59, -68, 61, 66]
include assignment in
private theorem clause1524 : Type2.RUP.trueClause a (checkedClause row1524) :=
  group90 a assignment _ (by decide +kernel)

private def row1525 : List Int := [-57, -69, 59, -68, -61, -66]
include assignment in
private theorem clause1525 : Type2.RUP.trueClause a (checkedClause row1525) :=
  group90 a assignment _ (by decide +kernel)

private def row1529 : List Int := [-57, 69, 59, 68, -61, 66]
include assignment in
private theorem clause1529 : Type2.RUP.trueClause a (checkedClause row1529) :=
  group90 a assignment _ (by decide +kernel)

private def row1530 : List Int := [-57, 69, -59, -68, 61, -66]
include assignment in
private theorem clause1530 : Type2.RUP.trueClause a (checkedClause row1530) :=
  group90 a assignment _ (by decide +kernel)

private def row1534 : List Int := [57, -69, -59, -68, 61, -66]
include assignment in
private theorem clause1534 : Type2.RUP.trueClause a (checkedClause row1534) :=
  group90 a assignment _ (by decide +kernel)

private def row1535 : List Int := [57, -69, -59, -68, -61, 66]
include assignment in
private theorem clause1535 : Type2.RUP.trueClause a (checkedClause row1535) :=
  group90 a assignment _ (by decide +kernel)

private def row1537 : List Int := [57, 69, 59, -68, -61, -66]
include assignment in
private theorem clause1537 : Type2.RUP.trueClause a (checkedClause row1537) :=
  group90 a assignment _ (by decide +kernel)

private def row1539 : List Int := [57, 69, -59, 68, -61, -66]
include assignment in
private theorem clause1539 : Type2.RUP.trueClause a (checkedClause row1539) :=
  group90 a assignment _ (by decide +kernel)

include assignment in
private theorem group91 (c : SignClause) (hc : c ∈ pluckerAt [3, 7] [1, 2, 4, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1546 : List Int := [39, -67, -48, -60, -50, 58]
include assignment in
private theorem clause1546 : Type2.RUP.trueClause a (checkedClause row1546) :=
  group91 a assignment _ (by decide +kernel)

private def row1548 : List Int := [-39, 67, 48, 60, -50, 58]
include assignment in
private theorem clause1548 : Type2.RUP.trueClause a (checkedClause row1548) :=
  group91 a assignment _ (by decide +kernel)

private def row1551 : List Int := [-39, 67, -48, -60, 50, -58]
include assignment in
private theorem clause1551 : Type2.RUP.trueClause a (checkedClause row1551) :=
  group91 a assignment _ (by decide +kernel)

private def row1552 : List Int := [-39, -67, 48, -60, -50, -58]
include assignment in
private theorem clause1552 : Type2.RUP.trueClause a (checkedClause row1552) :=
  group91 a assignment _ (by decide +kernel)

private def row1554 : List Int := [-39, -67, -48, 60, -50, -58]
include assignment in
private theorem clause1554 : Type2.RUP.trueClause a (checkedClause row1554) :=
  group91 a assignment _ (by decide +kernel)

include assignment in
private theorem group92 (c : SignClause) (hc : c ∈ pluckerAt [3, 7] [1, 2, 4, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1557 : List Int := [39, 68, 48, -61, 51, 58]
include assignment in
private theorem clause1557 : Type2.RUP.trueClause a (checkedClause row1557) :=
  group92 a assignment _ (by decide +kernel)

private def row1562 : List Int := [39, -68, -48, -61, -51, 58]
include assignment in
private theorem clause1562 : Type2.RUP.trueClause a (checkedClause row1562) :=
  group92 a assignment _ (by decide +kernel)

private def row1563 : List Int := [39, -68, -48, -61, 51, -58]
include assignment in
private theorem clause1563 : Type2.RUP.trueClause a (checkedClause row1563) :=
  group92 a assignment _ (by decide +kernel)

private def row1564 : List Int := [-39, 68, 48, 61, -51, 58]
include assignment in
private theorem clause1564 : Type2.RUP.trueClause a (checkedClause row1564) :=
  group92 a assignment _ (by decide +kernel)

private def row1565 : List Int := [-39, 68, 48, 61, 51, -58]
include assignment in
private theorem clause1565 : Type2.RUP.trueClause a (checkedClause row1565) :=
  group92 a assignment _ (by decide +kernel)

private def row1570 : List Int := [-39, -68, -48, 61, -51, -58]
include assignment in
private theorem clause1570 : Type2.RUP.trueClause a (checkedClause row1570) :=
  group92 a assignment _ (by decide +kernel)

include assignment in
private theorem group93 (c : SignClause) (hc : c ∈ pluckerAt [3, 7] [1, 2, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1577 : List Int := [39, -69, 50, 61, 51, -60]
include assignment in
private theorem clause1577 : Type2.RUP.trueClause a (checkedClause row1577) :=
  group93 a assignment _ (by decide +kernel)

private def row1587 : List Int := [-39, -69, -50, 61, 51, 60]
include assignment in
private theorem clause1587 : Type2.RUP.trueClause a (checkedClause row1587) :=
  group93 a assignment _ (by decide +kernel)

include assignment in
private theorem group94 (c : SignClause) (hc : c ∈ pluckerAt [3, 7] [1, 4, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1591 : List Int := [-48, 69, -50, -68, 51, -67]
include assignment in
private theorem clause1591 : Type2.RUP.trueClause a (checkedClause row1591) :=
  group94 a assignment _ (by decide +kernel)

private def row1592 : List Int := [-48, -69, 50, -68, -51, -67]
include assignment in
private theorem clause1592 : Type2.RUP.trueClause a (checkedClause row1592) :=
  group94 a assignment _ (by decide +kernel)

private def row1593 : List Int := [-48, -69, 50, -68, 51, 67]
include assignment in
private theorem clause1593 : Type2.RUP.trueClause a (checkedClause row1593) :=
  group94 a assignment _ (by decide +kernel)

private def row1600 : List Int := [48, -69, 50, 68, -51, 67]
include assignment in
private theorem clause1600 : Type2.RUP.trueClause a (checkedClause row1600) :=
  group94 a assignment _ (by decide +kernel)

private def row1603 : List Int := [48, -69, -50, -68, 51, -67]
include assignment in
private theorem clause1603 : Type2.RUP.trueClause a (checkedClause row1603) :=
  group94 a assignment _ (by decide +kernel)

include assignment in
private theorem group95 (c : SignClause) (hc : c ∈ pluckerAt [3, 7] [2, 4, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1604 : List Int := [-58, 69, 60, 68, -61, 67]
include assignment in
private theorem clause1604 : Type2.RUP.trueClause a (checkedClause row1604) :=
  group95 a assignment _ (by decide +kernel)

private def row1607 : List Int := [-58, 69, -60, -68, 61, -67]
include assignment in
private theorem clause1607 : Type2.RUP.trueClause a (checkedClause row1607) :=
  group95 a assignment _ (by decide +kernel)

private def row1609 : List Int := [-58, -69, 60, -68, 61, 67]
include assignment in
private theorem clause1609 : Type2.RUP.trueClause a (checkedClause row1609) :=
  group95 a assignment _ (by decide +kernel)

private def row1612 : List Int := [58, 69, 60, -68, -61, -67]
include assignment in
private theorem clause1612 : Type2.RUP.trueClause a (checkedClause row1612) :=
  group95 a assignment _ (by decide +kernel)

private def row1618 : List Int := [58, -69, -60, -68, -61, 67]
include assignment in
private theorem clause1618 : Type2.RUP.trueClause a (checkedClause row1618) :=
  group95 a assignment _ (by decide +kernel)

include assignment in
private theorem group96 (c : SignClause) (hc : c ∈ pluckerAt [4, 5] [1, 2, 3, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1621 : List Int := [40, 66, -46, 62, -52, -56]
include assignment in
private theorem clause1621 : Type2.RUP.trueClause a (checkedClause row1621) :=
  group96 a assignment _ (by decide +kernel)

private def row1623 : List Int := [40, 66, 46, -62, -52, -56]
include assignment in
private theorem clause1623 : Type2.RUP.trueClause a (checkedClause row1623) :=
  group96 a assignment _ (by decide +kernel)

private def row1625 : List Int := [40, -66, -46, -62, -52, 56]
include assignment in
private theorem clause1625 : Type2.RUP.trueClause a (checkedClause row1625) :=
  group96 a assignment _ (by decide +kernel)

private def row1628 : List Int := [-40, 66, -46, -62, 52, -56]
include assignment in
private theorem clause1628 : Type2.RUP.trueClause a (checkedClause row1628) :=
  group96 a assignment _ (by decide +kernel)

private def row1630 : List Int := [-40, 66, 46, 62, 52, -56]
include assignment in
private theorem clause1630 : Type2.RUP.trueClause a (checkedClause row1630) :=
  group96 a assignment _ (by decide +kernel)

private def row1634 : List Int := [-40, -66, 46, -62, 52, 56]
include assignment in
private theorem clause1634 : Type2.RUP.trueClause a (checkedClause row1634) :=
  group96 a assignment _ (by decide +kernel)

private def row1635 : List Int := [-40, -66, 46, -62, -52, -56]
include assignment in
private theorem clause1635 : Type2.RUP.trueClause a (checkedClause row1635) :=
  group96 a assignment _ (by decide +kernel)

include assignment in
private theorem group97 (c : SignClause) (hc : c ∈ pluckerAt [4, 5] [1, 2, 3, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1637 : List Int := [40, 67, -46, 63, -53, -56]
include assignment in
private theorem clause1637 : Type2.RUP.trueClause a (checkedClause row1637) :=
  group97 a assignment _ (by decide +kernel)

private def row1639 : List Int := [40, 67, 46, -63, -53, -56]
include assignment in
private theorem clause1639 : Type2.RUP.trueClause a (checkedClause row1639) :=
  group97 a assignment _ (by decide +kernel)

private def row1641 : List Int := [40, -67, -46, -63, -53, 56]
include assignment in
private theorem clause1641 : Type2.RUP.trueClause a (checkedClause row1641) :=
  group97 a assignment _ (by decide +kernel)

private def row1643 : List Int := [40, -67, 46, 63, -53, 56]
include assignment in
private theorem clause1643 : Type2.RUP.trueClause a (checkedClause row1643) :=
  group97 a assignment _ (by decide +kernel)

private def row1644 : List Int := [-40, 67, -46, -63, 53, -56]
include assignment in
private theorem clause1644 : Type2.RUP.trueClause a (checkedClause row1644) :=
  group97 a assignment _ (by decide +kernel)

private def row1648 : List Int := [-40, -67, -46, 63, 53, 56]
include assignment in
private theorem clause1648 : Type2.RUP.trueClause a (checkedClause row1648) :=
  group97 a assignment _ (by decide +kernel)

private def row1650 : List Int := [-40, -67, 46, -63, 53, 56]
include assignment in
private theorem clause1650 : Type2.RUP.trueClause a (checkedClause row1650) :=
  group97 a assignment _ (by decide +kernel)

include assignment in
private theorem group98 (c : SignClause) (hc : c ∈ pluckerAt [4, 5] [1, 2, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1653 : List Int := [40, 70, -52, 63, -53, -62]
include assignment in
private theorem clause1653 : Type2.RUP.trueClause a (checkedClause row1653) :=
  group98 a assignment _ (by decide +kernel)

private def row1658 : List Int := [40, -70, 52, 63, 53, -62]
include assignment in
private theorem clause1658 : Type2.RUP.trueClause a (checkedClause row1658) :=
  group98 a assignment _ (by decide +kernel)

private def row1659 : List Int := [40, -70, 52, 63, -53, 62]
include assignment in
private theorem clause1659 : Type2.RUP.trueClause a (checkedClause row1659) :=
  group98 a assignment _ (by decide +kernel)

private def row1660 : List Int := [-40, 70, -52, -63, 53, -62]
include assignment in
private theorem clause1660 : Type2.RUP.trueClause a (checkedClause row1660) :=
  group98 a assignment _ (by decide +kernel)

private def row1665 : List Int := [-40, -70, -52, 63, -53, -62]
include assignment in
private theorem clause1665 : Type2.RUP.trueClause a (checkedClause row1665) :=
  group98 a assignment _ (by decide +kernel)

include assignment in
private theorem group99 (c : SignClause) (hc : c ∈ pluckerAt [4, 5] [1, 3, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1668 : List Int := [46, 70, -52, 67, 53, 66]
include assignment in
private theorem clause1668 : Type2.RUP.trueClause a (checkedClause row1668) :=
  group99 a assignment _ (by decide +kernel)

private def row1669 : List Int := [46, 70, -52, 67, -53, -66]
include assignment in
private theorem clause1669 : Type2.RUP.trueClause a (checkedClause row1669) :=
  group99 a assignment _ (by decide +kernel)

private def row1671 : List Int := [46, 70, 52, -67, -53, -66]
include assignment in
private theorem clause1671 : Type2.RUP.trueClause a (checkedClause row1671) :=
  group99 a assignment _ (by decide +kernel)

private def row1672 : List Int := [46, -70, -52, -67, 53, -66]
include assignment in
private theorem clause1672 : Type2.RUP.trueClause a (checkedClause row1672) :=
  group99 a assignment _ (by decide +kernel)

private def row1675 : List Int := [46, -70, 52, 67, -53, 66]
include assignment in
private theorem clause1675 : Type2.RUP.trueClause a (checkedClause row1675) :=
  group99 a assignment _ (by decide +kernel)

private def row1676 : List Int := [-46, 70, -52, -67, 53, -66]
include assignment in
private theorem clause1676 : Type2.RUP.trueClause a (checkedClause row1676) :=
  group99 a assignment _ (by decide +kernel)

private def row1678 : List Int := [-46, 70, 52, 67, 53, -66]
include assignment in
private theorem clause1678 : Type2.RUP.trueClause a (checkedClause row1678) :=
  group99 a assignment _ (by decide +kernel)

private def row1679 : List Int := [-46, 70, 52, 67, -53, 66]
include assignment in
private theorem clause1679 : Type2.RUP.trueClause a (checkedClause row1679) :=
  group99 a assignment _ (by decide +kernel)

private def row1680 : List Int := [-46, -70, -52, 67, 53, 66]
include assignment in
private theorem clause1680 : Type2.RUP.trueClause a (checkedClause row1680) :=
  group99 a assignment _ (by decide +kernel)

private def row1682 : List Int := [-46, -70, 52, -67, 53, 66]
include assignment in
private theorem clause1682 : Type2.RUP.trueClause a (checkedClause row1682) :=
  group99 a assignment _ (by decide +kernel)

private def row1683 : List Int := [-46, -70, 52, -67, -53, -66]
include assignment in
private theorem clause1683 : Type2.RUP.trueClause a (checkedClause row1683) :=
  group99 a assignment _ (by decide +kernel)

include assignment in
private theorem group100 (c : SignClause) (hc : c ∈ pluckerAt [4, 5] [2, 3, 6, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1685 : List Int := [56, 70, -62, 67, -63, -66]
include assignment in
private theorem clause1685 : Type2.RUP.trueClause a (checkedClause row1685) :=
  group100 a assignment _ (by decide +kernel)

private def row1687 : List Int := [56, 70, 62, -67, -63, -66]
include assignment in
private theorem clause1687 : Type2.RUP.trueClause a (checkedClause row1687) :=
  group100 a assignment _ (by decide +kernel)

private def row1688 : List Int := [56, -70, -62, -67, 63, -66]
include assignment in
private theorem clause1688 : Type2.RUP.trueClause a (checkedClause row1688) :=
  group100 a assignment _ (by decide +kernel)

private def row1691 : List Int := [56, -70, 62, 67, -63, 66]
include assignment in
private theorem clause1691 : Type2.RUP.trueClause a (checkedClause row1691) :=
  group100 a assignment _ (by decide +kernel)

private def row1692 : List Int := [-56, 70, -62, -67, 63, -66]
include assignment in
private theorem clause1692 : Type2.RUP.trueClause a (checkedClause row1692) :=
  group100 a assignment _ (by decide +kernel)

private def row1695 : List Int := [-56, 70, 62, 67, -63, 66]
include assignment in
private theorem clause1695 : Type2.RUP.trueClause a (checkedClause row1695) :=
  group100 a assignment _ (by decide +kernel)

private def row1696 : List Int := [-56, -70, -62, 67, 63, 66]
include assignment in
private theorem clause1696 : Type2.RUP.trueClause a (checkedClause row1696) :=
  group100 a assignment _ (by decide +kernel)

include assignment in
private theorem group101 (c : SignClause) (hc : c ∈ pluckerAt [4, 6] [1, 2, 3, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1707 : List Int := [41, 66, 47, -62, 52, 57]
include assignment in
private theorem clause1707 : Type2.RUP.trueClause a (checkedClause row1707) :=
  group101 a assignment _ (by decide +kernel)

private def row1709 : List Int := [-41, -66, -47, 62, 52, 57]
include assignment in
private theorem clause1709 : Type2.RUP.trueClause a (checkedClause row1709) :=
  group101 a assignment _ (by decide +kernel)

private def row1710 : List Int := [-41, -66, 47, -62, -52, -57]
include assignment in
private theorem clause1710 : Type2.RUP.trueClause a (checkedClause row1710) :=
  group101 a assignment _ (by decide +kernel)

private def row1715 : List Int := [-41, 66, 47, 62, 52, -57]
include assignment in
private theorem clause1715 : Type2.RUP.trueClause a (checkedClause row1715) :=
  group101 a assignment _ (by decide +kernel)

include assignment in
private theorem group102 (c : SignClause) (hc : c ∈ pluckerAt [4, 6] [1, 2, 3, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1717 : List Int := [41, 68, -47, 64, -54, -57]
include assignment in
private theorem clause1717 : Type2.RUP.trueClause a (checkedClause row1717) :=
  group102 a assignment _ (by decide +kernel)

private def row1719 : List Int := [41, 68, 47, -64, -54, -57]
include assignment in
private theorem clause1719 : Type2.RUP.trueClause a (checkedClause row1719) :=
  group102 a assignment _ (by decide +kernel)

private def row1725 : List Int := [-41, 68, -47, -64, -54, 57]
include assignment in
private theorem clause1725 : Type2.RUP.trueClause a (checkedClause row1725) :=
  group102 a assignment _ (by decide +kernel)

private def row1728 : List Int := [-41, -68, -47, 64, 54, 57]
include assignment in
private theorem clause1728 : Type2.RUP.trueClause a (checkedClause row1728) :=
  group102 a assignment _ (by decide +kernel)

include assignment in
private theorem group103 (c : SignClause) (hc : c ∈ pluckerAt [4, 6] [1, 2, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1733 : List Int := [41, -70, 52, 64, -54, 62]
include assignment in
private theorem clause1733 : Type2.RUP.trueClause a (checkedClause row1733) :=
  group103 a assignment _ (by decide +kernel)

private def row1739 : List Int := [41, 70, -52, 64, -54, -62]
include assignment in
private theorem clause1739 : Type2.RUP.trueClause a (checkedClause row1739) :=
  group103 a assignment _ (by decide +kernel)

private def row1746 : List Int := [-41, 70, -52, -64, 54, -62]
include assignment in
private theorem clause1746 : Type2.RUP.trueClause a (checkedClause row1746) :=
  group103 a assignment _ (by decide +kernel)

include assignment in
private theorem group104 (c : SignClause) (hc : c ∈ pluckerAt [4, 6] [1, 3, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1749 : List Int := [47, -70, 52, 68, -54, 66]
include assignment in
private theorem clause1749 : Type2.RUP.trueClause a (checkedClause row1749) :=
  group104 a assignment _ (by decide +kernel)

private def row1750 : List Int := [47, -70, -52, -68, 54, -66]
include assignment in
private theorem clause1750 : Type2.RUP.trueClause a (checkedClause row1750) :=
  group104 a assignment _ (by decide +kernel)

private def row1754 : List Int := [47, 70, -52, 68, 54, 66]
include assignment in
private theorem clause1754 : Type2.RUP.trueClause a (checkedClause row1754) :=
  group104 a assignment _ (by decide +kernel)

private def row1757 : List Int := [-47, -70, 52, -68, -54, -66]
include assignment in
private theorem clause1757 : Type2.RUP.trueClause a (checkedClause row1757) :=
  group104 a assignment _ (by decide +kernel)

private def row1761 : List Int := [-47, 70, 52, 68, -54, 66]
include assignment in
private theorem clause1761 : Type2.RUP.trueClause a (checkedClause row1761) :=
  group104 a assignment _ (by decide +kernel)

include assignment in
private theorem group105 (c : SignClause) (hc : c ∈ pluckerAt [4, 6] [2, 3, 5, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1764 : List Int := [57, -70, 62, 68, 64, -66]
include assignment in
private theorem clause1764 : Type2.RUP.trueClause a (checkedClause row1764) :=
  group105 a assignment _ (by decide +kernel)

private def row1765 : List Int := [57, -70, 62, 68, -64, 66]
include assignment in
private theorem clause1765 : Type2.RUP.trueClause a (checkedClause row1765) :=
  group105 a assignment _ (by decide +kernel)

private def row1766 : List Int := [57, -70, -62, -68, 64, -66]
include assignment in
private theorem clause1766 : Type2.RUP.trueClause a (checkedClause row1766) :=
  group105 a assignment _ (by decide +kernel)

private def row1769 : List Int := [57, 70, 62, -68, -64, -66]
include assignment in
private theorem clause1769 : Type2.RUP.trueClause a (checkedClause row1769) :=
  group105 a assignment _ (by decide +kernel)

private def row1770 : List Int := [57, 70, -62, 68, 64, 66]
include assignment in
private theorem clause1770 : Type2.RUP.trueClause a (checkedClause row1770) :=
  group105 a assignment _ (by decide +kernel)

private def row1771 : List Int := [57, 70, -62, 68, -64, -66]
include assignment in
private theorem clause1771 : Type2.RUP.trueClause a (checkedClause row1771) :=
  group105 a assignment _ (by decide +kernel)

private def row1773 : List Int := [-57, -70, 62, -68, -64, -66]
include assignment in
private theorem clause1773 : Type2.RUP.trueClause a (checkedClause row1773) :=
  group105 a assignment _ (by decide +kernel)

private def row1774 : List Int := [-57, -70, -62, 68, 64, 66]
include assignment in
private theorem clause1774 : Type2.RUP.trueClause a (checkedClause row1774) :=
  group105 a assignment _ (by decide +kernel)

private def row1776 : List Int := [-57, 70, 62, 68, 64, -66]
include assignment in
private theorem clause1776 : Type2.RUP.trueClause a (checkedClause row1776) :=
  group105 a assignment _ (by decide +kernel)

private def row1778 : List Int := [-57, 70, -62, -68, 64, -66]
include assignment in
private theorem clause1778 : Type2.RUP.trueClause a (checkedClause row1778) :=
  group105 a assignment _ (by decide +kernel)

include assignment in
private theorem group106 (c : SignClause) (hc : c ∈ pluckerAt [4, 7] [1, 2, 3, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1780 : List Int := [42, -67, -48, -63, -53, 58]
include assignment in
private theorem clause1780 : Type2.RUP.trueClause a (checkedClause row1780) :=
  group106 a assignment _ (by decide +kernel)

private def row1786 : List Int := [42, 67, 48, -63, -53, -58]
include assignment in
private theorem clause1786 : Type2.RUP.trueClause a (checkedClause row1786) :=
  group106 a assignment _ (by decide +kernel)

private def row1788 : List Int := [-42, -67, -48, 63, -53, -58]
include assignment in
private theorem clause1788 : Type2.RUP.trueClause a (checkedClause row1788) :=
  group106 a assignment _ (by decide +kernel)

private def row1793 : List Int := [-42, 67, -48, -63, 53, -58]
include assignment in
private theorem clause1793 : Type2.RUP.trueClause a (checkedClause row1793) :=
  group106 a assignment _ (by decide +kernel)

include assignment in
private theorem group107 (c : SignClause) (hc : c ∈ pluckerAt [4, 7] [1, 2, 3, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1796 : List Int := [42, -68, -48, -64, -54, 58]
include assignment in
private theorem clause1796 : Type2.RUP.trueClause a (checkedClause row1796) :=
  group107 a assignment _ (by decide +kernel)

private def row1797 : List Int := [42, -68, -48, -64, 54, -58]
include assignment in
private theorem clause1797 : Type2.RUP.trueClause a (checkedClause row1797) :=
  group107 a assignment _ (by decide +kernel)

private def row1800 : List Int := [42, 68, -48, 64, -54, -58]
include assignment in
private theorem clause1800 : Type2.RUP.trueClause a (checkedClause row1800) :=
  group107 a assignment _ (by decide +kernel)

private def row1808 : List Int := [-42, 68, -48, -64, -54, 58]
include assignment in
private theorem clause1808 : Type2.RUP.trueClause a (checkedClause row1808) :=
  group107 a assignment _ (by decide +kernel)

private def row1810 : List Int := [-42, 68, 48, 64, -54, 58]
include assignment in
private theorem clause1810 : Type2.RUP.trueClause a (checkedClause row1810) :=
  group107 a assignment _ (by decide +kernel)

include assignment in
private theorem group108 (c : SignClause) (hc : c ∈ pluckerAt [4, 7] [1, 2, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1812 : List Int := [42, 70, 53, -64, -54, -63]
include assignment in
private theorem clause1812 : Type2.RUP.trueClause a (checkedClause row1812) :=
  group108 a assignment _ (by decide +kernel)

private def row1815 : List Int := [42, 70, -53, 64, 54, 63]
include assignment in
private theorem clause1815 : Type2.RUP.trueClause a (checkedClause row1815) :=
  group108 a assignment _ (by decide +kernel)

private def row1816 : List Int := [42, -70, 53, 64, -54, 63]
include assignment in
private theorem clause1816 : Type2.RUP.trueClause a (checkedClause row1816) :=
  group108 a assignment _ (by decide +kernel)

private def row1817 : List Int := [42, -70, 53, 64, 54, -63]
include assignment in
private theorem clause1817 : Type2.RUP.trueClause a (checkedClause row1817) :=
  group108 a assignment _ (by decide +kernel)

private def row1827 : List Int := [-42, -70, -53, 64, 54, 63]
include assignment in
private theorem clause1827 : Type2.RUP.trueClause a (checkedClause row1827) :=
  group108 a assignment _ (by decide +kernel)

include assignment in
private theorem group109 (c : SignClause) (hc : c ∈ pluckerAt [4, 7] [1, 3, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1829 : List Int := [48, 70, 53, -68, 54, 67]
include assignment in
private theorem clause1829 : Type2.RUP.trueClause a (checkedClause row1829) :=
  group109 a assignment _ (by decide +kernel)

private def row1830 : List Int := [48, 70, -53, 68, -54, -67]
include assignment in
private theorem clause1830 : Type2.RUP.trueClause a (checkedClause row1830) :=
  group109 a assignment _ (by decide +kernel)

private def row1831 : List Int := [48, 70, -53, 68, 54, 67]
include assignment in
private theorem clause1831 : Type2.RUP.trueClause a (checkedClause row1831) :=
  group109 a assignment _ (by decide +kernel)

private def row1832 : List Int := [48, -70, 53, 68, -54, 67]
include assignment in
private theorem clause1832 : Type2.RUP.trueClause a (checkedClause row1832) :=
  group109 a assignment _ (by decide +kernel)

private def row1835 : List Int := [48, -70, -53, -68, 54, -67]
include assignment in
private theorem clause1835 : Type2.RUP.trueClause a (checkedClause row1835) :=
  group109 a assignment _ (by decide +kernel)

private def row1837 : List Int := [-48, 70, 53, 68, 54, -67]
include assignment in
private theorem clause1837 : Type2.RUP.trueClause a (checkedClause row1837) :=
  group109 a assignment _ (by decide +kernel)

private def row1840 : List Int := [-48, -70, 53, -68, -54, -67]
include assignment in
private theorem clause1840 : Type2.RUP.trueClause a (checkedClause row1840) :=
  group109 a assignment _ (by decide +kernel)

private def row1841 : List Int := [-48, -70, 53, -68, 54, 67]
include assignment in
private theorem clause1841 : Type2.RUP.trueClause a (checkedClause row1841) :=
  group109 a assignment _ (by decide +kernel)

include assignment in
private theorem group110 (c : SignClause) (hc : c ∈ pluckerAt [4, 7] [2, 3, 5, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1844 : List Int := [58, 70, 63, -68, -64, -67]
include assignment in
private theorem clause1844 : Type2.RUP.trueClause a (checkedClause row1844) :=
  group110 a assignment _ (by decide +kernel)

private def row1847 : List Int := [58, 70, -63, 68, 64, 67]
include assignment in
private theorem clause1847 : Type2.RUP.trueClause a (checkedClause row1847) :=
  group110 a assignment _ (by decide +kernel)

private def row1848 : List Int := [58, -70, 63, 68, -64, 67]
include assignment in
private theorem clause1848 : Type2.RUP.trueClause a (checkedClause row1848) :=
  group110 a assignment _ (by decide +kernel)

private def row1854 : List Int := [-58, 70, -63, -68, -64, 67]
include assignment in
private theorem clause1854 : Type2.RUP.trueClause a (checkedClause row1854) :=
  group110 a assignment _ (by decide +kernel)

private def row1855 : List Int := [-58, 70, -63, -68, 64, -67]
include assignment in
private theorem clause1855 : Type2.RUP.trueClause a (checkedClause row1855) :=
  group110 a assignment _ (by decide +kernel)

include assignment in
private theorem group111 (c : SignClause) (hc : c ∈ pluckerAt [5, 6] [1, 2, 3, 4]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1860 : List Int := [43, 66, -49, 62, 52, 59]
include assignment in
private theorem clause1860 : Type2.RUP.trueClause a (checkedClause row1860) :=
  group111 a assignment _ (by decide +kernel)

private def row1862 : List Int := [43, 66, 49, -62, 52, 59]
include assignment in
private theorem clause1862 : Type2.RUP.trueClause a (checkedClause row1862) :=
  group111 a assignment _ (by decide +kernel)

private def row1864 : List Int := [43, -66, -49, -62, 52, -59]
include assignment in
private theorem clause1864 : Type2.RUP.trueClause a (checkedClause row1864) :=
  group111 a assignment _ (by decide +kernel)

private def row1865 : List Int := [43, -66, -49, -62, -52, 59]
include assignment in
private theorem clause1865 : Type2.RUP.trueClause a (checkedClause row1865) :=
  group111 a assignment _ (by decide +kernel)

private def row1875 : List Int := [-43, -66, 49, -62, -52, -59]
include assignment in
private theorem clause1875 : Type2.RUP.trueClause a (checkedClause row1875) :=
  group111 a assignment _ (by decide +kernel)

include assignment in
private theorem group112 (c : SignClause) (hc : c ∈ pluckerAt [5, 6] [1, 2, 3, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1880 : List Int := [43, -69, -49, -65, 55, -59]
include assignment in
private theorem clause1880 : Type2.RUP.trueClause a (checkedClause row1880) :=
  group112 a assignment _ (by decide +kernel)

private def row1887 : List Int := [-43, 69, 49, 65, -55, 59]
include assignment in
private theorem clause1887 : Type2.RUP.trueClause a (checkedClause row1887) :=
  group112 a assignment _ (by decide +kernel)

private def row1888 : List Int := [-43, -69, -49, 65, 55, 59]
include assignment in
private theorem clause1888 : Type2.RUP.trueClause a (checkedClause row1888) :=
  group112 a assignment _ (by decide +kernel)

private def row1889 : List Int := [-43, -69, -49, 65, -55, -59]
include assignment in
private theorem clause1889 : Type2.RUP.trueClause a (checkedClause row1889) :=
  group112 a assignment _ (by decide +kernel)

private def row1890 : List Int := [-43, -69, 49, -65, 55, 59]
include assignment in
private theorem clause1890 : Type2.RUP.trueClause a (checkedClause row1890) :=
  group112 a assignment _ (by decide +kernel)

include assignment in
private theorem group113 (c : SignClause) (hc : c ∈ pluckerAt [5, 6] [1, 2, 4, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1893 : List Int := [43, 70, -52, 65, -55, -62]
include assignment in
private theorem clause1893 : Type2.RUP.trueClause a (checkedClause row1893) :=
  group113 a assignment _ (by decide +kernel)

private def row1896 : List Int := [43, -70, -52, -65, 55, -62]
include assignment in
private theorem clause1896 : Type2.RUP.trueClause a (checkedClause row1896) :=
  group113 a assignment _ (by decide +kernel)

private def row1899 : List Int := [43, -70, 52, 65, -55, 62]
include assignment in
private theorem clause1899 : Type2.RUP.trueClause a (checkedClause row1899) :=
  group113 a assignment _ (by decide +kernel)

private def row1900 : List Int := [-43, 70, -52, -65, 55, -62]
include assignment in
private theorem clause1900 : Type2.RUP.trueClause a (checkedClause row1900) :=
  group113 a assignment _ (by decide +kernel)

private def row1904 : List Int := [-43, -70, -52, 65, 55, 62]
include assignment in
private theorem clause1904 : Type2.RUP.trueClause a (checkedClause row1904) :=
  group113 a assignment _ (by decide +kernel)

private def row1906 : List Int := [-43, -70, 52, -65, 55, 62]
include assignment in
private theorem clause1906 : Type2.RUP.trueClause a (checkedClause row1906) :=
  group113 a assignment _ (by decide +kernel)

include assignment in
private theorem group114 (c : SignClause) (hc : c ∈ pluckerAt [5, 6] [1, 3, 4, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1908 : List Int := [49, 70, -52, 69, 55, 66]
include assignment in
private theorem clause1908 : Type2.RUP.trueClause a (checkedClause row1908) :=
  group114 a assignment _ (by decide +kernel)

private def row1909 : List Int := [49, 70, -52, 69, -55, -66]
include assignment in
private theorem clause1909 : Type2.RUP.trueClause a (checkedClause row1909) :=
  group114 a assignment _ (by decide +kernel)

private def row1911 : List Int := [49, 70, 52, -69, -55, -66]
include assignment in
private theorem clause1911 : Type2.RUP.trueClause a (checkedClause row1911) :=
  group114 a assignment _ (by decide +kernel)

private def row1912 : List Int := [49, -70, -52, -69, 55, -66]
include assignment in
private theorem clause1912 : Type2.RUP.trueClause a (checkedClause row1912) :=
  group114 a assignment _ (by decide +kernel)

private def row1915 : List Int := [49, -70, 52, 69, -55, 66]
include assignment in
private theorem clause1915 : Type2.RUP.trueClause a (checkedClause row1915) :=
  group114 a assignment _ (by decide +kernel)

private def row1916 : List Int := [-49, 70, -52, -69, 55, -66]
include assignment in
private theorem clause1916 : Type2.RUP.trueClause a (checkedClause row1916) :=
  group114 a assignment _ (by decide +kernel)

private def row1920 : List Int := [-49, -70, -52, 69, 55, 66]
include assignment in
private theorem clause1920 : Type2.RUP.trueClause a (checkedClause row1920) :=
  group114 a assignment _ (by decide +kernel)

private def row1922 : List Int := [-49, -70, 52, -69, 55, 66]
include assignment in
private theorem clause1922 : Type2.RUP.trueClause a (checkedClause row1922) :=
  group114 a assignment _ (by decide +kernel)

private def row1923 : List Int := [-49, -70, 52, -69, -55, -66]
include assignment in
private theorem clause1923 : Type2.RUP.trueClause a (checkedClause row1923) :=
  group114 a assignment _ (by decide +kernel)

include assignment in
private theorem group115 (c : SignClause) (hc : c ∈ pluckerAt [5, 6] [2, 3, 4, 7]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1924 : List Int := [59, 70, -62, 69, 65, 66]
include assignment in
private theorem clause1924 : Type2.RUP.trueClause a (checkedClause row1924) :=
  group115 a assignment _ (by decide +kernel)

private def row1928 : List Int := [59, -70, -62, -69, 65, -66]
include assignment in
private theorem clause1928 : Type2.RUP.trueClause a (checkedClause row1928) :=
  group115 a assignment _ (by decide +kernel)

private def row1931 : List Int := [59, -70, 62, 69, -65, 66]
include assignment in
private theorem clause1931 : Type2.RUP.trueClause a (checkedClause row1931) :=
  group115 a assignment _ (by decide +kernel)

private def row1932 : List Int := [-59, 70, -62, -69, 65, -66]
include assignment in
private theorem clause1932 : Type2.RUP.trueClause a (checkedClause row1932) :=
  group115 a assignment _ (by decide +kernel)

private def row1934 : List Int := [-59, 70, 62, 69, 65, -66]
include assignment in
private theorem clause1934 : Type2.RUP.trueClause a (checkedClause row1934) :=
  group115 a assignment _ (by decide +kernel)

private def row1938 : List Int := [-59, -70, 62, -69, 65, 66]
include assignment in
private theorem clause1938 : Type2.RUP.trueClause a (checkedClause row1938) :=
  group115 a assignment _ (by decide +kernel)

private def row1939 : List Int := [-59, -70, 62, -69, -65, -66]
include assignment in
private theorem clause1939 : Type2.RUP.trueClause a (checkedClause row1939) :=
  group115 a assignment _ (by decide +kernel)

include assignment in
private theorem group116 (c : SignClause) (hc : c ∈ pluckerAt [5, 7] [1, 2, 3, 4]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1952 : List Int := [-44, -67, -50, 63, 53, 60]
include assignment in
private theorem clause1952 : Type2.RUP.trueClause a (checkedClause row1952) :=
  group116 a assignment _ (by decide +kernel)

include assignment in
private theorem group117 (c : SignClause) (hc : c ∈ pluckerAt [5, 7] [1, 2, 3, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1957 : List Int := [44, -69, -50, -65, 55, -60]
include assignment in
private theorem clause1957 : Type2.RUP.trueClause a (checkedClause row1957) :=
  group117 a assignment _ (by decide +kernel)

include assignment in
private theorem group118 (c : SignClause) (hc : c ∈ pluckerAt [5, 7] [1, 2, 4, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1978 : List Int := [44, 70, 53, -65, -55, -63]
include assignment in
private theorem clause1978 : Type2.RUP.trueClause a (checkedClause row1978) :=
  group118 a assignment _ (by decide +kernel)

private def row1979 : List Int := [44, 70, 53, -65, 55, 63]
include assignment in
private theorem clause1979 : Type2.RUP.trueClause a (checkedClause row1979) :=
  group118 a assignment _ (by decide +kernel)

private def row1980 : List Int := [-44, -70, -53, 65, -55, -63]
include assignment in
private theorem clause1980 : Type2.RUP.trueClause a (checkedClause row1980) :=
  group118 a assignment _ (by decide +kernel)

private def row1981 : List Int := [-44, -70, -53, 65, 55, 63]
include assignment in
private theorem clause1981 : Type2.RUP.trueClause a (checkedClause row1981) :=
  group118 a assignment _ (by decide +kernel)

private def row1985 : List Int := [-44, 70, -53, -65, 55, -63]
include assignment in
private theorem clause1985 : Type2.RUP.trueClause a (checkedClause row1985) :=
  group118 a assignment _ (by decide +kernel)

include assignment in
private theorem group119 (c : SignClause) (hc : c ∈ pluckerAt [5, 7] [1, 3, 4, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row1989 : List Int := [50, -70, -53, -69, 55, -67]
include assignment in
private theorem clause1989 : Type2.RUP.trueClause a (checkedClause row1989) :=
  group119 a assignment _ (by decide +kernel)

private def row1997 : List Int := [-50, -70, -53, 69, 55, 67]
include assignment in
private theorem clause1997 : Type2.RUP.trueClause a (checkedClause row1997) :=
  group119 a assignment _ (by decide +kernel)

private def row1998 : List Int := [-50, -70, 53, -69, -55, -67]
include assignment in
private theorem clause1998 : Type2.RUP.trueClause a (checkedClause row1998) :=
  group119 a assignment _ (by decide +kernel)

include assignment in
private theorem group120 (c : SignClause) (hc : c ∈ pluckerAt [5, 7] [2, 3, 4, 6]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row2010 : List Int := [60, 70, 63, -69, -65, -67]
include assignment in
private theorem clause2010 : Type2.RUP.trueClause a (checkedClause row2010) :=
  group120 a assignment _ (by decide +kernel)

private def row2014 : List Int := [-60, -70, 63, -69, -65, -67]
include assignment in
private theorem clause2014 : Type2.RUP.trueClause a (checkedClause row2014) :=
  group120 a assignment _ (by decide +kernel)

private def row2016 : List Int := [-60, 70, -63, -69, -65, 67]
include assignment in
private theorem clause2016 : Type2.RUP.trueClause a (checkedClause row2016) :=
  group120 a assignment _ (by decide +kernel)

private def row2017 : List Int := [-60, 70, -63, -69, 65, -67]
include assignment in
private theorem clause2017 : Type2.RUP.trueClause a (checkedClause row2017) :=
  group120 a assignment _ (by decide +kernel)

private def row2018 : List Int := [-60, 70, 63, 69, -65, 67]
include assignment in
private theorem clause2018 : Type2.RUP.trueClause a (checkedClause row2018) :=
  group120 a assignment _ (by decide +kernel)

include assignment in
private theorem group121 (c : SignClause) (hc : c ∈ pluckerAt [6, 7] [1, 2, 3, 4]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row2021 : List Int := [45, 68, -51, 64, -54, -61]
include assignment in
private theorem clause2021 : Type2.RUP.trueClause a (checkedClause row2021) :=
  group121 a assignment _ (by decide +kernel)

private def row2022 : List Int := [45, 68, 51, -64, 54, 61]
include assignment in
private theorem clause2022 : Type2.RUP.trueClause a (checkedClause row2022) :=
  group121 a assignment _ (by decide +kernel)

private def row2029 : List Int := [-45, 68, -51, -64, -54, 61]
include assignment in
private theorem clause2029 : Type2.RUP.trueClause a (checkedClause row2029) :=
  group121 a assignment _ (by decide +kernel)

private def row2032 : List Int := [-45, -68, -51, 64, 54, 61]
include assignment in
private theorem clause2032 : Type2.RUP.trueClause a (checkedClause row2032) :=
  group121 a assignment _ (by decide +kernel)

private def row2033 : List Int := [-45, -68, -51, 64, -54, -61]
include assignment in
private theorem clause2033 : Type2.RUP.trueClause a (checkedClause row2033) :=
  group121 a assignment _ (by decide +kernel)

private def row2034 : List Int := [-45, -68, 51, -64, 54, 61]
include assignment in
private theorem clause2034 : Type2.RUP.trueClause a (checkedClause row2034) :=
  group121 a assignment _ (by decide +kernel)

include assignment in
private theorem group122 (c : SignClause) (hc : c ∈ pluckerAt [6, 7] [1, 2, 3, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row2042 : List Int := [45, -69, 51, 65, 55, -61]
include assignment in
private theorem clause2042 : Type2.RUP.trueClause a (checkedClause row2042) :=
  group122 a assignment _ (by decide +kernel)

private def row2043 : List Int := [45, -69, 51, 65, -55, 61]
include assignment in
private theorem clause2043 : Type2.RUP.trueClause a (checkedClause row2043) :=
  group122 a assignment _ (by decide +kernel)

private def row2045 : List Int := [-45, 69, -51, -65, -55, 61]
include assignment in
private theorem clause2045 : Type2.RUP.trueClause a (checkedClause row2045) :=
  group122 a assignment _ (by decide +kernel)

private def row2046 : List Int := [-45, 69, 51, 65, 55, -61]
include assignment in
private theorem clause2046 : Type2.RUP.trueClause a (checkedClause row2046) :=
  group122 a assignment _ (by decide +kernel)

private def row2049 : List Int := [-45, -69, -51, 65, -55, -61]
include assignment in
private theorem clause2049 : Type2.RUP.trueClause a (checkedClause row2049) :=
  group122 a assignment _ (by decide +kernel)

private def row2050 : List Int := [-45, -69, 51, -65, 55, 61]
include assignment in
private theorem clause2050 : Type2.RUP.trueClause a (checkedClause row2050) :=
  group122 a assignment _ (by decide +kernel)

include assignment in
private theorem group123 (c : SignClause) (hc : c ∈ pluckerAt [6, 7] [1, 2, 4, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row2058 : List Int := [45, -70, 54, 65, 55, -64]
include assignment in
private theorem clause2058 : Type2.RUP.trueClause a (checkedClause row2058) :=
  group123 a assignment _ (by decide +kernel)

private def row2066 : List Int := [-45, -70, 54, -65, 55, 64]
include assignment in
private theorem clause2066 : Type2.RUP.trueClause a (checkedClause row2066) :=
  group123 a assignment _ (by decide +kernel)

include assignment in
private theorem group124 (c : SignClause) (hc : c ∈ pluckerAt [6, 7] [1, 3, 4, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row2071 : List Int := [51, 70, 54, -69, -55, -68]
include assignment in
private theorem clause2071 : Type2.RUP.trueClause a (checkedClause row2071) :=
  group124 a assignment _ (by decide +kernel)

private def row2072 : List Int := [51, -70, -54, -69, 55, -68]
include assignment in
private theorem clause2072 : Type2.RUP.trueClause a (checkedClause row2072) :=
  group124 a assignment _ (by decide +kernel)

private def row2073 : List Int := [51, -70, -54, -69, -55, 68]
include assignment in
private theorem clause2073 : Type2.RUP.trueClause a (checkedClause row2073) :=
  group124 a assignment _ (by decide +kernel)

private def row2080 : List Int := [-51, -70, -54, 69, 55, 68]
include assignment in
private theorem clause2080 : Type2.RUP.trueClause a (checkedClause row2080) :=
  group124 a assignment _ (by decide +kernel)

include assignment in
private theorem group125 (c : SignClause) (hc : c ∈ pluckerAt [6, 7] [2, 3, 4, 5]) :
    Type2.RUP.trueClause a c :=
  assignment c (plucker_mem (by decide +kernel) (by decide +kernel) hc)

private def row2088 : List Int := [61, -70, -64, -69, 65, -68]
include assignment in
private theorem clause2088 : Type2.RUP.trueClause a (checkedClause row2088) :=
  group125 a assignment _ (by decide +kernel)

private def row2094 : List Int := [-61, 70, 64, 69, 65, -68]
include assignment in
private theorem clause2094 : Type2.RUP.trueClause a (checkedClause row2094) :=
  group125 a assignment _ (by decide +kernel)

private def row2098 : List Int := [-61, -70, 64, -69, 65, 68]
include assignment in
private theorem clause2098 : Type2.RUP.trueClause a (checkedClause row2098) :=
  group125 a assignment _ (by decide +kernel)

private def row2099 : List Int := [-61, -70, 64, -69, -65, -68]
include assignment in
private theorem clause2099 : Type2.RUP.trueClause a (checkedClause row2099) :=
  group125 a assignment _ (by decide +kernel)

-- Each deduction checks its own displayed list of predecessors.

private def row2100 : List Int := [-61, 59, -69, -65]
include assignment in
private theorem clause2100 : Type2.RUP.trueClause a (checkedClause row2100) := by
  apply Type2.RUP.derive (premises := [row363, row366]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause363 a assignment, clause366 a assignment⟩

private def row2101 : List Int := [61, 57, -68, -64]
include assignment in
private theorem clause2101 : Type2.RUP.trueClause a (checkedClause row2101) := by
  apply Type2.RUP.derive (premises := [row345, row351]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause345 a assignment, clause351 a assignment⟩

private def row2102 : List Int := [62, -64, -65, -66, -68, -69, -70]
include assignment in
private theorem clause2102 : Type2.RUP.trueClause a (checkedClause row2102) := by
  apply Type2.RUP.derive (premises := [row1773, row1939, row2100, row2101]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1773 a assignment, clause1939 a assignment, clause2100 a assignment,
    clause2101 a assignment⟩

private def row2103 : List Int := [-62, -64, -70, -65]
include assignment in
private theorem clause2103 : Type2.RUP.trueClause a (checkedClause row2103) := by
  apply Type2.RUP.derive (premises := [row384, row392]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause384 a assignment, clause392 a assignment⟩

private def row2104 : List Int := [-64, -65, -70, -66, -68, -69]
include assignment in
private theorem clause2104 : Type2.RUP.trueClause a (checkedClause row2104) := by
  apply Type2.RUP.derive (premises := [row2102, row2103]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2102 a assignment, clause2103 a assignment⟩

private def row2105 : List Int := [-53, -54, -55, -66, -67, -68, -69, -70]
include assignment in
private theorem clause2105 : Type2.RUP.trueClause a (checkedClause row2105) := by
  apply Type2.RUP.derive (premises := [row286, row1683, row1757, row1923, row208]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause286 a assignment, clause1683 a assignment, clause1757 a assignment,
    clause1923 a assignment, clause208 a assignment⟩

private def row2106 : List Int := [48, -42, -58, -39]
include assignment in
private theorem clause2106 : Type2.RUP.trueClause a (checkedClause row2106) := by
  apply Type2.RUP.derive (premises := [row48, row56]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause48 a assignment, clause56 a assignment⟩

private def row2107 : List Int := [-54, -55, -62, -65, -66, -67, -68, -69, -70]
include assignment in
private theorem clause2107 : Type2.RUP.trueClause a (checkedClause row2107) := by
  apply Type2.RUP.derive (premises := [row2105, row292, row1757, row1923, row208, row214]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2105 a assignment, clause292 a assignment, clause1757 a assignment,
    clause1923 a assignment, clause208 a assignment, clause214 a assignment⟩

private def row2108 : List Int := [-41, -42, 64, 54]
include assignment in
private theorem clause2108 : Type2.RUP.trueClause a (checkedClause row2108) := by
  apply Type2.RUP.derive (premises := [row162, row167]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause162 a assignment, clause167 a assignment⟩

private def row2109 : List Int := [-42, 54, -55, 63, -62, 64, -70]
include assignment in
private theorem clause2109 : Type2.RUP.trueClause a (checkedClause row2109) := by
  apply Type2.RUP.derive (premises := [row2108, row165, row173]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2108 a assignment, clause165 a assignment, clause173 a assignment⟩

private def row2110 : List Int := [-40, 53, 63, 42]
include assignment in
private theorem clause2110 : Type2.RUP.trueClause a (checkedClause row2110) := by
  apply Type2.RUP.derive (premises := [row142, row150]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause142 a assignment, clause150 a assignment⟩

private def row2111 : List Int := [53, -41, 42, 54, -55, 63, -70]
include assignment in
private theorem clause2111 : Type2.RUP.trueClause a (checkedClause row2111) := by
  apply Type2.RUP.derive (premises := [row284, row639, row2110]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause284 a assignment, clause639 a assignment, clause2110 a assignment⟩

private def row2112 : List Int := [-53, 54, -70, -55]
include assignment in
private theorem clause2112 : Type2.RUP.trueClause a (checkedClause row2112) := by
  apply Type2.RUP.derive (premises := [row283, row291]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause283 a assignment, clause291 a assignment⟩

private def row2113 : List Int := [54, -55, -70, 63, -62, 64]
include assignment in
private theorem clause2113 : Type2.RUP.trueClause a (checkedClause row2113) := by
  apply Type2.RUP.derive (premises := [row2109, row2112, row284, row1658, row2110]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2109 a assignment, clause2112 a assignment, clause284 a assignment,
    clause1658 a assignment, clause2110 a assignment⟩

private def row2114 : List Int := [-55, -62, -65, -66, -67, -68, -69, -70]
include assignment in
private theorem clause2114 : Type2.RUP.trueClause a (checkedClause row2114) := by
  apply Type2.RUP.derive (premises := [row2103, row2107, row2113, row383]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2103 a assignment, clause2107 a assignment, clause2113 a assignment,
    clause383 a assignment⟩

private def row2115 : List Int := [53, 54, -70, 55]
include assignment in
private theorem clause2115 : Type2.RUP.trueClause a (checkedClause row2115) := by
  apply Type2.RUP.derive (premises := [row288, row294]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause288 a assignment, clause294 a assignment⟩

private def row2116 : List Int := [-49, 37, -59, -43]
include assignment in
private theorem clause2116 : Type2.RUP.trueClause a (checkedClause row2116) := by
  apply Type2.RUP.derive (premises := [row63, row66]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause63 a assignment, clause66 a assignment⟩

private def row2117 : List Int := [-52, -53, 55, -59, -56, 63, -62, -65, -66, -69, -70]
include assignment in
private theorem clause2117 : Type2.RUP.trueClause a (checkedClause row2117) := by
  apply Type2.RUP.derive (premises := [row1665, row1896, row1912, row2116, row1061]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1665 a assignment, clause1896 a assignment, clause1912 a assignment,
    clause2116 a assignment, clause1061 a assignment⟩

private def row2118 : List Int := [37, 36, -56, 46]
include assignment in
private theorem clause2118 : Type2.RUP.trueClause a (checkedClause row2118) := by
  apply Type2.RUP.derive (premises := [row6, row18]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause6 a assignment, clause18 a assignment⟩

private def row2119 : List Int := [-37, 36, 46, -56]
include assignment in
private theorem clause2119 : Type2.RUP.trueClause a (checkedClause row2119) := by
  apply Type2.RUP.derive (premises := [row3, row8]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause3 a assignment, clause8 a assignment⟩

private def row2120 : List Int := [36, 46, -56]
include assignment in
private theorem clause2120 : Type2.RUP.trueClause a (checkedClause row2120) := by
  apply Type2.RUP.derive (premises := [row2118, row2119]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2118 a assignment, clause2119 a assignment⟩

private def row2121 : List Int := [54, 55, -58, -57, -62, 64, -65, -66, -67, -69, -70]
include assignment in
private theorem clause2121 : Type2.RUP.trueClause a (checkedClause row2121) := by
  apply Type2.RUP.derive (premises := [row383, row403, row1054, row2014, row2066, row2099, row2115, row305, row1827, row1835, row1989, row2117,
    row1237, row1683, row2120, row521, row924]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause383 a assignment, clause403 a assignment, clause1054 a assignment,
    clause2014 a assignment, clause2066 a assignment, clause2099 a assignment,
    clause2115 a assignment, clause305 a assignment, clause1827 a assignment,
    clause1835 a assignment, clause1989 a assignment, clause2117 a assignment,
    clause1237 a assignment, clause1683 a assignment, clause2120 a assignment,
    clause521 a assignment, clause924 a assignment⟩

private def row2122 : List Int := [-49, -51, -69, 55]
include assignment in
private theorem clause2122 : Type2.RUP.trueClause a (checkedClause row2122) := by
  apply Type2.RUP.derive (premises := [row261, row276]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause261 a assignment, clause276 a assignment⟩

private def row2123 : List Int := [49, -51, -69, 55]
include assignment in
private theorem clause2123 : Type2.RUP.trueClause a (checkedClause row2123) := by
  apply Type2.RUP.derive (premises := [row268, row278]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause268 a assignment, clause278 a assignment⟩

private def row2124 : List Int := [-51, 55, -69]
include assignment in
private theorem clause2124 : Type2.RUP.trueClause a (checkedClause row2124) := by
  apply Type2.RUP.derive (premises := [row2122, row2123]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2122 a assignment, clause2123 a assignment⟩

private def row2125 : List Int := [-54, 55, -70, -69, -68]
include assignment in
private theorem clause2125 : Type2.RUP.trueClause a (checkedClause row2125) := by
  apply Type2.RUP.derive (premises := [row2072, row2122, row2123]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2072 a assignment, clause2122 a assignment, clause2123 a assignment⟩

private def row2126 : List Int := [-62, -65, -66, -67, -68, -69, -70]
include assignment in
private theorem clause2126 : Type2.RUP.trueClause a (checkedClause row2126) := by
  apply Type2.RUP.derive (premises := [row2103, row2114, row2125, row383, row1688, row1766, row2014, row2121, row334]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2103 a assignment, clause2114 a assignment, clause2125 a assignment,
    clause383 a assignment, clause1688 a assignment, clause1766 a assignment,
    clause2014 a assignment, clause2121 a assignment, clause334 a assignment⟩

private def row2127 : List Int := [-57, 59, -66, 62]
include assignment in
private theorem clause2127 : Type2.RUP.trueClause a (checkedClause row2127) := by
  apply Type2.RUP.derive (premises := [row303, row308]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause303 a assignment, clause308 a assignment⟩

private def row2128 : List Int := [43, -37, 59, 49]
include assignment in
private theorem clause2128 : Type2.RUP.trueClause a (checkedClause row2128) := by
  apply Type2.RUP.derive (premises := [row62, row67]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause62 a assignment, clause67 a assignment⟩

private def row2129 : List Int := [49, -50, 55, 60, 59, -65, -69]
include assignment in
private theorem clause2129 : Type2.RUP.trueClause a (checkedClause row2129) := by
  apply Type2.RUP.derive (premises := [row1419, row1890, row2128]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1419 a assignment, clause1890 a assignment, clause2128 a assignment⟩

private def row2130 : List Int := [55, -65, -66, -67, -68, -69, -70]
include assignment in
private theorem clause2130 : Type2.RUP.trueClause a (checkedClause row2130) := by
  apply Type2.RUP.derive (premises := [row2104, row2124, row2125, row2126, row391, row1939, row2014, row2099, row2115, row2127, row1989, row2129,
    row1502, row1518, row1728, row29, row37]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2104 a assignment, clause2124 a assignment, clause2125 a assignment,
    clause2126 a assignment, clause391 a assignment, clause1939 a assignment,
    clause2014 a assignment, clause2099 a assignment, clause2115 a assignment,
    clause2127 a assignment, clause1989 a assignment, clause2129 a assignment,
    clause1502 a assignment, clause1518 a assignment, clause1728 a assignment,
    clause29 a assignment, clause37 a assignment⟩

private def row2131 : List Int := [-53, -52, -55, -70]
include assignment in
private theorem clause2131 : Type2.RUP.trueClause a (checkedClause row2131) := by
  apply Type2.RUP.derive (premises := [row283, row286]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause283 a assignment, clause286 a assignment⟩

private def row2132 : List Int := [53, -52, -70, -55]
include assignment in
private theorem clause2132 : Type2.RUP.trueClause a (checkedClause row2132) := by
  apply Type2.RUP.derive (premises := [row284, row292]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause284 a assignment, clause292 a assignment⟩

private def row2133 : List Int := [-52, -55, -70]
include assignment in
private theorem clause2133 : Type2.RUP.trueClause a (checkedClause row2133) := by
  apply Type2.RUP.derive (premises := [row2131, row2132]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2131 a assignment, clause2132 a assignment⟩

private def row2134 : List Int := [-54, 53, -55, -58, 63, 61, 64, -65, -67, -68, -70]
include assignment in
private theorem clause2134 : Type2.RUP.trueClause a (checkedClause row2134) := by
  apply Type2.RUP.derive (premises := [row1816, row1840, row2106, row41, row58]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1816 a assignment, clause1840 a assignment, clause2106 a assignment,
    clause41 a assignment, clause58 a assignment⟩

private def row2135 : List Int := [41, -42, 64, 54]
include assignment in
private theorem clause2135 : Type2.RUP.trueClause a (checkedClause row2135) := by
  apply Type2.RUP.derive (premises := [row165, row173]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause165 a assignment, clause173 a assignment⟩

private def row2136 : List Int := [-42, 54, 64]
include assignment in
private theorem clause2136 : Type2.RUP.trueClause a (checkedClause row2136) := by
  apply Type2.RUP.derive (premises := [row2108, row2135]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2108 a assignment, clause2135 a assignment⟩

private def row2137 : List Int := [53, 49, -55, 59, 62, 61, 64, -65, -66, -67, -68, -70]
include assignment in
private theorem clause2137 : Type2.RUP.trueClause a (checkedClause row2137) := by
  apply Type2.RUP.derive (premises := [row391, row2127, row2132, row314, row348, row2134, row2136, row2110, row2111, row127, row1006, row1065,
    row1140, row9, row29, row208]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause391 a assignment, clause2127 a assignment, clause2132 a assignment,
    clause314 a assignment, clause348 a assignment, clause2134 a assignment,
    clause2136 a assignment, clause2110 a assignment, clause2111 a assignment,
    clause127 a assignment, clause1006 a assignment, clause1065 a assignment,
    clause1140 a assignment, clause9 a assignment, clause29 a assignment,
    clause208 a assignment⟩

private def row2138 : List Int := [-65, -66, -67, -68, -69, -70]
include assignment in
private theorem clause2138 : Type2.RUP.trueClause a (checkedClause row2138) := by
  apply Type2.RUP.derive (premises := [row2104, row2126, row2130, row2133, row1923, row1939, row2099, row2137, row291, row2105]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2104 a assignment, clause2126 a assignment, clause2130 a assignment,
    clause2133 a assignment, clause1923 a assignment, clause1939 a assignment,
    clause2099 a assignment, clause2137 a assignment, clause291 a assignment,
    clause2105 a assignment⟩

private def row2139 : List Int := [-53, -55, -66, -67, -68, -69, -70]
include assignment in
private theorem clause2139 : Type2.RUP.trueClause a (checkedClause row2139) := by
  apply Type2.RUP.derive (premises := [row2105, row2112]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2105 a assignment, clause2112 a assignment⟩

private def row2140 : List Int := [48, 47, -68, -54]
include assignment in
private theorem clause2140 : Type2.RUP.trueClause a (checkedClause row2140) := by
  apply Type2.RUP.derive (premises := [row245, row248]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause245 a assignment, clause248 a assignment⟩

private def row2141 : List Int := [-54, 53, 52, -66, -67, -68, -70]
include assignment in
private theorem clause2141 : Type2.RUP.trueClause a (checkedClause row2141) := by
  apply Type2.RUP.derive (premises := [row1757, row1840, row2140]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1757 a assignment, clause1840 a assignment, clause2140 a assignment⟩

private def row2142 : List Int := [47, 49, -66, 52]
include assignment in
private theorem clause2142 : Type2.RUP.trueClause a (checkedClause row2142) := by
  apply Type2.RUP.derive (premises := [row208, row214]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause208 a assignment, clause214 a assignment⟩

private def row2143 : List Int := [59, 62, 41, 64, 61, -48, -47, 49, -66, -68]
include assignment in
private theorem clause2143 : Type2.RUP.trueClause a (checkedClause row2143) := by
  apply Type2.RUP.derive (premises := [row2127, row348, row1337, row1475, row29]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2127 a assignment, clause348 a assignment, clause1337 a assignment,
    clause1475 a assignment, clause29 a assignment⟩

private def row2144 : List Int := [-38, -43, -59, 49]
include assignment in
private theorem clause2144 : Type2.RUP.trueClause a (checkedClause row2144) := by
  apply Type2.RUP.derive (premises := [row68, row76]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause68 a assignment, clause76 a assignment⟩

private def row2145 : List Int := [61, 54, -55, 65, -66, -68, -69, -70]
include assignment in
private theorem clause2145 : Type2.RUP.trueClause a (checkedClause row2145) := by
  apply Type2.RUP.derive (premises := [row412, row2088, row2112, row2132, row2136, row1817, row1923, row1998, row2110, row2111, row2113, row2142,
    row127, row203, row234, row2143, row2144, row61, row78]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause412 a assignment, clause2088 a assignment, clause2112 a assignment,
    clause2132 a assignment, clause2136 a assignment, clause1817 a assignment,
    clause1923 a assignment, clause1998 a assignment, clause2110 a assignment,
    clause2111 a assignment, clause2113 a assignment, clause2142 a assignment,
    clause127 a assignment, clause203 a assignment, clause234 a assignment,
    clause2143 a assignment, clause2144 a assignment, clause61 a assignment,
    clause78 a assignment⟩

private def row2146 : List Int := [-59, -61, -69, 65]
include assignment in
private theorem clause2146 : Type2.RUP.trueClause a (checkedClause row2146) := by
  apply Type2.RUP.derive (premises := [row361, row376]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause361 a assignment, clause376 a assignment⟩

private def row2147 : List Int := [38, 41, 57, -47]
include assignment in
private theorem clause2147 : Type2.RUP.trueClause a (checkedClause row2147) := by
  apply Type2.RUP.derive (premises := [row29, row37]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause29 a assignment, clause37 a assignment⟩

private def row2148 : List Int := [-55, -66, -67, -68, -69, -70]
include assignment in
private theorem clause2148 : Type2.RUP.trueClause a (checkedClause row2148) := by
  apply Type2.RUP.derive (premises := [row2133, row2138, row2139, row2141, row2145, row2146, row1525, row1923, row1928, row2142, row1475, row1709,
    row2147]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2133 a assignment, clause2138 a assignment, clause2139 a assignment,
    clause2141 a assignment, clause2145 a assignment, clause2146 a assignment,
    clause1525 a assignment, clause1923 a assignment, clause1928 a assignment,
    clause2142 a assignment, clause1475 a assignment, clause1709 a assignment,
    clause2147 a assignment⟩

private def row2149 : List Int := [-57, 41, 38, -47]
include assignment in
private theorem clause2149 : Type2.RUP.trueClause a (checkedClause row2149) := by
  apply Type2.RUP.derive (premises := [row23, row24]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause23 a assignment, clause24 a assignment⟩

private def row2150 : List Int := [41, -47, 38]
include assignment in
private theorem clause2150 : Type2.RUP.trueClause a (checkedClause row2150) := by
  apply Type2.RUP.derive (premises := [row2147, row2149]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2147 a assignment, clause2149 a assignment⟩

private def row2151 : List Int := [-43, -59, 38, -49]
include assignment in
private theorem clause2151 : Type2.RUP.trueClause a (checkedClause row2151) := by
  apply Type2.RUP.derive (premises := [row66, row72]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause66 a assignment, clause72 a assignment⟩

private def row2152 : List Int := [43, 45, 65, 55]
include assignment in
private theorem clause2152 : Type2.RUP.trueClause a (checkedClause row2152) := by
  apply Type2.RUP.derive (premises := [row189, row193]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause189 a assignment, clause193 a assignment⟩

private def row2153 : List Int := [-47, 38, 54, 55, 65, -66, -69, -70]
include assignment in
private theorem clause2153 : Type2.RUP.trueClause a (checkedClause row2153) := by
  apply Type2.RUP.derive (premises := [row2124, row2150, row760, row2042, row2152, row777, row1186, row2151]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2124 a assignment, clause2150 a assignment, clause760 a assignment,
    clause2042 a assignment, clause2152 a assignment, clause777 a assignment,
    clause1186 a assignment, clause2151 a assignment⟩

private def row2154 : List Int := [47, 54, 51, -66, -68, -69, -70]
include assignment in
private theorem clause2154 : Type2.RUP.trueClause a (checkedClause row2154) := by
  apply Type2.RUP.derive (premises := [row1518, row1750, row2142]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1518 a assignment, clause1750 a assignment, clause2142 a assignment⟩

private def row2155 : List Int := [49, -47, -50, 55, -66, -67, -69, -70]
include assignment in
private theorem clause2155 : Type2.RUP.trueClause a (checkedClause row2155) := by
  apply Type2.RUP.derive (premises := [row1435, row1912, row203]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1435 a assignment, clause1912 a assignment, clause203 a assignment⟩

private def row2156 : List Int := [-45, 43, 65, 55]
include assignment in
private theorem clause2156 : Type2.RUP.trueClause a (checkedClause row2156) := by
  apply Type2.RUP.derive (premises := [row184, row187]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause184 a assignment, clause187 a assignment⟩

private def row2157 : List Int := [43, -49, -38, 51, 55, 65]
include assignment in
private theorem clause2157 : Type2.RUP.trueClause a (checkedClause row2157) := by
  apply Type2.RUP.derive (premises := [row787, row2156]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause787 a assignment, clause2156 a assignment⟩

private def row2158 : List Int := [-66, -67, -70, -68, -69]
include assignment in
private theorem clause2158 : Type2.RUP.trueClause a (checkedClause row2158) := by
  apply Type2.RUP.derive (premises := [row2138, row2148, row2124, row2125, row2154, row254, row2115, row2153, row894, row2155, row2157, row1888,
    row2116, row2146, row551, row703, row835, row2088, row2108, row2135]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2138 a assignment, clause2148 a assignment, clause2124 a assignment,
    clause2125 a assignment, clause2154 a assignment, clause254 a assignment,
    clause2115 a assignment, clause2153 a assignment, clause894 a assignment,
    clause2155 a assignment, clause2157 a assignment, clause1888 a assignment,
    clause2116 a assignment, clause2146 a assignment, clause551 a assignment,
    clause703 a assignment, clause835 a assignment, clause2088 a assignment,
    clause2108 a assignment, clause2135 a assignment⟩

private def row2159 : List Int := [-52, -46, 66, -49]
include assignment in
private theorem clause2159 : Type2.RUP.trueClause a (checkedClause row2159) := by
  apply Type2.RUP.derive (premises := [row202, row209]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause202 a assignment, clause209 a assignment⟩

private def row2160 : List Int := [-49, -50, 55, 66, -67, -69, -70]
include assignment in
private theorem clause2160 : Type2.RUP.trueClause a (checkedClause row2160) := by
  apply Type2.RUP.derive (premises := [row1441, row1922, row2159]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1441 a assignment, clause1922 a assignment, clause2159 a assignment⟩

private def row2161 : List Int := [64, -62, -70, 65]
include assignment in
private theorem clause2161 : Type2.RUP.trueClause a (checkedClause row2161) := by
  apply Type2.RUP.derive (premises := [row388, row394]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause388 a assignment, clause394 a assignment⟩

private def row2162 : List Int := [-64, -62, -70, 65]
include assignment in
private theorem clause2162 : Type2.RUP.trueClause a (checkedClause row2162) := by
  apply Type2.RUP.derive (premises := [row381, row396]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause381 a assignment, clause396 a assignment⟩

private def row2163 : List Int := [-62, 65, -70]
include assignment in
private theorem clause2163 : Type2.RUP.trueClause a (checkedClause row2163) := by
  apply Type2.RUP.derive (premises := [row2161, row2162]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2161 a assignment, clause2162 a assignment⟩

private def row2164 : List Int := [-64, 52, 65, 54, 55, -70]
include assignment in
private theorem clause2164 : Type2.RUP.trueClause a (checkedClause row2164) := by
  apply Type2.RUP.derive (premises := [row2058, row2156, row182, row190]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2058 a assignment, clause2156 a assignment, clause182 a assignment,
    clause190 a assignment⟩

private def row2165 : List Int := [-37, -43, 59, 49]
include assignment in
private theorem clause2165 : Type2.RUP.trueClause a (checkedClause row2165) := by
  apply Type2.RUP.derive (premises := [row64, row70]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause64 a assignment, clause70 a assignment⟩

private def row2166 : List Int := [-43, 65, 55, -67, -68, -69, -70]
include assignment in
private theorem clause2166 : Type2.RUP.trueClause a (checkedClause row2166) := by
  apply Type2.RUP.derive (premises := [row2124, row2125, row2158, row2163, row1904, row1922, row1938, row2115, row2164, row2165, row1508, row1835,
    row1989, row2136, row207, row664, row1386, row1419, row1659, row1780, row328]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2124 a assignment, clause2125 a assignment, clause2158 a assignment,
    clause2163 a assignment, clause1904 a assignment, clause1922 a assignment,
    clause1938 a assignment, clause2115 a assignment, clause2164 a assignment,
    clause2165 a assignment, clause1508 a assignment, clause1835 a assignment,
    clause1989 a assignment, clause2136 a assignment, clause207 a assignment,
    clause664 a assignment, clause1386 a assignment, clause1419 a assignment,
    clause1659 a assignment, clause1780 a assignment, clause328 a assignment⟩

private def row2167 : List Int := [43, 65, 55]
include assignment in
private theorem clause2167 : Type2.RUP.trueClause a (checkedClause row2167) := by
  apply Type2.RUP.derive (premises := [row2152, row2156]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2152 a assignment, clause2156 a assignment⟩

private def row2168 : List Int := [65, 55, -70, -67, -68, -69]
include assignment in
private theorem clause2168 : Type2.RUP.trueClause a (checkedClause row2168) := by
  apply Type2.RUP.derive (premises := [row2166, row2167]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2166 a assignment, clause2167 a assignment⟩

private def row2169 : List Int := [-61, -59, -69, -65]
include assignment in
private theorem clause2169 : Type2.RUP.trueClause a (checkedClause row2169) := by
  apply Type2.RUP.derive (premises := [row364, row372]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause364 a assignment, clause372 a assignment⟩

private def row2170 : List Int := [-61, -65, -69]
include assignment in
private theorem clause2170 : Type2.RUP.trueClause a (checkedClause row2170) := by
  apply Type2.RUP.derive (premises := [row2100, row2169]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2100 a assignment, clause2169 a assignment⟩

private def row2171 : List Int := [-56, -63, -67, 60]
include assignment in
private theorem clause2171 : Type2.RUP.trueClause a (checkedClause row2171) := by
  apply Type2.RUP.derive (premises := [row325, row326]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause325 a assignment, clause326 a assignment⟩

private def row2172 : List Int := [-64, 62, 60, -59, 61, -65, 66, -67, -68, -70]
include assignment in
private theorem clause2172 : Type2.RUP.trueClause a (checkedClause row2172) := by
  apply Type2.RUP.derive (premises := [row386, row2101, row2171, row307]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause386 a assignment, clause2101 a assignment, clause2171 a assignment,
    clause307 a assignment⟩

private def row2173 : List Int := [57, 62, 66, -59]
include assignment in
private theorem clause2173 : Type2.RUP.trueClause a (checkedClause row2173) := by
  apply Type2.RUP.derive (premises := [row304, row310]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause304 a assignment, clause310 a assignment⟩

private def row2174 : List Int := [62, 60, -70, -59, 61, -65, 66, -67, -68]
include assignment in
private theorem clause2174 : Type2.RUP.trueClause a (checkedClause row2174) := by
  apply Type2.RUP.derive (premises := [row2172, row2173, row307, row391, row1139]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2172 a assignment, clause2173 a assignment, clause307 a assignment,
    clause391 a assignment, clause1139 a assignment⟩

private def row2175 : List Int := [-36, -41, -38, 47]
include assignment in
private theorem clause2175 : Type2.RUP.trueClause a (checkedClause row2175) := by
  apply Type2.RUP.derive (premises := [row22, row36]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause22 a assignment, clause36 a assignment⟩

private def row2176 : List Int := [-62, -38, -59, 43, 45, -65, 47, 49, -48, -53, 54, 66, -70]
include assignment in
private theorem clause2176 : Type2.RUP.trueClause a (checkedClause row2176) := by
  apply Type2.RUP.derive (premises := [row2103, row1196, row2175, row25, row28]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2103 a assignment, clause1196 a assignment, clause2175 a assignment,
    clause25 a assignment, clause28 a assignment⟩

private def row2177 : List Int := [-59, 43, 55, -67, -68, -69, -70]
include assignment in
private theorem clause2177 : Type2.RUP.trueClause a (checkedClause row2177) := by
  apply Type2.RUP.derive (premises := [row2124, row2125, row2158, row2167, row2169, row1880, row2050, row2115, row1180, row1508, row1835, row1989,
    row2176, row2173, row2174, row307, row972, row1143, row1160, row1347, row1427, row1797, row1957, row45,
    row86]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2124 a assignment, clause2125 a assignment, clause2158 a assignment,
    clause2167 a assignment, clause2169 a assignment, clause1880 a assignment,
    clause2050 a assignment, clause2115 a assignment, clause1180 a assignment,
    clause1508 a assignment, clause1835 a assignment, clause1989 a assignment,
    clause2176 a assignment, clause2173 a assignment, clause2174 a assignment,
    clause307 a assignment, clause972 a assignment, clause1143 a assignment,
    clause1160 a assignment, clause1347 a assignment, clause1427 a assignment,
    clause1797 a assignment, clause1957 a assignment, clause45 a assignment,
    clause86 a assignment⟩

private def row2178 : List Int := [59, -65, 49, -50, 55, -69]
include assignment in
private theorem clause2178 : Type2.RUP.trueClause a (checkedClause row2178) := by
  apply Type2.RUP.derive (premises := [row2100, row2129, row371]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2100 a assignment, clause2129 a assignment, clause371 a assignment⟩

private def row2179 : List Int := [55, -67, -68, -69, -70]
include assignment in
private theorem clause2179 : Type2.RUP.trueClause a (checkedClause row2179) := by
  apply Type2.RUP.derive (premises := [row2124, row2125, row2158, row2168, row2170, row2115, row1989, row2160, row2178, row1492, row2144, row2177]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2124 a assignment, clause2125 a assignment, clause2158 a assignment,
    clause2168 a assignment, clause2170 a assignment, clause2115 a assignment,
    clause1989 a assignment, clause2160 a assignment, clause2178 a assignment,
    clause1492 a assignment, clause2144 a assignment, clause2177 a assignment⟩

private def row2180 : List Int := [-50, 49, -69, -55]
include assignment in
private theorem clause2180 : Type2.RUP.trueClause a (checkedClause row2180) := by
  apply Type2.RUP.derive (premises := [row263, row271]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause263 a assignment, clause271 a assignment⟩

private def row2181 : List Int := [46, 49, 66, 52]
include assignment in
private theorem clause2181 : Type2.RUP.trueClause a (checkedClause row2181) := by
  apply Type2.RUP.derive (premises := [row207, row213]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause207 a assignment, clause213 a assignment⟩

private def row2182 : List Int := [49, 52, -55, 66, -67, -69]
include assignment in
private theorem clause2182 : Type2.RUP.trueClause a (checkedClause row2182) := by
  apply Type2.RUP.derive (premises := [row2180, row2181, row1434]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2180 a assignment, clause2181 a assignment, clause1434 a assignment⟩

private def row2183 : List Int := [50, -49, -69, -55]
include assignment in
private theorem clause2183 : Type2.RUP.trueClause a (checkedClause row2183) := by
  apply Type2.RUP.derive (premises := [row264, row272]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause264 a assignment, clause272 a assignment⟩

private def row2184 : List Int := [37, 43, -59, -49]
include assignment in
private theorem clause2184 : Type2.RUP.trueClause a (checkedClause row2184) := by
  apply Type2.RUP.derive (premises := [row65, row71]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause65 a assignment, clause71 a assignment⟩

private def row2185 : List Int := [37, -59, -49]
include assignment in
private theorem clause2185 : Type2.RUP.trueClause a (checkedClause row2185) := by
  apply Type2.RUP.derive (premises := [row2116, row2184]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2116 a assignment, clause2184 a assignment⟩

private def row2186 : List Int := [-56, -58, -67, -60]
include assignment in
private theorem clause2186 : Type2.RUP.trueClause a (checkedClause row2186) := by
  apply Type2.RUP.derive (premises := [row328, row336]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause328 a assignment, clause336 a assignment⟩

private def row2187 : List Int := [58, -56, -67, -60]
include assignment in
private theorem clause2187 : Type2.RUP.trueClause a (checkedClause row2187) := by
  apply Type2.RUP.derive (premises := [row321, row332]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause321 a assignment, clause332 a assignment⟩

private def row2188 : List Int := [-56, -60, -67]
include assignment in
private theorem clause2188 : Type2.RUP.trueClause a (checkedClause row2188) := by
  apply Type2.RUP.derive (premises := [row2186, row2187]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2186 a assignment, clause2187 a assignment⟩

private def row2189 : List Int := [-59, -46, -50, -49, 66, -67, -69]
include assignment in
private theorem clause2189 : Type2.RUP.trueClause a (checkedClause row2189) := by
  apply Type2.RUP.derive (premises := [row2185, row1395, row1407, row2186, row2187]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2185 a assignment, clause1395 a assignment, clause1407 a assignment,
    clause2186 a assignment, clause2187 a assignment⟩

private def row2190 : List Int := [-42, 58, -48, -39]
include assignment in
private theorem clause2190 : Type2.RUP.trueClause a (checkedClause row2190) := by
  apply Type2.RUP.derive (premises := [row47, row55]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause47 a assignment, clause55 a assignment⟩

private def row2191 : List Int := [58, -60, -48, -53, -50, -67]
include assignment in
private theorem clause2191 : Type2.RUP.trueClause a (checkedClause row2191) := by
  apply Type2.RUP.derive (premises := [row1546, row2190, row40, row59]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1546 a assignment, clause2190 a assignment, clause40 a assignment,
    clause59 a assignment⟩

private def row2192 : List Int := [-36, 56, -37, -46]
include assignment in
private theorem clause2192 : Type2.RUP.trueClause a (checkedClause row2192) := by
  apply Type2.RUP.derive (premises := [row7, row19]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause7 a assignment, clause19 a assignment⟩

private def row2193 : List Int := [-60, -47, -46, -48, -53, -50, -49, 66, -67, -68, -69]
include assignment in
private theorem clause2193 : Type2.RUP.trueClause a (checkedClause row2193) := by
  apply Type2.RUP.derive (premises := [row2188, row2191, row1321, row1399, row2192]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2188 a assignment, clause2191 a assignment, clause1321 a assignment,
    clause1399 a assignment, clause2192 a assignment⟩

private def row2194 : List Int := [-36, 37, 56, -46]
include assignment in
private theorem clause2194 : Type2.RUP.trueClause a (checkedClause row2194) := by
  apply Type2.RUP.derive (premises := [row2, row9]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2 a assignment, clause9 a assignment⟩

private def row2195 : List Int := [-36, -46, 56]
include assignment in
private theorem clause2195 : Type2.RUP.trueClause a (checkedClause row2195) := by
  apply Type2.RUP.derive (premises := [row2192, row2194]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2192 a assignment, clause2194 a assignment⟩

private def row2196 : List Int := [-61, 60, 59, -69]
include assignment in
private theorem clause2196 : Type2.RUP.trueClause a (checkedClause row2196) := by
  apply Type2.RUP.derive (premises := [row366, row378]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause366 a assignment, clause378 a assignment⟩

private def row2197 : List Int := [57, 61, 58, -68]
include assignment in
private theorem clause2197 : Type2.RUP.trueClause a (checkedClause row2197) := by
  apply Type2.RUP.derive (premises := [row345, row348]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause345 a assignment, clause348 a assignment⟩

private def row2198 : List Int := [-67, -68, -70, -69]
include assignment in
private theorem clause2198 : Type2.RUP.trueClause a (checkedClause row2198) := by
  apply Type2.RUP.derive (premises := [row2158, row2179, row2133, row2182, row2183, row266, row1441, row1603, row1682, row2112, row2189, row210,
    row2193, row2196, row1502, row1524, row1587, row2101, row2147, row104, row169, row179]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2158 a assignment, clause2179 a assignment, clause2133 a assignment,
    clause2182 a assignment, clause2183 a assignment, clause266 a assignment,
    clause1441 a assignment, clause1603 a assignment, clause1682 a assignment,
    clause2112 a assignment, clause2189 a assignment, clause210 a assignment,
    clause2193 a assignment, clause2196 a assignment, clause1502 a assignment,
    clause1524 a assignment, clause1587 a assignment, clause2101 a assignment,
    clause2147 a assignment, clause104 a assignment, clause169 a assignment,
    clause179 a assignment⟩

private def row2199 : List Int := [59, 60, 66, 67, -68, -69]
include assignment in
private theorem clause2199 : Type2.RUP.trueClause a (checkedClause row2199) := by
  apply Type2.RUP.derive (premises := [row2196, row1524, row1609, row2197]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2196 a assignment, clause1524 a assignment, clause1609 a assignment,
    clause2197 a assignment⟩

private def row2200 : List Int := [58, 56, 67, 60]
include assignment in
private theorem clause2200 : Type2.RUP.trueClause a (checkedClause row2200) := by
  apply Type2.RUP.derive (premises := [row329, row337]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause329 a assignment, clause337 a assignment⟩

private def row2201 : List Int := [-58, 56, 67, 60]
include assignment in
private theorem clause2201 : Type2.RUP.trueClause a (checkedClause row2201) := by
  apply Type2.RUP.derive (premises := [row320, row333]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause320 a assignment, clause333 a assignment⟩

private def row2202 : List Int := [56, 60, 67]
include assignment in
private theorem clause2202 : Type2.RUP.trueClause a (checkedClause row2202) := by
  apply Type2.RUP.derive (premises := [row2200, row2201]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2200 a assignment, clause2201 a assignment⟩

private def row2203 : List Int := [-59, 60, -69, 67, 66]
include assignment in
private theorem clause2203 : Type2.RUP.trueClause a (checkedClause row2203) := by
  apply Type2.RUP.derive (premises := [row1448, row2200, row2201]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1448 a assignment, clause2200 a assignment, clause2201 a assignment⟩

private def row2204 : List Int := [60, 66, -69, 67, -68]
include assignment in
private theorem clause2204 : Type2.RUP.trueClause a (checkedClause row2204) := by
  apply Type2.RUP.derive (premises := [row2199, row2203]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2199 a assignment, clause2203 a assignment⟩

private def row2205 : List Int := [-58, 56, 67, -60]
include assignment in
private theorem clause2205 : Type2.RUP.trueClause a (checkedClause row2205) := by
  apply Type2.RUP.derive (premises := [row327, row335]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause327 a assignment, clause335 a assignment⟩

private def row2206 : List Int := [56, -68, -69, -70]
include assignment in
private theorem clause2206 : Type2.RUP.trueClause a (checkedClause row2206) := by
  apply Type2.RUP.derive (premises := [row2198, row2202, row2205, row324, row412, row1459, row1618, row1691, row2197, row315]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2198 a assignment, clause2202 a assignment, clause2205 a assignment,
    clause324 a assignment, clause412 a assignment, clause1459 a assignment,
    clause1618 a assignment, clause1691 a assignment, clause2197 a assignment,
    clause315 a assignment⟩

private def row2207 : List Int := [58, -56, 66, 67, -68, -69]
include assignment in
private theorem clause2207 : Type2.RUP.trueClause a (checkedClause row2207) := by
  apply Type2.RUP.derive (premises := [row1376, row2197, row2204, row978, row1535]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1376 a assignment, clause2197 a assignment, clause2204 a assignment,
    clause978 a assignment, clause1535 a assignment⟩

private def row2208 : List Int := [-50, -48, 67, -46]
include assignment in
private theorem clause2208 : Type2.RUP.trueClause a (checkedClause row2208) := by
  apply Type2.RUP.derive (premises := [row222, row229]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause222 a assignment, clause229 a assignment⟩

private def row2209 : List Int := [40, 43, 62, 52]
include assignment in
private theorem clause2209 : Type2.RUP.trueClause a (checkedClause row2209) := by
  apply Type2.RUP.derive (premises := [row127, row133]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause127 a assignment, clause133 a assignment⟩

private def row2210 : List Int := [-39, 36, -58, 48]
include assignment in
private theorem clause2210 : Type2.RUP.trueClause a (checkedClause row2210) := by
  apply Type2.RUP.derive (premises := [row43, row48]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause43 a assignment, clause48 a assignment⟩

private def row2211 : List Int := [48, 61, -46, -58, -56, 66, 67, -68]
include assignment in
private theorem clause2211 : Type2.RUP.trueClause a (checkedClause row2211) := by
  apply Type2.RUP.derive (premises := [row1324, row2210, row46, row58]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1324 a assignment, clause2210 a assignment, clause46 a assignment,
    clause58 a assignment⟩

private def row2212 : List Int := [36, -47, 40, 52, 37, 49, -46]
include assignment in
private theorem clause2212 : Type2.RUP.trueClause a (checkedClause row2212) := by
  apply Type2.RUP.derive (premises := [row508, row580, row2147, row2149]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause508 a assignment, clause580 a assignment, clause2147 a assignment,
    clause2149 a assignment⟩

private def row2213 : List Int := [41, -36, -47, 42, 39, -51, 61]
include assignment in
private theorem clause2213 : Type2.RUP.trueClause a (checkedClause row2213) := by
  apply Type2.RUP.derive (premises := [row2150, row102, row109]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2150 a assignment, clause102 a assignment, clause109 a assignment⟩

private def row2214 : List Int := [-38, -41, -36, -47, -51, 61, -68]
include assignment in
private theorem clause2214 : Type2.RUP.trueClause a (checkedClause row2214) := by
  apply Type2.RUP.derive (premises := [row27, row1487]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause27 a assignment, clause1487 a assignment⟩

private def row2215 : List Int := [61, -46, -68, -69, -70]
include assignment in
private theorem clause2215 : Type2.RUP.trueClause a (checkedClause row2215) := by
  apply Type2.RUP.derive (premises := [row2198, row2206, row412, row2204, row2207, row2211, row322, row2208, row239, row1410, row1432, row1551,
    row1577, row1644, row1680, row1793, row1841, row243, row2212, row2213, row2214, row32, row434, row910,
    row2173, row123]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2198 a assignment, clause2206 a assignment, clause412 a assignment,
    clause2204 a assignment, clause2207 a assignment, clause2211 a assignment,
    clause322 a assignment, clause2208 a assignment, clause239 a assignment,
    clause1410 a assignment, clause1432 a assignment, clause1551 a assignment,
    clause1577 a assignment, clause1644 a assignment, clause1680 a assignment,
    clause1793 a assignment, clause1841 a assignment, clause243 a assignment,
    clause2212 a assignment, clause2213 a assignment, clause2214 a assignment,
    clause32 a assignment, clause434 a assignment, clause910 a assignment,
    clause2173 a assignment, clause123 a assignment⟩

private def row2216 : List Int := [38, -47, -54, -51, 45]
include assignment in
private theorem clause2216 : Type2.RUP.trueClause a (checkedClause row2216) := by
  apply Type2.RUP.derive (premises := [row757, row2147, row2149]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause757 a assignment, clause2147 a assignment, clause2149 a assignment⟩

private def row2217 : List Int := [-48, -46, -68, -69, -70]
include assignment in
private theorem clause2217 : Type2.RUP.trueClause a (checkedClause row2217) := by
  apply Type2.RUP.derive (premises := [row2198, row2206, row2208, row2215, row239, row412, row1432, row1593, row1841, row2123, row2170, row2204,
    row2207, row243, row1551, row2049, row2216, row106]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2198 a assignment, clause2206 a assignment, clause2208 a assignment,
    clause2215 a assignment, clause239 a assignment, clause412 a assignment,
    clause1432 a assignment, clause1593 a assignment, clause1841 a assignment,
    clause2123 a assignment, clause2170 a assignment, clause2204 a assignment,
    clause2207 a assignment, clause243 a assignment, clause1551 a assignment,
    clause2049 a assignment, clause2216 a assignment, clause106 a assignment⟩

private def row2218 : List Int := [39, 36, -58, 48]
include assignment in
private theorem clause2218 : Type2.RUP.trueClause a (checkedClause row2218) := by
  apply Type2.RUP.derive (premises := [row46, row58]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause46 a assignment, clause58 a assignment⟩

private def row2219 : List Int := [36, 48, -58]
include assignment in
private theorem clause2219 : Type2.RUP.trueClause a (checkedClause row2219) := by
  apply Type2.RUP.derive (premises := [row2210, row2218]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2210 a assignment, clause2218 a assignment⟩

private def row2220 : List Int := [48, -46, 67, -56, -58]
include assignment in
private theorem clause2220 : Type2.RUP.trueClause a (checkedClause row2220) := by
  apply Type2.RUP.derive (premises := [row1324, row2210, row2218]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1324 a assignment, clause2210 a assignment, clause2218 a assignment⟩

private def row2221 : List Int := [-46, -68, -69, -70]
include assignment in
private theorem clause2221 : Type2.RUP.trueClause a (checkedClause row2221) := by
  apply Type2.RUP.derive (premises := [row2198, row2206, row2215, row2217, row2220, row412, row1376, row1535, row1618, row2196]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2198 a assignment, clause2206 a assignment, clause2215 a assignment,
    clause2217 a assignment, clause2220 a assignment, clause412 a assignment,
    clause1376 a assignment, clause1535 a assignment, clause1618 a assignment,
    clause2196 a assignment⟩

private def row2222 : List Int := [39, 48, -58, -36]
include assignment in
private theorem clause2222 : Type2.RUP.trueClause a (checkedClause row2222) := by
  apply Type2.RUP.derive (premises := [row41, row54]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause41 a assignment, clause54 a assignment⟩

private def row2223 : List Int := [-55, 50, -68, -69, -70]
include assignment in
private theorem clause2223 : Type2.RUP.trueClause a (checkedClause row2223) := by
  apply Type2.RUP.derive (premises := [row2133, row2183, row2198, row2221, row412, row2181]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2133 a assignment, clause2183 a assignment, clause2198 a assignment,
    clause2221 a assignment, clause412 a assignment, clause2181 a assignment⟩

private def row2224 : List Int := [48, -68, -69, -70]
include assignment in
private theorem clause2224 : Type2.RUP.trueClause a (checkedClause row2224) := by
  apply Type2.RUP.derive (premises := [row2198, row2206, row2221, row412, row2120, row2204, row2207, row2222, row56, row322, row1786, row224,
    row2223, row2115, row2125]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2198 a assignment, clause2206 a assignment, clause2221 a assignment,
    clause412 a assignment, clause2120 a assignment, clause2204 a assignment,
    clause2207 a assignment, clause2222 a assignment, clause56 a assignment,
    clause322 a assignment, clause1786 a assignment, clause224 a assignment,
    clause2223 a assignment, clause2115 a assignment, clause2125 a assignment⟩

private def row2225 : List Int := [-52, 46, 66, -47]
include assignment in
private theorem clause2225 : Type2.RUP.trueClause a (checkedClause row2225) := by
  apply Type2.RUP.derive (premises := [row200, row215]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause200 a assignment, clause215 a assignment⟩

private def row2226 : List Int := [53, 46, 67, -48]
include assignment in
private theorem clause2226 : Type2.RUP.trueClause a (checkedClause row2226) := by
  apply Type2.RUP.derive (premises := [row227, row233]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause227 a assignment, clause233 a assignment⟩

private def row2227 : List Int := [67, -68, -70, -69]
include assignment in
private theorem clause2227 : Type2.RUP.trueClause a (checkedClause row2227) := by
  apply Type2.RUP.derive (premises := [row2221, row2224, row2226, row220, row235]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2221 a assignment, clause2224 a assignment, clause2226 a assignment,
    clause220 a assignment, clause235 a assignment⟩

private def row2228 : List Int := [-68, -69, -70]
include assignment in
private theorem clause2228 : Type2.RUP.trueClause a (checkedClause row2228) := by
  apply Type2.RUP.derive (premises := [row2198, row2227]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2198 a assignment, clause2227 a assignment⟩

private def row2229 : List Int := [-53, 46, 67, -48]
include assignment in
private theorem clause2229 : Type2.RUP.trueClause a (checkedClause row2229) := by
  apply Type2.RUP.derive (premises := [row220, row235]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause220 a assignment, clause235 a assignment⟩

private def row2230 : List Int := [46, -48, 67]
include assignment in
private theorem clause2230 : Type2.RUP.trueClause a (checkedClause row2230) := by
  apply Type2.RUP.derive (premises := [row2226, row2229]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2226 a assignment, clause2229 a assignment⟩

private def row2231 : List Int := [40, -42, 63, 53]
include assignment in
private theorem clause2231 : Type2.RUP.trueClause a (checkedClause row2231) := by
  apply Type2.RUP.derive (premises := [row147, row153]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause147 a assignment, clause153 a assignment⟩

private def row2232 : List Int := [-40, -56, -36, -46]
include assignment in
private theorem clause2232 : Type2.RUP.trueClause a (checkedClause row2232) := by
  apply Type2.RUP.derive (premises := [row4, row12]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause4 a assignment, clause12 a assignment⟩

private def row2233 : List Int := [-42, 40, -58, -48, 67]
include assignment in
private theorem clause2233 : Type2.RUP.trueClause a (checkedClause row2233) := by
  apply Type2.RUP.derive (premises := [row2230, row2208, row239, row1793, row2231]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2230 a assignment, clause2208 a assignment, clause239 a assignment,
    clause1793 a assignment, clause2231 a assignment⟩

private def row2234 : List Int := [-64, -57, 68, -58]
include assignment in
private theorem clause2234 : Type2.RUP.trueClause a (checkedClause row2234) := by
  apply Type2.RUP.derive (premises := [row349, row359]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause349 a assignment, clause359 a assignment⟩

private def row2235 : List Int := [-36, -58, -54, -47, -48, 67, 68]
include assignment in
private theorem clause2235 : Type2.RUP.trueClause a (checkedClause row2235) := by
  apply Type2.RUP.derive (premises := [row1341, row2230, row2234, row1325, row1800, row2232, row2233]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1341 a assignment, clause2230 a assignment, clause2234 a assignment,
    clause1325 a assignment, clause1800 a assignment, clause2232 a assignment,
    clause2233 a assignment⟩

private def row2236 : List Int := [-64, 57, 68, -58]
include assignment in
private theorem clause2236 : Type2.RUP.trueClause a (checkedClause row2236) := by
  apply Type2.RUP.derive (premises := [row340, row355]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause340 a assignment, clause355 a assignment⟩

private def row2237 : List Int := [-64, -58, 68]
include assignment in
private theorem clause2237 : Type2.RUP.trueClause a (checkedClause row2237) := by
  apply Type2.RUP.derive (premises := [row2234, row2236]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2234 a assignment, clause2236 a assignment⟩

private def row2238 : List Int := [-61, 64, -70, -69, 68]
include assignment in
private theorem clause2238 : Type2.RUP.trueClause a (checkedClause row2238) := by
  apply Type2.RUP.derive (premises := [row2098, row2100, row2169]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2098 a assignment, clause2100 a assignment, clause2169 a assignment⟩

private def row2239 : List Int := [-58, -54, -48, 67, -69, -70]
include assignment in
private theorem clause2239 : Type2.RUP.trueClause a (checkedClause row2239) := by
  apply Type2.RUP.derive (premises := [row2227, row2230, row2237, row2238, row353, row404, row1359, row1717, row1800, row2235, row45, row179,
    row456, row1171]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2227 a assignment, clause2230 a assignment, clause2237 a assignment,
    clause2238 a assignment, clause353 a assignment, clause404 a assignment,
    clause1359 a assignment, clause1717 a assignment, clause1800 a assignment,
    clause2235 a assignment, clause45 a assignment, clause179 a assignment,
    clause456 a assignment, clause1171 a assignment⟩

private def row2240 : List Int := [61, 64, 68, 58]
include assignment in
private theorem clause2240 : Type2.RUP.trueClause a (checkedClause row2240) := by
  apply Type2.RUP.derive (premises := [row342, row347]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause342 a assignment, clause347 a assignment⟩

private def row2241 : List Int := [64, 58, -69, -70]
include assignment in
private theorem clause2241 : Type2.RUP.trueClause a (checkedClause row2241) := by
  apply Type2.RUP.derive (premises := [row2228, row2238, row2240]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2228 a assignment, clause2238 a assignment, clause2240 a assignment⟩

private def row2242 : List Int := [45, -38, 61, -51]
include assignment in
private theorem clause2242 : Type2.RUP.trueClause a (checkedClause row2242) := by
  apply Type2.RUP.derive (premises := [row109, row119]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause109 a assignment, clause119 a assignment⟩

private def row2243 : List Int := [61, -64, 58, -51, -54, -47, 68]
include assignment in
private theorem clause2243 : Type2.RUP.trueClause a (checkedClause row2243) := by
  apply Type2.RUP.derive (premises := [row357, row1483, row2029, row2242]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause357 a assignment, clause1483 a assignment, clause2029 a assignment,
    clause2242 a assignment⟩

private def row2244 : List Int := [39, 42, -48, 58]
include assignment in
private theorem clause2244 : Type2.RUP.trueClause a (checkedClause row2244) := by
  apply Type2.RUP.derive (premises := [row49, row57]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause49 a assignment, clause57 a assignment⟩

private def row2245 : List Int := [-54, -48, 67, -69, -70]
include assignment in
private theorem clause2245 : Type2.RUP.trueClause a (checkedClause row2245) := by
  apply Type2.RUP.derive (premises := [row2227, row2239, row2241, row1808, row2244, row40, row59]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2227 a assignment, clause2239 a assignment, clause2241 a assignment,
    clause1808 a assignment, clause2244 a assignment, clause40 a assignment,
    clause59 a assignment⟩

private def row2246 : List Int := [54, -47, 68, -48]
include assignment in
private theorem clause2246 : Type2.RUP.trueClause a (checkedClause row2246) := by
  apply Type2.RUP.derive (premises := [row244, row249]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause244 a assignment, clause249 a assignment⟩

private def row2247 : List Int := [-48, 67, -69, -70]
include assignment in
private theorem clause2247 : Type2.RUP.trueClause a (checkedClause row2247) := by
  apply Type2.RUP.derive (premises := [row2227, row2245, row2246, row247, row253]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2227 a assignment, clause2245 a assignment, clause2246 a assignment,
    clause247 a assignment, clause253 a assignment⟩

private def row2248 : List Int := [-47, 54, 68, 48]
include assignment in
private theorem clause2248 : Type2.RUP.trueClause a (checkedClause row2248) := by
  apply Type2.RUP.derive (premises := [row242, row250]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause242 a assignment, clause250 a assignment⟩

private def row2249 : List Int := [-51, 54, 67, -69, -70]
include assignment in
private theorem clause2249 : Type2.RUP.trueClause a (checkedClause row2249) := by
  apply Type2.RUP.derive (premises := [row2124, row2133, row2227, row2247, row2248, row404, row806, row204, row210]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2124 a assignment, clause2133 a assignment, clause2227 a assignment,
    clause2247 a assignment, clause2248 a assignment, clause404 a assignment,
    clause806 a assignment, clause204 a assignment, clause210 a assignment⟩

private def row2250 : List Int := [52, -49, 66, 47]
include assignment in
private theorem clause2250 : Type2.RUP.trueClause a (checkedClause row2250) := by
  apply Type2.RUP.derive (premises := [row204, row210]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause204 a assignment, clause210 a assignment⟩

private def row2251 : List Int := [39, -64, 58, 51, 54, 48, 68]
include assignment in
private theorem clause2251 : Type2.RUP.trueClause a (checkedClause row2251) := by
  apply Type2.RUP.derive (premises := [row1557, row2022, row104, row110]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1557 a assignment, clause2022 a assignment, clause104 a assignment,
    clause110 a assignment⟩

private def row2252 : List Int := [61, 58, 55, -49, 66, -69, -70]
include assignment in
private theorem clause2252 : Type2.RUP.trueClause a (checkedClause row2252) := by
  apply Type2.RUP.derive (premises := [row1922, row2122, row2159, row2225, row2228, row2240, row274, row357, row411, row567, row1342, row1364,
    row2118, row2119]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1922 a assignment, clause2122 a assignment, clause2159 a assignment,
    clause2225 a assignment, clause2228 a assignment, clause2240 a assignment,
    clause274 a assignment, clause357 a assignment, clause411 a assignment,
    clause567 a assignment, clause1342 a assignment, clause1364 a assignment,
    clause2118 a assignment, clause2119 a assignment⟩

private def row2253 : List Int := [-61, 55, -49, -69]
include assignment in
private theorem clause2253 : Type2.RUP.trueClause a (checkedClause row2253) := by
  apply Type2.RUP.derive (premises := [row2122, row2170, row2042, row2156, row182, row190]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2122 a assignment, clause2170 a assignment, clause2042 a assignment,
    clause2156 a assignment, clause182 a assignment, clause190 a assignment⟩

private def row2254 : List Int := [-49, 54, 67, -69, -70]
include assignment in
private theorem clause2254 : Type2.RUP.trueClause a (checkedClause row2254) := by
  apply Type2.RUP.derive (premises := [row2227, row2247, row2248, row2249, row404, row2250, row2133, row2253, row2252, row1565, row2218, row2222]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2227 a assignment, clause2247 a assignment, clause2248 a assignment,
    clause2249 a assignment, clause404 a assignment, clause2250 a assignment,
    clause2133 a assignment, clause2253 a assignment, clause2252 a assignment,
    clause1565 a assignment, clause2218 a assignment, clause2222 a assignment⟩

private def row2255 : List Int := [-58, -46, 67, 48]
include assignment in
private theorem clause2255 : Type2.RUP.trueClause a (checkedClause row2255) := by
  apply Type2.RUP.derive (premises := [row2219, row2220, row2192, row2194]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2219 a assignment, clause2220 a assignment, clause2192 a assignment,
    clause2194 a assignment⟩

private def row2256 : List Int := [37, -39, -50, -60]
include assignment in
private theorem clause2256 : Type2.RUP.trueClause a (checkedClause row2256) := by
  apply Type2.RUP.derive (premises := [row83, row91]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause83 a assignment, clause91 a assignment⟩

private def row2257 : List Int := [-37, 59, 49]
include assignment in
private theorem clause2257 : Type2.RUP.trueClause a (checkedClause row2257) := by
  apply Type2.RUP.derive (premises := [row2128, row2165]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2128 a assignment, clause2165 a assignment⟩

private def row2258 : List Int := [-37, -46, 49, 66, -56]
include assignment in
private theorem clause2258 : Type2.RUP.trueClause a (checkedClause row2258) := by
  apply Type2.RUP.derive (premises := [row1394, row2128, row2165]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1394 a assignment, clause2128 a assignment, clause2165 a assignment⟩

private def row2259 : List Int := [-50, 54, 67, -69, -70]
include assignment in
private theorem clause2259 : Type2.RUP.trueClause a (checkedClause row2259) := by
  apply Type2.RUP.derive (premises := [row2227, row2247, row2248, row2249, row2254, row404, row566, row2255, row2241, row2251, row1548, row2256,
    row2258, row522, row1316]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2227 a assignment, clause2247 a assignment, clause2248 a assignment,
    clause2249 a assignment, clause2254 a assignment, clause404 a assignment,
    clause566 a assignment, clause2255 a assignment, clause2241 a assignment,
    clause2251 a assignment, clause1548 a assignment, clause2256 a assignment,
    clause2258 a assignment, clause522 a assignment, clause1316 a assignment⟩

private def row2260 : List Int := [-46, -37, 49, 47, 48, 66, 67, 68]
include assignment in
private theorem clause2260 : Type2.RUP.trueClause a (checkedClause row2260) := by
  apply Type2.RUP.derive (premises := [row2255, row2258, row1316, row2192]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2255 a assignment, clause2258 a assignment, clause1316 a assignment,
    clause2192 a assignment⟩

private def row2261 : List Int := [46, 49, 47, 66]
include assignment in
private theorem clause2261 : Type2.RUP.trueClause a (checkedClause row2261) := by
  apply Type2.RUP.derive (premises := [row207, row217]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause207 a assignment, clause217 a assignment⟩

private def row2262 : List Int := [-44, -39, 37, 50]
include assignment in
private theorem clause2262 : Type2.RUP.trueClause a (checkedClause row2262) := by
  apply Type2.RUP.derive (premises := [row85, row88]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause85 a assignment, clause88 a assignment⟩

private def row2263 : List Int := [56, 58, -46, 47, 66, 67, 68]
include assignment in
private theorem clause2263 : Type2.RUP.trueClause a (checkedClause row2263) := by
  apply Type2.RUP.derive (premises := [row1364, row2195, row1300]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1364 a assignment, clause2195 a assignment, clause1300 a assignment⟩

private def row2264 : List Int := [-62, -64, -70]
include assignment in
private theorem clause2264 : Type2.RUP.trueClause a (checkedClause row2264) := by
  apply Type2.RUP.derive (premises := [row2103, row2162]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2103 a assignment, clause2162 a assignment⟩

private def row2265 : List Int := [54, 67, -69, -70]
include assignment in
private theorem clause2265 : Type2.RUP.trueClause a (checkedClause row2265) := by
  apply Type2.RUP.derive (premises := [row2227, row2247, row2248, row2249, row2254, row2259, row404, row2261, row2255, row2260, row2263, row2241,
    row2251, row2262, row2264, row93, row330, row1049, row1086, row1308, row1621, row1715, row2209, row26,
    row427]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2227 a assignment, clause2247 a assignment, clause2248 a assignment,
    clause2249 a assignment, clause2254 a assignment, clause2259 a assignment,
    clause404 a assignment, clause2261 a assignment, clause2255 a assignment,
    clause2260 a assignment, clause2263 a assignment, clause2241 a assignment,
    clause2251 a assignment, clause2262 a assignment, clause2264 a assignment,
    clause93 a assignment, clause330 a assignment, clause1049 a assignment,
    clause1086 a assignment, clause1308 a assignment, clause1621 a assignment,
    clause1715 a assignment, clause2209 a assignment, clause26 a assignment,
    clause427 a assignment⟩

private def row2266 : List Int := [-51, 49, 48, 67, 68, -69]
include assignment in
private theorem clause2266 : Type2.RUP.trueClause a (checkedClause row2266) := by
  apply Type2.RUP.derive (premises := [row1600, row2123, row2180]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1600 a assignment, clause2123 a assignment, clause2180 a assignment⟩

private def row2267 : List Int := [-36, 39, 48, 58]
include assignment in
private theorem clause2267 : Type2.RUP.trueClause a (checkedClause row2267) := by
  apply Type2.RUP.derive (premises := [row44, row50]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause44 a assignment, clause50 a assignment⟩

private def row2268 : List Int := [-50, 37, -46, -56, 58, 48, 67]
include assignment in
private theorem clause2268 : Type2.RUP.trueClause a (checkedClause row2268) := by
  apply Type2.RUP.derive (premises := [row1403, row2256, row2267, row529]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1403 a assignment, clause2256 a assignment, clause2267 a assignment,
    clause529 a assignment⟩

private def row2269 : List Int := [-36, 50, 37, -46, -56, 58, -53, 48]
include assignment in
private theorem clause2269 : Type2.RUP.trueClause a (checkedClause row2269) := by
  apply Type2.RUP.derive (premises := [row12, row517, row679, row2262]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause12 a assignment, clause517 a assignment, clause679 a assignment,
    clause2262 a assignment⟩

private def row2270 : List Int := [-46, 55, 51, -47, 49, -56, 62, -64, 58, -53, 48, 66, 67, -69]
include assignment in
private theorem clause2270 : Type2.RUP.trueClause a (checkedClause row2270) := by
  apply Type2.RUP.derive (premises := [row219, row1360, row1679, row1765, row1848, row2258, row2268, row2269, row2212, row664, row2167, row2170,
    row1215, row1288, row1418]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause219 a assignment, clause1360 a assignment, clause1679 a assignment,
    clause1765 a assignment, clause1848 a assignment, clause2258 a assignment,
    clause2268 a assignment, clause2269 a assignment, clause2212 a assignment,
    clause664 a assignment, clause2167 a assignment, clause2170 a assignment,
    clause1215 a assignment, clause1288 a assignment, clause1418 a assignment⟩

private def row2271 : List Int := [49, 58, 67, -69, -70]
include assignment in
private theorem clause2271 : Type2.RUP.trueClause a (checkedClause row2271) := by
  apply Type2.RUP.derive (premises := [row2227, row2241, row2247, row2264, row2265, row2266, row257, row404, row1348, row1765, row1832, row2073,
    row2270, row307, row313]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2227 a assignment, clause2241 a assignment, clause2247 a assignment,
    clause2264 a assignment, clause2265 a assignment, clause2266 a assignment,
    clause257 a assignment, clause404 a assignment, clause1348 a assignment,
    clause1765 a assignment, clause1832 a assignment, clause2073 a assignment,
    clause2270 a assignment, clause307 a assignment, clause313 a assignment⟩

private def row2272 : List Int := [46, -56, 58, 48, 67]
include assignment in
private theorem clause2272 : Type2.RUP.trueClause a (checkedClause row2272) := by
  apply Type2.RUP.derive (premises := [row1326, row2118, row2119]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1326 a assignment, clause2118 a assignment, clause2119 a assignment⟩

private def row2273 : List Int := [58, 67, -69, -70]
include assignment in
private theorem clause2273 : Type2.RUP.trueClause a (checkedClause row2273) := by
  apply Type2.RUP.derive (premises := [row2227, row2241, row2247, row2264, row2265, row2271, row404, row1765, row1832, row1364, row2272, row1432,
    row2159, row2250, row572, row734, row266]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2227 a assignment, clause2241 a assignment, clause2247 a assignment,
    clause2264 a assignment, clause2265 a assignment, clause2271 a assignment,
    clause404 a assignment, clause1765 a assignment, clause1832 a assignment,
    clause1364 a assignment, clause2272 a assignment, clause1432 a assignment,
    clause2159 a assignment, clause2250 a assignment, clause572 a assignment,
    clause734 a assignment, clause266 a assignment⟩

private def row2274 : List Int := [67, 68, -70, -69]
include assignment in
private theorem clause2274 : Type2.RUP.trueClause a (checkedClause row2274) := by
  apply Type2.RUP.derive (premises := [row404, row2247, row2265, row2273, row1832, row2219, row2222, row2237, row2238, row2255, row237, row1443,
    row1565, row1675, row2122, row2131]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause404 a assignment, clause2247 a assignment, clause2265 a assignment,
    clause2273 a assignment, clause1832 a assignment, clause2219 a assignment,
    clause2222 a assignment, clause2237 a assignment, clause2238 a assignment,
    clause2255 a assignment, clause237 a assignment, clause1443 a assignment,
    clause1565 a assignment, clause1675 a assignment, clause2122 a assignment,
    clause2131 a assignment⟩

private def row2275 : List Int := [-67, 68, -70, -69]
include assignment in
private theorem clause2275 : Type2.RUP.trueClause a (checkedClause row2275) := by
  apply Type2.RUP.derive (premises := [row403, row411]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause403 a assignment, clause411 a assignment⟩

private def row2276 : List Int := [68, -69, -70]
include assignment in
private theorem clause2276 : Type2.RUP.trueClause a (checkedClause row2276) := by
  apply Type2.RUP.derive (premises := [row2274, row2275]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2274 a assignment, clause2275 a assignment⟩

private def row2277 : List Int := [-69, -70]
include assignment in
private theorem clause2277 : Type2.RUP.trueClause a (checkedClause row2277) := by
  apply Type2.RUP.derive (premises := [row2228, row2274, row2275]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2228 a assignment, clause2274 a assignment, clause2275 a assignment⟩

private def row2278 : List Int := [43, -37, 59, -49]
include assignment in
private theorem clause2278 : Type2.RUP.trueClause a (checkedClause row2278) := by
  apply Type2.RUP.derive (premises := [row69, row79]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause69 a assignment, clause79 a assignment⟩

private def row2279 : List Int := [-43, 40, -62, 52]
include assignment in
private theorem clause2279 : Type2.RUP.trueClause a (checkedClause row2279) := by
  apply Type2.RUP.derive (premises := [row128, row138]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause128 a assignment, clause138 a assignment⟩

private def row2280 : List Int := [46, -58, 48, -67, 68, -70]
include assignment in
private theorem clause2280 : Type2.RUP.trueClause a (checkedClause row2280) := by
  apply Type2.RUP.derive (premises := [row2219, row2222, row2237, row2275, row56, row406, row1330, row1350, row1373, row2186, row2225, row213,
    row325, row996, row1044, row2279, row14, row302, row2278]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2219 a assignment, clause2222 a assignment, clause2237 a assignment,
    clause2275 a assignment, clause56 a assignment, clause406 a assignment,
    clause1330 a assignment, clause1350 a assignment, clause1373 a assignment,
    clause2186 a assignment, clause2225 a assignment, clause213 a assignment,
    clause325 a assignment, clause996 a assignment, clause1044 a assignment,
    clause2279 a assignment, clause14 a assignment, clause302 a assignment,
    clause2278 a assignment⟩

private def row2281 : List Int := [-53, -46, -67, 48]
include assignment in
private theorem clause2281 : Type2.RUP.trueClause a (checkedClause row2281) := by
  apply Type2.RUP.derive (premises := [row226, row232]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause226 a assignment, clause232 a assignment⟩

private def row2282 : List Int := [-58, 48, -67, 68, -70]
include assignment in
private theorem clause2282 : Type2.RUP.trueClause a (checkedClause row2282) := by
  apply Type2.RUP.derive (premises := [row2280, row2281, row221, row234]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2280 a assignment, clause2281 a assignment, clause221 a assignment,
    clause234 a assignment⟩

private def row2283 : List Int := [53, -46, -67, 48]
include assignment in
private theorem clause2283 : Type2.RUP.trueClause a (checkedClause row2283) := by
  apply Type2.RUP.derive (premises := [row221, row234]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause221 a assignment, clause234 a assignment⟩

private def row2284 : List Int := [-46, 48, -67]
include assignment in
private theorem clause2284 : Type2.RUP.trueClause a (checkedClause row2284) := by
  apply Type2.RUP.derive (premises := [row2281, row2283]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2281 a assignment, clause2283 a assignment⟩

private def row2285 : List Int := [53, 46, -67, 48]
include assignment in
private theorem clause2285 : Type2.RUP.trueClause a (checkedClause row2285) := by
  apply Type2.RUP.derive (premises := [row228, row238]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause228 a assignment, clause238 a assignment⟩

private def row2286 : List Int := [-56, 58, -67]
include assignment in
private theorem clause2286 : Type2.RUP.trueClause a (checkedClause row2286) := by
  apply Type2.RUP.derive (premises := [row2187, row326, row334]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2187 a assignment, clause326 a assignment, clause334 a assignment⟩

private def row2287 : List Int := [62, 56, 66, -57]
include assignment in
private theorem clause2287 : Type2.RUP.trueClause a (checkedClause row2287) := by
  apply Type2.RUP.derive (premises := [row307, row313]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause307 a assignment, clause313 a assignment⟩

private def row2288 : List Int := [-62, -57, -70, 68, 66]
include assignment in
private theorem clause2288 : Type2.RUP.trueClause a (checkedClause row2288) := by
  apply Type2.RUP.derive (premises := [row1774, row2103, row2162]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1774 a assignment, clause2103 a assignment, clause2162 a assignment⟩

private def row2289 : List Int := [58, -67, 68, -70]
include assignment in
private theorem clause2289 : Type2.RUP.trueClause a (checkedClause row2289) := by
  apply Type2.RUP.derive (premises := [row2275, row2286, row406, row1366, row2287, row2288]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2275 a assignment, clause2286 a assignment, clause406 a assignment,
    clause1366 a assignment, clause2287 a assignment, clause2288 a assignment⟩

private def row2290 : List Int := [56, 57, 66, -62]
include assignment in
private theorem clause2290 : Type2.RUP.trueClause a (checkedClause row2290) := by
  apply Type2.RUP.derive (premises := [row309, row317]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause309 a assignment, clause317 a assignment⟩

private def row2291 : List Int := [46, -56, -48, -67, -58]
include assignment in
private theorem clause2291 : Type2.RUP.trueClause a (checkedClause row2291) := by
  apply Type2.RUP.derive (premises := [row1331, row2118, row2119]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1331 a assignment, clause2118 a assignment, clause2119 a assignment⟩

private def row2292 : List Int := [54, 47, 68, -48]
include assignment in
private theorem clause2292 : Type2.RUP.trueClause a (checkedClause row2292) := by
  apply Type2.RUP.derive (premises := [row247, row253]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause247 a assignment, clause253 a assignment⟩

private def row2293 : List Int := [-54, 47, 68, -48]
include assignment in
private theorem clause2293 : Type2.RUP.trueClause a (checkedClause row2293) := by
  apply Type2.RUP.derive (premises := [row240, row255]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause240 a assignment, clause255 a assignment⟩

private def row2294 : List Int := [47, -48, 68]
include assignment in
private theorem clause2294 : Type2.RUP.trueClause a (checkedClause row2294) := by
  apply Type2.RUP.derive (premises := [row2292, row2293]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2292 a assignment, clause2293 a assignment⟩

private def row2295 : List Int := [-62, -67, 68, -70]
include assignment in
private theorem clause2295 : Type2.RUP.trueClause a (checkedClause row2295) := by
  apply Type2.RUP.derive (premises := [row2264, row2275, row2289, row406, row1774, row2282, row2290, row2291, row2294, row1301, row1341]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2264 a assignment, clause2275 a assignment, clause2289 a assignment,
    clause406 a assignment, clause1774 a assignment, clause2282 a assignment,
    clause2290 a assignment, clause2291 a assignment, clause2294 a assignment,
    clause1301 a assignment, clause1341 a assignment⟩

private def row2296 : List Int := [-67, 68, -70, 69]
include assignment in
private theorem clause2296 : Type2.RUP.trueClause a (checkedClause row2296) := by
  apply Type2.RUP.derive (premises := [row406, row2289, row2295, row2237, row2282, row2294, row1357, row2225, row2246, row2291, row213, row1733,
    row1800, row2287, row179, row304, row353, row971, row1013, row1163, row1393, row1860, row45, row474,
    row525, row86]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause406 a assignment, clause2289 a assignment, clause2295 a assignment,
    clause2237 a assignment, clause2282 a assignment, clause2294 a assignment,
    clause1357 a assignment, clause2225 a assignment, clause2246 a assignment,
    clause2291 a assignment, clause213 a assignment, clause1733 a assignment,
    clause1800 a assignment, clause2287 a assignment, clause179 a assignment,
    clause304 a assignment, clause353 a assignment, clause971 a assignment,
    clause1013 a assignment, clause1163 a assignment, clause1393 a assignment,
    clause1860 a assignment, clause45 a assignment, clause474 a assignment,
    clause525 a assignment, clause86 a assignment⟩

private def row2297 : List Int := [56, 62, 68, -70]
include assignment in
private theorem clause2297 : Type2.RUP.trueClause a (checkedClause row2297) := by
  apply Type2.RUP.derive (premises := [row2276, row2296, row414, row1691, row2202, row2205, row324]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2276 a assignment, clause2296 a assignment, clause414 a assignment,
    clause1691 a assignment, clause2202 a assignment, clause2205 a assignment,
    clause324 a assignment⟩

private def row2298 : List Int := [-48, 67, 68, 69]
include assignment in
private theorem clause2298 : Type2.RUP.trueClause a (checkedClause row2298) := by
  apply Type2.RUP.derive (premises := [row2230, row2294, row2208, row2246, row259, row577, row1430, row1513]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2230 a assignment, clause2294 a assignment, clause2208 a assignment,
    clause2246 a assignment, clause259 a assignment, clause577 a assignment,
    clause1430 a assignment, clause1513 a assignment⟩

private def row2299 : List Int := [-47, 63, 57, -56, 68, -70]
include assignment in
private theorem clause2299 : Type2.RUP.trueClause a (checkedClause row2299) := by
  apply Type2.RUP.derive (premises := [row2276, row2296, row2298, row414, row1348, row1375, row1696, row1765, row2248, row1301, row1810, row2232,
    row998]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2276 a assignment, clause2296 a assignment, clause2298 a assignment,
    clause414 a assignment, clause1348 a assignment, clause1375 a assignment,
    clause1696 a assignment, clause1765 a assignment, clause2248 a assignment,
    clause1301 a assignment, clause1810 a assignment, clause2232 a assignment,
    clause998 a assignment⟩

private def row2300 : List Int := [-54, 47, -46, 68, -70]
include assignment in
private theorem clause2300 : Type2.RUP.trueClause a (checkedClause row2300) := by
  apply Type2.RUP.derive (premises := [row2276, row2293, row2296, row257, row414, row1749, row1832, row2080, row2131]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2276 a assignment, clause2293 a assignment, clause2296 a assignment,
    clause257 a assignment, clause414 a assignment, clause1749 a assignment,
    clause1832 a assignment, clause2080 a assignment, clause2131 a assignment⟩

private def row2301 : List Int := [-52, 55, -70, 65, 62]
include assignment in
private theorem clause2301 : Type2.RUP.trueClause a (checkedClause row2301) := by
  apply Type2.RUP.derive (premises := [row1904, row2152, row2156]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1904 a assignment, clause2152 a assignment, clause2156 a assignment⟩

private def row2302 : List Int := [-52, 65, 62, -70]
include assignment in
private theorem clause2302 : Type2.RUP.trueClause a (checkedClause row2302) := by
  apply Type2.RUP.derive (premises := [row2133, row2301]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2133 a assignment, clause2301 a assignment⟩

private def row2303 : List Int := [55, 37, 54, 63, 60, 65, 59, -70]
include assignment in
private theorem clause2303 : Type2.RUP.trueClause a (checkedClause row2303) := by
  apply Type2.RUP.derive (premises := [row2115, row2167, row1100, row1981]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2115 a assignment, clause2167 a assignment, clause1100 a assignment,
    clause1981 a assignment⟩

private def row2304 : List Int := [63, 52, 65, 59, 57, -56, 68, -70]
include assignment in
private theorem clause2304 : Type2.RUP.trueClause a (checkedClause row2304) := by
  apply Type2.RUP.derive (premises := [row2163, row2276, row2296, row2298, row2299, row314, row398, row1044, row1132, row1749, row2250, row2257,
    row2261, row2268, row2303, row277, row806]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2163 a assignment, clause2276 a assignment, clause2296 a assignment,
    clause2298 a assignment, clause2299 a assignment, clause314 a assignment,
    clause398 a assignment, clause1044 a assignment, clause1132 a assignment,
    clause1749 a assignment, clause2250 a assignment, clause2257 a assignment,
    clause2261 a assignment, clause2268 a assignment, clause2303 a assignment,
    clause277 a assignment, clause806 a assignment⟩

private def row2305 : List Int := [-55, -63, 52, 65, 64, 57, -56, 68, -70]
include assignment in
private theorem clause2305 : Type2.RUP.trueClause a (checkedClause row2305) := by
  apply Type2.RUP.derive (premises := [row388, row1764, row1899, row2173, row2276, row2296, row2298, row1375, row1447, row1887, row2250, row2272,
    row1301, row1387, row2267, row522, row706, row87]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause388 a assignment, clause1764 a assignment, clause1899 a assignment,
    clause2173 a assignment, clause2276 a assignment, clause2296 a assignment,
    clause2298 a assignment, clause1375 a assignment, clause1447 a assignment,
    clause1887 a assignment, clause2250 a assignment, clause2272 a assignment,
    clause1301 a assignment, clause1387 a assignment, clause2267 a assignment,
    clause522 a assignment, clause706 a assignment, clause87 a assignment⟩

private def row2306 : List Int := [-47, 57, 62, 68, -70]
include assignment in
private theorem clause2306 : Type2.RUP.trueClause a (checkedClause row2306) := by
  apply Type2.RUP.derive (premises := [row2276, row2296, row2297, row2298, row2299, row414, row1348, row1375, row1765, row2173, row2240, row2248,
    row391, row978, row1301, row1810, row1832, row2232, row2267, row145, row982, row1254, row2021, row27,
    row103]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2276 a assignment, clause2296 a assignment, clause2297 a assignment,
    clause2298 a assignment, clause2299 a assignment, clause414 a assignment,
    clause1348 a assignment, clause1375 a assignment, clause1765 a assignment,
    clause2173 a assignment, clause2240 a assignment, clause2248 a assignment,
    clause391 a assignment, clause978 a assignment, clause1301 a assignment,
    clause1810 a assignment, clause1832 a assignment, clause2232 a assignment,
    clause2267 a assignment, clause145 a assignment, clause982 a assignment,
    clause1254 a assignment, clause2021 a assignment, clause27 a assignment,
    clause103 a assignment⟩

private def row2307 : List Int := [57, 62, 68, -70]
include assignment in
private theorem clause2307 : Type2.RUP.trueClause a (checkedClause row2307) := by
  apply Type2.RUP.derive (premises := [row2276, row2296, row2297, row2298, row2306, row414, row1375, row1765, row2173, row2240, row2272, row2300,
    row1206, row2136, row2302, row2304, row2305, row210, row288, row1431, row2167, row2257, row2269, row601,
    row664]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2276 a assignment, clause2296 a assignment, clause2297 a assignment,
    clause2298 a assignment, clause2306 a assignment, clause414 a assignment,
    clause1375 a assignment, clause1765 a assignment, clause2173 a assignment,
    clause2240 a assignment, clause2272 a assignment, clause2300 a assignment,
    clause1206 a assignment, clause2136 a assignment, clause2302 a assignment,
    clause2304 a assignment, clause2305 a assignment, clause210 a assignment,
    clause288 a assignment, clause1431 a assignment, clause2167 a assignment,
    clause2257 a assignment, clause2269 a assignment, clause601 a assignment,
    clause664 a assignment⟩

private def row2308 : List Int := [47, 65, 55, 52, -57, -56, 62, 66, 69]
include assignment in
private theorem clause2308 : Type2.RUP.trueClause a (checkedClause row2308) := by
  apply Type2.RUP.derive (premises := [row1715, row2167, row2250, row2261, row130, row589, row751, row26]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1715 a assignment, clause2167 a assignment, clause2250 a assignment,
    clause2261 a assignment, clause130 a assignment, clause589 a assignment,
    clause751 a assignment, clause26 a assignment⟩

private def row2309 : List Int := [50, 51, 69, 55]
include assignment in
private theorem clause2309 : Type2.RUP.trueClause a (checkedClause row2309) := by
  apply Type2.RUP.derive (premises := [row262, row267]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause262 a assignment, clause267 a assignment⟩

private def row2310 : List Int := [-47, 55, 52, 68, -70]
include assignment in
private theorem clause2310 : Type2.RUP.trueClause a (checkedClause row2310) := by
  apply Type2.RUP.derive (premises := [row2276, row2296, row2298, row2248, row298, row1997, row2080, row2309]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2276 a assignment, clause2296 a assignment, clause2298 a assignment,
    clause2248 a assignment, clause298 a assignment, clause1997 a assignment,
    clause2080 a assignment, clause2309 a assignment⟩

private def row2311 : List Int := [43, 41, 62, 52]
include assignment in
private theorem clause2311 : Type2.RUP.trueClause a (checkedClause row2311) := by
  apply Type2.RUP.derive (premises := [row124, row127]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause124 a assignment, clause127 a assignment⟩

private def row2312 : List Int := [55, 52, 62, 68, -70]
include assignment in
private theorem clause2312 : Type2.RUP.trueClause a (checkedClause row2312) := by
  apply Type2.RUP.derive (premises := [row2276, row2296, row2297, row2307, row2310, row414, row1715, row2308, row2311, row1906]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2276 a assignment, clause2296 a assignment, clause2297 a assignment,
    clause2307 a assignment, clause2310 a assignment, clause414 a assignment,
    clause1715 a assignment, clause2308 a assignment, clause2311 a assignment,
    clause1906 a assignment⟩

private def row2313 : List Int := [43, -46, -49, 52, 62, 66]
include assignment in
private theorem clause2313 : Type2.RUP.trueClause a (checkedClause row2313) := by
  apply Type2.RUP.derive (premises := [row1860, row2184, row2209, row673]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1860 a assignment, clause2184 a assignment, clause2209 a assignment,
    clause673 a assignment⟩

private def row2314 : List Int := [50, -37, -40, -53, -46, -56, 48, 67]
include assignment in
private theorem clause2314 : Type2.RUP.trueClause a (checkedClause row2314) := by
  apply Type2.RUP.derive (premises := [row4, row526, row684, row1410, row82]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause4 a assignment, clause526 a assignment, clause684 a assignment,
    clause1410 a assignment, clause82 a assignment⟩

private def row2315 : List Int := [44, -65, -40, -43, -53, -54, -55, -70]
include assignment in
private theorem clause2315 : Type2.RUP.trueClause a (checkedClause row2315) := by
  apply Type2.RUP.derive (premises := [row186, row192]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause186 a assignment, clause192 a assignment⟩

private def row2316 : List Int := [-44, -65, -43, -55]
include assignment in
private theorem clause2316 : Type2.RUP.trueClause a (checkedClause row2316) := by
  apply Type2.RUP.derive (premises := [row185, row188]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause185 a assignment, clause188 a assignment⟩

private def row2317 : List Int := [-65, -40, -70, -43, -53, -54, -55]
include assignment in
private theorem clause2317 : Type2.RUP.trueClause a (checkedClause row2317) := by
  apply Type2.RUP.derive (premises := [row2315, row2316]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2315 a assignment, clause2316 a assignment⟩

private def row2318 : List Int := [-45, 39, -38, -51]
include assignment in
private theorem clause2318 : Type2.RUP.trueClause a (checkedClause row2318) := by
  apply Type2.RUP.derive (premises := [row102, row112]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause102 a assignment, clause112 a assignment⟩

private def row2319 : List Int := [-44, -51, -38, 65, -43, 58, -53, -55, -56, 68, -70]
include assignment in
private theorem clause2319 : Type2.RUP.trueClause a (checkedClause row2319) := by
  apply Type2.RUP.derive (premises := [row199, row1980, row2163, row2276, row2286, row2298, row2318, row330, row398, row1220, row1238, row1564]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause199 a assignment, clause1980 a assignment, clause2163 a assignment,
    clause2276 a assignment, clause2286 a assignment, clause2298 a assignment,
    clause2318 a assignment, clause330 a assignment, clause398 a assignment,
    clause1220 a assignment, clause1238 a assignment, clause1564 a assignment⟩

private def row2320 : List Int := [-59, 65, -40, -43, -53, -46, -49, -55, -56, 68, -70]
include assignment in
private theorem clause2320 : Type2.RUP.trueClause a (checkedClause row2320) := by
  apply Type2.RUP.derive (premises := [row1889, row2116, row2151, row2232, row2296, row2298, row2314, row279, row2219, row2319, row1092, row1548,
    row89]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1889 a assignment, clause2116 a assignment, clause2151 a assignment,
    clause2232 a assignment, clause2296 a assignment, clause2298 a assignment,
    clause2314 a assignment, clause279 a assignment, clause2219 a assignment,
    clause2319 a assignment, clause1092 a assignment, clause1548 a assignment,
    clause89 a assignment⟩

private def row2321 : List Int := [-40, 52, 62, 68, -70]
include assignment in
private theorem clause2321 : Type2.RUP.trueClause a (checkedClause row2321) := by
  apply Type2.RUP.derive (premises := [row2276, row2296, row2297, row2298, row2307, row2312, row414, row1630, row1915, row2220, row2250, row2313,
    row2248, row651, row2317, row2320, row1075, row1529, row2240, row2243, row2314, row279]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2276 a assignment, clause2296 a assignment, clause2297 a assignment,
    clause2298 a assignment, clause2307 a assignment, clause2312 a assignment,
    clause414 a assignment, clause1630 a assignment, clause1915 a assignment,
    clause2220 a assignment, clause2250 a assignment, clause2313 a assignment,
    clause2248 a assignment, clause651 a assignment, clause2317 a assignment,
    clause2320 a assignment, clause1075 a assignment, clause1529 a assignment,
    clause2240 a assignment, clause2243 a assignment, clause2314 a assignment,
    clause279 a assignment⟩

private def row2322 : List Int := [44, -63, -53, 40]
include assignment in
private theorem clause2322 : Type2.RUP.trueClause a (checkedClause row2322) := by
  apply Type2.RUP.derive (premises := [row145, row151]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause145 a assignment, clause151 a assignment⟩

private def row2323 : List Int := [52, 62, 68, -70]
include assignment in
private theorem clause2323 : Type2.RUP.trueClause a (checkedClause row2323) := by
  apply Type2.RUP.derive (premises := [row2276, row2296, row2297, row2298, row2312, row2321, row414, row1915, row2209, row2250, row1348, row2248,
    row651, row714, row1637, row2322]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2276 a assignment, clause2296 a assignment, clause2297 a assignment,
    clause2298 a assignment, clause2312 a assignment, clause2321 a assignment,
    clause414 a assignment, clause1915 a assignment, clause2209 a assignment,
    clause2250 a assignment, clause1348 a assignment, clause2248 a assignment,
    clause651 a assignment, clause714 a assignment, clause1637 a assignment,
    clause2322 a assignment⟩

private def row2324 : List Int := [46, 49, 48, 66, 67, 68]
include assignment in
private theorem clause2324 : Type2.RUP.trueClause a (checkedClause row2324) := by
  apply Type2.RUP.derive (premises := [row1348, row2261]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1348 a assignment, clause2261 a assignment⟩

private def row2325 : List Int := [43, -40, 62, -52]
include assignment in
private theorem clause2325 : Type2.RUP.trueClause a (checkedClause row2325) := by
  apply Type2.RUP.derive (premises := [row129, row139]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause129 a assignment, clause139 a assignment⟩

private def row2326 : List Int := [62, 68, -70]
include assignment in
private theorem clause2326 : Type2.RUP.trueClause a (checkedClause row2326) := by
  apply Type2.RUP.derive (premises := [row2276, row2296, row2297, row2298, row2323, row414, row2133, row2301, row1920, row1931, row2324, row1394,
    row1621, row2325, row68, row78]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2276 a assignment, clause2296 a assignment, clause2297 a assignment,
    clause2298 a assignment, clause2323 a assignment, clause414 a assignment,
    clause2133 a assignment, clause2301 a assignment, clause1920 a assignment,
    clause1931 a assignment, clause2324 a assignment, clause1394 a assignment,
    clause1621 a assignment, clause2325 a assignment, clause68 a assignment,
    clause78 a assignment⟩

private def row2327 : List Int := [67, 68, -70, 69]
include assignment in
private theorem clause2327 : Type2.RUP.trueClause a (checkedClause row2327) := by
  apply Type2.RUP.derive (premises := [row414, row2326, row2163, row2264, row2288, row2290, row383, row1045, row1375]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause414 a assignment, clause2326 a assignment, clause2163 a assignment,
    clause2264 a assignment, clause2288 a assignment, clause2290 a assignment,
    clause383 a assignment, clause1045 a assignment, clause1375 a assignment⟩

private def row2328 : List Int := [68, 69, -70]
include assignment in
private theorem clause2328 : Type2.RUP.trueClause a (checkedClause row2328) := by
  apply Type2.RUP.derive (premises := [row2296, row2327]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2296 a assignment, clause2327 a assignment⟩

private def row2329 : List Int := [67, -68, -70, 69]
include assignment in
private theorem clause2329 : Type2.RUP.trueClause a (checkedClause row2329) := by
  apply Type2.RUP.derive (premises := [row401, row418]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause401 a assignment, clause418 a assignment⟩

private def row2330 : List Int := [-67, -68, -70, 69]
include assignment in
private theorem clause2330 : Type2.RUP.trueClause a (checkedClause row2330) := by
  apply Type2.RUP.derive (premises := [row408, row416]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause408 a assignment, clause416 a assignment⟩

private def row2331 : List Int := [69, -70]
include assignment in
private theorem clause2331 : Type2.RUP.trueClause a (checkedClause row2331) := by
  apply Type2.RUP.derive (premises := [row2328, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2328 a assignment, clause2329 a assignment, clause2330 a assignment⟩

private def row2332 : List Int := [-70]
include assignment in
private theorem clause2332 : Type2.RUP.trueClause a (checkedClause row2332) := by
  apply Type2.RUP.derive (premises := [row2277, row2328, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2277 a assignment, clause2328 a assignment, clause2329 a assignment,
    clause2330 a assignment⟩

private def row2333 : List Int := [-56, -62, -67, -66]
include assignment in
private theorem clause2333 : Type2.RUP.trueClause a (checkedClause row2333) := by
  apply Type2.RUP.derive (premises := [row2188, row2286, row2332, row325, row1692]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2188 a assignment, clause2286 a assignment, clause2332 a assignment,
    clause325 a assignment, clause1692 a assignment⟩

private def row2334 : List Int := [60, -63, -67, 56]
include assignment in
private theorem clause2334 : Type2.RUP.trueClause a (checkedClause row2334) := by
  apply Type2.RUP.derive (premises := [row323, row331]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause323 a assignment, clause331 a assignment⟩

private def row2335 : List Int := [-46, -52, 58, -60, -66, -67]
include assignment in
private theorem clause2335 : Type2.RUP.trueClause a (checkedClause row2335) := by
  apply Type2.RUP.derive (premises := [row2284, row2332, row1676, row2191, row225]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2284 a assignment, clause2332 a assignment, clause1676 a assignment,
    clause2191 a assignment, clause225 a assignment⟩

private def row2336 : List Int := [-53, -48, 46, 58, -60, -67]
include assignment in
private theorem clause2336 : Type2.RUP.trueClause a (checkedClause row2336) := by
  apply Type2.RUP.derive (premises := [row231, row2191]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause231 a assignment, clause2191 a assignment⟩

private def row2337 : List Int := [-44, 40, -63, 53]
include assignment in
private theorem clause2337 : Type2.RUP.trueClause a (checkedClause row2337) := by
  apply Type2.RUP.derive (premises := [row148, row158]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause148 a assignment, clause158 a assignment⟩

private def row2338 : List Int := [53, 46, -52, 65, -63, 56, -66, -67, 69]
include assignment in
private theorem clause2338 : Type2.RUP.trueClause a (checkedClause row2338) := by
  apply Type2.RUP.derive (premises := [row1650, row1672, row1687, row2334, row2337, row1076, row1124, row2185, row5, row211, row367, row500,
    row662, row713, row1185, row2152]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1650 a assignment, clause1672 a assignment, clause1687 a assignment,
    clause2334 a assignment, clause2337 a assignment, clause1076 a assignment,
    clause1124 a assignment, clause2185 a assignment, clause5 a assignment,
    clause211 a assignment, clause367 a assignment, clause500 a assignment,
    clause662 a assignment, clause713 a assignment, clause1185 a assignment,
    clause2152 a assignment⟩

private def row2339 : List Int := [-52, 58, -63, 56, -67, 69, -68]
include assignment in
private theorem clause2339 : Type2.RUP.trueClause a (checkedClause row2339) := by
  apply Type2.RUP.derive (premises := [row323, row2330, row405, row1368, row1455, row2197, row2335, row369, row2338, row2336, row223, row1352,
    row1439, row2140, row258, row279, row1484, row2046, row2151, row2152]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause323 a assignment, clause2330 a assignment, clause405 a assignment,
    clause1368 a assignment, clause1455 a assignment, clause2197 a assignment,
    clause2335 a assignment, clause369 a assignment, clause2338 a assignment,
    clause2336 a assignment, clause223 a assignment, clause1352 a assignment,
    clause1439 a assignment, clause2140 a assignment, clause258 a assignment,
    clause279 a assignment, clause1484 a assignment, clause2046 a assignment,
    clause2151 a assignment, clause2152 a assignment⟩

private def row2340 : List Int := [46, 52, 65, -64, -63, -62, -66, -67]
include assignment in
private theorem clause2340 : Type2.RUP.trueClause a (checkedClause row2340) := by
  apply Type2.RUP.derive (premises := [row396, row1671, row2333, row1634, row2279, row2337, row123, row1201, row2152, row197]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause396 a assignment, clause1671 a assignment, clause2333 a assignment,
    clause1634 a assignment, clause2279 a assignment, clause2337 a assignment,
    clause123 a assignment, clause1201 a assignment, clause2152 a assignment,
    clause197 a assignment⟩

private def row2341 : List Int := [55, 53, 52]
include assignment in
private theorem clause2341 : Type2.RUP.trueClause a (checkedClause row2341) := by
  apply Type2.RUP.derive (premises := [row2332, row282, row287]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause282 a assignment, clause287 a assignment⟩

private def row2342 : List Int := [53, -46, 52, -64, -61, 58, -60, -67, 69, -68]
include assignment in
private theorem clause2342 : Type2.RUP.trueClause a (checkedClause row2342) := by
  apply Type2.RUP.derive (premises := [row2283, row2330, row2341, row236, row297, row898, row1562, row1796, row2190]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2283 a assignment, clause2330 a assignment, clause2341 a assignment,
    clause236 a assignment, clause297 a assignment, clause898 a assignment,
    clause1562 a assignment, clause1796 a assignment, clause2190 a assignment⟩

private def row2343 : List Int := [58, -63, -62, -67, 69, -68]
include assignment in
private theorem clause2343 : Type2.RUP.trueClause a (checkedClause row2343) := by
  apply Type2.RUP.derive (premises := [row2286, row2330, row2334, row2339, row405, row1368, row1455, row2197, row358, row369, row2340, row2342,
    row1641, row2195, row2281, row15, row225, row677, row1087]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2286 a assignment, clause2330 a assignment, clause2334 a assignment,
    clause2339 a assignment, clause405 a assignment, clause1368 a assignment,
    clause1455 a assignment, clause2197 a assignment, clause358 a assignment,
    clause369 a assignment, clause2340 a assignment, clause2342 a assignment,
    clause1641 a assignment, clause2195 a assignment, clause2281 a assignment,
    clause15 a assignment, clause225 a assignment, clause677 a assignment,
    clause1087 a assignment⟩

private def row2344 : List Int := [-61, -64, -68, -58]
include assignment in
private theorem clause2344 : Type2.RUP.trueClause a (checkedClause row2344) := by
  apply Type2.RUP.derive (premises := [row343, row346]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause343 a assignment, clause346 a assignment⟩

private def row2345 : List Int := [-63, -62, -67, 69, -68]
include assignment in
private theorem clause2345 : Type2.RUP.trueClause a (checkedClause row2345) := by
  apply Type2.RUP.derive (premises := [row2330, row2343, row405, row1855, row2333, row2334, row2344, row351, row1455, row1530]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2330 a assignment, clause2343 a assignment, clause405 a assignment,
    clause1855 a assignment, clause2333 a assignment, clause2334 a assignment,
    clause2344 a assignment, clause351 a assignment, clause1455 a assignment,
    clause1530 a assignment⟩

private def row2346 : List Int := [-46, -58, 56, -67]
include assignment in
private theorem clause2346 : Type2.RUP.trueClause a (checkedClause row2346) := by
  apply Type2.RUP.derive (premises := [row2195, row2219, row1321]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2195 a assignment, clause2219 a assignment, clause1321 a assignment⟩

private def row2347 : List Int := [-48, -53, -61, -58, -62, -67, 69, -68]
include assignment in
private theorem clause2347 : Type2.RUP.trueClause a (checkedClause row2347) := by
  apply Type2.RUP.derive (premises := [row2330, row2344, row2345, row356, row405, row1379, row1537, row1788, row1815, row2094, row2346, row231,
    row369, row1554, row1563, row1671, row1739, row2033, row169]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2330 a assignment, clause2344 a assignment, clause2345 a assignment,
    clause356 a assignment, clause405 a assignment, clause1379 a assignment,
    clause1537 a assignment, clause1788 a assignment, clause1815 a assignment,
    clause2094 a assignment, clause2346 a assignment, clause231 a assignment,
    clause369 a assignment, clause1554 a assignment, clause1563 a assignment,
    clause1671 a assignment, clause1739 a assignment, clause2033 a assignment,
    clause169 a assignment⟩

private def row2348 : List Int := [48, 46, 56, -67, -58]
include assignment in
private theorem clause2348 : Type2.RUP.trueClause a (checkedClause row2348) := by
  apply Type2.RUP.derive (premises := [row1330, row2210, row2218]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1330 a assignment, clause2210 a assignment, clause2218 a assignment⟩

private def row2349 : List Int := [-50, 53, 60, -59, -61, -48, 46, 63, -67, 69, -68]
include assignment in
private theorem clause2349 : Type2.RUP.trueClause a (checkedClause row2349) := by
  apply Type2.RUP.derive (premises := [row1612, row1952, row2291, row1397, row1554, row89]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1612 a assignment, clause1952 a assignment, clause2291 a assignment,
    clause1397 a assignment, clause1554 a assignment, clause89 a assignment⟩

private def row2350 : List Int := [-55, -54, -53, -52]
include assignment in
private theorem clause2350 : Type2.RUP.trueClause a (checkedClause row2350) := by
  apply Type2.RUP.derive (premises := [row286, row289]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause286 a assignment, clause289 a assignment⟩

private def row2351 : List Int := [55, -54, 53, -52]
include assignment in
private theorem clause2351 : Type2.RUP.trueClause a (checkedClause row2351) := by
  apply Type2.RUP.derive (premises := [row281, row290]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause281 a assignment, clause290 a assignment⟩

private def row2352 : List Int := [-55, -54, -53, 52]
include assignment in
private theorem clause2352 : Type2.RUP.trueClause a (checkedClause row2352) := by
  apply Type2.RUP.derive (premises := [row295, row2277, row2328, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause295 a assignment, clause2277 a assignment, clause2328 a assignment,
    clause2329 a assignment, clause2330 a assignment⟩

private def row2353 : List Int := [-55, 54, 53, 52]
include assignment in
private theorem clause2353 : Type2.RUP.trueClause a (checkedClause row2353) := by
  apply Type2.RUP.derive (premises := [row297, row2277, row2328, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause297 a assignment, clause2277 a assignment, clause2328 a assignment,
    clause2329 a assignment, clause2330 a assignment⟩

private def row2354 : List Int := [-55, 54, -53, -52]
include assignment in
private theorem clause2354 : Type2.RUP.trueClause a (checkedClause row2354) := by
  apply Type2.RUP.derive (premises := [row283, row299]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause283 a assignment, clause299 a assignment⟩

private def row2355 : List Int := [-64, 65, 63, 62]
include assignment in
private theorem clause2355 : Type2.RUP.trueClause a (checkedClause row2355) := by
  apply Type2.RUP.derive (premises := [row382, row398]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause382 a assignment, clause398 a assignment⟩

private def row2356 : List Int := [63, 62, 65, 64]
include assignment in
private theorem clause2356 : Type2.RUP.trueClause a (checkedClause row2356) := by
  apply Type2.RUP.derive (premises := [row385, row2277, row2302, row2323, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause385 a assignment, clause2277 a assignment, clause2302 a assignment,
    clause2323 a assignment, clause2329 a assignment, clause2330 a assignment⟩

private def row2357 : List Int := [65, 64, -62, -63]
include assignment in
private theorem clause2357 : Type2.RUP.trueClause a (checkedClause row2357) := by
  apply Type2.RUP.derive (premises := [row387, row388]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause387 a assignment, clause388 a assignment⟩

private def row2358 : List Int := [-65, -64, 63, 62]
include assignment in
private theorem clause2358 : Type2.RUP.trueClause a (checkedClause row2358) := by
  apply Type2.RUP.derive (premises := [row386, row389]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause386 a assignment, clause389 a assignment⟩

private def row2359 : List Int := [-63, 62, 65, 64]
include assignment in
private theorem clause2359 : Type2.RUP.trueClause a (checkedClause row2359) := by
  apply Type2.RUP.derive (premises := [row393, row2277, row2302, row2323, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause393 a assignment, clause2277 a assignment, clause2302 a assignment,
    clause2323 a assignment, clause2329 a assignment, clause2330 a assignment⟩

private def row2360 : List Int := [-65, 64, 63, 62]
include assignment in
private theorem clause2360 : Type2.RUP.trueClause a (checkedClause row2360) := by
  apply Type2.RUP.derive (premises := [row397, row2277, row2326, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause397 a assignment, clause2277 a assignment, clause2326 a assignment,
    clause2329 a assignment, clause2330 a assignment⟩

private def row2361 : List Int := [-65, 64, -63, -62]
include assignment in
private theorem clause2361 : Type2.RUP.trueClause a (checkedClause row2361) := by
  apply Type2.RUP.derive (premises := [row383, row399]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause383 a assignment, clause399 a assignment⟩

private def row2362 : List Int := [66, 67, 69, -68]
include assignment in
private theorem clause2362 : Type2.RUP.trueClause a (checkedClause row2362) := by
  apply Type2.RUP.derive (premises := [row402, row418]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause402 a assignment, clause418 a assignment⟩

private def row2363 : List Int := [66, -67, 69, -68]
include assignment in
private theorem clause2363 : Type2.RUP.trueClause a (checkedClause row2363) := by
  apply Type2.RUP.derive (premises := [row405, row408]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause405 a assignment, clause408 a assignment⟩

private def row2364 : List Int := [-69, 67, -68, 66]
include assignment in
private theorem clause2364 : Type2.RUP.trueClause a (checkedClause row2364) := by
  apply Type2.RUP.derive (premises := [row407, row2227]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause407 a assignment, clause2227 a assignment⟩

private def row2365 : List Int := [-66, 67, 69, -68]
include assignment in
private theorem clause2365 : Type2.RUP.trueClause a (checkedClause row2365) := by
  apply Type2.RUP.derive (premises := [row401, row410]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause401 a assignment, clause410 a assignment⟩

private def row2366 : List Int := [-69, -67, -68, 66]
include assignment in
private theorem clause2366 : Type2.RUP.trueClause a (checkedClause row2366) := by
  apply Type2.RUP.derive (premises := [row415, row2198]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause415 a assignment, clause2198 a assignment⟩

private def row2367 : List Int := [-52, 40, 63, -53, -62]
include assignment in
private theorem clause2367 : Type2.RUP.trueClause a (checkedClause row2367) := by
  apply Type2.RUP.derive (premises := [row1653, row2277, row2328, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1653 a assignment, clause2277 a assignment, clause2328 a assignment,
    clause2329 a assignment, clause2330 a assignment⟩

private def row2368 : List Int := [-40, -52, -63, 53, -62]
include assignment in
private theorem clause2368 : Type2.RUP.trueClause a (checkedClause row2368) := by
  apply Type2.RUP.derive (premises := [row1660, row2277, row2328, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1660 a assignment, clause2277 a assignment, clause2328 a assignment,
    clause2329 a assignment, clause2330 a assignment⟩

private def row2369 : List Int := [-52, 46, 67, 53, 66]
include assignment in
private theorem clause2369 : Type2.RUP.trueClause a (checkedClause row2369) := by
  apply Type2.RUP.derive (premises := [row1668, row2277, row2327, row2329]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1668 a assignment, clause2277 a assignment, clause2327 a assignment,
    clause2329 a assignment⟩

private def row2370 : List Int := [52, -46, 67, 53, -66]
include assignment in
private theorem clause2370 : Type2.RUP.trueClause a (checkedClause row2370) := by
  apply Type2.RUP.derive (premises := [row1678, row2277, row2327, row2329]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1678 a assignment, clause2277 a assignment, clause2327 a assignment,
    clause2329 a assignment⟩

private def row2371 : List Int := [62, 56, -67, -63, -66]
include assignment in
private theorem clause2371 : Type2.RUP.trueClause a (checkedClause row2371) := by
  apply Type2.RUP.derive (premises := [row1687, row2277, row2296, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1687 a assignment, clause2277 a assignment, clause2296 a assignment,
    clause2330 a assignment⟩

private def row2372 : List Int := [-47, 52, 68, 54, -66]
include assignment in
private theorem clause2372 : Type2.RUP.trueClause a (checkedClause row2372) := by
  apply Type2.RUP.derive (premises := [row2246, row2248]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2246 a assignment, clause2248 a assignment⟩

private def row2373 : List Int := [-57, 64, -68, -62, -66]
include assignment in
private theorem clause2373 : Type2.RUP.trueClause a (checkedClause row2373) := by
  apply Type2.RUP.derive (premises := [row1778, row2228, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1778 a assignment, clause2228 a assignment, clause2329 a assignment,
    clause2330 a assignment⟩

private def row2374 : List Int := [42, -54, -64, 53, -63]
include assignment in
private theorem clause2374 : Type2.RUP.trueClause a (checkedClause row2374) := by
  apply Type2.RUP.derive (premises := [row1812, row2264, row2277, row2326, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1812 a assignment, clause2264 a assignment, clause2277 a assignment,
    clause2326 a assignment, clause2329 a assignment, clause2330 a assignment⟩

private def row2375 : List Int := [-53, 48, 68, -54, -67]
include assignment in
private theorem clause2375 : Type2.RUP.trueClause a (checkedClause row2375) := by
  apply Type2.RUP.derive (premises := [row1830, row2282, row2289]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1830 a assignment, clause2282 a assignment, clause2289 a assignment⟩

private def row2376 : List Int := [-64, 58, -68, 63, -67]
include assignment in
private theorem clause2376 : Type2.RUP.trueClause a (checkedClause row2376) := by
  apply Type2.RUP.derive (premises := [row1844, row2198, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1844 a assignment, clause2198 a assignment, clause2330 a assignment⟩

private def row2377 : List Int := [-63, 58, 68, 64, 67]
include assignment in
private theorem clause2377 : Type2.RUP.trueClause a (checkedClause row2377) := by
  apply Type2.RUP.derive (premises := [row1847, row2241, row2327]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1847 a assignment, clause2241 a assignment, clause2327 a assignment⟩

private def row2378 : List Int := [-58, 64, -68, -63, -67]
include assignment in
private theorem clause2378 : Type2.RUP.trueClause a (checkedClause row2378) := by
  apply Type2.RUP.derive (premises := [row1855, row2198, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1855 a assignment, clause2198 a assignment, clause2330 a assignment⟩

private def row2379 : List Int := [43, -55, 65, -52, -62]
include assignment in
private theorem clause2379 : Type2.RUP.trueClause a (checkedClause row2379) := by
  apply Type2.RUP.derive (premises := [row1893, row2131, row2132]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1893 a assignment, clause2131 a assignment, clause2132 a assignment⟩

private def row2380 : List Int := [-43, 55, -65, -52, -62]
include assignment in
private theorem clause2380 : Type2.RUP.trueClause a (checkedClause row2380) := by
  apply Type2.RUP.derive (premises := [row1900, row2277, row2328, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1900 a assignment, clause2277 a assignment, clause2328 a assignment,
    clause2329 a assignment, clause2330 a assignment⟩

private def row2381 : List Int := [49, 55, 69, -52, 66]
include assignment in
private theorem clause2381 : Type2.RUP.trueClause a (checkedClause row2381) := by
  apply Type2.RUP.derive (premises := [row1908, row2328, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1908 a assignment, clause2328 a assignment, clause2329 a assignment,
    clause2330 a assignment⟩

private def row2382 : List Int := [49, -55, 69, -52, -66]
include assignment in
private theorem clause2382 : Type2.RUP.trueClause a (checkedClause row2382) := by
  apply Type2.RUP.derive (premises := [row1909, row2131, row2132]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1909 a assignment, clause2131 a assignment, clause2132 a assignment⟩

private def row2383 : List Int := [49, 52, -69, -55, -66]
include assignment in
private theorem clause2383 : Type2.RUP.trueClause a (checkedClause row2383) := by
  apply Type2.RUP.derive (premises := [row1911, row2180, row2223, row2274, row2275]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1911 a assignment, clause2180 a assignment, clause2223 a assignment,
    clause2274 a assignment, clause2275 a assignment⟩

private def row2384 : List Int := [-59, 62, 69, 65, -66]
include assignment in
private theorem clause2384 : Type2.RUP.trueClause a (checkedClause row2384) := by
  apply Type2.RUP.derive (premises := [row1934, row2302, row2323, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1934 a assignment, clause2302 a assignment, clause2323 a assignment,
    clause2329 a assignment, clause2330 a assignment⟩

private def row2385 : List Int := [44, -55, -65, 53, -63]
include assignment in
private theorem clause2385 : Type2.RUP.trueClause a (checkedClause row2385) := by
  apply Type2.RUP.derive (premises := [row1978, row2277, row2328, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1978 a assignment, clause2277 a assignment, clause2328 a assignment,
    clause2329 a assignment, clause2330 a assignment⟩

private def row2386 : List Int := [44, 55, -65, 53, 63]
include assignment in
private theorem clause2386 : Type2.RUP.trueClause a (checkedClause row2386) := by
  apply Type2.RUP.derive (premises := [row1979, row2277, row2328, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1979 a assignment, clause2277 a assignment, clause2328 a assignment,
    clause2329 a assignment, clause2330 a assignment⟩

private def row2387 : List Int := [-44, 55, -65, -53, -63]
include assignment in
private theorem clause2387 : Type2.RUP.trueClause a (checkedClause row2387) := by
  apply Type2.RUP.derive (premises := [row1985, row2277, row2328, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1985 a assignment, clause2277 a assignment, clause2328 a assignment,
    clause2329 a assignment, clause2330 a assignment⟩

private def row2388 : List Int := [-60, -65, 69, 63, 67]
include assignment in
private theorem clause2388 : Type2.RUP.trueClause a (checkedClause row2388) := by
  apply Type2.RUP.derive (premises := [row2018, row2327, row2329]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2018 a assignment, clause2327 a assignment, clause2329 a assignment⟩

private def row2389 : List Int := [64, 65, 69, -61, -68]
include assignment in
private theorem clause2389 : Type2.RUP.trueClause a (checkedClause row2389) := by
  apply Type2.RUP.derive (premises := [row2094, row2329, row2330]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2094 a assignment, clause2329 a assignment, clause2330 a assignment⟩

private def row2390 : List Int := [-51, 47, 36, 50, 53, -59, 64, -48, 46, 63, 56, -68]
include assignment in
private theorem clause2390 : Type2.RUP.trueClause a (checkedClause row2390) := by
  apply Type2.RUP.derive (premises := [row243, row571, row2136, row2185, row13, row142, row150]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause243 a assignment, clause571 a assignment, clause2136 a assignment,
    clause2185 a assignment, clause13 a assignment, clause142 a assignment,
    clause150 a assignment⟩

private def row2391 : List Int := [36, 50, 53, -59, -61, -48, 46, -58, 63, 56, -66, -68]
include assignment in
private theorem clause2391 : Type2.RUP.trueClause a (checkedClause row2391) := by
  apply Type2.RUP.derive (premises := [row2344, row356, row1307, row2390, row251, row1563, row2136, row51]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2344 a assignment, clause356 a assignment, clause1307 a assignment,
    clause2390 a assignment, clause251 a assignment, clause1563 a assignment,
    clause2136 a assignment, clause51 a assignment⟩

private def row2392 : List Int := [-39, 37, 60, 50]
include assignment in
private theorem clause2392 : Type2.RUP.trueClause a (checkedClause row2392) := by
  apply Type2.RUP.derive (premises := [row85, row93]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause85 a assignment, clause93 a assignment⟩

private def row2393 : List Int := [-39, -36, 50, 60, -58, 56]
include assignment in
private theorem clause2393 : Type2.RUP.trueClause a (checkedClause row2393) := by
  apply Type2.RUP.derive (premises := [row925, row2392]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause925 a assignment, clause2392 a assignment⟩

private def row2394 : List Int := [-61, -58, -62, -67, 69, -68]
include assignment in
private theorem clause2394 : Type2.RUP.trueClause a (checkedClause row2394) := by
  apply Type2.RUP.derive (premises := [row2344, row2345, row2363, row2373, row2389, row1379, row1537, row2346, row2348, row369, row2347, row2349,
    row2391, row2393, row52, row946, row1244, row1563, row106]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2344 a assignment, clause2345 a assignment, clause2363 a assignment,
    clause2373 a assignment, clause2389 a assignment, clause1379 a assignment,
    clause1537 a assignment, clause2346 a assignment, clause2348 a assignment,
    clause369 a assignment, clause2347 a assignment, clause2349 a assignment,
    clause2391 a assignment, clause2393 a assignment, clause52 a assignment,
    clause946 a assignment, clause1244 a assignment, clause1563 a assignment,
    clause106 a assignment⟩

private def row2395 : List Int := [45, -51, 39, 61]
include assignment in
private theorem clause2395 : Type2.RUP.trueClause a (checkedClause row2395) := by
  apply Type2.RUP.derive (premises := [row109, row117]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause109 a assignment, clause117 a assignment⟩

private def row2396 : List Int := [-51, 39, 64, -65, 53, 61, 69, -68]
include assignment in
private theorem clause2396 : Type2.RUP.trueClause a (checkedClause row2396) := by
  apply Type2.RUP.derive (premises := [row2395, row2032, row2045, row2341, row2351]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2395 a assignment, clause2032 a assignment, clause2045 a assignment,
    clause2341 a assignment, clause2351 a assignment⟩

private def row2397 : List Int := [-55, 51, 69, 50]
include assignment in
private theorem clause2397 : Type2.RUP.trueClause a (checkedClause row2397) := by
  apply Type2.RUP.derive (premises := [row269, row277]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause269 a assignment, clause277 a assignment⟩

private def row2398 : List Int := [51, 50, 69]
include assignment in
private theorem clause2398 : Type2.RUP.trueClause a (checkedClause row2398) := by
  apply Type2.RUP.derive (premises := [row2309, row2397]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2309 a assignment, clause2397 a assignment⟩

private def row2399 : List Int := [65, 61, 69, 60]
include assignment in
private theorem clause2399 : Type2.RUP.trueClause a (checkedClause row2399) := by
  apply Type2.RUP.derive (premises := [row362, row365]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause362 a assignment, clause365 a assignment⟩

private def row2400 : List Int := [51, -48, -67, 69, -68]
include assignment in
private theorem clause2400 : Type2.RUP.trueClause a (checkedClause row2400) := by
  apply Type2.RUP.derive (premises := [row1591, row2309, row2397]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1591 a assignment, clause2309 a assignment, clause2397 a assignment⟩

private def row2401 : List Int := [-58, -62, -67, 69, -68]
include assignment in
private theorem clause2401 : Type2.RUP.trueClause a (checkedClause row2401) := by
  apply Type2.RUP.derive (premises := [row2330, row2345, row2363, row2394, row1607, row1692, row2346, row2348, row2399, row2400, row377, row965,
    row1205, row1570, row2395, row2396, row102, row231, row958, row1397]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2330 a assignment, clause2345 a assignment, clause2363 a assignment,
    clause2394 a assignment, clause1607 a assignment, clause1692 a assignment,
    clause2346 a assignment, clause2348 a assignment, clause2399 a assignment,
    clause2400 a assignment, clause377 a assignment, clause965 a assignment,
    clause1205 a assignment, clause1570 a assignment, clause2395 a assignment,
    clause2396 a assignment, clause102 a assignment, clause231 a assignment,
    clause958 a assignment, clause1397 a assignment⟩

private def row2402 : List Int := [-62, -67, 69, -68]
include assignment in
private theorem clause2402 : Type2.RUP.trueClause a (checkedClause row2402) := by
  apply Type2.RUP.derive (premises := [row2330, row2345, row2363, row2401, row1844, row2373, row348, row358]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2330 a assignment, clause2345 a assignment, clause2363 a assignment,
    clause2401 a assignment, clause1844 a assignment, clause2373 a assignment,
    clause348 a assignment, clause358 a assignment⟩

private def row2403 : List Int := [58, -61, -67, 69, -68]
include assignment in
private theorem clause2403 : Type2.RUP.trueClause a (checkedClause row2403) := by
  apply Type2.RUP.derive (premises := [row1612, row2187, row2330, row2363, row2402, row338, row1687]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1612 a assignment, clause2187 a assignment, clause2330 a assignment,
    clause2363 a assignment, clause2402 a assignment, clause338 a assignment,
    clause1687 a assignment⟩

private def row2404 : List Int := [-61, -67, 69, -68]
include assignment in
private theorem clause2404 : Type2.RUP.trueClause a (checkedClause row2404) := by
  apply Type2.RUP.derive (premises := [row2330, row2402, row2403, row2344, row2378, row2389, row397]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2330 a assignment, clause2402 a assignment, clause2403 a assignment,
    clause2344 a assignment, clause2378 a assignment, clause2389 a assignment,
    clause397 a assignment⟩

private def row2405 : List Int := [-58, -67, 69, -68]
include assignment in
private theorem clause2405 : Type2.RUP.trueClause a (checkedClause row2405) := by
  apply Type2.RUP.derive (premises := [row2330, row2363, row2401, row2404, row1607, row2399, row377, row1444, row1530, row1687, row1769, row2360]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2330 a assignment, clause2363 a assignment, clause2401 a assignment,
    clause2404 a assignment, clause1607 a assignment, clause2399 a assignment,
    clause377 a assignment, clause1444 a assignment, clause1530 a assignment,
    clause1687 a assignment, clause1769 a assignment, clause2360 a assignment⟩

private def row2406 : List Int := [-67, 69, -68]
include assignment in
private theorem clause2406 : Type2.RUP.trueClause a (checkedClause row2406) := by
  apply Type2.RUP.derive (premises := [row2363, row2402, row2404, row2405, row2197, row2286, row2371, row2376, row354]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2363 a assignment, clause2402 a assignment, clause2404 a assignment,
    clause2405 a assignment, clause2197 a assignment, clause2286 a assignment,
    clause2371 a assignment, clause2376 a assignment, clause354 a assignment⟩

private def row2407 : List Int := [67, 69, -68]
include assignment in
private theorem clause2407 : Type2.RUP.trueClause a (checkedClause row2407) := by
  apply Type2.RUP.derive (premises := [row2362, row2365]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2362 a assignment, clause2365 a assignment⟩

private def row2408 : List Int := [69, -68]
include assignment in
private theorem clause2408 : Type2.RUP.trueClause a (checkedClause row2408) := by
  apply Type2.RUP.derive (premises := [row2406, row2407]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2406 a assignment, clause2407 a assignment⟩

private def row2409 : List Int := [-52, -53, -55]
include assignment in
private theorem clause2409 : Type2.RUP.trueClause a (checkedClause row2409) := by
  apply Type2.RUP.derive (premises := [row2350, row2354]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2350 a assignment, clause2354 a assignment⟩

private def row2410 : List Int := [-42, -45, 54, -64]
include assignment in
private theorem clause2410 : Type2.RUP.trueClause a (checkedClause row2410) := by
  apply Type2.RUP.derive (premises := [row168, row176]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause168 a assignment, clause176 a assignment⟩

private def row2411 : List Int := [-39, 36, 58, -48]
include assignment in
private theorem clause2411 : Type2.RUP.trueClause a (checkedClause row2411) := by
  apply Type2.RUP.derive (premises := [row40, row55]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause40 a assignment, clause55 a assignment⟩

private def row2412 : List Int := [50, -52, -51, 56, 58, 61, 67, -68]
include assignment in
private theorem clause2412 : Type2.RUP.trueClause a (checkedClause row2412) := by
  apply Type2.RUP.derive (premises := [row2197, row2332, row2407, row354, row407, row2124, row2183, row2409, row729, row1509, row2195, row1316,
    row2411, row57, row243, row2395, row2410]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2197 a assignment, clause2332 a assignment, clause2407 a assignment,
    clause354 a assignment, clause407 a assignment, clause2124 a assignment,
    clause2183 a assignment, clause2409 a assignment, clause729 a assignment,
    clause1509 a assignment, clause2195 a assignment, clause1316 a assignment,
    clause2411 a assignment, clause57 a assignment, clause243 a assignment,
    clause2395 a assignment, clause2410 a assignment⟩

private def row2413 : List Int := [-50, -51, -69]
include assignment in
private theorem clause2413 : Type2.RUP.trueClause a (checkedClause row2413) := by
  apply Type2.RUP.derive (premises := [row2124, row2180, row266]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2124 a assignment, clause2180 a assignment, clause266 a assignment⟩

private def row2414 : List Int := [-51, 56, 58, 61, 67, -68]
include assignment in
private theorem clause2414 : Type2.RUP.trueClause a (checkedClause row2414) := by
  apply Type2.RUP.derive (premises := [row2332, row2407, row2413, row407, row2124, row2183, row2383, row2412]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2407 a assignment, clause2413 a assignment,
    clause407 a assignment, clause2124 a assignment, clause2183 a assignment,
    clause2383 a assignment, clause2412 a assignment⟩

private def row2415 : List Int := [52, -55, 51, 67, -68]
include assignment in
private theorem clause2415 : Type2.RUP.trueClause a (checkedClause row2415) := by
  apply Type2.RUP.derive (premises := [row2332, row2407, row407, row1911, row2071, row2183, row2352, row2370, row224, row227]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2407 a assignment, clause407 a assignment,
    clause1911 a assignment, clause2071 a assignment, clause2183 a assignment,
    clause2352 a assignment, clause2370 a assignment, clause224 a assignment,
    clause227 a assignment⟩

private def row2416 : List Int := [48, -54, 51, -68]
include assignment in
private theorem clause2416 : Type2.RUP.trueClause a (checkedClause row2416) := by
  apply Type2.RUP.derive (premises := [row245, row246]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause245 a assignment, clause246 a assignment⟩

private def row2417 : List Int := [-55, 51, 67, -68]
include assignment in
private theorem clause2417 : Type2.RUP.trueClause a (checkedClause row2417) := by
  apply Type2.RUP.derive (premises := [row2332, row2407, row2415, row2071, row2350, row2416, row251, row650, row2226]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2407 a assignment, clause2415 a assignment,
    clause2071 a assignment, clause2350 a assignment, clause2416 a assignment,
    clause251 a assignment, clause650 a assignment, clause2226 a assignment⟩

private def row2418 : List Int := [-48, 51, 67, -68]
include assignment in
private theorem clause2418 : Type2.RUP.trueClause a (checkedClause row2418) := by
  apply Type2.RUP.derive (premises := [row2230, row2407, row1593, row2208]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2230 a assignment, clause2407 a assignment, clause1593 a assignment,
    clause2208 a assignment⟩

private def row2419 : List Int := [56, 58, 61, 67, -68]
include assignment in
private theorem clause2419 : Type2.RUP.trueClause a (checkedClause row2419) := by
  apply Type2.RUP.derive (premises := [row2197, row2200, row2332, row2407, row2414, row2417, row2418, row324, row354, row407, row1059, row1288,
    row2127, row2167, row2416, row254, row1476, row1518, row2144]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2197 a assignment, clause2200 a assignment, clause2332 a assignment,
    clause2407 a assignment, clause2414 a assignment, clause2417 a assignment,
    clause2418 a assignment, clause324 a assignment, clause354 a assignment,
    clause407 a assignment, clause1059 a assignment, clause1288 a assignment,
    clause2127 a assignment, clause2167 a assignment, clause2416 a assignment,
    clause254 a assignment, clause1476 a assignment, clause1518 a assignment,
    clause2144 a assignment⟩

private def row2420 : List Int := [59, -56, -57, -66]
include assignment in
private theorem clause2420 : Type2.RUP.trueClause a (checkedClause row2420) := by
  apply Type2.RUP.derive (premises := [row305, row308]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause305 a assignment, clause308 a assignment⟩

private def row2421 : List Int := [51, -38, 49, 58, 61, 67, -68]
include assignment in
private theorem clause2421 : Type2.RUP.trueClause a (checkedClause row2421) := by
  apply Type2.RUP.derive (premises := [row2197, row2332, row2407, row2417, row2418, row2419, row354, row407, row2272, row2416, row2420, row254,
    row316, row972, row1217, row1304, row1382, row1829, row2142, row2232, row2267, row2367, row2387, row87,
    row99]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2197 a assignment, clause2332 a assignment, clause2407 a assignment,
    clause2417 a assignment, clause2418 a assignment, clause2419 a assignment,
    clause354 a assignment, clause407 a assignment, clause2272 a assignment,
    clause2416 a assignment, clause2420 a assignment, clause254 a assignment,
    clause316 a assignment, clause972 a assignment, clause1217 a assignment,
    clause1304 a assignment, clause1382 a assignment, clause1829 a assignment,
    clause2142 a assignment, clause2232 a assignment, clause2267 a assignment,
    clause2367 a assignment, clause2387 a assignment, clause87 a assignment,
    clause99 a assignment⟩

private def row2422 : List Int := [-38, 49, 58, 61, 67, -68]
include assignment in
private theorem clause2422 : Type2.RUP.trueClause a (checkedClause row2422) := by
  apply Type2.RUP.derive (premises := [row2197, row2332, row2407, row2419, row2421, row354, row407, row1487, row2123, row2142, row2180, row2242,
    row2318, row2409, row2420, row729, row933, row972, row1159, row1382, row2232, row87, row2337, row147,
    row166, row178]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2197 a assignment, clause2332 a assignment, clause2407 a assignment,
    clause2419 a assignment, clause2421 a assignment, clause354 a assignment,
    clause407 a assignment, clause1487 a assignment, clause2123 a assignment,
    clause2142 a assignment, clause2180 a assignment, clause2242 a assignment,
    clause2318 a assignment, clause2409 a assignment, clause2420 a assignment,
    clause729 a assignment, clause933 a assignment, clause972 a assignment,
    clause1159 a assignment, clause1382 a assignment, clause2232 a assignment,
    clause87 a assignment, clause2337 a assignment, clause147 a assignment,
    clause166 a assignment, clause178 a assignment⟩

private def row2423 : List Int := [49, 58, 61, 67, -68]
include assignment in
private theorem clause2423 : Type2.RUP.trueClause a (checkedClause row2423) := by
  apply Type2.RUP.derive (premises := [row2197, row2332, row2407, row2419, row2422, row407, row2420, row316, row1467, row1476, row2123, row2142,
    row2180, row2409, row729, row1304, row1710, row34]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2197 a assignment, clause2332 a assignment, clause2407 a assignment,
    clause2419 a assignment, clause2422 a assignment, clause407 a assignment,
    clause2420 a assignment, clause316 a assignment, clause1467 a assignment,
    clause1476 a assignment, clause2123 a assignment, clause2142 a assignment,
    clause2180 a assignment, clause2409 a assignment, clause729 a assignment,
    clause1304 a assignment, clause1710 a assignment, clause34 a assignment⟩

private def row2424 : List Int := [50, -49, -69]
include assignment in
private theorem clause2424 : Type2.RUP.trueClause a (checkedClause row2424) := by
  apply Type2.RUP.derive (premises := [row2183, row261, row274]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2183 a assignment, clause261 a assignment, clause274 a assignment⟩

private def row2425 : List Int := [58, 61, 67, -68]
include assignment in
private theorem clause2425 : Type2.RUP.trueClause a (checkedClause row2425) := by
  apply Type2.RUP.derive (premises := [row2332, row2407, row2419, row2423, row2424, row407, row1433, row2230, row2272]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2407 a assignment, clause2419 a assignment,
    clause2423 a assignment, clause2424 a assignment, clause407 a assignment,
    clause1433 a assignment, clause2230 a assignment, clause2272 a assignment⟩

private def row2426 : List Int := [57, 59, -66, -56]
include assignment in
private theorem clause2426 : Type2.RUP.trueClause a (checkedClause row2426) := by
  apply Type2.RUP.derive (premises := [row306, row314]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause306 a assignment, clause314 a assignment⟩

private def row2427 : List Int := [61, 67, -68]
include assignment in
private theorem clause2427 : Type2.RUP.trueClause a (checkedClause row2427) := by
  apply Type2.RUP.derive (premises := [row2332, row2407, row2425, row1609, row2205, row322, row1854, row2016, row2357, row2359]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2407 a assignment, clause2425 a assignment,
    clause1609 a assignment, clause2205 a assignment, clause322 a assignment,
    clause1854 a assignment, clause2016 a assignment, clause2357 a assignment,
    clause2359 a assignment⟩

private def row2428 : List Int := [67, -69, -68]
include assignment in
private theorem clause2428 : Type2.RUP.trueClause a (checkedClause row2428) := by
  apply Type2.RUP.derive (premises := [row2364, row2427, row2170, row2146, row2196, row1525, row1618, row2205, row2426]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2364 a assignment, clause2427 a assignment, clause2170 a assignment,
    clause2146 a assignment, clause2196 a assignment, clause1525 a assignment,
    clause1618 a assignment, clause2205 a assignment, clause2426 a assignment⟩

private def row2429 : List Int := [38, -39, 51, -61]
include assignment in
private theorem clause2429 : Type2.RUP.trueClause a (checkedClause row2429) := by
  apply Type2.RUP.derive (premises := [row103, row108]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause103 a assignment, clause108 a assignment⟩

private def row2430 : List Int := [-38, -47, 57, -36]
include assignment in
private theorem clause2430 : Type2.RUP.trueClause a (checkedClause row2430) := by
  apply Type2.RUP.derive (premises := [row27, row39]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause27 a assignment, clause39 a assignment⟩

private def row2431 : List Int := [-49, -61, -58, 57, 56, -68]
include assignment in
private theorem clause2431 : Type2.RUP.trueClause a (checkedClause row2431) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2424, row2428, row415, row2346, row2348, row2413, row567, row1307, row1563, row2429,
    row2430]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2424 a assignment,
    clause2428 a assignment, clause415 a assignment, clause2346 a assignment,
    clause2348 a assignment, clause2413 a assignment, clause567 a assignment,
    clause1307 a assignment, clause1563 a assignment, clause2429 a assignment,
    clause2430 a assignment⟩

private def row2432 : List Int := [-51, -48, -68]
include assignment in
private theorem clause2432 : Type2.RUP.trueClause a (checkedClause row2432) := by
  apply Type2.RUP.derive (premises := [row2408, row2413, row2428, row1592]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2408 a assignment, clause2413 a assignment, clause2428 a assignment,
    clause1592 a assignment⟩

private def row2433 : List Int := [-61, -58, 57, 56, 59, -68]
include assignment in
private theorem clause2433 : Type2.RUP.trueClause a (checkedClause row2433) := by
  apply Type2.RUP.derive (premises := [row971, row2205, row2346, row2348, row2404, row2431, row2432, row1500, row1563, row2429]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause971 a assignment, clause2205 a assignment, clause2346 a assignment,
    clause2348 a assignment, clause2404 a assignment, clause2431 a assignment,
    clause2432 a assignment, clause1500 a assignment, clause1563 a assignment,
    clause2429 a assignment⟩

private def row2434 : List Int := [-39, 38, 61, 51]
include assignment in
private theorem clause2434 : Type2.RUP.trueClause a (checkedClause row2434) := by
  apply Type2.RUP.derive (premises := [row107, row113]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause107 a assignment, clause113 a assignment⟩

private def row2435 : List Int := [38, 65, 61, 51, -60, 59]
include assignment in
private theorem clause2435 : Type2.RUP.trueClause a (checkedClause row2435) := by
  apply Type2.RUP.derive (premises := [row373, row2434, row104, row1186, row2043, row2152]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause373 a assignment, clause2434 a assignment, clause104 a assignment,
    clause1186 a assignment, clause2043 a assignment, clause2152 a assignment⟩

private def row2436 : List Int := [-58, -60, 57, 56, 59, -68]
include assignment in
private theorem clause2436 : Type2.RUP.trueClause a (checkedClause row2436) := by
  apply Type2.RUP.derive (premises := [row2205, row2332, row2346, row2348, row2405, row2432, row2433, row351, row371, row415, row1855, row2435,
    row1486, row1502, row2142, row2257, row73, row251, row652, row662, row2110, row2136]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2205 a assignment, clause2332 a assignment, clause2346 a assignment,
    clause2348 a assignment, clause2405 a assignment, clause2432 a assignment,
    clause2433 a assignment, clause351 a assignment, clause371 a assignment,
    clause415 a assignment, clause1855 a assignment, clause2435 a assignment,
    clause1486 a assignment, clause1502 a assignment, clause2142 a assignment,
    clause2257 a assignment, clause73 a assignment, clause251 a assignment,
    clause652 a assignment, clause662 a assignment, clause2110 a assignment,
    clause2136 a assignment⟩

private def row2437 : List Int := [-60, 57, 56, 59, -68]
include assignment in
private theorem clause2437 : Type2.RUP.trueClause a (checkedClause row2437) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2428, row2436, row338, row966, row2017, row2100]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2428 a assignment,
    clause2436 a assignment, clause338 a assignment, clause966 a assignment,
    clause2017 a assignment, clause2100 a assignment⟩

private def row2438 : List Int := [60, 56, 59, -68]
include assignment in
private theorem clause2438 : Type2.RUP.trueClause a (checkedClause row2438) := by
  apply Type2.RUP.derive (premises := [row2202, row2332, row2334, row2406, row2010, row2196, row368]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2202 a assignment, clause2332 a assignment, clause2334 a assignment,
    clause2406 a assignment, clause2010 a assignment, clause2196 a assignment,
    clause368 a assignment⟩

private def row2439 : List Int := [56, 59, -68]
include assignment in
private theorem clause2439 : Type2.RUP.trueClause a (checkedClause row2439) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2428, row2438, row415, row2437, row303, row311]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2428 a assignment,
    clause2438 a assignment, clause415 a assignment, clause2437 a assignment,
    clause303 a assignment, clause311 a assignment⟩

private def row2440 : List Int := [59, -68]
include assignment in
private theorem clause2440 : Type2.RUP.trueClause a (checkedClause row2440) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2428, row2439, row415, row2420, row2426]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2428 a assignment,
    clause2439 a assignment, clause415 a assignment, clause2420 a assignment,
    clause2426 a assignment⟩

private def row2441 : List Int := [-56, -68]
include assignment in
private theorem clause2441 : Type2.RUP.trueClause a (checkedClause row2441) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2428, row2440, row415, row2333, row301, row316]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2428 a assignment,
    clause2440 a assignment, clause415 a assignment, clause2333 a assignment,
    clause301 a assignment, clause316 a assignment⟩

private def row2442 : List Int := [65, 63, 62]
include assignment in
private theorem clause2442 : Type2.RUP.trueClause a (checkedClause row2442) := by
  apply Type2.RUP.derive (premises := [row2355, row2356]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2355 a assignment, clause2356 a assignment⟩

private def row2443 : List Int := [62, -68]
include assignment in
private theorem clause2443 : Type2.RUP.trueClause a (checkedClause row2443) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2428, row2441, row415, row1687, row2442, row389, row397]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2428 a assignment,
    clause2441 a assignment, clause415 a assignment, clause1687 a assignment,
    clause2442 a assignment, clause389 a assignment, clause397 a assignment⟩

private def row2444 : List Int := [47, 43, 49, 63, -57, -68]
include assignment in
private theorem clause2444 : Type2.RUP.trueClause a (checkedClause row2444) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2428, row2440, row2441, row2443, row315, row1368, row1456, row1778, row1932, row2142,
    row2346, row2348, row2432, row251, row652, row807, row1314, row1388, row1797, row1979, row45, row86,
    row98]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2428 a assignment,
    clause2440 a assignment, clause2441 a assignment, clause2443 a assignment,
    clause315 a assignment, clause1368 a assignment, clause1456 a assignment,
    clause1778 a assignment, clause1932 a assignment, clause2142 a assignment,
    clause2346 a assignment, clause2348 a assignment, clause2432 a assignment,
    clause251 a assignment, clause652 a assignment, clause807 a assignment,
    clause1314 a assignment, clause1388 a assignment, clause1797 a assignment,
    clause1979 a assignment, clause45 a assignment, clause86 a assignment,
    clause98 a assignment⟩

private def row2445 : List Int := [-47, 49, -66, 46]
include assignment in
private theorem clause2445 : Type2.RUP.trueClause a (checkedClause row2445) := by
  apply Type2.RUP.derive (premises := [row203, row211]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause203 a assignment, clause211 a assignment⟩

private def row2446 : List Int := [49, -38, 63, -57, -68]
include assignment in
private theorem clause2446 : Type2.RUP.trueClause a (checkedClause row2446) := by
  apply Type2.RUP.derive (premises := [row2408, row2428, row2440, row2441, row2443, row315, row1368, row2144, row2346, row2444, row2445]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2408 a assignment, clause2428 a assignment, clause2440 a assignment,
    clause2441 a assignment, clause2443 a assignment, clause315 a assignment,
    clause1368 a assignment, clause2144 a assignment, clause2346 a assignment,
    clause2444 a assignment, clause2445 a assignment⟩

private def row2447 : List Int := [43, -39, -49, 63, -58, -68]
include assignment in
private theorem clause2447 : Type2.RUP.trueClause a (checkedClause row2447) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2424, row2428, row2440, row2441, row2443, row415, row1456, row1552, row1864, row1916,
    row2184, row2346, row2409, row671, row688, row828, row2110]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2424 a assignment,
    clause2428 a assignment, clause2440 a assignment, clause2441 a assignment,
    clause2443 a assignment, clause415 a assignment, clause1456 a assignment,
    clause1552 a assignment, clause1864 a assignment, clause1916 a assignment,
    clause2184 a assignment, clause2346 a assignment, clause2409 a assignment,
    clause671 a assignment, clause688 a assignment, clause828 a assignment,
    clause2110 a assignment⟩

private def row2448 : List Int := [-52, -41, -62, -43]
include assignment in
private theorem clause2448 : Type2.RUP.trueClause a (checkedClause row2448) := by
  apply Type2.RUP.derive (premises := [row125, row126]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause125 a assignment, clause126 a assignment⟩

private def row2449 : List Int := [-38, 63, -57, -68]
include assignment in
private theorem clause2449 : Type2.RUP.trueClause a (checkedClause row2449) := by
  apply Type2.RUP.derive (premises := [row2408, row2428, row2440, row2441, row2443, row2446, row315, row1368, row1472, row2185, row2346, row2348,
    row2432, row514, row535, row2447, row1144, row2448, row128, row136]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2408 a assignment, clause2428 a assignment, clause2440 a assignment,
    clause2441 a assignment, clause2443 a assignment, clause2446 a assignment,
    clause315 a assignment, clause1368 a assignment, clause1472 a assignment,
    clause2185 a assignment, clause2346 a assignment, clause2348 a assignment,
    clause2432 a assignment, clause514 a assignment, clause535 a assignment,
    clause2447 a assignment, clause1144 a assignment, clause2448 a assignment,
    clause128 a assignment, clause136 a assignment⟩

private def row2450 : List Int := [38, -58, -68]
include assignment in
private theorem clause2450 : Type2.RUP.trueClause a (checkedClause row2450) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2428, row2440, row2441, row2443, row415, row1932, row2169, row2346, row2348, row2432,
    row2434, row104, row1180, row1492, row2151]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2428 a assignment,
    clause2440 a assignment, clause2441 a assignment, clause2443 a assignment,
    clause415 a assignment, clause1932 a assignment, clause2169 a assignment,
    clause2346 a assignment, clause2348 a assignment, clause2432 a assignment,
    clause2434 a assignment, clause104 a assignment, clause1180 a assignment,
    clause1492 a assignment, clause2151 a assignment⟩

private def row2451 : List Int := [-44, -49, -57, -68]
include assignment in
private theorem clause2451 : Type2.RUP.trueClause a (checkedClause row2451) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2428, row2440, row2441, row2443, row315, row1368, row1456, row1932, row2185, row2450,
    row1099, row1144, row2316, row2380, row128, row136]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2428 a assignment,
    clause2440 a assignment, clause2441 a assignment, clause2443 a assignment,
    clause315 a assignment, clause1368 a assignment, clause1456 a assignment,
    clause1932 a assignment, clause2185 a assignment, clause2450 a assignment,
    clause1099 a assignment, clause1144 a assignment, clause2316 a assignment,
    clause2380 a assignment, clause128 a assignment, clause136 a assignment⟩

private def row2452 : List Int := [-49, -57, -68]
include assignment in
private theorem clause2452 : Type2.RUP.trueClause a (checkedClause row2452) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2424, row2428, row2440, row2441, row2443, row2451, row315, row1368, row1456, row1932,
    row1957, row2185, row2346, row2413, row2450, row2071, row2449, row1076, row1634, row1650, row2350]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2424 a assignment,
    clause2428 a assignment, clause2440 a assignment, clause2441 a assignment,
    clause2443 a assignment, clause2451 a assignment, clause315 a assignment,
    clause1368 a assignment, clause1456 a assignment, clause1932 a assignment,
    clause1957 a assignment, clause2185 a assignment, clause2346 a assignment,
    clause2413 a assignment, clause2450 a assignment, clause2071 a assignment,
    clause2449 a assignment, clause1076 a assignment, clause1634 a assignment,
    clause1650 a assignment, clause2350 a assignment⟩

private def row2453 : List Int := [-57, -68]
include assignment in
private theorem clause2453 : Type2.RUP.trueClause a (checkedClause row2453) := by
  apply Type2.RUP.derive (premises := [row2332, row2408, row2428, row2440, row2441, row2443, row2452, row315, row1368, row1778, row1932, row2169,
    row2346, row2348, row2432, row2445, row2450, row208, row251, row652, row1314, row1388, row1797, row1875,
    row2034, row2444, row5, row45, row156, row468]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2408 a assignment, clause2428 a assignment,
    clause2440 a assignment, clause2441 a assignment, clause2443 a assignment,
    clause2452 a assignment, clause315 a assignment, clause1368 a assignment,
    clause1778 a assignment, clause1932 a assignment, clause2169 a assignment,
    clause2346 a assignment, clause2348 a assignment, clause2432 a assignment,
    clause2445 a assignment, clause2450 a assignment, clause208 a assignment,
    clause251 a assignment, clause652 a assignment, clause1314 a assignment,
    clause1388 a assignment, clause1797 a assignment, clause1875 a assignment,
    clause2034 a assignment, clause2444 a assignment, clause5 a assignment,
    clause45 a assignment, clause156 a assignment, clause468 a assignment⟩

private def row2454 : List Int := [-67, -69, -68]
include assignment in
private theorem clause2454 : Type2.RUP.trueClause a (checkedClause row2454) := by
  apply Type2.RUP.derive (premises := [row2198, row2366, row2440, row2443, row2453, row1534, row1932, row2169]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2198 a assignment, clause2366 a assignment, clause2440 a assignment,
    clause2443 a assignment, clause2453 a assignment, clause1534 a assignment,
    clause1932 a assignment, clause2169 a assignment⟩

private def row2455 : List Int := [-69, -68]
include assignment in
private theorem clause2455 : Type2.RUP.trueClause a (checkedClause row2455) := by
  apply Type2.RUP.derive (premises := [row2428, row2454]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2428 a assignment, clause2454 a assignment⟩

private def row2456 : List Int := [-68]
include assignment in
private theorem clause2456 : Type2.RUP.trueClause a (checkedClause row2456) := by
  apply Type2.RUP.derive (premises := [row2408, row2428, row2454]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2408 a assignment, clause2428 a assignment, clause2454 a assignment⟩

private def row2457 : List Int := [-69, -67]
include assignment in
private theorem clause2457 : Type2.RUP.trueClause a (checkedClause row2457) := by
  apply Type2.RUP.derive (premises := [row2277, row2454, row400, row419]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2277 a assignment, clause2454 a assignment, clause400 a assignment,
    clause419 a assignment⟩

private def row2458 : List Int := [64, 61, 57]
include assignment in
private theorem clause2458 : Type2.RUP.trueClause a (checkedClause row2458) := by
  apply Type2.RUP.derive (premises := [row2456, row347, row353]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2456 a assignment, clause347 a assignment, clause353 a assignment⟩

private def row2459 : List Int := [61, 57]
include assignment in
private theorem clause2459 : Type2.RUP.trueClause a (checkedClause row2459) := by
  apply Type2.RUP.derive (premises := [row2456, row2458, row340, row357]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2456 a assignment, clause2458 a assignment, clause340 a assignment,
    clause357 a assignment⟩

private def row2460 : List Int := [-64, 63, 57, -66]
include assignment in
private theorem clause2460 : Type2.RUP.trueClause a (checkedClause row2460) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row1771, row2355, row2358]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause1771 a assignment,
    clause2355 a assignment, clause2358 a assignment⟩

private def row2461 : List Int := [-52, 49, 57, -67]
include assignment in
private theorem clause2461 : Type2.RUP.trueClause a (checkedClause row2461) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2457, row2459, row413, row1539, row1909, row2257, row2426, row1367, row1455, row2334,
    row2460, row1291, row2167, row2356, row2448, row132, row1069]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2457 a assignment,
    clause2459 a assignment, clause413 a assignment, clause1539 a assignment,
    clause1909 a assignment, clause2257 a assignment, clause2426 a assignment,
    clause1367 a assignment, clause1455 a assignment, clause2334 a assignment,
    clause2460 a assignment, clause1291 a assignment, clause2167 a assignment,
    clause2356 a assignment, clause2448 a assignment, clause132 a assignment,
    clause1069 a assignment⟩

private def row2462 : List Int := [49, 57, -67]
include assignment in
private theorem clause2462 : Type2.RUP.trueClause a (checkedClause row2462) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2457, row2459, row2461, row413, row1539, row2142, row2257, row2372, row2426, row2445,
    row1455, row1475, row1496, row2194, row2212, row2216, row2334, row664, row1090, row1107, row1648, row2156,
    row2352]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2457 a assignment,
    clause2459 a assignment, clause2461 a assignment, clause413 a assignment,
    clause1539 a assignment, clause2142 a assignment, clause2257 a assignment,
    clause2372 a assignment, clause2426 a assignment, clause2445 a assignment,
    clause1455 a assignment, clause1475 a assignment, clause1496 a assignment,
    clause2194 a assignment, clause2212 a assignment, clause2216 a assignment,
    clause2334 a assignment, clause664 a assignment, clause1090 a assignment,
    clause1107 a assignment, clause1648 a assignment, clause2156 a assignment,
    clause2352 a assignment⟩

private def row2463 : List Int := [-46, 52, -66, -49]
include assignment in
private theorem clause2463 : Type2.RUP.trueClause a (checkedClause row2463) := by
  apply Type2.RUP.derive (premises := [row201, row216]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause201 a assignment, clause216 a assignment⟩

private def row2464 : List Int := [52, -49, -62, 56, 59, -66]
include assignment in
private theorem clause2464 : Type2.RUP.trueClause a (checkedClause row2464) := by
  apply Type2.RUP.derive (premises := [row2463, row1381, row1634, row2278, row2279]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2463 a assignment, clause1381 a assignment, clause1634 a assignment,
    clause2278 a assignment, clause2279 a assignment⟩

private def row2465 : List Int := [57, -67]
include assignment in
private theorem clause2465 : Type2.RUP.trueClause a (checkedClause row2465) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2457, row2459, row2462, row413, row1539, row2426, row1367, row1455, row2334, row2460,
    row1291, row2356, row2464, row1865, row2448, row132, row1625, row1643, row1739, row1837, row2285]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2457 a assignment,
    clause2459 a assignment, clause2462 a assignment, clause413 a assignment,
    clause1539 a assignment, clause2426 a assignment, clause1367 a assignment,
    clause1455 a assignment, clause2334 a assignment, clause2460 a assignment,
    clause1291 a assignment, clause2356 a assignment, clause2464 a assignment,
    clause1865 a assignment, clause2448 a assignment, clause132 a assignment,
    clause1625 a assignment, clause1643 a assignment, clause1739 a assignment,
    clause1837 a assignment, clause2285 a assignment⟩

private def row2466 : List Int := [-43, -59, -62, -52, -49, -57]
include assignment in
private theorem clause2466 : Type2.RUP.trueClause a (checkedClause row2466) := by
  apply Type2.RUP.derive (premises := [row2151, row2448, row1144]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2151 a assignment, clause2448 a assignment, clause1144 a assignment⟩

private def row2467 : List Int := [43, 65, -62, -52]
include assignment in
private theorem clause2467 : Type2.RUP.trueClause a (checkedClause row2467) := by
  apply Type2.RUP.derive (premises := [row2167, row2379]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2167 a assignment, clause2379 a assignment⟩

private def row2468 : List Int := [-61, -38, -65, 43, -59, -49, 69]
include assignment in
private theorem clause2468 : Type2.RUP.trueClause a (checkedClause row2468) := by
  apply Type2.RUP.derive (premises := [row71, row369, row961, row1173, row1506, row106]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause71 a assignment, clause369 a assignment, clause961 a assignment,
    clause1173 a assignment, clause1506 a assignment, clause106 a assignment⟩

private def row2469 : List Int := [39, -48, 58, -36]
include assignment in
private theorem clause2469 : Type2.RUP.trueClause a (checkedClause row2469) := by
  apply Type2.RUP.derive (premises := [row42, row49]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause42 a assignment, clause49 a assignment⟩

private def row2470 : List Int := [39, 58, -36]
include assignment in
private theorem clause2470 : Type2.RUP.trueClause a (checkedClause row2470) := by
  apply Type2.RUP.derive (premises := [row2267, row2469]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2267 a assignment, clause2469 a assignment⟩

private def row2471 : List Int := [-48, 58, -36, -39]
include assignment in
private theorem clause2471 : Type2.RUP.trueClause a (checkedClause row2471) := by
  apply Type2.RUP.derive (premises := [row47, row59]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause47 a assignment, clause59 a assignment⟩

private def row2472 : List Int := [-38, -62, 46, -52, -49, -67]
include assignment in
private theorem clause2472 : Type2.RUP.trueClause a (checkedClause row2472) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2457, row2465, row413, row2333, row311, row1472, row2185, row2466, row2467, row2468,
    row379, row514, row965, row2470, row2471, row2248, row2285, row2375]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2457 a assignment,
    clause2465 a assignment, clause413 a assignment, clause2333 a assignment,
    clause311 a assignment, clause1472 a assignment, clause2185 a assignment,
    clause2466 a assignment, clause2467 a assignment, clause2468 a assignment,
    clause379 a assignment, clause514 a assignment, clause965 a assignment,
    clause2470 a assignment, clause2471 a assignment, clause2248 a assignment,
    clause2285 a assignment, clause2375 a assignment⟩

private def row2473 : List Int := [38, 47, -57, 41]
include assignment in
private theorem clause2473 : Type2.RUP.trueClause a (checkedClause row2473) := by
  apply Type2.RUP.derive (premises := [row26, row34]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause26 a assignment, clause34 a assignment⟩

private def row2474 : List Int := [41, 38, -57]
include assignment in
private theorem clause2474 : Type2.RUP.trueClause a (checkedClause row2474) := by
  apply Type2.RUP.derive (premises := [row2149, row2473]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2149 a assignment, clause2473 a assignment⟩

private def row2475 : List Int := [-62, 46, -52, -49, -67]
include assignment in
private theorem clause2475 : Type2.RUP.trueClause a (checkedClause row2475) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2457, row2465, row2472, row2474, row413, row1710, row2448, row32, row131, row586]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2457 a assignment,
    clause2465 a assignment, clause2472 a assignment, clause2474 a assignment,
    clause413 a assignment, clause1710 a assignment, clause2448 a assignment,
    clause32 a assignment, clause131 a assignment, clause586 a assignment⟩

private def row2476 : List Int := [62, -67]
include assignment in
private theorem clause2476 : Type2.RUP.trueClause a (checkedClause row2476) := by
  apply Type2.RUP.derive (premises := [row2332, row2443, row2457, row2465, row413, row1776, row2127, row2234, row2286, row2371, row2384, row389]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2443 a assignment, clause2457 a assignment,
    clause2465 a assignment, clause413 a assignment, clause1776 a assignment,
    clause2127 a assignment, clause2234 a assignment, clause2286 a assignment,
    clause2371 a assignment, clause2384 a assignment, clause389 a assignment⟩

private def row2477 : List Int := [-46, -52, -66, -49]
include assignment in
private theorem clause2477 : Type2.RUP.trueClause a (checkedClause row2477) := by
  apply Type2.RUP.derive (premises := [row206, row212]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause206 a assignment, clause212 a assignment⟩

private def row2478 : List Int := [-52, -49, -67]
include assignment in
private theorem clause2478 : Type2.RUP.trueClause a (checkedClause row2478) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2457, row2476, row413, row2475, row2477]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2457 a assignment,
    clause2476 a assignment, clause413 a assignment, clause2475 a assignment,
    clause2477 a assignment⟩

private def row2479 : List Int := [-49, -67]
include assignment in
private theorem clause2479 : Type2.RUP.trueClause a (checkedClause row2479) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2457, row2476, row2478, row413, row2333, row2463, row2464, row1634, row1864, row2279]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2457 a assignment,
    clause2476 a assignment, clause2478 a assignment, clause413 a assignment,
    clause2333 a assignment, clause2463 a assignment, clause2464 a assignment,
    clause1634 a assignment, clause1864 a assignment, clause2279 a assignment⟩

private def row2480 : List Int := [-47, -46, -66, -57, 56]
include assignment in
private theorem clause2480 : Type2.RUP.trueClause a (checkedClause row2480) := by
  apply Type2.RUP.derive (premises := [row1305, row2192, row2194]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause1305 a assignment, clause2192 a assignment, clause2194 a assignment⟩

private def row2481 : List Int := [-47, -67]
include assignment in
private theorem clause2481 : Type2.RUP.trueClause a (checkedClause row2481) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2457, row2465, row2476, row2479, row413, row2333, row2445, row2480]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2457 a assignment,
    clause2465 a assignment, clause2476 a assignment, clause2479 a assignment,
    clause413 a assignment, clause2333 a assignment, clause2445 a assignment,
    clause2480 a assignment⟩

private def row2482 : List Int := [69, -67]
include assignment in
private theorem clause2482 : Type2.RUP.trueClause a (checkedClause row2482) := by
  apply Type2.RUP.derive (premises := [row2331, row2406, row2479, row2481, row413, row2142, row2294, row2382, row2284, row2285, row223, row265,
    row273]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2331 a assignment, clause2406 a assignment, clause2479 a assignment,
    clause2481 a assignment, clause413 a assignment, clause2142 a assignment,
    clause2294 a assignment, clause2382 a assignment, clause2284 a assignment,
    clause2285 a assignment, clause223 a assignment, clause265 a assignment,
    clause273 a assignment⟩

private def row2483 : List Int := [-67]
include assignment in
private theorem clause2483 : Type2.RUP.trueClause a (checkedClause row2483) := by
  apply Type2.RUP.derive (premises := [row2457, row2482]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2457 a assignment, clause2482 a assignment⟩

private def row2484 : List Int := [56, -57, -66]
include assignment in
private theorem clause2484 : Type2.RUP.trueClause a (checkedClause row2484) := by
  apply Type2.RUP.derive (premises := [row2332, row2453, row2483, row409, row1365, row2200, row324, row1453, row1685, row2127]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2453 a assignment, clause2483 a assignment,
    clause409 a assignment, clause1365 a assignment, clause2200 a assignment,
    clause324 a assignment, clause1453 a assignment, clause1685 a assignment,
    clause2127 a assignment⟩

private def row2485 : List Int := [-57, 49, 47, -66, 46]
include assignment in
private theorem clause2485 : Type2.RUP.trueClause a (checkedClause row2485) := by
  apply Type2.RUP.derive (premises := [row208, row2332, row2453, row2483, row2484, row409, row1669, row1909, row2120, row2226, row2272, row2420,
    row224, row316, row1635, row1875, row2167, row2222, row2234, row2361, row2386, row2388, row2392, row690]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause208 a assignment, clause2332 a assignment, clause2453 a assignment,
    clause2483 a assignment, clause2484 a assignment, clause409 a assignment,
    clause1669 a assignment, clause1909 a assignment, clause2120 a assignment,
    clause2226 a assignment, clause2272 a assignment, clause2420 a assignment,
    clause224 a assignment, clause316 a assignment, clause1635 a assignment,
    clause1875 a assignment, clause2167 a assignment, clause2222 a assignment,
    clause2234 a assignment, clause2361 a assignment, clause2386 a assignment,
    clause2388 a assignment, clause2392 a assignment, clause690 a assignment⟩

private def row2486 : List Int := [49, 47, -66, 46]
include assignment in
private theorem clause2486 : Type2.RUP.trueClause a (checkedClause row2486) := by
  apply Type2.RUP.derive (premises := [row208, row2332, row2456, row2483, row2485, row409, row1669, row2226, row2459, row224, row1539, row2257,
    row2426, row1400, row1604, row2200]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause208 a assignment, clause2332 a assignment, clause2456 a assignment,
    clause2483 a assignment, clause2485 a assignment, clause409 a assignment,
    clause1669 a assignment, clause2226 a assignment, clause2459 a assignment,
    clause224 a assignment, clause1539 a assignment, clause2257 a assignment,
    clause2426 a assignment, clause1400 a assignment, clause1604 a assignment,
    clause2200 a assignment⟩

private def row2487 : List Int := [47, -66, 46]
include assignment in
private theorem clause2487 : Type2.RUP.trueClause a (checkedClause row2487) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2483, row2486, row409, row1437, row1523, row2309, row2397]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2483 a assignment,
    clause2486 a assignment, clause409 a assignment, clause1437 a assignment,
    clause1523 a assignment, clause2309 a assignment, clause2397 a assignment⟩

private def row2488 : List Int := [57, -66, 46]
include assignment in
private theorem clause2488 : Type2.RUP.trueClause a (checkedClause row2488) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2459, row2465, row2487, row409, row1349, row1539, row2426, row2445, row1307, row1381,
    row1437, row2202, row2205, row2267, row2398, row2430, row29, row96, row111, row324, row467, row1000,
    row1076]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2459 a assignment,
    clause2465 a assignment, clause2487 a assignment, clause409 a assignment,
    clause1349 a assignment, clause1539 a assignment, clause2426 a assignment,
    clause2445 a assignment, clause1307 a assignment, clause1381 a assignment,
    clause1437 a assignment, clause2202 a assignment, clause2205 a assignment,
    clause2267 a assignment, clause2398 a assignment, clause2430 a assignment,
    clause29 a assignment, clause96 a assignment, clause111 a assignment,
    clause324 a assignment, clause467 a assignment, clause1000 a assignment,
    clause1076 a assignment⟩

private def row2489 : List Int := [-66, 46]
include assignment in
private theorem clause2489 : Type2.RUP.trueClause a (checkedClause row2489) := by
  apply Type2.RUP.derive (premises := [row2487, row2488, row2484, row1315, row2118, row2119]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2487 a assignment, clause2488 a assignment, clause2484 a assignment,
    clause1315 a assignment, clause2118 a assignment, clause2119 a assignment⟩

private def row2490 : List Int := [-56, -57, 46]
include assignment in
private theorem clause2490 : Type2.RUP.trueClause a (checkedClause row2490) := by
  apply Type2.RUP.derive (premises := [row2120, row2441, row2483, row2489, row2230, row2272, row2324, row1340, row2222, row2234, row2250, row2369,
    row56, row611, row1623, row1639, row2356, row2360]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2120 a assignment, clause2441 a assignment, clause2483 a assignment,
    clause2489 a assignment, clause2230 a assignment, clause2272 a assignment,
    clause2324 a assignment, clause1340 a assignment, clause2222 a assignment,
    clause2234 a assignment, clause2250 a assignment, clause2369 a assignment,
    clause56 a assignment, clause611 a assignment, clause1623 a assignment,
    clause1639 a assignment, clause2356 a assignment, clause2360 a assignment⟩

private def row2491 : List Int := [56, -62, 66, -57]
include assignment in
private theorem clause2491 : Type2.RUP.trueClause a (checkedClause row2491) := by
  apply Type2.RUP.derive (premises := [row300, row315]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause300 a assignment, clause315 a assignment⟩

private def row2492 : List Int := [56, -57, 66]
include assignment in
private theorem clause2492 : Type2.RUP.trueClause a (checkedClause row2492) := by
  apply Type2.RUP.derive (premises := [row2287, row2491]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2287 a assignment, clause2491 a assignment⟩

private def row2493 : List Int := [-57, 46]
include assignment in
private theorem clause2493 : Type2.RUP.trueClause a (checkedClause row2493) := by
  apply Type2.RUP.derive (premises := [row2489, row2490, row2492]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2489 a assignment, clause2490 a assignment, clause2492 a assignment⟩

private def row2494 : List Int := [56, 46]
include assignment in
private theorem clause2494 : Type2.RUP.trueClause a (checkedClause row2494) := by
  apply Type2.RUP.derive (premises := [row2456, row2483, row2489, row2492, row2202, row2205, row2230, row2290, row2324, row304, row1348, row1393,
    row1400, row1468, row2250, row2256, row2267, row5, row77, row660]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2456 a assignment, clause2483 a assignment, clause2489 a assignment,
    clause2492 a assignment, clause2202 a assignment, clause2205 a assignment,
    clause2230 a assignment, clause2290 a assignment, clause2324 a assignment,
    clause304 a assignment, clause1348 a assignment, clause1393 a assignment,
    clause1400 a assignment, clause1468 a assignment, clause2250 a assignment,
    clause2256 a assignment, clause2267 a assignment, clause5 a assignment,
    clause77 a assignment, clause660 a assignment⟩

private def row2495 : List Int := [46]
include assignment in
private theorem clause2495 : Type2.RUP.trueClause a (checkedClause row2495) := by
  apply Type2.RUP.derive (premises := [row2456, row2483, row2489, row2493, row2494, row1375, row2230, row2272]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2456 a assignment, clause2483 a assignment, clause2489 a assignment,
    clause2493 a assignment, clause2494 a assignment, clause1375 a assignment,
    clause2230 a assignment, clause2272 a assignment⟩

private def row2496 : List Int := [62, -56, -61, 66]
include assignment in
private theorem clause2496 : Type2.RUP.trueClause a (checkedClause row2496) := by
  apply Type2.RUP.derive (premises := [row2332, row2476, row1695, row2442, row389, row397]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2476 a assignment, clause1695 a assignment,
    clause2442 a assignment, clause389 a assignment, clause397 a assignment⟩

private def row2497 : List Int := [41, 47, 63, -56, 57, 66]
include assignment in
private theorem clause2497 : Type2.RUP.trueClause a (checkedClause row2497) := by
  apply Type2.RUP.derive (premises := [row2332, row2441, row2459, row2465, row2495, row2496, row302, row417, row1359, row1375, row1447, row1707,
    row2159, row2257, row2268, row2381, row2392, row2409, row2470, row585, row598, row2110]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2441 a assignment, clause2459 a assignment,
    clause2465 a assignment, clause2495 a assignment, clause2496 a assignment,
    clause302 a assignment, clause417 a assignment, clause1359 a assignment,
    clause1375 a assignment, clause1447 a assignment, clause1707 a assignment,
    clause2159 a assignment, clause2257 a assignment, clause2268 a assignment,
    clause2381 a assignment, clause2392 a assignment, clause2409 a assignment,
    clause2470 a assignment, clause585 a assignment, clause598 a assignment,
    clause2110 a assignment⟩

private def row2498 : List Int := [-52, 53, -41, 47, -65, 59, -62, -56, 66]
include assignment in
private theorem clause2498 : Type2.RUP.trueClause a (checkedClause row2498) := by
  apply Type2.RUP.derive (premises := [row319, row2440, row2448, row2465, row2495, row131, row594, row1359, row1644, row2110, row598]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause319 a assignment, clause2440 a assignment, clause2448 a assignment,
    clause2465 a assignment, clause2495 a assignment, clause131 a assignment,
    clause594 a assignment, clause1359 a assignment, clause1644 a assignment,
    clause2110 a assignment, clause598 a assignment⟩

private def row2499 : List Int := [52, 47, 59, -62, -56, 66]
include assignment in
private theorem clause2499 : Type2.RUP.trueClause a (checkedClause row2499) := by
  apply Type2.RUP.derive (premises := [row2250, row2261, row1628, row1862, row2279]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2250 a assignment, clause2261 a assignment, clause1628 a assignment,
    clause1862 a assignment, clause2279 a assignment⟩

private def row2500 : List Int := [47, 63, -56, 57, 66]
include assignment in
private theorem clause2500 : Type2.RUP.trueClause a (checkedClause row2500) := by
  apply Type2.RUP.derive (premises := [row2332, row2441, row2459, row2465, row2495, row2496, row2497, row302, row417, row1770, row1924, row2499,
    row202, row1746, row1908, row2350, row2498]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2441 a assignment, clause2459 a assignment,
    clause2465 a assignment, clause2495 a assignment, clause2496 a assignment,
    clause2497 a assignment, clause302 a assignment, clause417 a assignment,
    clause1770 a assignment, clause1924 a assignment, clause2499 a assignment,
    clause202 a assignment, clause1746 a assignment, clause1908 a assignment,
    clause2350 a assignment, clause2498 a assignment⟩

private def row2501 : List Int := [-47, -56, 57, 66]
include assignment in
private theorem clause2501 : Type2.RUP.trueClause a (checkedClause row2501) := by
  apply Type2.RUP.derive (premises := [row2332, row2441, row2459, row2465, row2495, row2496, row417, row1301, row1770, row2298, row2430, row29,
    row1725, row2248]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2441 a assignment, clause2459 a assignment,
    clause2465 a assignment, clause2495 a assignment, clause2496 a assignment,
    clause417 a assignment, clause1301 a assignment, clause1770 a assignment,
    clause2298 a assignment, clause2430 a assignment, clause29 a assignment,
    clause1725 a assignment, clause2248 a assignment⟩

private def row2502 : List Int := [-56, 57, 66]
include assignment in
private theorem clause2502 : Type2.RUP.trueClause a (checkedClause row2502) := by
  apply Type2.RUP.derive (premises := [row2332, row2441, row2459, row2465, row2495, row2496, row2501, row302, row417, row1770, row1924, row2499,
    row2500, row202, row1754, row1908, row2350, row2368, row2374, row2385, row148]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2441 a assignment, clause2459 a assignment,
    clause2465 a assignment, clause2495 a assignment, clause2496 a assignment,
    clause2501 a assignment, clause302 a assignment, clause417 a assignment,
    clause1770 a assignment, clause1924 a assignment, clause2499 a assignment,
    clause2500 a assignment, clause202 a assignment, clause1754 a assignment,
    clause1908 a assignment, clause2350 a assignment, clause2368 a assignment,
    clause2374 a assignment, clause2385 a assignment, clause148 a assignment⟩

private def row2503 : List Int := [-54, -47, 66]
include assignment in
private theorem clause2503 : Type2.RUP.trueClause a (checkedClause row2503) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2495, row1761, row2159, row219]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2495 a assignment,
    clause1761 a assignment, clause2159 a assignment, clause219 a assignment⟩

private def row2504 : List Int := [-47, 66]
include assignment in
private theorem clause2504 : Type2.RUP.trueClause a (checkedClause row2504) := by
  apply Type2.RUP.derive (premises := [row2456, row2503, row2246, row2248]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2456 a assignment, clause2503 a assignment, clause2246 a assignment,
    clause2248 a assignment⟩

private def row2505 : List Int := [-41, 36, -57, 47]
include assignment in
private theorem clause2505 : Type2.RUP.trueClause a (checkedClause row2505) := by
  apply Type2.RUP.derive (premises := [row28, row38]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause28 a assignment, clause38 a assignment⟩

private def row2506 : List Int := [64, 66]
include assignment in
private theorem clause2506 : Type2.RUP.trueClause a (checkedClause row2506) := by
  apply Type2.RUP.derive (premises := [row2456, row2483, row2495, row2504, row1359, row2255, row2263, row2377, row2500, row342, row350]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2456 a assignment, clause2483 a assignment, clause2495 a assignment,
    clause2504 a assignment, clause1359 a assignment, clause2255 a assignment,
    clause2263 a assignment, clause2377 a assignment, clause2500 a assignment,
    clause342 a assignment, clause350 a assignment⟩

private def row2507 : List Int := [41, 66]
include assignment in
private theorem clause2507 : Type2.RUP.trueClause a (checkedClause row2507) := by
  apply Type2.RUP.derive (premises := [row2332, row2456, row2483, row2495, row2504, row2506, row1359, row2237, row2263, row2502, row1719, row1754,
    row1831, row2341, row2353]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2456 a assignment, clause2483 a assignment,
    clause2495 a assignment, clause2504 a assignment, clause2506 a assignment,
    clause1359 a assignment, clause2237 a assignment, clause2263 a assignment,
    clause2502 a assignment, clause1719 a assignment, clause1754 a assignment,
    clause1831 a assignment, clause2341 a assignment, clause2353 a assignment⟩

private def row2508 : List Int := [-56, 66]
include assignment in
private theorem clause2508 : Type2.RUP.trueClause a (checkedClause row2508) := by
  apply Type2.RUP.derive (premises := [row2495, row2502, row2504, row2507, row1308, row2505]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2495 a assignment, clause2502 a assignment, clause2504 a assignment,
    clause2507 a assignment, clause1308 a assignment, clause2505 a assignment⟩

private def row2509 : List Int := [66]
include assignment in
private theorem clause2509 : Type2.RUP.trueClause a (checkedClause row2509) := by
  apply Type2.RUP.derive (premises := [row2456, row2483, row2495, row2504, row2508, row2202, row2205, row2263]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2456 a assignment, clause2483 a assignment, clause2495 a assignment,
    clause2504 a assignment, clause2508 a assignment, clause2202 a assignment,
    clause2205 a assignment, clause2263 a assignment⟩

private def row2510 : List Int := [-69]
include assignment in
private theorem clause2510 : Type2.RUP.trueClause a (checkedClause row2510) := by
  apply Type2.RUP.derive (premises := [row2277, row2455, row2457, row2509, row409]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2277 a assignment, clause2455 a assignment, clause2457 a assignment,
    clause2509 a assignment, clause409 a assignment⟩

private def row2511 : List Int := [-48]
include assignment in
private theorem clause2511 : Type2.RUP.trueClause a (checkedClause row2511) := by
  apply Type2.RUP.derive (premises := [row2456, row2483, row2510, row2298]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2456 a assignment, clause2483 a assignment, clause2510 a assignment,
    clause2298 a assignment⟩

private def row2512 : List Int := [47]
include assignment in
private theorem clause2512 : Type2.RUP.trueClause a (checkedClause row2512) := by
  apply Type2.RUP.derive (premises := [row2456, row2483, row2495, row2509, row2511, row1358]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2456 a assignment, clause2483 a assignment, clause2495 a assignment,
    clause2509 a assignment, clause2511 a assignment, clause1358 a assignment⟩

private def row2513 : List Int := [54]
include assignment in
private theorem clause2513 : Type2.RUP.trueClause a (checkedClause row2513) := by
  apply Type2.RUP.derive (premises := [row2456, row2511, row2512, row242, row250]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2456 a assignment, clause2511 a assignment, clause2512 a assignment,
    clause242 a assignment, clause250 a assignment⟩

private def row2514 : List Int := [52, -53]
include assignment in
private theorem clause2514 : Type2.RUP.trueClause a (checkedClause row2514) := by
  apply Type2.RUP.derive (premises := [row2332, row2513, row285, row295]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2332 a assignment, clause2513 a assignment, clause285 a assignment,
    clause295 a assignment⟩

private def row2515 : List Int := [52]
include assignment in
private theorem clause2515 : Type2.RUP.trueClause a (checkedClause row2515) := by
  apply Type2.RUP.derive (premises := [row2495, row2511, row2512, row2513, row2514, row651]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2495 a assignment, clause2511 a assignment, clause2512 a assignment,
    clause2513 a assignment, clause2514 a assignment, clause651 a assignment⟩

private def row2516 : List Int := [-49]
include assignment in
private theorem clause2516 : Type2.RUP.trueClause a (checkedClause row2516) := by
  apply Type2.RUP.derive (premises := [row2495, row2509, row2512, row2515, row206]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2495 a assignment, clause2509 a assignment, clause2512 a assignment,
    clause2515 a assignment, clause206 a assignment⟩

private def row2517 : List Int := []
include assignment in
private theorem clause2517 : Type2.RUP.trueClause a (checkedClause row2517) := by
  apply Type2.RUP.derive (premises := [row2495, row2509, row2512, row2515, row2516, row205]) (by decide +kernel)
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨clause2495 a assignment, clause2509 a assignment, clause2512 a assignment,
    clause2515 a assignment, clause2516 a assignment, clause205 a assignment⟩

/-- The circuit and Grassmann–Plücker constraints for an embedded,
strictly exposed collapsed realization are inconsistent. -/
theorem hull_signs_impossible (a : Nat → Bool) :
    ¬ ∀ c ∈ hullSignClauses, Type2.RUP.trueClause a c := by
  intro h
  obtain ⟨l, hl, _⟩ := clause2517 a h
  exact List.not_mem_nil hl

end OrigamiTorus.Type1
