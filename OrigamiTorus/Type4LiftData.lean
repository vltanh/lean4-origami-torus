module

public import OrigamiTorus.StripPolynomial
public import OrigamiTorus.Type4Strips
import Mathlib.Tactic

/-! Rational coefficient data for the Type 4 chart heights. -/

@[expose] public section

namespace OrigamiTorus.Type4

namespace StripLift

open StripPolynomial (Coefficients C T H)

local infixl:65 " +ₚ " => StripPolynomial.add
local infixl:65 " -ₚ " => StripPolynomial.sub
local infixl:70 " *ₚ " => StripPolynomial.mul
local infixr:80 " ^ₚ " => StripPolynomial.pow

def pointCoeffs (second : Bool) (x w : Coefficients) : Vertex → Coefficients × Coefficients :=
  let H := if second then C 1 +ₚ C (3/2) *ₚ (C 1 -ₚ C 2 *ₚ x)^ₚ2 else C 33
  let J := if second then C 1 else C 20 +ₚ C 26 *ₚ x
  let c := C (if second then 2/3 else 1/3)
  let A := H *ₚ x
  let D := H -ₚ J +ₚ A
  let Q := D^ₚ2 +ₚ H^ₚ2 *ₚ w
  let S := (A^ₚ2 -ₚ A*ₚJ -ₚ (C 1-ₚc)*ₚH^ₚ2*ₚw -ₚ D*ₚ(C 2*ₚA-ₚc*ₚD-ₚJ)) *ₚ
    C (if second then 3 else 3/2)
  let U := A^ₚ2 -ₚ A*ₚJ +ₚ H^ₚ2*ₚw -ₚ D*ₚJ
  ![([],[]),((J-ₚA+ₚc*ₚD)*ₚQ,(C 1-ₚc)*ₚH*ₚQ),(C (1/2)*ₚJ*ₚQ,[]),
    (A*ₚQ+ₚD*ₚS,H*ₚQ+ₚH*ₚS),(J*ₚQ,[]),(J*ₚQ+ₚD*ₚU,H*ₚU),(A*ₚQ,H*ₚQ),((J-ₚA)*ₚQ,H*ₚQ)]

def areaCoeffs (p : Vertex → Coefficients × Coefficients) (a b c : Vertex) : Coefficients :=
  (p b).1 *ₚ ((p c).2 -ₚ (p a).2) +ₚ (p c).1 *ₚ ((p a).2 -ₚ (p b).2) +ₚ (p a).1 *ₚ ((p b).2 -ₚ (p c).2)

def volumeCoeffs (p : Vertex → Coefficients × Coefficients) (h : Vertex → Coefficients)
    (a b c d : Vertex) : Coefficients :=
  StripPolynomial.neg (h a) *ₚ areaCoeffs p b c d +ₚ h b *ₚ areaCoeffs p a c d -ₚ
    h c *ₚ areaCoeffs p a b d +ₚ h d *ₚ areaCoeffs p a b c

def endX := C (9/20) +ₚ C (1/20) *ₚ T
def endP := pointCoeffs true endX (C 1 -ₚ endX^ₚ2 +ₚ H)
def endZ : Vertex → Coefficients :=
  let δ := C 1 -ₚ C 2 *ₚ endX
  ![[],C 6*ₚδ,C 1,C (-5/2)*ₚδ^ₚ2,[],C 2,[],C (9/8)*ₚδ]

def endVolume (a b c d : Vertex) := volumeCoeffs endP endZ a b c d

def sgn (p : Coefficients) : Int :=
  if StripPolynomial.strictOnOpen p then 1
    else if StripPolynomial.strictOnOpen (StripPolynomial.neg p) then -1 else 0

def quads : List (Vertex × Vertex × Vertex × Vertex) :=
  (List.finRange 8).flatMap fun a => (List.finRange 8).flatMap fun b =>
    (List.finRange 8).flatMap fun c => ((List.finRange 8).filter fun d => a<b ∧ b<c ∧ c<d).map (a,b,c,·)

def pairCheck (p : Edge × Triangle) : Bool :=
  let ((a,b),c,d,e) := p
  let v₀ := sgn (endVolume b c d e)
  let v₁ := sgn (endVolume a c d e)
  let v₂ := sgn (endVolume a b d e)
  let v₃ := sgn (endVolume a b c e)
  let v₄ := sgn (endVolume a b c d)
  decide (0 < v₀*v₁ ∨ 0 < v₂*v₃ ∨ 0 < v₃*v₄ ∨ v₂*v₄ < 0)

def pairChunk (i : Fin 28) : List (Edge × Triangle) :=
  ((Type7.disjointPairs Type7.flippedFaces).drop (5*i.val)).take 5

private theorem pairChunks_cover :
    (List.finRange 28).flatMap pairChunk = Type7.disjointPairs Type7.flippedFaces := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk0 : (pairChunk 0).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk1 : (pairChunk 1).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk2 : (pairChunk 2).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk3 : (pairChunk 3).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk4 : (pairChunk 4).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk5 : (pairChunk 5).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk6 : (pairChunk 6).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk7 : (pairChunk 7).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk8 : (pairChunk 8).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk9 : (pairChunk 9).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk10 : (pairChunk 10).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk11 : (pairChunk 11).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk12 : (pairChunk 12).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk13 : (pairChunk 13).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk14 : (pairChunk 14).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk15 : (pairChunk 15).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk16 : (pairChunk 16).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk17 : (pairChunk 17).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk18 : (pairChunk 18).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk19 : (pairChunk 19).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk20 : (pairChunk 20).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk21 : (pairChunk 21).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk22 : (pairChunk 22).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk23 : (pairChunk 23).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk24 : (pairChunk 24).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk25 : (pairChunk 25).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk26 : (pairChunk 26).all pairCheck = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem pairChunk27 : (pairChunk 27).all pairCheck = true := by decide +kernel

theorem allPairs : (Type7.disjointPairs Type7.flippedFaces).all pairCheck = true := by
  rw [← pairChunks_cover]
  apply List.all_eq_true.mpr
  intro q hq
  obtain ⟨i,_,hqi⟩ := List.mem_flatMap.mp hq
  have h (i : Fin 28) : (pairChunk i).all pairCheck = true := by
    fin_cases i
    · exact pairChunk0
    · exact pairChunk1
    · exact pairChunk2
    · exact pairChunk3
    · exact pairChunk4
    · exact pairChunk5
    · exact pairChunk6
    · exact pairChunk7
    · exact pairChunk8
    · exact pairChunk9
    · exact pairChunk10
    · exact pairChunk11
    · exact pairChunk12
    · exact pairChunk13
    · exact pairChunk14
    · exact pairChunk15
    · exact pairChunk16
    · exact pairChunk17
    · exact pairChunk18
    · exact pairChunk19
    · exact pairChunk20
    · exact pairChunk21
    · exact pairChunk22
    · exact pairChunk23
    · exact pairChunk24
    · exact pairChunk25
    · exact pairChunk26
    · exact pairChunk27
  exact (List.all_eq_true.mp (h i)) q hqi

end StripLift

end OrigamiTorus.Type4
