module

public import OrigamiTorus.Type4LiftData
import Mathlib.Tactic

/-! The five closed height cells through (x=9/20).
The height rows clear the same positive height denominator (1+h). -/

@[expose] public section

namespace OrigamiTorus.Type4.StripLift

open StripPolynomial (Coefficients C T H)
local infixl:65 " +ₚ " => StripPolynomial.add
local infixl:65 " -ₚ " => StripPolynomial.sub
local infixl:70 " *ₚ " => StripPolynomial.mul
local infixr:80 " ^ₚ " => StripPolynomial.pow

def wideBounds : Fin 5 → ℚ × ℚ := ![(0,1/10), (1/10,1/5), (1/5,3/10), (3/10,2/5), (2/5,9/20)]

def wideZ : Fin 5 → Vertex → Coefficients := ![
  ![
    [],
    [[10233031370/5000000000,6649166785/5000000000],[-2954078804/5000000000,-2864535642/5000000000],[181494506/5000000000,306940457/5000000000]],
    [[1,1]],
    [[-2865899585/5000000000,-4256352250/5000000000],[586688797/5000000000,1987162865/5000000000],[-2701776/5000000000,-227178483/5000000000]],
    [],
    [[13711070230/5000000000,13232287785/5000000000],[-1560670721/5000000000,-1914022442/5000000000],[163691335/5000000000,253512977/5000000000]],
    [],
    [[8655486150/5000000000,5709844030/5000000000],[-3264945740/5000000000,-2839906401/5000000000],[306769702/5000000000,339587519/5000000000]]
  ],
  ![
    [],
    [[7618364512/5000000000,4454916876/5000000000],[-2458951888/5000000000,-2076341683/5000000000],[138590190/5000000000,240653116/5000000000]],
    [[1,1]],
    [[-2383722180/5000000000,-4022405156/5000000000],[759343241/5000000000,1319446109/5000000000],[-40853174/5000000000,-78461205/5000000000]],
    [],
    [[12202105024/5000000000,12153447272/5000000000],[-1366512920/5000000000,-1147388070/5000000000],[203996666/5000000000,152256563/5000000000]],
    [],
    [[5881879176/5000000000,3545794768/5000000000],[-2647294370/5000000000,-1982998968/5000000000],[294206144/5000000000,274137569/5000000000]]
  ],
  ![
    [],
    [[5432658645/5000000000,2723005224/5000000000],[-1757841526/5000000000,-1517960235/5000000000],[-17681563/5000000000,203430609/5000000000]],
    [[1,1]],
    [[-1835573337/5000000000,-2712559221/5000000000],[544154859/5000000000,1156247475/5000000000],[22567640/5000000000,-84020356/5000000000]],
    [],
    [[11122420300/5000000000,11283741337/5000000000],[-835692686/5000000000,-761071048/5000000000],[153850862/5000000000,111052423/5000000000]],
    [],
    [[3642160092/5000000000,1930800036/5000000000],[-1970683739/5000000000,-1340947036/5000000000],[252210125/5000000000,232449008/5000000000]]
  ],
  ![
    [],
    [[3744351212/5000000000,1338158094/5000000000],[-1034478482/5000000000,-1010720965/5000000000],[-418848562/5000000000,170820959/5000000000]],
    [[1,1]],
    [[-1036590528/5000000000,-1521346440/5000000000],[205003878/5000000000,840205634/5000000000],[156645693/5000000000,-39766207/5000000000]],
    [],
    [[10483035462/5000000000,10720927604/5000000000],[-527424607/5000000000,-659931330/5000000000],[142953438/5000000000,149733764/5000000000]],
    [],
    [[2151203506/5000000000,759346546/5000000000],[-1774218557/5000000000,-750112627/5000000000],[349308402/5000000000,185219677/5000000000]]
  ],
  ![
    [],
    [[2350039492/5000000000,456440342/5000000000],[-36204144/5000000000,-299359271/5000000000],[-569407801/5000000000,35569550/5000000000]],
    [[1,1]],
    [[-1412872896/10000000000,-1517829036/10000000000],[679472952/10000000000,795941080/10000000000],[13481748/10000000000,-18513281/10000000000]],
    [],
    [[10118305432/5000000000,10303708406/5000000000],[-132067440/5000000000,-319840069/5000000000],[36457362/5000000000,83992933/5000000000]],
    [],
    [[1782240894/10000000000,328728350/10000000000],[-1482003345/10000000000,-308292535/10000000000],[295441449/10000000000,71964180/10000000000]]
  ]
]

def wideX (i : Fin 5) := C (wideBounds i).1 +ₚ C ((wideBounds i).2-(wideBounds i).1) *ₚ T
def wideP (i : Fin 5) := pointCoeffs false (wideX i) (C 1 -ₚ (wideX i)^ₚ2 +ₚ H)

def signClosed (p : Coefficients) : Int :=
  if StripPolynomial.strictOnClosed p then 1
    else if StripPolynomial.strictOnClosed (StripPolynomial.neg p) then -1 else 0

def pairCheckWide (i : Fin 5) (p : Edge × Triangle) : Bool :=
  let ((a,b),c,d,e) := p
  let v u v w x := signClosed (volumeCoeffs (wideP i) (wideZ i) u v w x)
  let v₀ := v b c d e
  let v₁ := v a c d e
  let v₂ := v a b d e
  let v₃ := v a b c e
  let v₄ := v a b c d
  decide (0 < v₀*v₁ ∨ 0 < v₂*v₃ ∨ 0 < v₃*v₄ ∨ v₂*v₄ < 0)


def areaCheckWide (i : Fin 5) (q : Vertex × Vertex × Vertex × Vertex) : Bool :=
  let (a,b,c,d) := q
  let p := wideP i
  [areaCoeffs p b c d,areaCoeffs p a c d,areaCoeffs p a b d,areaCoeffs p a b c].any
    (fun q => signClosed q != 0)

def tetrahedronChunk (i : Fin 14) : List (Vertex × Vertex × Vertex × Vertex) :=
  (quads.drop (5*i.val)).take 5

theorem tetrahedronChunks_cover :
    (List.finRange 14).flatMap tetrahedronChunk = quads := by decide +kernel

open Lean Elab Command in
/-- Elaborate separate kernel-checked declarations to keep the finite coefficient
computations in small batches. -/
elab "check_wide_chunks " name:ident " for " n:num " using " chunk:ident " with " check:term : command => do
  let mut proofs := #[]
  for i in [:n.getNat] do
    let idx := Syntax.mkNumLit (toString i)
    let batch := mkIdent (name.getId.appendAfter (toString i))
    elabCommand (← `(set_option maxRecDepth 65536 in
      set_option maxHeartbeats 0 in
      private theorem $batch : ($chunk $idx).all $check = true := by decide +kernel))
    proofs := proofs.push (← `(tactic| next => exact $batch))
  elabCommand (← `(theorem $name : ∀ i : Fin $n, ($chunk i).all $check = true := by
    intro i
    fin_cases i
    $[$proofs:tactic]*))

end OrigamiTorus.Type4.StripLift
