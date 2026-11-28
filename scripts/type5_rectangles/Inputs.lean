module

meta import OrigamiTorus.EightVertex.Type5.Square
import OrigamiTorus.EightVertex.Type5.Square
import Lean.Data.Json

open OrigamiTorus OrigamiTorus.Type5

/-- Export the oriented complex and its square marking for the rectangle certificate. -/
public def main : IO Unit := do
  let triangles := faces.map fun (a,b,c) => [a.val,b.val,c.val]
  let shifts := edgeList.map fun (a,b) =>
    let k := squareShift a b
    [Int.ofNat a.val, Int.ofNat b.val, k.1, k.2]
  IO.println (Lean.Json.mkObj [("faces", Lean.toJson triangles), ("shifts", Lean.toJson shifts)]).compress
