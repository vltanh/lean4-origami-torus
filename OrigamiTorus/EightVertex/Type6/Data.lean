module

public import OrigamiTorus.Defs

/-! The original Type 6 labels and explicit directions for the lift. -/

@[expose] public section

namespace OrigamiTorus

def type6Faces : List Triangle :=
  [(0,1,2), (0,3,1), (0,2,4), (0,5,3), (0,4,5), (1,5,2), (1,3,6), (1,6,4),
   (1,4,7), (1,7,5), (2,7,4), (2,5,6), (2,6,7), (3,5,7), (3,7,6), (4,6,5)]

def flipRelabeling : Vertex → Vertex := ![3,7,0,6,1,5,2,4]

def lift {R : Type*} [Ring R] (second : Bool) : Vertex → R :=
  if second then ![0,-361,2527,2525,5105,2527,1,19639] else ![0,0,-11,-1,-3,-15,0,977]

def generalPositionDirection {R : Type*} [Ring R] (second : Bool) : Vertex → R :=
  if second then ![0,-2017,0,-2,-1,-3,0,1430] else ![0,0,-11,-1,-3,-15,0,977]

end OrigamiTorus
