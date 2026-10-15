import CoveringDesigns.Foundations.Relabelling

/-! The two explicit minimum (11,5,2) coverings.  Their definitions have no
dependency on a classification theorem or a computational certificate. -/

namespace CoveringDesigns

def stantonRepresentative (tag : Bool) : Family (Fin 11) :=
  if tag then {{0, 1, 4, 5, 8}, {2, 3, 6, 7, 8}, {0, 2, 4, 6, 9}, {1, 3, 5, 7, 9}, {1, 2, 5, 6, 10}, {0, 3, 4, 7, 10}, {0, 4, 8, 9, 10}}
  else {{0, 1, 2, 3, 4}, {2, 5, 6, 7, 8}, {0, 3, 5, 7, 9}, {1, 3, 6, 8, 9}, {1, 4, 5, 7, 10}, {0, 4, 6, 8, 10}, {2, 3, 4, 9, 10}}

end CoveringDesigns
