import CoveringDesigns.Foundations.Encoding
import Mathlib.Data.List.FinRange

/-! Small encodings used only to check explicit Figure 1 isomorphisms. -/

namespace CoveringDesigns.GPPTStructural.CompletionVerification

abbrev Pair := Fin 12 × Fin 12

def pairSet (p : Pair) : Finset (Fin 12) := {p.1, p.2}

def mapPair (f : Fin 12 → Fin 12) (p : Pair) : Pair := (f p.1, f p.2)

def pairEq (p q : Pair) : Bool :=
  (p.1 == q.1 && p.2 == q.2) || (p.1 == q.2 && p.2 == q.1)

def pointMap (w : BitVec 48) (q : Fin 12) : Fin 12 :=
  ⟨(w.extractLsb' (4*q.val) 4).toNat % 12, Nat.mod_lt _ (by decide)⟩

def fibreMap (w : BitVec 6) (i : Fin 3) : Fin 3 :=
  ⟨(w.extractLsb' (2*i.val) 2).toNat % 3, Nat.mod_lt _ (by decide)⟩

abbrev AutCert := BitVec 48 × BitVec 48 × BitVec 6

/-- Rows are the twelve six-point blocks in the source Figure 1 order. -/
def coreCode : BitVec 144 := 12350009147783749611176362336870665064845375#144

/-- The point map, block map and spine map must all be permutations, and must
preserve every incidence of the displayed partial covering. -/
def autCheck (w : AutCert) : Bool :=
  decide (((List.finRange 12).map (pointMap w.1)).Nodup) &&
  decide (((List.finRange 12).map (pointMap w.2.1)).Nodup) &&
  decide (((List.finRange 3).map (fibreMap w.2.2)).Nodup) &&
  (List.finRange 12).all (fun q =>
    decide ((pointMap w.1 q).val / 4 =
      (fibreMap w.2.2 ⟨q.val / 4, by omega⟩).val)) &&
  (List.finRange 12).all (fun r => (List.finRange 12).all fun q =>
    coreCode.getLsbD (12*q.val+r.val) ==
      coreCode.getLsbD (12*(pointMap w.1 q).val+(pointMap w.2.1 r).val))

abbrev NormalInput := Bool × Fin 28 × Fin 28
abbrev CompletionRow := NormalInput × (Fin 256 × Fin 67)

def firstPair (b : Bool) : Pair := if b then (4, 8) else (4, 5)

def allNormalInputs : List NormalInput :=
  [false, true].flatMap fun b => (List.finRange 28).flatMap fun j =>
    (List.finRange 28).map fun k => (b, j, k)

end CoveringDesigns.GPPTStructural.CompletionVerification
