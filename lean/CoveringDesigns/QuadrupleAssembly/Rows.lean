import CoveringDesigns.QuadrupleAssembly.ProductSubstitution

namespace CoveringDesigns.QuadrupleAssembly
open Finset

def orderedMembers {m : ℕ} (B : Finset (Fin m)) : List (Fin m) :=
  (List.finRange m).filter (fun x => decide (x ∈ B))

private theorem orderedMembers_eq_sort {m : ℕ} (B : Finset (Fin m)) :
    orderedMembers B = B.sort := by
  have hs : (orderedMembers B).SortedLT :=
    ((List.sortedLT_finRange m).pairwise.sublist (List.filter_sublist)).sortedLT
  exact hs.eq_of_mem_iff B.sortedLT_sort (by simp [orderedMembers])

def memberAt {m : ℕ} (B : Finset (Fin m)) (i : Fin B.card) : Fin m :=
  (orderedMembers B)[i.val]'(by rw [orderedMembers_eq_sort, length_sort]; exact i.isLt)

private theorem memberAt_eq {m : ℕ} (B : Finset (Fin m)) (i : Fin B.card) :
    memberAt B i = B.orderEmbOfFin rfl i := by
  simp only [memberAt, orderedMembers_eq_sort, orderEmbOfFin_apply, Fin.getElem_fin]

/-- The same increasing embedding as blockLift, evaluated by a bounded scan
of Fin m instead of normalizing a general merge-sort termination proof. -/
def fastBlockLift {m : ℕ} {A : Type*} (B : Finset (Fin m)) :
    (Fin B.card × A) ↪ (Fin m × A) where
  toFun := fun p => (memberAt B p.1,p.2)
  inj' := by
    intro x y he
    apply (blockLift B).injective
    change ((B.orderEmbOfFin rfl) x.1,x.2) = ((B.orderEmbOfFin rfl) y.1,y.2)
    simpa only [memberAt_eq] using he

theorem fastBlockLift_eq {m : ℕ} {A : Type*} (B : Finset (Fin m)) :
    fastBlockLift (A := A) B = blockLift B := by
  apply Function.Embedding.ext
  intro p
  exact Prod.ext (memberAt_eq B p.1) rfl

/-- List-level substitution exposes a linear correspondence boundary. -/
def substitutionRows {m : ℕ} {A : Type*} [DecidableEq A]
    (masters : List (Finset (Fin m))) (templates : (n : ℕ) → List (Finset (Fin n × A))) :
    List (Finset (Fin m × A)) :=
  masters.flatMap (fun B => (templates B.card).map (fun D => D.map (fastBlockLift B)))

theorem substitutionRows_family {m : ℕ} {A : Type*} [DecidableEq A]
    (masters : List (Finset (Fin m))) (templates : (n : ℕ) → List (Finset (Fin n × A))) :
    (substitutionRows masters templates).toFinset =
      productSubstitute masters.toFinset (fun n => (templates n).toFinset) := by
  ext D
  simp [substitutionRows,productSubstitute,replaceBlock,fastBlockLift_eq]

def transportRows {α β : Type*} (e : α ≃ β) (rows : List (Finset α)) : List (Finset β) :=
  rows.map (fun B => B.map e.toEmbedding)

theorem transportRows_family {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (rows : List (Finset α)) :
    (transportRows e rows).toFinset = CoveringDesigns.relabel e rows.toFinset := by
  ext D
  simp [transportRows,CoveringDesigns.relabel]

end CoveringDesigns.QuadrupleAssembly
