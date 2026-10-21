import CoveringDesigns.C18_10_3
import CoveringDesigns.BoundaryRank.SquareDuality

/-! Retained square-core interfaces, audited separately from the lower-proof
import route. The covering deduction uses the direct incidence obstruction. -/
namespace CoveringDesigns.C18_10_3
open Finset Matrix Module
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Select eleven distinct actual row indices. Equal original supports are
never quotiented; the returned embedding retains their actual labels. -/
theorem core_representatives (R : Matrix ι κ ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℕ)
    (hl : Fintype.card ι = 16) (hb : Fintype.card κ = 11)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hrow : ∀ i, (∑ j, E i j) + (δ i : ℝ) = 3) (htotal : ∑ i, δ i = 18)
    (hgram : R * R.transpose = Matrix.diagonal (fun _ => (3 : ℝ)) + E +
      Matrix.of (fun _ _ => (3 : ℝ))) :
    ∃ f : κ ↪ ι, Matrix.of (fun i j => R (f i) j) * Matrix.transpose (fun i j => R (f i) j) =
      Matrix.diagonal (fun _ => (3 : ℝ)) + Matrix.of (fun _ _ => (3 : ℝ)) := by
  classical
  obtain ⟨e,_,_,hcross,_,hiso,_⟩ := core_pairing R E δ hl hb hs hn hz hrow htotal hgram
  let pick : Fin 5 ⊕ Fin 6 → (Fin 5 × Bool) ⊕ Fin 6 :=
    Sum.map (fun i => (i,false)) id
  have hpi : Function.Injective pick := by
    intro i j h
    cases i <;> cases j <;> simp_all [pick]
  let a : κ ≃ Fin 5 ⊕ Fin 6 := Fintype.equivOfCardEq (by simp [hb])
  let f : κ ↪ ι := ⟨fun i => e (pick (a i)), e.injective.comp (hpi.comp a.injective)⟩
  have hE (i j : κ) (hij : i ≠ j) : E (f i) (f j) = 0 := by
    have ha : a i ≠ a j := fun h => hij (a.injective h)
    change E (e (pick (a i))) (e (pick (a j))) = 0
    generalize a i = x at *
    generalize a j = y at *
    cases x with
    | inl x =>
      cases y with
      | inl y => exact hcross x y (by simpa using ha) false false
      | inr y => rw [hs]; exact hiso y _
    | inr x => exact hiso x _
  refine ⟨f,?_⟩
  ext i j
  change (R * R.transpose) (f i) (f j) = _
  rw [hgram]
  by_cases hij : i=j
  · subst j
    simp [hz]
  · have hfij : f i ≠ f j := fun h => hij (f.injective h)
    simp [hij,hfij,hE i j hij]


variable {α : Type*} [Fintype α] [DecidableEq α]

theorem row_support (C : Family α) (H : Finset α) (x : Outside H) :
    BoundaryRank.binarySupport (rowIncidence C H x) = pointSupport C x.val := by
  classical
  ext B
  simp [BoundaryRank.binarySupport,rowIncidence,pointSupport]

end CoveringDesigns.C18_10_3
