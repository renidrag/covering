import CoveringDesigns.TwoKMinusTwo.AffineWeights
import CoveringDesigns.TwoKMinusTwo.Expansion

/-! An actual ordinary covering with at most fourteen blocks, for every k≥3. -/
namespace CoveringDesigns.TwoKMinusTwo
open Finset AffineConstructions
open scoped LinearAlgebra.Projectivization

/-- All subsets of at most three base points, including the empty set,
are covered by the indexed affine planes. -/
theorem small_base_subset (T : Finset Base) (hT : T.card ≤ 3) :
    ∃ p : Direction (ZMod 2) 3, ∃ c : ZMod 2, T ⊆ hyperplane p c := by
  classical
  obtain ⟨U,hTU,_,hU⟩ := exists_subsuperset_card_eq (subset_univ T) hT
    (by simpa [base_card] using (show 3 ≤ Fintype.card Base by rw [base_card]; omega))
  obtain ⟨p,c,h⟩ := hyperplanes_cover (F := ZMod 2) (by decide : 0<3) U hU
  exact ⟨p,c,hTU.trans h⟩

/-- The construction on arbitrary point labels, with duplicates removed. -/
theorem upper_bound {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) :
    ∃ C : Family α, IsCover C k 3 ∧ C.card ≤ 14 := by
  classical
  let a := (k-3)/4
  let j := (k-3)%4
  have hj : j<4 := Nat.mod_lt _ (by decide)
  have hsplit : 3+4*a+j=k := by
    have h := Nat.mod_add_div (k-3) 4
    dsimp [a,j]
    omega
  let w := weight a j
  have hsum : (∑ x, w x) = 2*k-2 := by
    simpa [w,hsplit] using weight_sum a j hj
  let P := Direction (ZMod 2) 3
  have : Finite (Module.Dual (ZMod 2) Base) := Module.finite_of_finite (ZMod 2)
  let : Fintype P := Fintype.ofFinite _
  let B : P × ZMod 2 → Finset Base := fun i => hyperplane i.1 i.2
  have hi : Fintype.card (P × ZMod 2) = 14 := by
    rw [← Nat.card_eq_fintype_card]
    simpa [P] using hyperplane_indices_card (ZMod 2) 3
  obtain ⟨C,hC,hcard⟩ := weighted_expansion w B
    (k := k) (t := 3) (by rw [hsum]; omega)
    (by intro i; simpa [w,B,hsplit] using weight_plane_le a j hj i.1 i.2)
    (by intro T hT; obtain ⟨p,c,h⟩ := small_base_subset T hT; exact ⟨(p,c),h⟩)
  have he : Fintype.card (Σ x, Fin (w x)) = Fintype.card α := by
    simp only [Fintype.card_sigma, Fintype.card_fin]
    rw [hsum,hv]
  exact exists_cover_of_card_eq he ⟨C,hC,by simpa [hi] using hcard⟩

end CoveringDesigns.TwoKMinusTwo
