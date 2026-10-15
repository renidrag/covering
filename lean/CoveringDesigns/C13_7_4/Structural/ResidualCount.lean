import CoveringDesigns.C13_7_4.Structural.Basic

/-! Two residual blocks cannot both contain the same seven required points. -/

namespace CoveringDesigns.C13Structural

open Finset

variable {α : Type*} [DecidableEq α]

/-- The constant-coordinate branch leaves seven points of degree thirteen
inside a twenty-seven-block union. Two additional distinct seven-blocks
cannot raise every one of their degrees to fifteen. -/
theorem residual_two_blocks_impossible {C U : Family α} {X : Finset α}
    (hU : U ⊆ C) (hu : U.card = 27) (hb : C.card ≤ 29)
    (hC : Uniform C 7) (hx : X.card = 7)
    (hdegree : ∀ x ∈ X, degree U x = 13)
    (hlower : ∀ x ∈ X, 15 ≤ degree C x) : False := by
  let R := C \ U
  have hdis : Disjoint U R := by
    apply disjoint_left.mpr
    intro B hBU hBR
    exact (mem_sdiff.mp hBR).2 hBU
  have hunion : U ∪ R = C := union_sdiff_of_subset hU
  have hcard : U.card + R.card = C.card := by
    rw [← card_union_of_disjoint hdis, hunion]
  have hr : R.card ≤ 2 := by omega
  have hsplit (x : α) : degree C x = degree U x + degree R x := by
    rw [← hunion]
    unfold degree star
    rw [filter_union, card_union_of_disjoint
      (hdis.mono (filter_subset _ _) (filter_subset _ _))]
  have hfull (x : α) (hxm : x ∈ X) : star R x = R := by
    have hs := hsplit x
    have hd := hdegree x hxm
    have hl := hlower x hxm
    exact eq_of_subset_of_card_le (filter_subset _ _) (by change R.card ≤ degree R x; omega)
  have hsub : R ⊆ {X} := by
    intro B hB
    have hXB : X ⊆ B := by
      intro x hxm
      have hBx : B ∈ star R x := by rwa [hfull x hxm]
      exact (mem_filter.mp hBx).2
    have hBC : B ∈ C := (mem_sdiff.mp hB).1
    have he : X = B := eq_of_subset_of_card_le hXB (by rw [hx, hC B hBC])
    simp only [mem_singleton]
    exact he.symm
  have hsmall : R.card ≤ 1 := by simpa using card_le_card hsub
  obtain ⟨x, hxm⟩ := card_pos.mp (by omega : 0 < X.card)
  have hfullcard := congrArg Finset.card (hfull x hxm)
  have hs := hsplit x
  have hd := hdegree x hxm
  have hl := hlower x hxm
  change degree R x = R.card at hfullcard
  omega

#guard_standard_axioms residual_two_blocks_impossible

end CoveringDesigns.C13Structural
