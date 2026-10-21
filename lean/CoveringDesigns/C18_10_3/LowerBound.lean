import CoveringDesigns.C18_10_3.SaturatedMatching
import CoveringDesigns.C18_10_3.Exceptional

/-! Unconditional exclusion on arbitrary finite point labels. -/
namespace CoveringDesigns

/-- Every ordinary (18,10,3) covering has at least twelve blocks. All degree,
pair, profile, rank and core premises are derived inside the proof. -/
theorem lower_bound_18_10_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) : 12 ≤ C.card := by
  classical
  have he := C18_10_3.eleven_le_card hv hC
  by_contra hn
  have hb : C.card = 11 := by omega
  have hpair := C18_10_3.pair_ge_three hv hC hb
  rcases C18_10_3.degree_profiles hv hC hb with ⟨h,hh,hlow⟩ | ⟨h,g,hne,hh,hg,hlow⟩
  · exact C18_10_3.one_high_impossible hv hC hb hpair hh hlow
  · exact C18_10_3.two_high_impossible hv hC hb hpair hne hh hg hlow

/-- Repeated block occurrences are allowed. Deduplication preserves ordinary
triple coverage, and its cardinality is bounded by the number of indices. -/
theorem indexed_lower_bound_18_10_3 {α ι : Type*} [Fintype α] [Fintype ι]
    (B : ι → Finset α) (hv : Fintype.card α = 18)
    (hu : ∀ i, (B i).card = 10)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ i, T ⊆ B i) :
    12 ≤ Fintype.card ι := by
  classical
  let C : Family α := Finset.univ.image B
  have hC : IsCover C 10 3 := by
    constructor
    · intro A hA
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
      exact hu i
    · intro T hT
      obtain ⟨i,hi⟩ := hc T hT
      exact ⟨B i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩
  have hcard : C.card ≤ Fintype.card ι := by
    simpa only [C,Finset.card_univ] using Finset.card_image_le (s := Finset.univ) (f := B)
  exact (lower_bound_18_10_3 hv hC).trans hcard

end CoveringDesigns
