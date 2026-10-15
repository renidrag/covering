import CoveringDesigns.C12_6_3.Structural.Exceptional
import CoveringDesigns.C12_6_3.Structural.TriplicateContradiction
import CoveringDesigns.C12_6_3.Structural.TriplicateReindex

/-!
The three cases of GPPT Lemma 5.8. The repeated, nonconstant case is
excluded by the six-incidence budget and the local Stanton contradiction.
All coordinate changes merely reorder the three roots and the three triads.
-/

namespace CoveringDesigns.GPPTStructural

open Finset

namespace TriplicateFrame

variable {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}

/-- The final Case 3 contradiction with arbitrary root and triad indices. -/
theorem repeated_column_minimum_contradiction (F : TriplicateFrame C)
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hc : C.card = 15)
    {j k r s : Fin 3} (hkj : k ≠ j) (hrs : r ≠ s)
    (he : (F.row r).selected j = (F.row s).selected j)
    (hnonconstant : ¬ ∃ x, ∀ a, (F.row a).selected j = x)
    (hi : ∀ l, l ≠ j → Function.Injective fun a => (F.row a).selected l)
    (hmin : degree C ((F.row r).selected k) = 7) : False := by
  obtain ⟨t, ht⟩ : ∃ t, (F.row t).selected j ≠ (F.row r).selected j := by
    by_contra! hall
    exact hnonconstant ⟨(F.row r).selected j, hall⟩
  have hrt : r ≠ t := fun h => ht (h ▸ rfl)
  have hst : s ≠ t := fun h => ht (h ▸ he.symm)
  obtain ⟨l, hjl, hkl⟩ := fin3_exists_third hkj.symm
  let ρ := fin3_indexPerm r s t hrs hrt hst
  let σ := fin3_indexPerm j k l hkj.symm hjl hkl
  let G := F.reindex ρ σ
  apply G.repeated_column_minimum_selected_contradiction hn hC hc
  · simpa [G, ρ, σ] using he.symm
  · simpa [G, ρ, σ] using ht
  · change Function.Injective (fun a => (F.row (ρ a)).selected (σ 1))
    simpa only [σ, fin3_indexPerm_one, Function.comp_def] using (hi k hkj).comp ρ.injective
  · change Function.Injective (fun a => (F.row (ρ a)).selected (σ 2))
    simpa only [σ, fin3_indexPerm_two, Function.comp_def] using (hi l hjl.symm).comp ρ.injective
  · simpa [G, ρ, σ] using hmin

/-- Every triplicate frame has either three injective selection columns or
a column with a point selected by all three roots. -/
theorem columns_injective_or_common (F : TriplicateFrame C)
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hc : C.card = 15) :
    (∀ j, Function.Injective fun r => (F.row r).selected j) ∨
      ∃ j x, ∀ r, (F.row r).selected j = x := by
  by_cases hcommon : ∃ j x, ∀ r, (F.row r).selected j = x
  · exact Or.inr hcommon
  have hnonconstant (j : Fin 3) : ¬ ∃ x, ∀ r, (F.row r).selected j = x := by
    intro h
    exact hcommon ⟨j, h⟩
  apply Or.inl
  intro j
  by_contra hrepeat
  obtain ⟨r, s, he, hrs⟩ : ∃ r s, (F.row r).selected j = (F.row s).selected j ∧ r ≠ s := by
    by_contra! h
    exact hrepeat h
  have hi := F.other_columns_injective_of_repeated hn hC hc hnonconstant hrepeat
  obtain ⟨k, hkj, hmin | hmin⟩ :=
    F.exists_minimum_selected_other_column hn hC hc hnonconstant hrs he
  · exact F.repeated_column_minimum_contradiction hn hC hc hkj hrs he
      (hnonconstant j) hi hmin
  · exact F.repeated_column_minimum_contradiction hn hC hc hkj hrs.symm he.symm
      (hnonconstant j) hi hmin

omit [Fintype α] [DecidableEq α] in
/-- GPPT Lemma 5.8: an arbitrary fifteen-block triplicate frame is a template
completion or the exceptional Figure 6 covering. -/
theorem classification {D : Family (Fin 12)} (F : TriplicateFrame D)
    (hC : IsCover D 6 3) (hc : D.card = 15) :
    IsomorphicTemplateCompletion D ∨ Isomorphic D figure6 := by
  rcases F.columns_injective_or_common (by simp) hC hc with hi | ⟨j, x, hsel⟩
  · exact Or.inl (F.injective_isomorphicTemplateCompletion hi)
  · have hx : x ∈ F.common.triad j := hsel 0 ▸ (F.row 0).selected_mem j
    exact Or.inr (F.common_column_isomorphic_figure6 (by simp) hC hc hx hsel)

#guard_standard_axioms repeated_column_minimum_contradiction
  columns_injective_or_common classification

end TriplicateFrame

end CoveringDesigns.GPPTStructural
