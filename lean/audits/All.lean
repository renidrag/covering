import CoveringDesigns

/-! The three public covering numbers, checked with their full statements
and only Lean's standard foundational axioms. Component audits additionally
check explicit finite-set statements and their prerequisite boundaries. -/

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover

#check (CoveringDesigns.covering_number_11_5_2 :
  (∃ C : Finset (Finset (Fin 11)), CoveringDesigns.IsCover C 5 2 ∧ C.card = 7) ∧
  (∀ C : Finset (Finset (Fin 11)), CoveringDesigns.IsCover C 5 2 → 7 ≤ C.card))

#check (CoveringDesigns.covering_number_12_6_3 :
  (∃ C : Finset (Finset (Fin 12)), CoveringDesigns.IsCover C 6 3 ∧ C.card = 15) ∧
  (∀ C : Finset (Finset (Fin 12)), CoveringDesigns.IsCover C 6 3 → 15 ≤ C.card))

#check (CoveringDesigns.covering_number_13_7_4 :
  (∃ C : Finset (Finset (Fin 13)), CoveringDesigns.IsCover C 7 4 ∧ C.card = 30) ∧
  (∀ C : Finset (Finset (Fin 13)), CoveringDesigns.IsCover C 7 4 → 30 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_11_5_2
  CoveringDesigns.covering_number_12_6_3 CoveringDesigns.covering_number_13_7_4
  CoveringDesigns.stanton_classification CoveringDesigns.gppt_structural_reduction
  CoveringDesigns.gppt_classification

#print axioms CoveringDesigns.covering_number_11_5_2
#print axioms CoveringDesigns.covering_number_12_6_3
#print axioms CoveringDesigns.covering_number_13_7_4
#print axioms CoveringDesigns.stanton_classification
#print axioms CoveringDesigns.gppt_structural_reduction
#print axioms CoveringDesigns.gppt_classification
