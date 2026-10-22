import CoveringDesigns.QuadrupleAssembly

open CoveringDesigns CoveringDesigns.QuadrupleAssembly Finset

#print CoveringDesigns.QuadrupleAssembly.GroupDesign

#print CoveringDesigns.QuadrupleAssembly.Factors

#print CoveringDesigns.QuadrupleAssembly.HSeed

#print CoveringDesigns.QuadrupleAssembly.GDDSeed

namespace CoveringDesigns.AuditQuadrupleAssembly
/-- Expanded ordinary-family output; every input contract is explicit above. -/
theorem assembly_explicit {u : ℕ} (hu : 3 ≤ u) {H G : Family (Core u)}
    {L : Family Local} {F : Fin 5 → Family (Fin 6)}
    (hH : HSeed H) (hG : GDDSeed G) (hL : IsCover L 4 3)
    (hLc : L.card = 78) (hF : Factors F) :
    (∀ B ∈ assembly H G L F, B.card = 4) ∧
    (∀ T : Finset (Point u), T.card = 3 → ∃ B ∈ assembly H G L F, T ⊆ B) ∧
    (assembly H G L F).card = 6*u^2*(12*u+1) := by
  have h := assembly_optimal hu hH hG hL hLc hF
  exact ⟨h.1.1,h.1.2,h.2⟩
end CoveringDesigns.AuditQuadrupleAssembly

#check (@CoveringDesigns.QuadrupleAssembly.assembly_optimal : ∀ {u : ℕ}, 3 ≤ u → ∀ {H G : Family (Core u)} {L : Family Local} {F : Fin 5 → Family (Fin 6)}, HSeed H → GDDSeed G → IsCover L 4 3 → L.card = 78 → Factors F → IsCover (assembly H G L F) 4 3 ∧ (assembly H G L F).card = 6*u^2*(12*u+1))

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.assembly_optimal

#print axioms CoveringDesigns.QuadrupleAssembly.assembly_optimal

#check (@CoveringDesigns.QuadrupleAssembly.assembly_sharp : ∀ {u : ℕ}, 3 ≤ u → ∀ {H G : Family (Core u)} {L : Family Local} {F : Fin 5 → Family (Fin 6)}, HSeed H → GDDSeed G → IsCover L 4 3 → L.card = 78 → Factors F → (assembly H G L F).card = 6*u^2*(12*u+1) ∧ (classA H).card = 54*(2*u).choose 3 ∧ (classB G).card = 24*u*(u-1) ∧ (classC (u := u) L).card = 78*u ∧ (classD (u := u) F).card = 90*u*(u-1) ∧ Disjoint (classA H) (classB G) ∧ Disjoint (classA H ∪ classB G) (classC L) ∧ Disjoint (classA H ∪ classB G ∪ classC L) (classD F))

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.assembly_sharp

#print axioms CoveringDesigns.QuadrupleAssembly.assembly_sharp

#check (@CoveringDesigns.QuadrupleAssembly.sources_injective : ∀ {u : ℕ}, 3 ≤ u → ∀ {H G : Family (Core u)} {L : Family Local} {F : Fin 5 → Family (Fin 6)}, HSeed H → GDDSeed G → IsCover L 4 3 → L.card = 78 → Factors F → Set.InjOn (fun B => B.map (coreEmbedding u)) (H : Set (Finset (Core u))) ∧ Set.InjOn (fun B => insert none (B.map (coreEmbedding u))) (G : Set (Finset (Core u))) ∧ Function.Injective (fillingBlock (u := u) (L := L)) ∧ Function.Injective (pairBlock (u := u) (F := F)))

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.sources_injective

#print axioms CoveringDesigns.QuadrupleAssembly.sources_injective

#check (@CoveringDesigns.QuadrupleAssembly.classes_disjoint : ∀ {u : ℕ}, 3 ≤ u → ∀ {H G : Family (Core u)} {L : Family Local} {F : Fin 5 → Family (Fin 6)}, HSeed H → GDDSeed G → IsCover L 4 3 → L.card = 78 → Factors F → Disjoint (classA H) (classB G) ∧ Disjoint (classA H) (classC L) ∧ Disjoint (classA H) (classD F) ∧ Disjoint (classB G) (classC L) ∧ Disjoint (classB G) (classD F) ∧ Disjoint (classC (u := u) L) (classD F))

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.classes_disjoint

#print axioms CoveringDesigns.QuadrupleAssembly.classes_disjoint

#check (@CoveringDesigns.QuadrupleAssembly.ceilings : ∀ {u : ℕ}, 3 ≤ u → Schoenheim.ceilDiv (12*u-1) 2 = 6*u ∧ Schoenheim.ceilDiv (12*u*(6*u)) 3 = 24*u^2 ∧ Schoenheim.ceilDiv ((12*u+1)*(24*u^2)) 4 = 6*u^2*(12*u+1))

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.ceilings

#print axioms CoveringDesigns.QuadrupleAssembly.ceilings

#check (@CoveringDesigns.QuadrupleAssembly.lower_bound : ∀ {α : Type*} [Fintype α] [DecidableEq α] {u : ℕ}, 3 ≤ u → Fintype.card α = 12*u+1 → ∀ {C : Family α}, IsCover C 4 3 → 6*u^2*(12*u+1) ≤ C.card)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.lower_bound

#print axioms CoveringDesigns.QuadrupleAssembly.lower_bound

#check (@CoveringDesigns.QuadrupleAssembly.h_seed_card : ∀ {u : ℕ} {H : Family (Core u)}, HSeed H → H.card = 54*(2*u).choose 3)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.h_seed_card

#print axioms CoveringDesigns.QuadrupleAssembly.h_seed_card

#check (@CoveringDesigns.QuadrupleAssembly.gdd_seed_card : ∀ {u : ℕ} {G : Family (Core u)}, GDDSeed G → G.card = 24*u*(u-1))

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.gdd_seed_card

#print axioms CoveringDesigns.QuadrupleAssembly.gdd_seed_card

#check (@CoveringDesigns.QuadrupleAssembly.h_valid : ∀ {u : ℕ}, 3 ≤ u → u ≤ 8 → HSeed (hRows u).toFinset)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.h_valid

#print axioms CoveringDesigns.QuadrupleAssembly.h_valid

#check (@CoveringDesigns.QuadrupleAssembly.g_valid : ∀ {u : ℕ}, 3 ≤ u → u ≤ 8 → GDDSeed (gRows u).toFinset)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.g_valid

#print axioms CoveringDesigns.QuadrupleAssembly.g_valid

#check (@CoveringDesigns.QuadrupleAssembly.filling_valid : IsCover filling 4 3)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.filling_valid

#print axioms CoveringDesigns.QuadrupleAssembly.filling_valid

#check (@CoveringDesigns.QuadrupleAssembly.filling_card : filling.card = 78)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.filling_card

#print axioms CoveringDesigns.QuadrupleAssembly.filling_card

#check (@CoveringDesigns.QuadrupleAssembly.factors_valid : Factors factors)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.factors_valid

#print axioms CoveringDesigns.QuadrupleAssembly.factors_valid

#check (@CoveringDesigns.QuadrupleAssembly.label_some : ∀ {u : ℕ} (h : Fin u) (b : Fin 2) (i : Fin 6), (labelEquiv u (some ((h,b),i))).val = 12*h.val+6*b.val+i.val)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.label_some

#print axioms CoveringDesigns.QuadrupleAssembly.label_some

#check (@CoveringDesigns.QuadrupleAssembly.productSubstitute_valid : ∀ {β A γ : Type*} [LinearOrder β] [DecidableEq A] (g : β → γ) {k t : ℕ} {M : Family β}, Master g t M → ∀ (template : (n : ℕ) → Family (Fin n × A)), (∀ B ∈ M, GroupDesign Prod.fst k t (template B.card)) → GroupDesign (fun p : β × A => g p.1) k t (productSubstitute M template))

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.productSubstitute_valid

#print axioms CoveringDesigns.QuadrupleAssembly.productSubstitute_valid

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V37.rows_eq : CoveringDesigns.QuadrupleAssembly.WitnessData.V37.rows = labelledRows 3)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V37.rows_eq

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V37.rows_eq

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V37.correspondence : CoveringDesigns.QuadrupleAssembly.WitnessData.V37.blocks = labelledFamily 3)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V37.correspondence

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V37.correspondence

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V37.optimal : IsCover CoveringDesigns.QuadrupleAssembly.WitnessData.V37.blocks 4 3 ∧ CoveringDesigns.QuadrupleAssembly.WitnessData.V37.blocks.card = 1998)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V37.optimal

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V37.optimal

#check (@CoveringDesigns.knownCover1998_37_4_3_optimal : IsCover CoveringDesigns.knownCover1998_37_4_3 4 3 ∧ CoveringDesigns.knownCover1998_37_4_3.card = 1998)

#guard_standard_axioms CoveringDesigns.knownCover1998_37_4_3_optimal

#print axioms CoveringDesigns.knownCover1998_37_4_3_optimal

#check (@CoveringDesigns.knownCover1998_37_4_3_on_optimal : ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 37), IsCover (CoveringDesigns.knownCover1998_37_4_3_on hv) 4 3 ∧ (CoveringDesigns.knownCover1998_37_4_3_on hv).card = 1998)

#guard_standard_axioms CoveringDesigns.knownCover1998_37_4_3_on_optimal

#print axioms CoveringDesigns.knownCover1998_37_4_3_on_optimal

#check (@CoveringDesigns.lower_bound_37_4_3 : ∀ {α : Type*} [Fintype α] {C : Family α}, Fintype.card α = 37 → IsCover C 4 3 → 1998 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_37_4_3

#print axioms CoveringDesigns.lower_bound_37_4_3

#check (@CoveringDesigns.covering_number_37_4_3_on : ∀ {α : Type*} [Fintype α], Fintype.card α = 37 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = 1998) ∧ (∀ C : Family α, IsCover C 4 3 → 1998 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_37_4_3_on

#print axioms CoveringDesigns.covering_number_37_4_3_on

#check (@CoveringDesigns.covering_number_37_4_3 : (∃ C : Family (Fin 37), IsCover C 4 3 ∧ C.card = 1998) ∧ (∀ C : Family (Fin 37), IsCover C 4 3 → 1998 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_37_4_3

#print axioms CoveringDesigns.covering_number_37_4_3

namespace CoveringDesigns.AuditQuadrupleAssembly
theorem exact_37_explicit {α : Type*} [Fintype α] (hv : Fintype.card α = 37) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 1998) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 1998 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hl⟩ := covering_number_37_4_3_on hv
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hl C ⟨hu,hc⟩⟩
end CoveringDesigns.AuditQuadrupleAssembly

#guard_standard_axioms CoveringDesigns.AuditQuadrupleAssembly.exact_37_explicit

#print axioms CoveringDesigns.AuditQuadrupleAssembly.exact_37_explicit

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V49.rows_eq : CoveringDesigns.QuadrupleAssembly.WitnessData.V49.rows = labelledRows 4)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V49.rows_eq

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V49.rows_eq

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V49.correspondence : CoveringDesigns.QuadrupleAssembly.WitnessData.V49.blocks = labelledFamily 4)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V49.correspondence

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V49.correspondence

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V49.optimal : IsCover CoveringDesigns.QuadrupleAssembly.WitnessData.V49.blocks 4 3 ∧ CoveringDesigns.QuadrupleAssembly.WitnessData.V49.blocks.card = 4704)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V49.optimal

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V49.optimal

#check (@CoveringDesigns.knownCover4704_49_4_3_optimal : IsCover CoveringDesigns.knownCover4704_49_4_3 4 3 ∧ CoveringDesigns.knownCover4704_49_4_3.card = 4704)

#guard_standard_axioms CoveringDesigns.knownCover4704_49_4_3_optimal

#print axioms CoveringDesigns.knownCover4704_49_4_3_optimal

#check (@CoveringDesigns.knownCover4704_49_4_3_on_optimal : ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 49), IsCover (CoveringDesigns.knownCover4704_49_4_3_on hv) 4 3 ∧ (CoveringDesigns.knownCover4704_49_4_3_on hv).card = 4704)

#guard_standard_axioms CoveringDesigns.knownCover4704_49_4_3_on_optimal

#print axioms CoveringDesigns.knownCover4704_49_4_3_on_optimal

#check (@CoveringDesigns.lower_bound_49_4_3 : ∀ {α : Type*} [Fintype α] {C : Family α}, Fintype.card α = 49 → IsCover C 4 3 → 4704 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_49_4_3

#print axioms CoveringDesigns.lower_bound_49_4_3

#check (@CoveringDesigns.covering_number_49_4_3_on : ∀ {α : Type*} [Fintype α], Fintype.card α = 49 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = 4704) ∧ (∀ C : Family α, IsCover C 4 3 → 4704 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_49_4_3_on

#print axioms CoveringDesigns.covering_number_49_4_3_on

#check (@CoveringDesigns.covering_number_49_4_3 : (∃ C : Family (Fin 49), IsCover C 4 3 ∧ C.card = 4704) ∧ (∀ C : Family (Fin 49), IsCover C 4 3 → 4704 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_49_4_3

#print axioms CoveringDesigns.covering_number_49_4_3

namespace CoveringDesigns.AuditQuadrupleAssembly
theorem exact_49_explicit {α : Type*} [Fintype α] (hv : Fintype.card α = 49) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 4704) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 4704 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hl⟩ := covering_number_49_4_3_on hv
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hl C ⟨hu,hc⟩⟩
end CoveringDesigns.AuditQuadrupleAssembly

#guard_standard_axioms CoveringDesigns.AuditQuadrupleAssembly.exact_49_explicit

#print axioms CoveringDesigns.AuditQuadrupleAssembly.exact_49_explicit

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V61.rows_eq : CoveringDesigns.QuadrupleAssembly.WitnessData.V61.rows = labelledRows 5)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V61.rows_eq

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V61.rows_eq

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V61.correspondence : CoveringDesigns.QuadrupleAssembly.WitnessData.V61.blocks = labelledFamily 5)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V61.correspondence

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V61.correspondence

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V61.optimal : IsCover CoveringDesigns.QuadrupleAssembly.WitnessData.V61.blocks 4 3 ∧ CoveringDesigns.QuadrupleAssembly.WitnessData.V61.blocks.card = 9150)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V61.optimal

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V61.optimal

#check (@CoveringDesigns.knownCover9150_61_4_3_optimal : IsCover CoveringDesigns.knownCover9150_61_4_3 4 3 ∧ CoveringDesigns.knownCover9150_61_4_3.card = 9150)

#guard_standard_axioms CoveringDesigns.knownCover9150_61_4_3_optimal

#print axioms CoveringDesigns.knownCover9150_61_4_3_optimal

#check (@CoveringDesigns.knownCover9150_61_4_3_on_optimal : ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 61), IsCover (CoveringDesigns.knownCover9150_61_4_3_on hv) 4 3 ∧ (CoveringDesigns.knownCover9150_61_4_3_on hv).card = 9150)

#guard_standard_axioms CoveringDesigns.knownCover9150_61_4_3_on_optimal

#print axioms CoveringDesigns.knownCover9150_61_4_3_on_optimal

#check (@CoveringDesigns.lower_bound_61_4_3 : ∀ {α : Type*} [Fintype α] {C : Family α}, Fintype.card α = 61 → IsCover C 4 3 → 9150 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_61_4_3

#print axioms CoveringDesigns.lower_bound_61_4_3

#check (@CoveringDesigns.covering_number_61_4_3_on : ∀ {α : Type*} [Fintype α], Fintype.card α = 61 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = 9150) ∧ (∀ C : Family α, IsCover C 4 3 → 9150 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_61_4_3_on

#print axioms CoveringDesigns.covering_number_61_4_3_on

#check (@CoveringDesigns.covering_number_61_4_3 : (∃ C : Family (Fin 61), IsCover C 4 3 ∧ C.card = 9150) ∧ (∀ C : Family (Fin 61), IsCover C 4 3 → 9150 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_61_4_3

#print axioms CoveringDesigns.covering_number_61_4_3

namespace CoveringDesigns.AuditQuadrupleAssembly
theorem exact_61_explicit {α : Type*} [Fintype α] (hv : Fintype.card α = 61) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 9150) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 9150 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hl⟩ := covering_number_61_4_3_on hv
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hl C ⟨hu,hc⟩⟩
end CoveringDesigns.AuditQuadrupleAssembly

#guard_standard_axioms CoveringDesigns.AuditQuadrupleAssembly.exact_61_explicit

#print axioms CoveringDesigns.AuditQuadrupleAssembly.exact_61_explicit

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V73.rows_eq : CoveringDesigns.QuadrupleAssembly.WitnessData.V73.rows = labelledRows 6)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V73.rows_eq

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V73.rows_eq

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V73.correspondence : CoveringDesigns.QuadrupleAssembly.WitnessData.V73.blocks = labelledFamily 6)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V73.correspondence

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V73.correspondence

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V73.optimal : IsCover CoveringDesigns.QuadrupleAssembly.WitnessData.V73.blocks 4 3 ∧ CoveringDesigns.QuadrupleAssembly.WitnessData.V73.blocks.card = 15768)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V73.optimal

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V73.optimal

#check (@CoveringDesigns.knownCover15768_73_4_3_optimal : IsCover CoveringDesigns.knownCover15768_73_4_3 4 3 ∧ CoveringDesigns.knownCover15768_73_4_3.card = 15768)

#guard_standard_axioms CoveringDesigns.knownCover15768_73_4_3_optimal

#print axioms CoveringDesigns.knownCover15768_73_4_3_optimal

#check (@CoveringDesigns.knownCover15768_73_4_3_on_optimal : ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 73), IsCover (CoveringDesigns.knownCover15768_73_4_3_on hv) 4 3 ∧ (CoveringDesigns.knownCover15768_73_4_3_on hv).card = 15768)

#guard_standard_axioms CoveringDesigns.knownCover15768_73_4_3_on_optimal

#print axioms CoveringDesigns.knownCover15768_73_4_3_on_optimal

#check (@CoveringDesigns.lower_bound_73_4_3 : ∀ {α : Type*} [Fintype α] {C : Family α}, Fintype.card α = 73 → IsCover C 4 3 → 15768 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_73_4_3

#print axioms CoveringDesigns.lower_bound_73_4_3

#check (@CoveringDesigns.covering_number_73_4_3_on : ∀ {α : Type*} [Fintype α], Fintype.card α = 73 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = 15768) ∧ (∀ C : Family α, IsCover C 4 3 → 15768 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_73_4_3_on

#print axioms CoveringDesigns.covering_number_73_4_3_on

#check (@CoveringDesigns.covering_number_73_4_3 : (∃ C : Family (Fin 73), IsCover C 4 3 ∧ C.card = 15768) ∧ (∀ C : Family (Fin 73), IsCover C 4 3 → 15768 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_73_4_3

#print axioms CoveringDesigns.covering_number_73_4_3

namespace CoveringDesigns.AuditQuadrupleAssembly
theorem exact_73_explicit {α : Type*} [Fintype α] (hv : Fintype.card α = 73) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 15768) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 15768 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hl⟩ := covering_number_73_4_3_on hv
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hl C ⟨hu,hc⟩⟩
end CoveringDesigns.AuditQuadrupleAssembly

#guard_standard_axioms CoveringDesigns.AuditQuadrupleAssembly.exact_73_explicit

#print axioms CoveringDesigns.AuditQuadrupleAssembly.exact_73_explicit

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V85.rows_eq : CoveringDesigns.QuadrupleAssembly.WitnessData.V85.rows = labelledRows 7)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V85.rows_eq

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V85.rows_eq

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V85.correspondence : CoveringDesigns.QuadrupleAssembly.WitnessData.V85.blocks = labelledFamily 7)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V85.correspondence

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V85.correspondence

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V85.optimal : IsCover CoveringDesigns.QuadrupleAssembly.WitnessData.V85.blocks 4 3 ∧ CoveringDesigns.QuadrupleAssembly.WitnessData.V85.blocks.card = 24990)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V85.optimal

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V85.optimal

#check (@CoveringDesigns.knownCover24990_85_4_3_optimal : IsCover CoveringDesigns.knownCover24990_85_4_3 4 3 ∧ CoveringDesigns.knownCover24990_85_4_3.card = 24990)

#guard_standard_axioms CoveringDesigns.knownCover24990_85_4_3_optimal

#print axioms CoveringDesigns.knownCover24990_85_4_3_optimal

#check (@CoveringDesigns.knownCover24990_85_4_3_on_optimal : ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 85), IsCover (CoveringDesigns.knownCover24990_85_4_3_on hv) 4 3 ∧ (CoveringDesigns.knownCover24990_85_4_3_on hv).card = 24990)

#guard_standard_axioms CoveringDesigns.knownCover24990_85_4_3_on_optimal

#print axioms CoveringDesigns.knownCover24990_85_4_3_on_optimal

#check (@CoveringDesigns.lower_bound_85_4_3 : ∀ {α : Type*} [Fintype α] {C : Family α}, Fintype.card α = 85 → IsCover C 4 3 → 24990 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_85_4_3

#print axioms CoveringDesigns.lower_bound_85_4_3

#check (@CoveringDesigns.covering_number_85_4_3_on : ∀ {α : Type*} [Fintype α], Fintype.card α = 85 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = 24990) ∧ (∀ C : Family α, IsCover C 4 3 → 24990 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_85_4_3_on

#print axioms CoveringDesigns.covering_number_85_4_3_on

#check (@CoveringDesigns.covering_number_85_4_3 : (∃ C : Family (Fin 85), IsCover C 4 3 ∧ C.card = 24990) ∧ (∀ C : Family (Fin 85), IsCover C 4 3 → 24990 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_85_4_3

#print axioms CoveringDesigns.covering_number_85_4_3

namespace CoveringDesigns.AuditQuadrupleAssembly
theorem exact_85_explicit {α : Type*} [Fintype α] (hv : Fintype.card α = 85) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 24990) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 24990 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hl⟩ := covering_number_85_4_3_on hv
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hl C ⟨hu,hc⟩⟩
end CoveringDesigns.AuditQuadrupleAssembly

#guard_standard_axioms CoveringDesigns.AuditQuadrupleAssembly.exact_85_explicit

#print axioms CoveringDesigns.AuditQuadrupleAssembly.exact_85_explicit

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V97.rows_eq : CoveringDesigns.QuadrupleAssembly.WitnessData.V97.rows = labelledRows 8)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V97.rows_eq

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V97.rows_eq

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V97.correspondence : CoveringDesigns.QuadrupleAssembly.WitnessData.V97.blocks = labelledFamily 8)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V97.correspondence

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V97.correspondence

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V97.optimal : IsCover CoveringDesigns.QuadrupleAssembly.WitnessData.V97.blocks 4 3 ∧ CoveringDesigns.QuadrupleAssembly.WitnessData.V97.blocks.card = 37248)

#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V97.optimal

#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V97.optimal

#check (@CoveringDesigns.knownCover37248_97_4_3_optimal : IsCover CoveringDesigns.knownCover37248_97_4_3 4 3 ∧ CoveringDesigns.knownCover37248_97_4_3.card = 37248)

#guard_standard_axioms CoveringDesigns.knownCover37248_97_4_3_optimal

#print axioms CoveringDesigns.knownCover37248_97_4_3_optimal

#check (@CoveringDesigns.knownCover37248_97_4_3_on_optimal : ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 97), IsCover (CoveringDesigns.knownCover37248_97_4_3_on hv) 4 3 ∧ (CoveringDesigns.knownCover37248_97_4_3_on hv).card = 37248)

#guard_standard_axioms CoveringDesigns.knownCover37248_97_4_3_on_optimal

#print axioms CoveringDesigns.knownCover37248_97_4_3_on_optimal

#check (@CoveringDesigns.lower_bound_97_4_3 : ∀ {α : Type*} [Fintype α] {C : Family α}, Fintype.card α = 97 → IsCover C 4 3 → 37248 ≤ C.card)

#guard_standard_axioms CoveringDesigns.lower_bound_97_4_3

#print axioms CoveringDesigns.lower_bound_97_4_3

#check (@CoveringDesigns.covering_number_97_4_3_on : ∀ {α : Type*} [Fintype α], Fintype.card α = 97 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = 37248) ∧ (∀ C : Family α, IsCover C 4 3 → 37248 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_97_4_3_on

#print axioms CoveringDesigns.covering_number_97_4_3_on

#check (@CoveringDesigns.covering_number_97_4_3 : (∃ C : Family (Fin 97), IsCover C 4 3 ∧ C.card = 37248) ∧ (∀ C : Family (Fin 97), IsCover C 4 3 → 37248 ≤ C.card))

#guard_standard_axioms CoveringDesigns.covering_number_97_4_3

#print axioms CoveringDesigns.covering_number_97_4_3

namespace CoveringDesigns.AuditQuadrupleAssembly
theorem exact_97_explicit {α : Type*} [Fintype α] (hv : Fintype.card α = 97) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 37248) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 37248 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hl⟩ := covering_number_97_4_3_on hv
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hl C ⟨hu,hc⟩⟩
end CoveringDesigns.AuditQuadrupleAssembly

#guard_standard_axioms CoveringDesigns.AuditQuadrupleAssembly.exact_97_explicit

#print axioms CoveringDesigns.AuditQuadrupleAssembly.exact_97_explicit

#guard_standard_axioms CoveringDesigns.AuditQuadrupleAssembly.assembly_explicit

#print axioms CoveringDesigns.AuditQuadrupleAssembly.assembly_explicit

-- Small cases and complete admissible finite range.

#check (@CoveringDesigns.QuadrupleAssembly.ceilings_13 : Schoenheim.ceilDiv 11 2 = 6 ∧ Schoenheim.ceilDiv (12*6) 3 = 24 ∧ Schoenheim.ceilDiv (13*24) 4 = 78)
#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.ceilings_13
#print axioms CoveringDesigns.QuadrupleAssembly.ceilings_13

#check (@CoveringDesigns.QuadrupleAssembly.schoenheim_13 : Schoenheim.bound 13 4 3 = 78)
#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.schoenheim_13
#print axioms CoveringDesigns.QuadrupleAssembly.schoenheim_13

#check (@CoveringDesigns.QuadrupleAssembly.ceilings_25 : Schoenheim.ceilDiv 23 2 = 12 ∧ Schoenheim.ceilDiv (24*12) 3 = 96 ∧ Schoenheim.ceilDiv (25*96) 4 = 600)
#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.ceilings_25
#print axioms CoveringDesigns.QuadrupleAssembly.ceilings_25

#check (@CoveringDesigns.QuadrupleAssembly.schoenheim_25 : Schoenheim.bound 25 4 3 = 600)
#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.schoenheim_25
#print axioms CoveringDesigns.QuadrupleAssembly.schoenheim_25

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V25.checked : selectorCoverCheck id 3 WitnessData.V25.rows WitnessData.V25.ownerIndex = true)
#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.checked
#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.checked

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V25.valid : IsCover WitnessData.V25.blocks 4 3)
#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.valid
#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.valid

#check (@CoveringDesigns.QuadrupleAssembly.WitnessData.V25.size : WitnessData.V25.blocks.card = 600)
#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.size
#print axioms CoveringDesigns.QuadrupleAssembly.WitnessData.V25.size

#check (@CoveringDesigns.knownCover78_13_4_3_correspondence : knownCover78_13_4_3 = SeedData.Filling.rows.toFinset)
#guard_standard_axioms CoveringDesigns.knownCover78_13_4_3_correspondence
#print axioms CoveringDesigns.knownCover78_13_4_3_correspondence

#check (@CoveringDesigns.knownCover78_13_4_3_optimal : IsCover knownCover78_13_4_3 4 3 ∧ knownCover78_13_4_3.card = 78)
#guard_standard_axioms CoveringDesigns.knownCover78_13_4_3_optimal
#print axioms CoveringDesigns.knownCover78_13_4_3_optimal

#check (@CoveringDesigns.knownCover78_13_4_3_on_optimal : ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 13), IsCover (knownCover78_13_4_3_on hv) 4 3 ∧ (knownCover78_13_4_3_on hv).card = 78)
#guard_standard_axioms CoveringDesigns.knownCover78_13_4_3_on_optimal
#print axioms CoveringDesigns.knownCover78_13_4_3_on_optimal

#check (@CoveringDesigns.lower_bound_13_4_3 : ∀ {α : Type*} [Fintype α] {C : Family α}, Fintype.card α = 13 → IsCover C 4 3 → 78 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_13_4_3
#print axioms CoveringDesigns.lower_bound_13_4_3

#check (@CoveringDesigns.covering_number_13_4_3_on : ∀ {α : Type*} [Fintype α], Fintype.card α = 13 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = 78) ∧ (∀ C : Family α, IsCover C 4 3 → 78 ≤ C.card))
#guard_standard_axioms CoveringDesigns.covering_number_13_4_3_on
#print axioms CoveringDesigns.covering_number_13_4_3_on

#check (@CoveringDesigns.covering_number_13_4_3 : (∃ C : Family (Fin 13), IsCover C 4 3 ∧ C.card = 78) ∧ (∀ C : Family (Fin 13), IsCover C 4 3 → 78 ≤ C.card))
#guard_standard_axioms CoveringDesigns.covering_number_13_4_3
#print axioms CoveringDesigns.covering_number_13_4_3

#check (@CoveringDesigns.knownCover600_25_4_3_correspondence : knownCover600_25_4_3 = WitnessData.V25.rows.toFinset)
#guard_standard_axioms CoveringDesigns.knownCover600_25_4_3_correspondence
#print axioms CoveringDesigns.knownCover600_25_4_3_correspondence

#check (@CoveringDesigns.knownCover600_25_4_3_optimal : IsCover knownCover600_25_4_3 4 3 ∧ knownCover600_25_4_3.card = 600)
#guard_standard_axioms CoveringDesigns.knownCover600_25_4_3_optimal
#print axioms CoveringDesigns.knownCover600_25_4_3_optimal

#check (@CoveringDesigns.knownCover600_25_4_3_on_optimal : ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 25), IsCover (knownCover600_25_4_3_on hv) 4 3 ∧ (knownCover600_25_4_3_on hv).card = 600)
#guard_standard_axioms CoveringDesigns.knownCover600_25_4_3_on_optimal
#print axioms CoveringDesigns.knownCover600_25_4_3_on_optimal

#check (@CoveringDesigns.lower_bound_25_4_3 : ∀ {α : Type*} [Fintype α] {C : Family α}, Fintype.card α = 25 → IsCover C 4 3 → 600 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_25_4_3
#print axioms CoveringDesigns.lower_bound_25_4_3

#check (@CoveringDesigns.covering_number_25_4_3_on : ∀ {α : Type*} [Fintype α], Fintype.card α = 25 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = 600) ∧ (∀ C : Family α, IsCover C 4 3 → 600 ≤ C.card))
#guard_standard_axioms CoveringDesigns.covering_number_25_4_3_on
#print axioms CoveringDesigns.covering_number_25_4_3_on

#check (@CoveringDesigns.covering_number_25_4_3 : (∃ C : Family (Fin 25), IsCover C 4 3 ∧ C.card = 600) ∧ (∀ C : Family (Fin 25), IsCover C 4 3 → 600 ≤ C.card))
#guard_standard_axioms CoveringDesigns.covering_number_25_4_3
#print axioms CoveringDesigns.covering_number_25_4_3

#check (@CoveringDesigns.QuadrupleAssembly.admissible_below_100_iff : ∀ n : ℕ, (4 ≤ n ∧ n < 100 ∧ n % 12 = 1) ↔ (n = 13 ∨ n = 25 ∨ n = 37 ∨ n = 49 ∨ n = 61 ∨ n = 73 ∨ n = 85 ∨ n = 97))
#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.admissible_below_100_iff
#print axioms CoveringDesigns.QuadrupleAssembly.admissible_below_100_iff

#check (@CoveringDesigns.QuadrupleAssembly.formula_divisible_below_100 : ∀ {n : ℕ}, 4 ≤ n → n < 100 → n % 12 = 1 → 24 ∣ n * (n-1)^2)
#guard_standard_axioms CoveringDesigns.QuadrupleAssembly.formula_divisible_below_100
#print axioms CoveringDesigns.QuadrupleAssembly.formula_divisible_below_100

#check (@CoveringDesigns.covering_number_one_mod_twelve_below_100_on : ∀ {α : Type*} [Fintype α] {n : ℕ}, Fintype.card α = n → 4 ≤ n → n < 100 → n % 12 = 1 → (∃ C : Family α, IsCover C 4 3 ∧ C.card = n * (n-1)^2 / 24) ∧ (∀ C : Family α, IsCover C 4 3 → n * (n-1)^2 / 24 ≤ C.card))
#guard_standard_axioms CoveringDesigns.covering_number_one_mod_twelve_below_100_on
#print axioms CoveringDesigns.covering_number_one_mod_twelve_below_100_on

#check (@CoveringDesigns.covering_number_one_mod_twelve_below_100 : ∀ {n : ℕ}, 4 ≤ n → n < 100 → n % 12 = 1 → (∃ C : Family (Fin n), IsCover C 4 3 ∧ C.card = n * (n-1)^2 / 24) ∧ (∀ C : Family (Fin n), IsCover C 4 3 → n * (n-1)^2 / 24 ≤ C.card))
#guard_standard_axioms CoveringDesigns.covering_number_one_mod_twelve_below_100
#print axioms CoveringDesigns.covering_number_one_mod_twelve_below_100

namespace CoveringDesigns.AuditQuadrupleAssembly
theorem exact_13_explicit {α : Type*} [Fintype α] (hv : Fintype.card α = 13) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 78) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 78 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hl⟩ := covering_number_13_4_3_on hv
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hl C ⟨hu,hc⟩⟩
end CoveringDesigns.AuditQuadrupleAssembly
#guard_standard_axioms CoveringDesigns.AuditQuadrupleAssembly.exact_13_explicit
#print axioms CoveringDesigns.AuditQuadrupleAssembly.exact_13_explicit

namespace CoveringDesigns.AuditQuadrupleAssembly
theorem exact_25_explicit {α : Type*} [Fintype α] (hv : Fintype.card α = 25) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 600) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 600 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hl⟩ := covering_number_25_4_3_on hv
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hl C ⟨hu,hc⟩⟩
end CoveringDesigns.AuditQuadrupleAssembly
#guard_standard_axioms CoveringDesigns.AuditQuadrupleAssembly.exact_25_explicit
#print axioms CoveringDesigns.AuditQuadrupleAssembly.exact_25_explicit

namespace CoveringDesigns.AuditQuadrupleAssembly
theorem finite_range_explicit {α : Type*} [Fintype α] {n : ℕ}
    (hv : Fintype.card α = n) (hn : 4 ≤ n) (h100 : n < 100) (hmod : n % 12 = 1) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = n*(n-1)^2/24) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 4) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → n*(n-1)^2/24 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hl⟩ := covering_number_one_mod_twelve_below_100_on hv hn h100 hmod
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hl C ⟨hu,hc⟩⟩
end CoveringDesigns.AuditQuadrupleAssembly
#guard_standard_axioms CoveringDesigns.AuditQuadrupleAssembly.finite_range_explicit
#print axioms CoveringDesigns.AuditQuadrupleAssembly.finite_range_explicit
