import CoveringDesigns.C19_9_3
import CoveringDesigns.C19_9_3.TwoSingleExclusion
import CoveringDesigns.C19_9_3.FourSingleExclusion

open Finset
open scoped BigOperators
universe u_1 u_2 u_3 u_4
set_option linter.unusedVariables false

-- Explicit contracts and transitive foundational-axiom checks.
-- Bookkeeping in C19_9_3.Internal is reached through the final theorem.

#print CoveringDesigns.Family
#print CoveringDesigns.IsCover
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.Multicover.IsCover
#print CoveringDesigns.C19_9_3.AffineConfiguration
#print CoveringDesigns.C19_9_3.WeakColumnForm
#print CoveringDesigns.C19_9_3.WeakCompletion
#print CoveringDesigns.knownBlocks17_19_9_3
#print CoveringDesigns.knownCover17_19_9_3
#print CoveringDesigns.knownCover17_19_9_3_on

#check (@CoveringDesigns.C19_9_3.actual_weak_completion :
  ∀ {V : Type u_1} {I : Type u_2} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    {B : I → Finset V}, Fintype.card V = 19 → CoveringDesigns.Multicover.IsCover B 9 3 1 →
    Fintype.card I = 16 → Nonempty (CoveringDesigns.C19_9_3.WeakCompletion
      {x : V // x ∉ CoveringDesigns.C19_9_3.minimumPoints B}))
#guard_standard_axioms CoveringDesigns.C19_9_3.actual_weak_completion
#print axioms CoveringDesigns.C19_9_3.actual_weak_completion

#check (@CoveringDesigns.C19_9_3.weak_completion_impossible :
  ∀ {X : Type u_1} [Fintype X] [DecidableEq X],
    CoveringDesigns.C19_9_3.WeakCompletion X → Fintype.card X = 11 → False)
#guard_standard_axioms CoveringDesigns.C19_9_3.weak_completion_impossible
#print axioms CoveringDesigns.C19_9_3.weak_completion_impossible

#check (@CoveringDesigns.C19_9_3.minimum_root_fano : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 →
        ∀ (x : V),
          CoveringDesigns.indexedDegree B x = 7 →
            ∃ (g : Fin 7 ↪ I) (p : Fin 7 ↪ V),
              CoveringDesigns.SevenBlock.pointSupport B x = Finset.map g Finset.univ ∧
                Finset.map p Finset.univ = (CoveringDesigns.C19_9_3.minimumPoints B).erase x ∧
                  ∀ (l i : Fin 7), p l ∈ B (g i) ↔ i ∈ CoveringDesigns.SevenBlock.line l)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_root_fano
#print axioms CoveringDesigns.C19_9_3.minimum_root_fano

#check (@CoveringDesigns.C19_9_3.minimum_trace_four : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 →
        ∀ (i : I),
          ∀ x ∈ CoveringDesigns.C19_9_3.minimumPoints B,
            x ∈ B i → (B i ∩ CoveringDesigns.C19_9_3.minimumPoints B).card = 4)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_trace_four
#print axioms CoveringDesigns.C19_9_3.minimum_trace_four

#check (@CoveringDesigns.C19_9_3.minimum_subset_multiplicity : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 →
        ∀ T ⊆ CoveringDesigns.C19_9_3.minimumPoints B, T.card = 3 → CoveringDesigns.indexedSubsetDegree B T = 1)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_subset_multiplicity
#print axioms CoveringDesigns.C19_9_3.minimum_subset_multiplicity

#check (@CoveringDesigns.C19_9_3.minimum_traces_intersection : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 →
        ∀ (i j : I),
          i ≠ j →
            (B i ∩ CoveringDesigns.C19_9_3.minimumPoints B ∩ (B j ∩ CoveringDesigns.C19_9_3.minimumPoints B)).card ≤ 2)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_traces_intersection
#print axioms CoveringDesigns.C19_9_3.minimum_traces_intersection

#check (@CoveringDesigns.C19_9_3.actual_affine_configuration : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 → Nonempty (CoveringDesigns.C19_9_3.AffineConfiguration B))
#guard_standard_axioms CoveringDesigns.C19_9_3.actual_affine_configuration
#print axioms CoveringDesigns.C19_9_3.actual_affine_configuration

#check (@CoveringDesigns.C19_9_3.actual_column_forms : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 →
        ∀ (F : CoveringDesigns.C19_9_3.AffineConfiguration B),
          ∀ x ∉ CoveringDesigns.C19_9_3.minimumPoints B,
            ((F.emptyColumn x).card = 2 ∧
                ∃ (l : Fin 7),
                  F.planeColumn x = CoveringDesigns.C19_9_3.completeDirections (CoveringDesigns.SevenBlock.line l)) ∨
              ((F.emptyColumn x).card = 1 ∧
                  ∃ (l : Fin 7) (n : Fin 7) (b : Bool),
                    n ∉ CoveringDesigns.SevenBlock.line l ∧
                      F.planeColumn x =
                        Insert.insert (n, b)
                          (CoveringDesigns.C19_9_3.completeDirections (CoveringDesigns.SevenBlock.line l))) ∨
                (F.emptyColumn x).card = 0 ∧
                  ∃ (D : Finset (Fin 7)),
                    D.card = 4 ∧
                      (∃ (l : Fin 7), CoveringDesigns.SevenBlock.line l ⊆ D) ∧
                        F.planeColumn x = CoveringDesigns.C19_9_3.completeDirections D)
#guard_standard_axioms CoveringDesigns.C19_9_3.actual_column_forms
#print axioms CoveringDesigns.C19_9_3.actual_column_forms

#check (@CoveringDesigns.C19_9_3.affine_nonminimum_row : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 →
        ∀ (F : CoveringDesigns.C19_9_3.AffineConfiguration B) (p : CoveringDesigns.C19_9_3.PlanePosition),
          (B (F.planes p) \ CoveringDesigns.C19_9_3.minimumPoints B).card = 5)
#guard_standard_axioms CoveringDesigns.C19_9_3.affine_nonminimum_row
#print axioms CoveringDesigns.C19_9_3.affine_nonminimum_row

#check (@CoveringDesigns.C19_9_3.empty_nonminimum_row : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  CoveringDesigns.Multicover.Uniform B 9 →
    ∀ (F : CoveringDesigns.C19_9_3.AffineConfiguration B) (b : Bool),
      (B (F.empty b) \ CoveringDesigns.C19_9_3.minimumPoints B).card = 9)
#guard_standard_axioms CoveringDesigns.C19_9_3.empty_nonminimum_row
#print axioms CoveringDesigns.C19_9_3.empty_nonminimum_row

#check (@CoveringDesigns.C19_9_3.affine_plane_card : ∀ (p : CoveringDesigns.C19_9_3.PlanePosition),
  (CoveringDesigns.C19_9_3.affinePlane p).card = 4)
#guard_standard_axioms CoveringDesigns.C19_9_3.affine_plane_card
#print axioms CoveringDesigns.C19_9_3.affine_plane_card

#check (@CoveringDesigns.C19_9_3.affine_point_degree : ∀ (x : Fin 8), (CoveringDesigns.C19_9_3.affinePointSupport x).card = 7)
#guard_standard_axioms CoveringDesigns.C19_9_3.affine_point_degree
#print axioms CoveringDesigns.C19_9_3.affine_point_degree

#check (@CoveringDesigns.C19_9_3.affine_pair_degree : ∀ (x y : Fin 8),
  x ≠ y → (CoveringDesigns.C19_9_3.affinePointSupport x ∩ CoveringDesigns.C19_9_3.affinePointSupport y).card = 3)
#guard_standard_axioms CoveringDesigns.C19_9_3.affine_pair_degree
#print axioms CoveringDesigns.C19_9_3.affine_pair_degree

#check (@CoveringDesigns.C19_9_3.affine_triple_degree : ∀ (x y z : Fin 8),
  x ≠ y →
    x ≠ z →
      y ≠ z →
        (CoveringDesigns.C19_9_3.affinePointSupport x ∩ CoveringDesigns.C19_9_3.affinePointSupport y ∩
              CoveringDesigns.C19_9_3.affinePointSupport z).card =
          1)
#guard_standard_axioms CoveringDesigns.C19_9_3.affine_triple_degree
#print axioms CoveringDesigns.C19_9_3.affine_triple_degree

#check (@CoveringDesigns.C19_9_3.affine_root_line : ∀ (x y : Fin 8),
  x ≠ y →
    ∃ (l : Fin 7),
      (Finset.univ.filter fun n : Fin 7 => CoveringDesigns.C19_9_3.orientation n x = CoveringDesigns.C19_9_3.orientation n y) =
        CoveringDesigns.SevenBlock.line l)
#guard_standard_axioms CoveringDesigns.C19_9_3.affine_root_line
#print axioms CoveringDesigns.C19_9_3.affine_root_line

#check (@CoveringDesigns.C19_9_3.affine_root_all_lines : ∀ (x : Fin 8) (l : Fin 7),
  ∃ (y : Fin 8),
    x ≠ y ∧
      (Finset.univ.filter fun n : Fin 7 => CoveringDesigns.C19_9_3.orientation n x = CoveringDesigns.C19_9_3.orientation n y) =
        CoveringDesigns.SevenBlock.line l)
#guard_standard_axioms CoveringDesigns.C19_9_3.affine_root_all_lines
#print axioms CoveringDesigns.C19_9_3.affine_root_all_lines

#check (@CoveringDesigns.C19_9_3.column_character_identity : ∀ (U : Finset CoveringDesigns.C19_9_3.PlanePosition) (x : Fin 8),
  2 * ↑(CoveringDesigns.C19_9_3.columnValue U x) - ↑U.card =
    ∑ n : Fin 7, CoveringDesigns.C19_9_3.columnCoefficient U n * CoveringDesigns.C19_9_3.character n x)
#guard_standard_axioms CoveringDesigns.C19_9_3.column_character_identity
#print axioms CoveringDesigns.C19_9_3.column_character_identity

#check (@CoveringDesigns.C19_9_3.column_incidence_sum : ∀ (U : Finset CoveringDesigns.C19_9_3.PlanePosition),
  ∑ x : Fin 8, CoveringDesigns.C19_9_3.columnValue U x = 4 * U.card)
#guard_standard_axioms CoveringDesigns.C19_9_3.column_incidence_sum
#print axioms CoveringDesigns.C19_9_3.column_incidence_sum

#check (@CoveringDesigns.C19_9_3.column_forms : ∀ (U : Finset CoveringDesigns.C19_9_3.PlanePosition),
  ∀ j ≤ 2,
    U.card + j = 8 →
      (∀ (x : Fin 8), 3 ≤ CoveringDesigns.C19_9_3.columnValue U x ∧ CoveringDesigns.C19_9_3.columnValue U x ≤ 4) →
        (∀ (x : Fin 8),
            CoveringDesigns.C19_9_3.columnValue U x = 3 →
              ∃ (l : Fin 7), CoveringDesigns.C19_9_3.columnDirections U x = CoveringDesigns.SevenBlock.line l) →
          (∀ (x : Fin 8),
              CoveringDesigns.C19_9_3.columnValue U x = 4 →
                ∀ (l : Fin 7),
                  (CoveringDesigns.C19_9_3.columnDirections U x ∩ CoveringDesigns.SevenBlock.line l).Nonempty) →
            (j = 2 ∧
                ∃ (l : Fin 7), U = CoveringDesigns.C19_9_3.completeDirections (CoveringDesigns.SevenBlock.line l)) ∨
              (j = 1 ∧
                  ∃ (l : Fin 7) (n : Fin 7) (b : Bool),
                    n ∉ CoveringDesigns.SevenBlock.line l ∧
                      U =
                        Insert.insert (n, b)
                          (CoveringDesigns.C19_9_3.completeDirections (CoveringDesigns.SevenBlock.line l))) ∨
                j = 0 ∧
                  ∃ (D : Finset (Fin 7)),
                    D.card = 4 ∧
                      (∃ (l : Fin 7), CoveringDesigns.SevenBlock.line l ⊆ D) ∧
                        U = CoveringDesigns.C19_9_3.completeDirections D)
#guard_standard_axioms CoveringDesigns.C19_9_3.column_forms
#print axioms CoveringDesigns.C19_9_3.column_forms

#check (@CoveringDesigns.covering_number_19_9_3_on : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V],
  Fintype.card V = 19 →
    (∃ (C : CoveringDesigns.Family V), CoveringDesigns.IsCover C 9 3 ∧ Finset.card C = 17) ∧
      ∀ (C : CoveringDesigns.Family V), CoveringDesigns.IsCover C 9 3 → 17 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.covering_number_19_9_3_on
#print axioms CoveringDesigns.covering_number_19_9_3_on

#check (@CoveringDesigns.covering_number_19_9_3 : (∃ (C : CoveringDesigns.Family (Fin 19)),
    CoveringDesigns.IsCover C 9 3 ∧ Finset.card C = 17) ∧
  ∀ (C : CoveringDesigns.Family (Fin 19)), CoveringDesigns.IsCover C 9 3 → 17 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.covering_number_19_9_3
#print axioms CoveringDesigns.covering_number_19_9_3

#check (@CoveringDesigns.covering_number_19_9_3_expanded_on : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V],
  Fintype.card V = 19 →
    (∃ (C : Finset (Finset V)), C.card = 17 ∧ (∀ B ∈ C, B.card = 9) ∧ ∀ (T : Finset V), T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧
      ∀ (C : Finset (Finset V)), (∀ B ∈ C, B.card = 9) → (∀ (T : Finset V), T.card = 3 → ∃ B ∈ C, T ⊆ B) → 17 ≤ C.card)
#guard_standard_axioms CoveringDesigns.covering_number_19_9_3_expanded_on
#print axioms CoveringDesigns.covering_number_19_9_3_expanded_on

#check (@CoveringDesigns.C19_9_3.minimum_exceptional_trace : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ (x p q : V),
        CoveringDesigns.indexedDegree B x = 7 →
          p ≠ x →
            q ≠ x →
              p ≠ q →
                CoveringDesigns.indexedSubsetDegree B {x, p} = 4 →
                  CoveringDesigns.indexedSubsetDegree B {x, q} = 4 →
                    CoveringDesigns.indexedSubsetDegree B {x, p, q} = 2 ∨
                      CoveringDesigns.indexedSubsetDegree B {x, p, q} = 4)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_exceptional_trace
#print axioms CoveringDesigns.C19_9_3.minimum_exceptional_trace

#check (@CoveringDesigns.C19_9_3.minimum_contained_trace_companion : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [inst_3 : DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ (r x z : V),
        CoveringDesigns.indexedDegree B r = 7 →
          r ≠ x →
            r ≠ z →
              CoveringDesigns.indexedSubsetDegree B {r, x} = 3 →
                CoveringDesigns.indexedSubsetDegree B {r, z} = 4 →
                  CoveringDesigns.indexedSubsetDegree B {r, x, z} = 3 →
                    ∃ (w : V),
                      w ≠ r ∧
                        w ≠ x ∧
                          w ≠ z ∧
                            (CoveringDesigns.indexedSubsetDegree B {r, w} = 3 ∧
                                CoveringDesigns.SevenBlock.pointSupport B r ∩
                                    CoveringDesigns.SevenBlock.pointSupport B w =
                                  CoveringDesigns.SevenBlock.pointSupport B r ∩
                                    CoveringDesigns.SevenBlock.pointSupport B x ∨
                              CoveringDesigns.indexedSubsetDegree B {r, w} = 4 ∧
                                CoveringDesigns.SevenBlock.pointSupport B r ∩
                                    CoveringDesigns.SevenBlock.pointSupport B w =
                                  CoveringDesigns.SevenBlock.pointSupport B r ∩
                                    CoveringDesigns.SevenBlock.pointSupport B z))
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_contained_trace_companion
#print axioms CoveringDesigns.C19_9_3.minimum_contained_trace_companion

#check (@CoveringDesigns.C19_9_3.no_minimum_triple_three : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 →
        ∀ (x y z : V),
          x ≠ y →
            x ≠ z →
              y ≠ z →
                CoveringDesigns.indexedDegree B x = 7 →
                  CoveringDesigns.indexedDegree B y = 7 →
                    CoveringDesigns.indexedDegree B z = 7 → CoveringDesigns.indexedSubsetDegree B {x, y, z} ≠ 3)
#guard_standard_axioms CoveringDesigns.C19_9_3.no_minimum_triple_three
#print axioms CoveringDesigns.C19_9_3.no_minimum_triple_three

#check (@CoveringDesigns.C19_9_3.sixteen_le_card : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] {B : I → Finset V},
  Fintype.card V = 19 → CoveringDesigns.Multicover.IsCover B 9 3 1 → 16 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C19_9_3.sixteen_le_card
#print axioms CoveringDesigns.C19_9_3.sixteen_le_card

#check (@CoveringDesigns.C19_9_3.ordinary_sixteen_le_card : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V]
  {C : CoveringDesigns.Family V}, Fintype.card V = 19 → CoveringDesigns.IsCover C 9 3 → 16 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C19_9_3.ordinary_sixteen_le_card
#print axioms CoveringDesigns.C19_9_3.ordinary_sixteen_le_card

#check (@CoveringDesigns.C19_9_3.no_fifteen : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] {B : I → Finset V},
  Fintype.card V = 19 → CoveringDesigns.Multicover.IsCover B 9 3 1 → Fintype.card I = 15 → False)
#guard_standard_axioms CoveringDesigns.C19_9_3.no_fifteen
#print axioms CoveringDesigns.C19_9_3.no_fifteen

#check (@CoveringDesigns.C19_9_3.sixteen_blocks_injective : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] {B : I → Finset V},
  Fintype.card V = 19 → CoveringDesigns.Multicover.IsCover B 9 3 1 → Fintype.card I = 16 → Function.Injective B)
#guard_standard_axioms CoveringDesigns.C19_9_3.sixteen_blocks_injective
#print axioms CoveringDesigns.C19_9_3.sixteen_blocks_injective

#check (@CoveringDesigns.C19_9_3.pair_floor : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ {T : Finset V}, T.card = 2 → 3 ≤ CoveringDesigns.indexedSubsetDegree B T)
#guard_standard_axioms CoveringDesigns.C19_9_3.pair_floor
#print axioms CoveringDesigns.C19_9_3.pair_floor

#check (@CoveringDesigns.C19_9_3.degree_floor : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] {B : I → Finset V},
  Fintype.card V = 19 → CoveringDesigns.Multicover.IsCover B 9 3 1 → ∀ (x : V), 7 ≤ CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.C19_9_3.degree_floor
#print axioms CoveringDesigns.C19_9_3.degree_floor

#check (@CoveringDesigns.C19_9_3.mem_minimumPoints : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] (B : I → Finset V) (x : V),
  x ∈ CoveringDesigns.C19_9_3.minimumPoints B ↔ CoveringDesigns.indexedDegree B x = 7)
#guard_standard_axioms CoveringDesigns.C19_9_3.mem_minimumPoints
#print axioms CoveringDesigns.C19_9_3.mem_minimumPoints

#check (@CoveringDesigns.C19_9_3.minimum_count_bound : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      152 ≤ 9 * Fintype.card I + (CoveringDesigns.C19_9_3.minimumPoints B).card)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_count_bound
#print axioms CoveringDesigns.C19_9_3.minimum_count_bound

#check (@CoveringDesigns.C19_9_3.eight_minimum_points : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 → 8 ≤ (CoveringDesigns.C19_9_3.minimumPoints B).card)
#guard_standard_axioms CoveringDesigns.C19_9_3.eight_minimum_points
#print axioms CoveringDesigns.C19_9_3.eight_minimum_points

#check (@CoveringDesigns.C19_9_3.degree_excess : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∑ x : V, (CoveringDesigns.indexedDegree B x - 7) + 133 = 9 * Fintype.card I)
#guard_standard_axioms CoveringDesigns.C19_9_3.degree_excess
#print axioms CoveringDesigns.C19_9_3.degree_excess

#check (@CoveringDesigns.C19_9_3.pair_sum : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] {B : I → Finset V},
  CoveringDesigns.Multicover.Uniform B 9 →
    ∀ (x : V),
      ∑ y ∈ Finset.univ.erase x, CoveringDesigns.indexedSubsetDegree B {x, y} = 8 * CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.C19_9_3.pair_sum
#print axioms CoveringDesigns.C19_9_3.pair_sum

#check (@CoveringDesigns.C19_9_3.minimum_incidence_coordinates : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [inst_3 : DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ (x : V),
        CoveringDesigns.indexedDegree B x = 7 →
          ∃ (tag : Bool) (e : { y : V // y ∉ ({x} : Finset V) } ≃ CoveringDesigns.SevenBlock.TemplatePoint 2 tag) (g : Fin 7 ↪ I),
            CoveringDesigns.SevenBlock.pointSupport B x = Finset.map g Finset.univ ∧
              ∀ (y : { y : V // y ∉ ({x} : Finset V) }),
                CoveringDesigns.SevenBlock.pointSupport B x ∩ CoveringDesigns.SevenBlock.pointSupport B ↑y =
                  Finset.map g (CoveringDesigns.SevenBlock.templateSupport 2 tag (e y)))
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_incidence_coordinates
#print axioms CoveringDesigns.C19_9_3.minimum_incidence_coordinates

#check (@CoveringDesigns.C19_9_3.minimum_ordinary_trace : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ (x y z : V),
        CoveringDesigns.indexedDegree B x = 7 →
          x ≠ y →
            x ≠ z →
              CoveringDesigns.indexedSubsetDegree B {x, y} = 3 →
                CoveringDesigns.indexedSubsetDegree B {x, z} = 3 →
                  CoveringDesigns.indexedSubsetDegree B {x, y, z} = 1 ∨
                    CoveringDesigns.indexedSubsetDegree B {x, y, z} = 3)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_ordinary_trace
#print axioms CoveringDesigns.C19_9_3.minimum_ordinary_trace

#check (@CoveringDesigns.C19_9_3.minimum_two_trace_exceptional : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ (x y z : V),
        CoveringDesigns.indexedDegree B x = 7 →
          x ≠ y →
            x ≠ z →
              CoveringDesigns.indexedSubsetDegree B {x, y} = 3 →
                CoveringDesigns.indexedSubsetDegree B {x, y, z} = 2 → CoveringDesigns.indexedSubsetDegree B {x, z} = 4)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_two_trace_exceptional
#print axioms CoveringDesigns.C19_9_3.minimum_two_trace_exceptional

#check (@CoveringDesigns.C19_9_3.minimum_two_trace_agreement : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ (x y z : V),
        CoveringDesigns.indexedDegree B x = 7 →
          CoveringDesigns.indexedDegree B y = 7 →
            x ≠ y →
              x ≠ z →
                y ≠ z →
                  CoveringDesigns.indexedSubsetDegree B {x, y} = 3 →
                    CoveringDesigns.indexedSubsetDegree B {x, y, z} = 2 →
                      CoveringDesigns.indexedSubsetDegree B {x, z} = 4 ∧
                        CoveringDesigns.indexedSubsetDegree B {y, z} = 4)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_two_trace_agreement
#print axioms CoveringDesigns.C19_9_3.minimum_two_trace_agreement

#check (@CoveringDesigns.C19_9_3.no_three_minimum_exceptions : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ (x p q r : V),
        CoveringDesigns.indexedDegree B x = 7 →
          p ≠ x →
            q ≠ x →
              r ≠ x →
                p ≠ q →
                  p ≠ r →
                    q ≠ r →
                      CoveringDesigns.indexedSubsetDegree B {x, p} = 4 →
                        CoveringDesigns.indexedSubsetDegree B {x, q} = 4 →
                          CoveringDesigns.indexedSubsetDegree B {x, r} = 4 → False)
#guard_standard_axioms CoveringDesigns.C19_9_3.no_three_minimum_exceptions
#print axioms CoveringDesigns.C19_9_3.no_three_minimum_exceptions

#check (@CoveringDesigns.C19_9_3.minimum_ordinary_pair_profile : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ (x y : V),
        CoveringDesigns.indexedDegree B x = 7 →
          x ≠ y →
            CoveringDesigns.indexedSubsetDegree B {x, y} = 3 →
              (CoveringDesigns.C19_9_3.thirdPoints B x y 3).card = 2 ∧
                  (CoveringDesigns.C19_9_3.thirdPoints B x y 2).card = 0 ∨
                (CoveringDesigns.C19_9_3.thirdPoints B x y 3).card = 1 ∧
                  (CoveringDesigns.C19_9_3.thirdPoints B x y 2).card = 2)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_ordinary_pair_profile
#print axioms CoveringDesigns.C19_9_3.minimum_ordinary_pair_profile

#check (@CoveringDesigns.C19_9_3.no_sixteen : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] {B : I → Finset V},
  Fintype.card V = 19 → CoveringDesigns.Multicover.IsCover B 9 3 1 → Fintype.card I = 16 → False)
#guard_standard_axioms CoveringDesigns.C19_9_3.no_sixteen
#print axioms CoveringDesigns.C19_9_3.no_sixteen

#check (@CoveringDesigns.C19_9_3.seventeen_le_card : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] {B : I → Finset V},
  Fintype.card V = 19 → CoveringDesigns.Multicover.IsCover B 9 3 1 → 17 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C19_9_3.seventeen_le_card
#print axioms CoveringDesigns.C19_9_3.seventeen_le_card

#check (@CoveringDesigns.C19_9_3.seventeen_le_card_expanded : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [DecidableEq V]
  [inst_2 : Fintype I] (B : I → Finset V),
  Fintype.card V = 19 →
    (∀ (i : I), (B i).card = 9) → (∀ (T : Finset V), T.card = 3 → ∃ (i : I), T ⊆ B i) → 17 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C19_9_3.seventeen_le_card_expanded
#print axioms CoveringDesigns.C19_9_3.seventeen_le_card_expanded

#check (@CoveringDesigns.lower_bound_19_9_3_on : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V],
  Fintype.card V = 19 → ∀ {C : CoveringDesigns.Family V}, CoveringDesigns.IsCover C 9 3 → 17 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.lower_bound_19_9_3_on
#print axioms CoveringDesigns.lower_bound_19_9_3_on

#check (@CoveringDesigns.lower_bound_19_9_3 : ∀ {C : CoveringDesigns.Family (Fin 19)},
  CoveringDesigns.IsCover C 9 3 → 17 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.lower_bound_19_9_3
#print axioms CoveringDesigns.lower_bound_19_9_3

#check (@CoveringDesigns.lower_bound_19_9_3_expanded : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V],
  Fintype.card V = 19 →
    ∀ (C : Finset (Finset V)), (∀ B ∈ C, B.card = 9) → (∀ (T : Finset V), T.card = 3 → ∃ B ∈ C, T ⊆ B) → 17 ≤ C.card)
#guard_standard_axioms CoveringDesigns.lower_bound_19_9_3_expanded
#print axioms CoveringDesigns.lower_bound_19_9_3_expanded

#check (@CoveringDesigns.C19_9_3.minimum_link_classification : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ (x : V),
        CoveringDesigns.indexedDegree B x = 7 →
          ∃ (tag : Bool),
            CoveringDesigns.SevenBlock.IndexedIsomorphic (CoveringDesigns.Multicover.subsetLink B {x})
              (CoveringDesigns.SevenBlock.templateBlock 2 tag))
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_link_classification
#print axioms CoveringDesigns.C19_9_3.minimum_link_classification

#check (@CoveringDesigns.C19_9_3.actual_link_degree : ∀ {V : Type u_1} {I : Type u_2} [Fintype V] [inst : DecidableEq V]
  [inst_1 : Fintype I] [DecidableEq I] (B : I → Finset V) (x : V) (y : { y : V // y ∉ ({x} : Finset V) }),
  CoveringDesigns.indexedDegree (CoveringDesigns.Multicover.subsetLink B {x}) y =
    CoveringDesigns.indexedSubsetDegree B {x, ↑y})
#guard_standard_axioms CoveringDesigns.C19_9_3.actual_link_degree
#print axioms CoveringDesigns.C19_9_3.actual_link_degree

#check (@CoveringDesigns.C19_9_3.actual_link_codegree : ∀ {V : Type u_1} {I : Type u_2} [Fintype V] [inst : DecidableEq V]
  [inst_1 : Fintype I] [DecidableEq I] (B : I → Finset V) (x : V) (y z : { y : V // y ∉ ({x} : Finset V) }),
  CoveringDesigns.indexedSubsetDegree (CoveringDesigns.Multicover.subsetLink B {x}) {y, z} =
    CoveringDesigns.indexedSubsetDegree B {x, ↑y, ↑z})
#guard_standard_axioms CoveringDesigns.C19_9_3.actual_link_codegree
#print axioms CoveringDesigns.C19_9_3.actual_link_codegree

#check (@CoveringDesigns.C19_9_3.minimum_profile : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ (x : V),
        CoveringDesigns.indexedDegree B x = 7 →
          ∃ (p : V) (q : V),
            p ≠ x ∧
              q ≠ x ∧
                p ≠ q ∧
                  CoveringDesigns.indexedSubsetDegree B {x, p} = 4 ∧
                    CoveringDesigns.indexedSubsetDegree B {x, q} = 4 ∧
                      (∀ (y : V), y ≠ x → y ≠ p → y ≠ q → CoveringDesigns.indexedSubsetDegree B {x, y} = 3) ∧
                        (CoveringDesigns.indexedSubsetDegree B {x, p, q} = 2 ∨
                          CoveringDesigns.indexedSubsetDegree B {x, p, q} = 4))
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_profile
#print axioms CoveringDesigns.C19_9_3.minimum_profile

#check (@CoveringDesigns.C19_9_3.minimum_pair_le_four : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      ∀ (x y : V), CoveringDesigns.indexedDegree B x = 7 → x ≠ y → CoveringDesigns.indexedSubsetDegree B {x, y} ≤ 4)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_pair_le_four
#print axioms CoveringDesigns.C19_9_3.minimum_pair_le_four

#check (@CoveringDesigns.C19_9_3.minimum_pair_ordinary : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 →
        ∀ (x y : V),
          CoveringDesigns.indexedDegree B x = 7 →
            CoveringDesigns.indexedDegree B y = 7 → x ≠ y → CoveringDesigns.indexedSubsetDegree B {x, y} = 3)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_pair_ordinary
#print axioms CoveringDesigns.C19_9_3.minimum_pair_ordinary

#check (@CoveringDesigns.C19_9_3.minimum_points_card : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 → (CoveringDesigns.C19_9_3.minimumPoints B).card = 8)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_points_card
#print axioms CoveringDesigns.C19_9_3.minimum_points_card

#check (@CoveringDesigns.C19_9_3.nonminimum_degree : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 → ∀ w ∉ CoveringDesigns.C19_9_3.minimumPoints B, CoveringDesigns.indexedDegree B w = 8)
#guard_standard_axioms CoveringDesigns.C19_9_3.nonminimum_degree
#print axioms CoveringDesigns.C19_9_3.nonminimum_degree

#check (@CoveringDesigns.C19_9_3.minimum_triple_one : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 →
        ∀ (x y z : V),
          x ≠ y →
            x ≠ z →
              y ≠ z →
                CoveringDesigns.indexedDegree B x = 7 →
                  CoveringDesigns.indexedDegree B y = 7 →
                    CoveringDesigns.indexedDegree B z = 7 → CoveringDesigns.indexedSubsetDegree B {x, y, z} = 1)
#guard_standard_axioms CoveringDesigns.C19_9_3.minimum_triple_one
#print axioms CoveringDesigns.C19_9_3.minimum_triple_one

#check (@CoveringDesigns.C19_9_3.character_sign : ∀ (n : Fin 7) (x : Fin 8),
  CoveringDesigns.C19_9_3.character n x = 1 ∨ CoveringDesigns.C19_9_3.character n x = -1)
#guard_standard_axioms CoveringDesigns.C19_9_3.character_sign
#print axioms CoveringDesigns.C19_9_3.character_sign

#check (@CoveringDesigns.C19_9_3.character_balanced : ∀ (n : Fin 7), ∑ x : Fin 8, CoveringDesigns.C19_9_3.character n x = 0)
#guard_standard_axioms CoveringDesigns.C19_9_3.character_balanced
#print axioms CoveringDesigns.C19_9_3.character_balanced

#check (@CoveringDesigns.C19_9_3.character_orthogonal : ∀ (n m : Fin 7),
  ∑ x : Fin 8, CoveringDesigns.C19_9_3.character n x * CoveringDesigns.C19_9_3.character m x = if n = m then 8 else 0)
#guard_standard_axioms CoveringDesigns.C19_9_3.character_orthogonal
#print axioms CoveringDesigns.C19_9_3.character_orthogonal

#check (@CoveringDesigns.C19_9_3.coefficient_extraction : ∀ (c : Fin 7 → ℤ) (n : Fin 7),
  ∑ x : Fin 8, (∑ m : Fin 7, c m * CoveringDesigns.C19_9_3.character m x) * CoveringDesigns.C19_9_3.character n x =
    8 * c n)
#guard_standard_axioms CoveringDesigns.C19_9_3.coefficient_extraction
#print axioms CoveringDesigns.C19_9_3.coefficient_extraction

#check (@CoveringDesigns.C19_9_3.character_parseval : ∀ (c : Fin 7 → ℤ),
  ∑ x : Fin 8, (∑ n : Fin 7, c n * CoveringDesigns.C19_9_3.character n x) ^ 2 = 8 * ∑ n : Fin 7, c n ^ 2)
#guard_standard_axioms CoveringDesigns.C19_9_3.character_parseval
#print axioms CoveringDesigns.C19_9_3.character_parseval

#check (@CoveringDesigns.C19_9_3.coefficients_zero : ∀ (c : Fin 7 → ℤ),
  (∀ (x : Fin 8), ∑ n : Fin 7, c n * CoveringDesigns.C19_9_3.character n x = 0) → ∀ (n : Fin 7), c n = 0)
#guard_standard_axioms CoveringDesigns.C19_9_3.coefficients_zero
#print axioms CoveringDesigns.C19_9_3.coefficients_zero

#check (@CoveringDesigns.C19_9_3.character_unit_square : ∀ (c : Fin 7 → ℤ),
  (∀ (x : Fin 8), (∑ n : Fin 7, c n * CoveringDesigns.C19_9_3.character n x) ^ 2 = 1) →
    ∃ (n : Fin 7), (c n = 1 ∨ c n = -1) ∧ ∀ (m : Fin 7), m ≠ n → c m = 0)
#guard_standard_axioms CoveringDesigns.C19_9_3.character_unit_square
#print axioms CoveringDesigns.C19_9_3.character_unit_square

#check (@CoveringDesigns.C19_9_3.three_support_count : ∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I]
  (R₀ R₁ R₂ T S : Finset I),
  R₀ ∩ R₁ = T →
    R₀ ∩ R₂ = T →
      R₁ ∩ R₂ = T →
        (S ∩ R₀).card + (S ∩ R₁).card + (S ∩ R₂).card + (S ∩ (Finset.univ \ (R₀ ∪ R₁ ∪ R₂))).card =
          S.card + 2 * (S ∩ T).card)
#guard_standard_axioms CoveringDesigns.C19_9_3.three_support_count
#print axioms CoveringDesigns.C19_9_3.three_support_count

#check (@CoveringDesigns.C19_9_3.pointSupport_triple : ∀ {V : Type u_1} {I : Type u_2} [Fintype V] [inst : DecidableEq V]
  [inst_1 : Fintype I] [inst_2 : DecidableEq I] (B : I → Finset V) (x y z : V),
  (CoveringDesigns.SevenBlock.pointSupport B x ∩ CoveringDesigns.SevenBlock.pointSupport B y ∩
        CoveringDesigns.SevenBlock.pointSupport B z).card =
    CoveringDesigns.indexedSubsetDegree B {x, y, z})
#guard_standard_axioms CoveringDesigns.C19_9_3.pointSupport_triple
#print axioms CoveringDesigns.C19_9_3.pointSupport_triple

#check (@CoveringDesigns.C19_9_3.three_ordinary_roots_no_fourth : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [inst_3 : DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 →
        ∀ (x y z : V),
          x ≠ y →
            x ≠ z →
              y ≠ z →
                CoveringDesigns.indexedDegree B x = 7 →
                  CoveringDesigns.indexedDegree B y = 7 →
                    CoveringDesigns.indexedDegree B z = 7 →
                      CoveringDesigns.indexedSubsetDegree B {x, y} = 3 →
                        CoveringDesigns.indexedSubsetDegree B {x, z} = 3 →
                          CoveringDesigns.indexedSubsetDegree B {y, z} = 3 →
                            CoveringDesigns.indexedSubsetDegree B {x, y, z} = 3 →
                              ∀ (w : V),
                                w ≠ x →
                                  w ≠ y →
                                    w ≠ z →
                                      ¬CoveringDesigns.SevenBlock.pointSupport B x ∩
                                              CoveringDesigns.SevenBlock.pointSupport B y ∩
                                            CoveringDesigns.SevenBlock.pointSupport B z ⊆
                                          CoveringDesigns.SevenBlock.pointSupport B w)
#guard_standard_axioms CoveringDesigns.C19_9_3.three_ordinary_roots_no_fourth
#print axioms CoveringDesigns.C19_9_3.three_ordinary_roots_no_fourth

#check (@CoveringDesigns.C19_9_3.no_three_ordinary_minima : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {B : I → Finset V},
  Fintype.card V = 19 →
    CoveringDesigns.Multicover.IsCover B 9 3 1 →
      Fintype.card I = 16 →
        ∀ (x y z : V),
          x ≠ y →
            x ≠ z →
              y ≠ z →
                CoveringDesigns.indexedDegree B x = 7 →
                  CoveringDesigns.indexedDegree B y = 7 →
                    CoveringDesigns.indexedDegree B z = 7 →
                      CoveringDesigns.indexedSubsetDegree B {x, y} = 3 →
                        CoveringDesigns.indexedSubsetDegree B {x, z} = 3 →
                          CoveringDesigns.indexedSubsetDegree B {y, z} = 3 →
                            CoveringDesigns.indexedSubsetDegree B {x, y, z} ≠ 3)
#guard_standard_axioms CoveringDesigns.C19_9_3.no_three_ordinary_minima
#print axioms CoveringDesigns.C19_9_3.no_three_ordinary_minima

#check (@CoveringDesigns.C19_9_3.literal_link_trace : ∀ {V : Type u_1} {I : Type u_2} [Fintype V] [inst : DecidableEq V]
  [inst_1 : Fintype I] [inst_2 : DecidableEq I] (B : I → Finset V) (x : V) (y : { y : V // y ∉ ({x} : Finset V) }),
  Finset.map (Function.Embedding.subtype fun (i : I) => {x} ⊆ B i)
      (CoveringDesigns.SevenBlock.pointSupport (CoveringDesigns.Multicover.subsetLink B {x}) y) =
    CoveringDesigns.SevenBlock.pointSupport B x ∩ CoveringDesigns.SevenBlock.pointSupport B ↑y)
#guard_standard_axioms CoveringDesigns.C19_9_3.literal_link_trace
#print axioms CoveringDesigns.C19_9_3.literal_link_trace

#check (@CoveringDesigns.C19_9_3.literal_link_pair_trace : ∀ {V : Type u_1} {I : Type u_2} [Fintype V] [inst : DecidableEq V]
  [inst_1 : Fintype I] [inst_2 : DecidableEq I] (B : I → Finset V) (x : V) (y z : { y : V // y ∉ ({x} : Finset V) }),
  Finset.map (Function.Embedding.subtype fun (i : I) => {x} ⊆ B i)
      (CoveringDesigns.SevenBlock.pointSupport (CoveringDesigns.Multicover.subsetLink B {x}) y ∩
        CoveringDesigns.SevenBlock.pointSupport (CoveringDesigns.Multicover.subsetLink B {x}) z) =
    CoveringDesigns.SevenBlock.pointSupport B x ∩ CoveringDesigns.SevenBlock.pointSupport B ↑y ∩
      CoveringDesigns.SevenBlock.pointSupport B ↑z)
#guard_standard_axioms CoveringDesigns.C19_9_3.literal_link_pair_trace
#print axioms CoveringDesigns.C19_9_3.literal_link_pair_trace

#check (@CoveringDesigns.C19_9_3.complementary_agreement_identity : ∀ {X : Type u_1} {J : Type u_2} [inst : Fintype X]
  [DecidableEq X] [inst_2 : DecidableEq J] (trace : Fin 3 → X → Finset J) (w : X),
  (∀ (y : X), y ≠ w → (Finset.univ.filter fun d : Fin 3 => trace d y = trace d w).card = 1) →
    ∑ d : Fin 3, ((Finset.univ.filter fun y : X => trace d y = trace d w).card - 1) = Fintype.card X - 1)
#guard_standard_axioms CoveringDesigns.C19_9_3.complementary_agreement_identity
#print axioms CoveringDesigns.C19_9_3.complementary_agreement_identity

#check (@CoveringDesigns.knownBlocks17_19_9_3_distinct : CoveringDesigns.knownBlocks17_19_9_3.Nodup)
#guard_standard_axioms CoveringDesigns.knownBlocks17_19_9_3_distinct
#print axioms CoveringDesigns.knownBlocks17_19_9_3_distinct

#check (@CoveringDesigns.knownBlocks17_19_9_3_length : CoveringDesigns.knownBlocks17_19_9_3.length = 17)
#guard_standard_axioms CoveringDesigns.knownBlocks17_19_9_3_length
#print axioms CoveringDesigns.knownBlocks17_19_9_3_length

#check (@CoveringDesigns.knownCover17_19_9_3_mem : ∀ (B : Finset (Fin 19)),
  B ∈ CoveringDesigns.knownCover17_19_9_3 ↔ B ∈ CoveringDesigns.knownBlocks17_19_9_3)
#guard_standard_axioms CoveringDesigns.knownCover17_19_9_3_mem
#print axioms CoveringDesigns.knownCover17_19_9_3_mem

#check (@CoveringDesigns.triple_count_19_9_3 : (Finset.powersetCard 3 Finset.univ).card = 969)
#guard_standard_axioms CoveringDesigns.triple_count_19_9_3
#print axioms CoveringDesigns.triple_count_19_9_3

#check (@CoveringDesigns.knownCover17_19_9_3_card : Finset.card CoveringDesigns.knownCover17_19_9_3 = 17)
#guard_standard_axioms CoveringDesigns.knownCover17_19_9_3_card
#print axioms CoveringDesigns.knownCover17_19_9_3_card

#check (@CoveringDesigns.knownCover17_19_9_3_uniform : CoveringDesigns.Uniform CoveringDesigns.knownCover17_19_9_3 9)
#guard_standard_axioms CoveringDesigns.knownCover17_19_9_3_uniform
#print axioms CoveringDesigns.knownCover17_19_9_3_uniform

#check (@CoveringDesigns.knownCover17_19_9_3_covers : CoveringDesigns.Covers CoveringDesigns.knownCover17_19_9_3 3)
#guard_standard_axioms CoveringDesigns.knownCover17_19_9_3_covers
#print axioms CoveringDesigns.knownCover17_19_9_3_covers

#check (@CoveringDesigns.knownCover17_19_9_3_isCover : CoveringDesigns.IsCover CoveringDesigns.knownCover17_19_9_3 9 3)
#guard_standard_axioms CoveringDesigns.knownCover17_19_9_3_isCover
#print axioms CoveringDesigns.knownCover17_19_9_3_isCover

#check (@CoveringDesigns.upper_bound_19_9_3 : ∃ (C : CoveringDesigns.Family (Fin 19)),
  CoveringDesigns.IsCover C 9 3 ∧ Finset.card C = 17)
#guard_standard_axioms CoveringDesigns.upper_bound_19_9_3
#print axioms CoveringDesigns.upper_bound_19_9_3

#check (@CoveringDesigns.knownCover17_19_9_3_on_card : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (hv : Fintype.card α = 19), Finset.card (CoveringDesigns.knownCover17_19_9_3_on hv) = 17)
#guard_standard_axioms CoveringDesigns.knownCover17_19_9_3_on_card
#print axioms CoveringDesigns.knownCover17_19_9_3_on_card

#check (@CoveringDesigns.knownCover17_19_9_3_on_isCover : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (hv : Fintype.card α = 19), CoveringDesigns.IsCover (CoveringDesigns.knownCover17_19_9_3_on hv) 9 3)
#guard_standard_axioms CoveringDesigns.knownCover17_19_9_3_on_isCover
#print axioms CoveringDesigns.knownCover17_19_9_3_on_isCover

#check (@CoveringDesigns.upper_bound_19_9_3_on : ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α],
  Fintype.card α = 19 → ∃ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 9 3 ∧ Finset.card C = 17)
#guard_standard_axioms CoveringDesigns.upper_bound_19_9_3_on
#print axioms CoveringDesigns.upper_bound_19_9_3_on

#check (@CoveringDesigns.IndexedPadding.nonempty_occurrences : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] {B : I → Finset V} {k t : ℕ},
  t ≤ Fintype.card V → CoveringDesigns.Multicover.IsCover B k t 1 → Nonempty I)
#guard_standard_axioms CoveringDesigns.IndexedPadding.nonempty_occurrences
#print axioms CoveringDesigns.IndexedPadding.nonempty_occurrences

#check (@CoveringDesigns.IndexedPadding.pad : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] {B : I → Finset V} {k t b : ℕ},
  t ≤ Fintype.card V →
    CoveringDesigns.Multicover.IsCover B k t 1 →
      Fintype.card I ≤ b → ∃ (D : Fin b → Finset V), CoveringDesigns.Multicover.IsCover D k t 1)
#guard_standard_axioms CoveringDesigns.IndexedPadding.pad
#print axioms CoveringDesigns.IndexedPadding.pad

#check (@CoveringDesigns.IndexedPadding.lower_of_fixed_exclusion : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] {B : I → Finset V} {k t b : ℕ},
  t ≤ Fintype.card V →
    CoveringDesigns.Multicover.IsCover B k t 1 →
      (∀ (D : Fin b → Finset V), ¬CoveringDesigns.Multicover.IsCover D k t 1) → b + 1 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.IndexedPadding.lower_of_fixed_exclusion
#print axioms CoveringDesigns.IndexedPadding.lower_of_fixed_exclusion


