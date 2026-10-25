import CoveringDesigns.SevenBlock.Core

open Finset
open scoped BigOperators
universe u_1 u_2 u_3 u_4 u_5 u_6
set_option linter.unusedVariables false

-- Explicit contracts and transitive foundational-axiom checks.
-- Bookkeeping in C19_9_3.Internal is reached through the final theorem.

#print CoveringDesigns.Multicover.IsCover
#print CoveringDesigns.SevenBlock.IndexedIsomorphic
#print CoveringDesigns.SevenBlock.TemplatePoint
#print CoveringDesigns.SevenBlock.weight
#print CoveringDesigns.SevenBlock.line
#print CoveringDesigns.SevenBlock.highSupport
#print CoveringDesigns.SevenBlock.templateSupport
#print CoveringDesigns.SevenBlock.templateBlock
#print CoveringDesigns.SevenBlock.supportExcess
#print CoveringDesigns.SevenBlock.balancedMoment
#print CoveringDesigns.SevenBlock.partialOverlap
#print CoveringDesigns.SevenBlock.supportImbalance

#check (@CoveringDesigns.SevenBlock.classification_ge_two : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {a : ℕ},
  2 ≤ a →
    ∀ {B : I → Finset V},
      Fintype.card V = 7 * a + 4 →
        CoveringDesigns.Multicover.IsCover B (3 * a + 2) 2 1 →
          Fintype.card I = 7 →
            ∃ (tag : Bool),
              CoveringDesigns.SevenBlock.IndexedIsomorphic B (CoveringDesigns.SevenBlock.templateBlock a tag))
#guard_standard_axioms CoveringDesigns.SevenBlock.classification_ge_two
#print axioms CoveringDesigns.SevenBlock.classification_ge_two

#check (@CoveringDesigns.SevenBlock.classification_ge_two_expanded : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {a : ℕ},
  2 ≤ a →
    ∀ (B : I → Finset V),
      Fintype.card V = 7 * a + 4 →
        Fintype.card I = 7 →
          (∀ (i : I), (B i).card = 3 * a + 2) →
            (∀ (T : Finset V), T.card = 2 → ∃ (i : I), T ⊆ B i) →
              ∃ (tag : Bool) (e : V ≃ CoveringDesigns.SevenBlock.TemplatePoint a tag) (f : I ≃ Fin 7),
                ∀ (x : V) (i : I), x ∈ B i ↔ e x ∈ CoveringDesigns.SevenBlock.templateBlock a tag (f i))
#guard_standard_axioms CoveringDesigns.SevenBlock.classification_ge_two_expanded
#print axioms CoveringDesigns.SevenBlock.classification_ge_two_expanded

#check (@CoveringDesigns.SevenBlock.mem_pointSupport : ∀ {V : Type u_1} {I : Type u_2} [Fintype V] [inst : DecidableEq V]
  [inst_1 : Fintype I] [DecidableEq I] (B : I → Finset V) (x : V) (i : I),
  i ∈ CoveringDesigns.SevenBlock.pointSupport B x ↔ x ∈ B i)
#guard_standard_axioms CoveringDesigns.SevenBlock.mem_pointSupport
#print axioms CoveringDesigns.SevenBlock.mem_pointSupport

#check (@CoveringDesigns.SevenBlock.pointSupport_card : ∀ {V : Type u_1} {I : Type u_2} [Fintype V] [inst : DecidableEq V]
  [inst_1 : Fintype I] [DecidableEq I] (B : I → Finset V) (x : V),
  (CoveringDesigns.SevenBlock.pointSupport B x).card = CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.SevenBlock.pointSupport_card
#print axioms CoveringDesigns.SevenBlock.pointSupport_card

#check (@CoveringDesigns.SevenBlock.pointSupport_pair : ∀ {V : Type u_1} {I : Type u_2} [Fintype V] [inst : DecidableEq V]
  [inst_1 : Fintype I] [inst_2 : DecidableEq I] (B : I → Finset V) (x y : V),
  (CoveringDesigns.SevenBlock.pointSupport B x ∩ CoveringDesigns.SevenBlock.pointSupport B y).card =
    CoveringDesigns.indexedSubsetDegree B {x, y})
#guard_standard_axioms CoveringDesigns.SevenBlock.pointSupport_pair
#print axioms CoveringDesigns.SevenBlock.pointSupport_pair

#check (@CoveringDesigns.SevenBlock.pointSupports_meet : ∀ {V : Type u_1} {I : Type u_2} [Fintype V] [inst : DecidableEq V]
  [inst_1 : Fintype I] [inst_2 : DecidableEq I] {B : I → Finset V} {k : ℕ},
  CoveringDesigns.Multicover.IsCover B k 2 1 →
    ∀ (x y : V),
      x ≠ y → (CoveringDesigns.SevenBlock.pointSupport B x ∩ CoveringDesigns.SevenBlock.pointSupport B y).Nonempty)
#guard_standard_axioms CoveringDesigns.SevenBlock.pointSupports_meet
#print axioms CoveringDesigns.SevenBlock.pointSupports_meet

#check (@CoveringDesigns.SevenBlock.covering_degree_profile : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {a : ℕ},
  1 ≤ a →
    ∀ {B : I → Finset V},
      Fintype.card V = 7 * a + 4 →
        CoveringDesigns.Multicover.IsCover B (3 * a + 2) 2 1 →
          Fintype.card I = 7 →
            ∃ (p : V) (q : V),
              p ≠ q ∧
                CoveringDesigns.indexedDegree B p = 4 ∧
                  CoveringDesigns.indexedDegree B q = 4 ∧
                    ∀ (x : V), x ≠ p → x ≠ q → CoveringDesigns.indexedDegree B x = 3)
#guard_standard_axioms CoveringDesigns.SevenBlock.covering_degree_profile
#print axioms CoveringDesigns.SevenBlock.covering_degree_profile

#check (@CoveringDesigns.SevenBlock.covering_slack : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] [inst_3 : DecidableEq I] {a : ℕ} {B : I → Finset V},
  Fintype.card V = 7 * a + 4 →
    CoveringDesigns.Multicover.Uniform B (3 * a + 2) →
      Fintype.card I = 7 →
        ∀ (p q : V),
          p ≠ q →
            CoveringDesigns.indexedDegree B p = 4 →
              CoveringDesigns.indexedDegree B q = 4 →
                CoveringDesigns.SevenBlock.partialOverlap (CoveringDesigns.SevenBlock.remainingSupports B {p, q}) 3 +
                    2 *
                      CoveringDesigns.SevenBlock.supportImbalance
                        (CoveringDesigns.SevenBlock.remainingSupports B {p, q}) a 6 =
                  3 * (↑(CoveringDesigns.indexedSubsetDegree B {p, q}) - 2))
#guard_standard_axioms CoveringDesigns.SevenBlock.covering_slack
#print axioms CoveringDesigns.SevenBlock.covering_slack

#check (@CoveringDesigns.SevenBlock.line_card : ∀ (l : Fin 7), (CoveringDesigns.SevenBlock.line l).card = 3)
#guard_standard_axioms CoveringDesigns.SevenBlock.line_card
#print axioms CoveringDesigns.SevenBlock.line_card

#check (@CoveringDesigns.SevenBlock.line_meet : ∀ (l m : Fin 7),
  (CoveringDesigns.SevenBlock.line l ∩ CoveringDesigns.SevenBlock.line m).Nonempty)
#guard_standard_axioms CoveringDesigns.SevenBlock.line_meet
#print axioms CoveringDesigns.SevenBlock.line_meet

#check (@CoveringDesigns.SevenBlock.line_inter_card : ∀ (l m : Fin 7),
  l ≠ m → (CoveringDesigns.SevenBlock.line l ∩ CoveringDesigns.SevenBlock.line m).card = 1)
#guard_standard_axioms CoveringDesigns.SevenBlock.line_inter_card
#print axioms CoveringDesigns.SevenBlock.line_inter_card

#check (@CoveringDesigns.SevenBlock.line_injective : Function.Injective CoveringDesigns.SevenBlock.line)
#guard_standard_axioms CoveringDesigns.SevenBlock.line_injective
#print axioms CoveringDesigns.SevenBlock.line_injective

#check (@CoveringDesigns.SevenBlock.pair_unique_line : ∀ (i j : Fin 7),
  i ≠ j → ∃! l : Fin 7, i ∈ CoveringDesigns.SevenBlock.line l ∧ j ∈ CoveringDesigns.SevenBlock.line l)
#guard_standard_axioms CoveringDesigns.SevenBlock.pair_unique_line
#print axioms CoveringDesigns.SevenBlock.pair_unique_line

#check (@CoveringDesigns.SevenBlock.position_degree : ∀ (i : Fin 7),
  (Finset.univ.filter fun l : Fin 7 => i ∈ CoveringDesigns.SevenBlock.line l).card = 3)
#guard_standard_axioms CoveringDesigns.SevenBlock.position_degree
#print axioms CoveringDesigns.SevenBlock.position_degree

#check (@CoveringDesigns.SevenBlock.high_card : ∀ (tag h : Bool), (CoveringDesigns.SevenBlock.highSupport tag h).card = 4)
#guard_standard_axioms CoveringDesigns.SevenBlock.high_card
#print axioms CoveringDesigns.SevenBlock.high_card

#check (@CoveringDesigns.SevenBlock.high_line_meet : ∀ (tag h : Bool) (l : Fin 7),
  (CoveringDesigns.SevenBlock.highSupport tag h ∩ CoveringDesigns.SevenBlock.line l).Nonempty)
#guard_standard_axioms CoveringDesigns.SevenBlock.high_line_meet
#print axioms CoveringDesigns.SevenBlock.high_line_meet

#check (@CoveringDesigns.SevenBlock.high_high_meet : ∀ (tag h g : Bool),
  (CoveringDesigns.SevenBlock.highSupport tag h ∩ CoveringDesigns.SevenBlock.highSupport tag g).Nonempty)
#guard_standard_axioms CoveringDesigns.SevenBlock.high_high_meet
#print axioms CoveringDesigns.SevenBlock.high_high_meet

#check (@CoveringDesigns.SevenBlock.exceptional_codegree : ∀ (tag : Bool),
  (CoveringDesigns.SevenBlock.highSupport tag Bool.false ∩ CoveringDesigns.SevenBlock.highSupport tag Bool.true).card =
    if tag = Bool.true then 4 else 2)
#guard_standard_axioms CoveringDesigns.SevenBlock.exceptional_codegree
#print axioms CoveringDesigns.SevenBlock.exceptional_codegree

#check (@CoveringDesigns.SevenBlock.fano_incidence_identity : ∀ (W : Fin 7 → ℤ) (l : Fin 7),
  2 * W l + ∑ m : Fin 7, W m =
    ∑ i ∈ CoveringDesigns.SevenBlock.line l, ∑ m : Fin 7, if i ∈ CoveringDesigns.SevenBlock.line m then W m else 0)
#guard_standard_axioms CoveringDesigns.SevenBlock.fano_incidence_identity
#print axioms CoveringDesigns.SevenBlock.fano_incidence_identity

#check (@CoveringDesigns.SevenBlock.fano_weights_unique : ∀ (W U : Fin 7 → ℤ),
  (∀ (i : Fin 7),
      (∑ l : Fin 7, if i ∈ CoveringDesigns.SevenBlock.line l then W l else 0) =
        ∑ l : Fin 7, if i ∈ CoveringDesigns.SevenBlock.line l then U l else 0) →
    W = U)
#guard_standard_axioms CoveringDesigns.SevenBlock.fano_weights_unique
#print axioms CoveringDesigns.SevenBlock.fano_weights_unique

#check (@CoveringDesigns.SevenBlock.exceptional_support_normal_form : ∀ (H G : Finset (Fin 7)),
  H.card = 4 →
    G.card = 4 →
      (∀ (l : Fin 7),
          (H ∩ CoveringDesigns.SevenBlock.line l).Nonempty ∧ (G ∩ CoveringDesigns.SevenBlock.line l).Nonempty) →
        (∀ (l : Fin 7),
            Even ((H ∩ CoveringDesigns.SevenBlock.line l).card + (G ∩ CoveringDesigns.SevenBlock.line l).card)) →
          (H ∩ G).card = 2 ∨ (H ∩ G).card = 4 →
            ∃ (e : Equiv.Perm (Fin 7)) (tag : Bool) (swap : Bool),
              CoveringDesigns.relabel e (Finset.image CoveringDesigns.SevenBlock.line Finset.univ) =
                  Finset.image CoveringDesigns.SevenBlock.line Finset.univ ∧
                Finset.map (Equiv.toEmbedding e) H = CoveringDesigns.SevenBlock.highSupport tag swap ∧
                  Finset.map (Equiv.toEmbedding e) G = CoveringDesigns.SevenBlock.highSupport tag !swap)
#guard_standard_axioms CoveringDesigns.SevenBlock.exceptional_support_normal_form
#print axioms CoveringDesigns.SevenBlock.exceptional_support_normal_form

#check (@CoveringDesigns.SevenBlock.IndexedIsomorphic.refl : ∀ {V : Type u_1} {I : Type u_2} (B : I → Finset V),
  CoveringDesigns.SevenBlock.IndexedIsomorphic B B)
#guard_standard_axioms CoveringDesigns.SevenBlock.IndexedIsomorphic.refl
#print axioms CoveringDesigns.SevenBlock.IndexedIsomorphic.refl

#check (@CoveringDesigns.SevenBlock.IndexedIsomorphic.symm : ∀ {V : Type u_1} {I : Type u_2} {W : Type u_3} {J : Type u_4}
  {B : I → Finset V} {C : J → Finset W},
  CoveringDesigns.SevenBlock.IndexedIsomorphic B C → CoveringDesigns.SevenBlock.IndexedIsomorphic C B)
#guard_standard_axioms CoveringDesigns.SevenBlock.IndexedIsomorphic.symm
#print axioms CoveringDesigns.SevenBlock.IndexedIsomorphic.symm

#check (@CoveringDesigns.SevenBlock.IndexedIsomorphic.trans : ∀ {V : Type u_1} {I : Type u_2} {W : Type u_3} {J : Type u_4}
  {U : Type u_5} {K : Type u_6} {B : I → Finset V} {C : J → Finset W} {D : K → Finset U},
  CoveringDesigns.SevenBlock.IndexedIsomorphic B C →
    CoveringDesigns.SevenBlock.IndexedIsomorphic C D → CoveringDesigns.SevenBlock.IndexedIsomorphic B D)
#guard_standard_axioms CoveringDesigns.SevenBlock.IndexedIsomorphic.trans
#print axioms CoveringDesigns.SevenBlock.IndexedIsomorphic.trans

#check (@CoveringDesigns.SevenBlock.incidence_degree_eq : ∀ {V : Type u_1} {I : Type u_2} {W : Type u_3} {J : Type u_4}
  [inst : DecidableEq V] [inst_1 : DecidableEq W] [inst_2 : Fintype I] [inst_3 : Fintype J] {B : I → Finset V}
  {C : J → Finset W} (e : V ≃ W) (f : I ≃ J),
  (∀ (x : V) (i : I), x ∈ B i ↔ e x ∈ C (f i)) →
    ∀ (x : V), CoveringDesigns.indexedDegree B x = CoveringDesigns.indexedDegree C (e x))
#guard_standard_axioms CoveringDesigns.SevenBlock.incidence_degree_eq
#print axioms CoveringDesigns.SevenBlock.incidence_degree_eq

#check (@CoveringDesigns.SevenBlock.incidence_codegree_eq : ∀ {V : Type u_1} {I : Type u_2} {W : Type u_3} {J : Type u_4}
  [inst : DecidableEq V] [inst_1 : DecidableEq W] [inst_2 : Fintype I] [inst_3 : Fintype J] {B : I → Finset V}
  {C : J → Finset W} (e : V ≃ W) (f : I ≃ J),
  (∀ (x : V) (i : I), x ∈ B i ↔ e x ∈ C (f i)) →
    ∀ (x y : V), CoveringDesigns.indexedSubsetDegree B {x, y} = CoveringDesigns.indexedSubsetDegree C {e x, e y})
#guard_standard_axioms CoveringDesigns.SevenBlock.incidence_codegree_eq
#print axioms CoveringDesigns.SevenBlock.incidence_codegree_eq

#check (@CoveringDesigns.SevenBlock.degree_floor : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] {a : ℕ},
  1 ≤ a →
    ∀ {B : I → Finset V},
      Fintype.card V = 7 * a + 4 →
        CoveringDesigns.Multicover.IsCover B (3 * a + 2) 2 1 → ∀ (x : V), 3 ≤ CoveringDesigns.indexedDegree B x)
#guard_standard_axioms CoveringDesigns.SevenBlock.degree_floor
#print axioms CoveringDesigns.SevenBlock.degree_floor

#check (@CoveringDesigns.SevenBlock.seven_le_card : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V]
  [inst_2 : Fintype I] {a : ℕ},
  1 ≤ a →
    ∀ {B : I → Finset V},
      Fintype.card V = 7 * a + 4 → CoveringDesigns.Multicover.IsCover B (3 * a + 2) 2 1 → 7 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.SevenBlock.seven_le_card
#print axioms CoveringDesigns.SevenBlock.seven_le_card

#check (@CoveringDesigns.SevenBlock.ordinary_seven_le_card : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {a : ℕ},
  1 ≤ a →
    ∀ {C : CoveringDesigns.Family V},
      Fintype.card V = 7 * a + 4 → CoveringDesigns.IsCover C (3 * a + 2) 2 → 7 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.SevenBlock.ordinary_seven_le_card
#print axioms CoveringDesigns.SevenBlock.ordinary_seven_le_card

#check (@CoveringDesigns.SevenBlock.blocks_injective : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] {a : ℕ},
  1 ≤ a →
    ∀ {B : I → Finset V},
      Fintype.card V = 7 * a + 4 →
        CoveringDesigns.Multicover.IsCover B (3 * a + 2) 2 1 → Fintype.card I = 7 → Function.Injective B)
#guard_standard_axioms CoveringDesigns.SevenBlock.blocks_injective
#print axioms CoveringDesigns.SevenBlock.blocks_injective

#check (@CoveringDesigns.SevenBlock.indexed_ordinary_equivalence : ∀ {V : Type u_1} {I : Type u_2} [Fintype V]
  [inst : DecidableEq V] [inst_1 : Fintype I] {B : I → Finset V},
  Function.Injective B →
    CoveringDesigns.SevenBlock.IndexedIsomorphic B
      (CoveringDesigns.Multicover.ofFamily (CoveringDesigns.Multicover.deduplicate B)))
#guard_standard_axioms CoveringDesigns.SevenBlock.indexed_ordinary_equivalence
#print axioms CoveringDesigns.SevenBlock.indexed_ordinary_equivalence

#check (@CoveringDesigns.SevenBlock.ordinary_isomorphism_to_indexed : ∀ {V : Type u_1} {I : Type u_2} [Fintype V]
  [inst : DecidableEq V] [inst_1 : Fintype I] {W : Type u_3} {J : Type u_4} [inst_2 : DecidableEq W]
  [inst_3 : Fintype J] {B : I → Finset V} {C : J → Finset W},
  Function.Injective B →
    Function.Injective C →
      CoveringDesigns.Isomorphic (CoveringDesigns.Multicover.deduplicate B) (CoveringDesigns.Multicover.deduplicate C) →
        CoveringDesigns.SevenBlock.IndexedIsomorphic B C)
#guard_standard_axioms CoveringDesigns.SevenBlock.ordinary_isomorphism_to_indexed
#print axioms CoveringDesigns.SevenBlock.ordinary_isomorphism_to_indexed

#check (@CoveringDesigns.SevenBlock.low_support_fano : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [inst_3 : DecidableEq I] {a : ℕ},
  2 ≤ a →
    ∀ {B : I → Finset V},
      Fintype.card V = 7 * a + 4 →
        CoveringDesigns.Multicover.IsCover B (3 * a + 2) 2 1 →
          Fintype.card I = 7 →
            ∀ (p q : V),
              p ≠ q →
                CoveringDesigns.indexedDegree B p = 4 →
                  CoveringDesigns.indexedDegree B q = 4 →
                    (∀ (x : V), x ≠ p → x ≠ q → CoveringDesigns.indexedDegree B x = 3) →
                      ∃ (e : I ≃ Fin 7),
                        CoveringDesigns.relabel e
                            (Finset.image (CoveringDesigns.SevenBlock.remainingSupports B {p, q}) Finset.univ) =
                          Finset.image CoveringDesigns.SevenBlock.line Finset.univ)
#guard_standard_axioms CoveringDesigns.SevenBlock.low_support_fano
#print axioms CoveringDesigns.SevenBlock.low_support_fano

#check (@CoveringDesigns.SevenBlock.fano_partial_overlap_zero : ∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I]
  {X : Type u_2} [inst_2 : Fintype X] [inst_3 : DecidableEq X] (S : X → Finset I) (e : I ≃ Fin 7),
  CoveringDesigns.relabel e (Finset.image S Finset.univ) = Finset.image CoveringDesigns.SevenBlock.line Finset.univ →
    CoveringDesigns.SevenBlock.partialOverlap S 3 = 0)
#guard_standard_axioms CoveringDesigns.SevenBlock.fano_partial_overlap_zero
#print axioms CoveringDesigns.SevenBlock.fano_partial_overlap_zero

#check (@CoveringDesigns.SevenBlock.exceptional_codegree_dichotomy : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] {a : ℕ},
  2 ≤ a →
    ∀ {B : I → Finset V},
      Fintype.card V = 7 * a + 4 →
        CoveringDesigns.Multicover.IsCover B (3 * a + 2) 2 1 →
          Fintype.card I = 7 →
            ∀ (p q : V),
              p ≠ q →
                CoveringDesigns.indexedDegree B p = 4 →
                  CoveringDesigns.indexedDegree B q = 4 →
                    (∀ (x : V), x ≠ p → x ≠ q → CoveringDesigns.indexedDegree B x = 3) →
                      CoveringDesigns.indexedSubsetDegree B {p, q} = 2 ∨
                        CoveringDesigns.indexedSubsetDegree B {p, q} = 4)
#guard_standard_axioms CoveringDesigns.SevenBlock.exceptional_codegree_dichotomy
#print axioms CoveringDesigns.SevenBlock.exceptional_codegree_dichotomy

#check (@CoveringDesigns.SevenBlock.low_support_shadow : ∀ {V : Type u_1} {I : Type u_2} [inst : Fintype V]
  [inst_1 : DecidableEq V] [inst_2 : Fintype I] [inst_3 : DecidableEq I] {a : ℕ},
  2 ≤ a →
    ∀ {B : I → Finset V},
      Fintype.card V = 7 * a + 4 →
        CoveringDesigns.Multicover.IsCover B (3 * a + 2) 2 1 →
          Fintype.card I = 7 →
            ∀ (p q : V),
              p ≠ q →
                CoveringDesigns.indexedDegree B p = 4 →
                  CoveringDesigns.indexedDegree B q = 4 →
                    (∀ (x : V), x ≠ p → x ≠ q → CoveringDesigns.indexedDegree B x = 3) →
                      ∀ (P : Finset I),
                        P.card = 2 →
                          0 <
                            CoveringDesigns.indexedSubsetDegree (CoveringDesigns.SevenBlock.remainingSupports B {p, q})
                              P)
#guard_standard_axioms CoveringDesigns.SevenBlock.low_support_shadow
#print axioms CoveringDesigns.SevenBlock.low_support_shadow

#check (@CoveringDesigns.SevenBlock.complete_pair_shadow : ∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I],
  Fintype.card I = 7 →
    ∀ (H : CoveringDesigns.Family I),
      (∀ T ∈ H, T.card = 3) →
        (∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) →
          (∀ (i j : I), i ≠ j → ∃ T ∈ H, i ∈ T ∧ j ∈ T) →
            (∃ (c : I), ∀ (T : Finset I), T ∈ H ↔ T.card = 3 ∧ c ∈ T) ∨
              ∃ (e : I ≃ Fin 7), CoveringDesigns.relabel e H = Finset.image CoveringDesigns.SevenBlock.line Finset.univ)
#guard_standard_axioms CoveringDesigns.SevenBlock.complete_pair_shadow
#print axioms CoveringDesigns.SevenBlock.complete_pair_shadow

#check (@CoveringDesigns.SevenBlock.support_fibre_isomorphism : ∀ {V : Type u_1} {I : Type u_2} {W : Type u_3} {J : Type u_4}
  [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype I] [DecidableEq I] [inst_4 : Fintype W]
  [inst_5 : DecidableEq W] [inst_6 : Fintype J] [inst_7 : DecidableEq J] (B : I → Finset V) (C : J → Finset W)
  (f : I ≃ J),
  (∀ (T : Finset J),
      Fintype.card { x : V // Finset.map f.toEmbedding (CoveringDesigns.SevenBlock.pointSupport B x) = T } =
        Fintype.card { y : W // CoveringDesigns.SevenBlock.pointSupport C y = T }) →
    CoveringDesigns.SevenBlock.IndexedIsomorphic B C)
#guard_standard_axioms CoveringDesigns.SevenBlock.support_fibre_isomorphism
#print axioms CoveringDesigns.SevenBlock.support_fibre_isomorphism

#check (@CoveringDesigns.SevenBlock.fibre_weight_sum : ∀ {X : Type u_1} [inst : Fintype X] (f : X → Fin 7),
  ∑ l : Fin 7, CoveringDesigns.SevenBlock.fibreWeight f l = Fintype.card X)
#guard_standard_axioms CoveringDesigns.SevenBlock.fibre_weight_sum
#print axioms CoveringDesigns.SevenBlock.fibre_weight_sum

#check (@CoveringDesigns.SevenBlock.fibre_weight_row : ∀ {X : Type u_1} {I : Type u_2} [inst : Fintype X] [Fintype I]
  [inst_2 : DecidableEq I] (S : X → Finset I) (e : I ≃ Fin 7) (f : X → Fin 7),
  (∀ (x : X), Finset.map e.toEmbedding (S x) = CoveringDesigns.SevenBlock.line (f x)) →
    ∀ (i : I),
      (∑ l : Fin 7, if e i ∈ CoveringDesigns.SevenBlock.line l then CoveringDesigns.SevenBlock.fibreWeight f l else 0) =
        CoveringDesigns.indexedDegree S i)
#guard_standard_axioms CoveringDesigns.SevenBlock.fibre_weight_row
#print axioms CoveringDesigns.SevenBlock.fibre_weight_row

#check (@CoveringDesigns.SevenBlock.zero_partial_shadow_divisible : ∀ {X : Type u_1} {I : Type u_2} [inst : Fintype X]
  [inst_1 : Fintype I] [inst_2 : DecidableEq X] [inst_3 : DecidableEq I] (S : X → Finset I),
  (∀ (x : X), (S x).card = 3) →
    (∀ (x y : X), x ≠ y → (S x ∩ S y).Nonempty) →
      CoveringDesigns.SevenBlock.partialOverlap S 3 = 0 → 3 ∣ (CoveringDesigns.SevenBlock.pairShadow S).card)
#guard_standard_axioms CoveringDesigns.SevenBlock.zero_partial_shadow_divisible
#print axioms CoveringDesigns.SevenBlock.zero_partial_shadow_divisible

#check (@CoveringDesigns.SevenBlock.shadow_positive : ∀ {X : Type u_1} {I : Type u_2} [inst : Fintype X] [inst_1 : Fintype I]
  [inst_2 : DecidableEq X] [inst_3 : DecidableEq I] (S : X → Finset I) {a : ℕ},
  2 ≤ a →
    Fintype.card I = 7 →
      (∀ (x : X), (S x).card = 3) →
        (∀ (x y : X), x ≠ y → (S x ∩ S y).Nonempty) →
          Fintype.card X * Nat.choose 3 2 = (Fintype.card I).choose 2 * a + 6 →
            CoveringDesigns.SevenBlock.partialOverlap S 3 + 2 * CoveringDesigns.SevenBlock.supportImbalance S a 6 ≤ 6 →
              ∀ (P : Finset I), P.card = 2 → 0 < CoveringDesigns.indexedSubsetDegree S P)
#guard_standard_axioms CoveringDesigns.SevenBlock.shadow_positive
#print axioms CoveringDesigns.SevenBlock.shadow_positive

#check (@CoveringDesigns.SevenBlock.consecutive_nonneg : ∀ (z : ℤ), 0 ≤ z * (z - 1))
#guard_standard_axioms CoveringDesigns.SevenBlock.consecutive_nonneg
#print axioms CoveringDesigns.SevenBlock.consecutive_nonneg

#check (@CoveringDesigns.SevenBlock.imbalance_identity : ∀ {ι : Type u_1} (T : Finset ι) (n : ι → ℕ) (A s : ℕ),
  ∑ i ∈ T, n i = T.card * A + s →
    (2 : ℤ) * (∑ i ∈ T, ↑((n i).choose 2) - (↑T.card * ↑(A.choose 2) + ↑s * ↑A)) = ∑ i ∈ T, (↑(n i) - ↑A) * (↑(n i) - ↑A - 1))
#guard_standard_axioms CoveringDesigns.SevenBlock.imbalance_identity
#print axioms CoveringDesigns.SevenBlock.imbalance_identity

#check (@CoveringDesigns.SevenBlock.imbalance_nonneg : ∀ {ι : Type u_1} (T : Finset ι) (n : ι → ℕ) (A s : ℕ),
  ∑ i ∈ T, n i = T.card * A + s → (0 : ℤ) ≤ ∑ i ∈ T, ↑((n i).choose 2) - (↑T.card * ↑(A.choose 2) + ↑s * ↑A))
#guard_standard_axioms CoveringDesigns.SevenBlock.imbalance_nonneg
#print axioms CoveringDesigns.SevenBlock.imbalance_nonneg

#check (@CoveringDesigns.SevenBlock.support_excess_eq : ∀ {X : Type u_1} {I : Type u_2} [inst : Fintype X] [inst_1 : Fintype I]
  [inst_2 : DecidableEq X] [inst_3 : DecidableEq I] (S : X → Finset I),
  CoveringDesigns.SevenBlock.supportExcess S =
    ∑ P ∈ Finset.powersetCard 2 Finset.univ, (↑(CoveringDesigns.indexedCommon S P).card - 1))
#guard_standard_axioms CoveringDesigns.SevenBlock.support_excess_eq
#print axioms CoveringDesigns.SevenBlock.support_excess_eq

#check (@CoveringDesigns.SevenBlock.support_moment_eq : ∀ {X : Type u_1} {I : Type u_2} [inst : Fintype X] [inst_1 : Fintype I]
  [inst_2 : DecidableEq X] [inst_3 : DecidableEq I] (S : X → Finset I),
  CoveringDesigns.SevenBlock.supportMoment S =
    ∑ P ∈ Finset.powersetCard 2 Finset.univ, ↑((CoveringDesigns.indexedCommon S P).card.choose 2))
#guard_standard_axioms CoveringDesigns.SevenBlock.support_moment_eq
#print axioms CoveringDesigns.SevenBlock.support_moment_eq

#check (@CoveringDesigns.SevenBlock.support_slack_identity : ∀ {X : Type u_1} {I : Type u_2} [inst : Fintype X]
  [inst_1 : Fintype I] [inst_2 : DecidableEq X] [inst_3 : DecidableEq I] (S : X → Finset I) (r A s : ℕ),
  ↑r * CoveringDesigns.SevenBlock.supportExcess S - 2 * CoveringDesigns.SevenBlock.balancedMoment I A s =
    CoveringDesigns.SevenBlock.partialOverlap S r + 2 * CoveringDesigns.SevenBlock.supportImbalance S A s)
#guard_standard_axioms CoveringDesigns.SevenBlock.support_slack_identity
#print axioms CoveringDesigns.SevenBlock.support_slack_identity

#check (@CoveringDesigns.SevenBlock.support_imbalance_identity : ∀ {X : Type u_1} {I : Type u_2} [inst : Fintype X]
  [inst_1 : Fintype I] [DecidableEq X] [inst_3 : DecidableEq I] (S : X → Finset I) (r A s : ℕ),
  (∀ (x : X), (S x).card = r) →
    Fintype.card X * r.choose 2 = (Fintype.card I).choose 2 * A + s →
      2 * CoveringDesigns.SevenBlock.supportImbalance S A s =
        ∑ P ∈ Finset.powersetCard 2 Finset.univ,
          (↑(CoveringDesigns.indexedSubsetDegree S P) - ↑A) * (↑(CoveringDesigns.indexedSubsetDegree S P) - ↑A - 1))
#guard_standard_axioms CoveringDesigns.SevenBlock.support_imbalance_identity
#print axioms CoveringDesigns.SevenBlock.support_imbalance_identity

#check (@CoveringDesigns.SevenBlock.support_imbalance_nonneg : ∀ {X : Type u_1} {I : Type u_2} [inst : Fintype X]
  [inst_1 : Fintype I] [DecidableEq X] [inst_3 : DecidableEq I] (S : X → Finset I) (r A s : ℕ),
  (∀ (x : X), (S x).card = r) →
    Fintype.card X * r.choose 2 = (Fintype.card I).choose 2 * A + s →
      0 ≤ CoveringDesigns.SevenBlock.supportImbalance S A s)
#guard_standard_axioms CoveringDesigns.SevenBlock.support_imbalance_nonneg
#print axioms CoveringDesigns.SevenBlock.support_imbalance_nonneg

#check (@CoveringDesigns.SevenBlock.partial_overlap_nonneg : ∀ {X : Type u_1} {I : Type u_2} [inst : Fintype X]
  [inst_1 : Fintype I] [inst_2 : DecidableEq X] [inst_3 : DecidableEq I] (S : X → Finset I) (r : ℕ),
  (∀ (x : X), (S x).card = r) →
    (∀ (x y : X), x ≠ y → (S x ∩ S y).Nonempty) → 0 ≤ CoveringDesigns.SevenBlock.partialOverlap S r)
#guard_standard_axioms CoveringDesigns.SevenBlock.partial_overlap_nonneg
#print axioms CoveringDesigns.SevenBlock.partial_overlap_nonneg

#check (@CoveringDesigns.SevenBlock.partial_overlap_three : ∀ {X : Type u_1} {I : Type u_2} [inst : Fintype X]
  [inst_1 : Fintype I] [inst_2 : DecidableEq X] [inst_3 : DecidableEq I] (S : X → Finset I),
  (∀ (x : X), (S x).card = 3) →
    (∀ (x y : X), x ≠ y → (S x ∩ S y).Nonempty) →
      CoveringDesigns.SevenBlock.partialOverlap S 3 =
        ↑{P ∈ Finset.powersetCard 2 Finset.univ | (CoveringDesigns.indexedCommon S P).card = 2}.card)
#guard_standard_axioms CoveringDesigns.SevenBlock.partial_overlap_three
#print axioms CoveringDesigns.SevenBlock.partial_overlap_three

#check (@CoveringDesigns.SevenBlock.mem_templateBlock : ∀ (a : ℕ) (tag : Bool) (i : Fin 7)
  (x : CoveringDesigns.SevenBlock.TemplatePoint a tag),
  x ∈ CoveringDesigns.SevenBlock.templateBlock a tag i ↔ i ∈ CoveringDesigns.SevenBlock.templateSupport a tag x)
#guard_standard_axioms CoveringDesigns.SevenBlock.mem_templateBlock
#print axioms CoveringDesigns.SevenBlock.mem_templateBlock

#check (@CoveringDesigns.SevenBlock.template_point_card : ∀ {a : ℕ},
  1 ≤ a → ∀ (tag : Bool), Fintype.card (CoveringDesigns.SevenBlock.TemplatePoint a tag) = 7 * a + 4)
#guard_standard_axioms CoveringDesigns.SevenBlock.template_point_card
#print axioms CoveringDesigns.SevenBlock.template_point_card

#check (@CoveringDesigns.SevenBlock.template_uniform : ∀ {a : ℕ},
  1 ≤ a →
    ∀ (tag : Bool), CoveringDesigns.Multicover.Uniform (CoveringDesigns.SevenBlock.templateBlock a tag) (3 * a + 2))
#guard_standard_axioms CoveringDesigns.SevenBlock.template_uniform
#print axioms CoveringDesigns.SevenBlock.template_uniform

#check (@CoveringDesigns.SevenBlock.template_supports_meet : ∀ (a : ℕ) (tag : Bool)
  (x y : CoveringDesigns.SevenBlock.TemplatePoint a tag),
  (CoveringDesigns.SevenBlock.templateSupport a tag x ∩ CoveringDesigns.SevenBlock.templateSupport a tag y).Nonempty)
#guard_standard_axioms CoveringDesigns.SevenBlock.template_supports_meet
#print axioms CoveringDesigns.SevenBlock.template_supports_meet

#check (@CoveringDesigns.SevenBlock.template_covers : ∀ (a : ℕ) (tag : Bool),
  CoveringDesigns.Multicover.Covers (CoveringDesigns.SevenBlock.templateBlock a tag) 2 1)
#guard_standard_axioms CoveringDesigns.SevenBlock.template_covers
#print axioms CoveringDesigns.SevenBlock.template_covers

#check (@CoveringDesigns.SevenBlock.template_isCover : ∀ {a : ℕ},
  1 ≤ a →
    ∀ (tag : Bool), CoveringDesigns.Multicover.IsCover (CoveringDesigns.SevenBlock.templateBlock a tag) (3 * a + 2) 2 1)
#guard_standard_axioms CoveringDesigns.SevenBlock.template_isCover
#print axioms CoveringDesigns.SevenBlock.template_isCover

#check (@CoveringDesigns.SevenBlock.template_injective : ∀ {a : ℕ},
  1 ≤ a → ∀ (tag : Bool), Function.Injective (CoveringDesigns.SevenBlock.templateBlock a tag))
#guard_standard_axioms CoveringDesigns.SevenBlock.template_injective
#print axioms CoveringDesigns.SevenBlock.template_injective

#check (@CoveringDesigns.SevenBlock.template_degree : ∀ (a : ℕ) (tag : Bool)
  (x : CoveringDesigns.SevenBlock.TemplatePoint a tag),
  CoveringDesigns.indexedDegree (CoveringDesigns.SevenBlock.templateBlock a tag) x =
    match x with
    | Sum.inl val => 4
    | Sum.inr val => 3)
#guard_standard_axioms CoveringDesigns.SevenBlock.template_degree
#print axioms CoveringDesigns.SevenBlock.template_degree

#check (@CoveringDesigns.SevenBlock.template_degree_four_iff : ∀ (a : ℕ) (tag : Bool)
  (x : CoveringDesigns.SevenBlock.TemplatePoint a tag),
  CoveringDesigns.indexedDegree (CoveringDesigns.SevenBlock.templateBlock a tag) x = 4 ↔ ∃ (h : Bool), x = Sum.inl h)
#guard_standard_axioms CoveringDesigns.SevenBlock.template_degree_four_iff
#print axioms CoveringDesigns.SevenBlock.template_degree_four_iff

#check (@CoveringDesigns.SevenBlock.template_line_fibre_card : ∀ (a : ℕ) (tag : Bool) (l : Fin 7),
  Fintype.card
      { x : CoveringDesigns.SevenBlock.TemplatePoint a tag //
        CoveringDesigns.SevenBlock.templateSupport a tag x = CoveringDesigns.SevenBlock.line l } =
    CoveringDesigns.SevenBlock.weight a tag l)
#guard_standard_axioms CoveringDesigns.SevenBlock.template_line_fibre_card
#print axioms CoveringDesigns.SevenBlock.template_line_fibre_card

#check (@CoveringDesigns.SevenBlock.template_exceptional_codegree : ∀ (a : ℕ) (tag : Bool),
  CoveringDesigns.indexedSubsetDegree (CoveringDesigns.SevenBlock.templateBlock a tag)
      {Sum.inl Bool.false, Sum.inl Bool.true} =
    if tag = Bool.true then 4 else 2)
#guard_standard_axioms CoveringDesigns.SevenBlock.template_exceptional_codegree
#print axioms CoveringDesigns.SevenBlock.template_exceptional_codegree

#check (@CoveringDesigns.SevenBlock.templates_not_isomorphic : ∀ (a : ℕ),
  ¬CoveringDesigns.SevenBlock.IndexedIsomorphic (CoveringDesigns.SevenBlock.templateBlock a Bool.false)
      (CoveringDesigns.SevenBlock.templateBlock a Bool.true))
#guard_standard_axioms CoveringDesigns.SevenBlock.templates_not_isomorphic
#print axioms CoveringDesigns.SevenBlock.templates_not_isomorphic

#check (@CoveringDesigns.SevenBlock.template_family_isCover : ∀ {a : ℕ},
  1 ≤ a → ∀ (tag : Bool), CoveringDesigns.IsCover (CoveringDesigns.SevenBlock.templateFamily a tag) (3 * a + 2) 2)
#guard_standard_axioms CoveringDesigns.SevenBlock.template_family_isCover
#print axioms CoveringDesigns.SevenBlock.template_family_isCover

#check (@CoveringDesigns.SevenBlock.template_family_card : ∀ {a : ℕ},
  1 ≤ a → ∀ (tag : Bool), Finset.card (CoveringDesigns.SevenBlock.templateFamily a tag) = 7)
#guard_standard_axioms CoveringDesigns.SevenBlock.template_family_card
#print axioms CoveringDesigns.SevenBlock.template_family_card

#check (@CoveringDesigns.SevenBlock.template_attainment : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {a : ℕ},
  1 ≤ a →
    Fintype.card V = 7 * a + 4 →
      ∀ (tag : Bool), ∃ (C : CoveringDesigns.Family V), CoveringDesigns.IsCover C (3 * a + 2) 2 ∧ Finset.card C = 7)
#guard_standard_axioms CoveringDesigns.SevenBlock.template_attainment
#print axioms CoveringDesigns.SevenBlock.template_attainment

#check (@CoveringDesigns.SevenBlock.covering_number_on : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {a : ℕ},
  1 ≤ a →
    Fintype.card V = 7 * a + 4 →
      (∃ (C : CoveringDesigns.Family V), CoveringDesigns.IsCover C (3 * a + 2) 2 ∧ Finset.card C = 7) ∧
        ∀ (C : CoveringDesigns.Family V), CoveringDesigns.IsCover C (3 * a + 2) 2 → 7 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.SevenBlock.covering_number_on
#print axioms CoveringDesigns.SevenBlock.covering_number_on


