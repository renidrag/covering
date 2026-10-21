import CoveringDesigns.C18_10_3.SquareSupport

open CoveringDesigns Finset Matrix Module
open scoped BigOperators
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
universe u_1 u_2 u_3

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.star
#print CoveringDesigns.degree
#print CoveringDesigns.knownBlocks12_18_10_3
#print CoveringDesigns.knownCover12_18_10_3
#print CoveringDesigns.knownCover12_18_10_3_on
#print CoveringDesigns.C18_10_3.rowIncidence
#print CoveringDesigns.C18_10_3.rowExcess
#print CoveringDesigns.C18_10_3.rowDeficit
#print CoveringDesigns.C18_10_3.pointSupport
#print CoveringDesigns.BoundaryRank.binarySupport

namespace CoveringDesigns.Audit18_10_3

/-- Ordinary exactness with uniformity and every triple exposed. -/
theorem covering_number_explicit {α : Type*} [Fintype α]
    (hv : Fintype.card α = 18) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 10) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 12) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 10) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 12 ≤ C.card) := by
  obtain ⟨⟨C, hC, hcard⟩, hlower⟩ := covering_number_18_10_3_on hv
  exact ⟨⟨C, hC.1, hC.2, hcard⟩, fun C hu hc => hlower C ⟨hu, hc⟩⟩

/-- The indexed adapter counts actual occurrences, including repetitions. -/
theorem indexed_explicit {α ι : Type*} [Fintype α] [Fintype ι]
    (B : ι → Finset α) (hv : Fintype.card α = 18)
    (hu : ∀ i, (B i).card = 10)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ i, T ⊆ B i) :
    12 ≤ Fintype.card ι := indexed_lower_bound_18_10_3 B hv hu hc

end CoveringDesigns.Audit18_10_3

-- Complete typed contracts and transitive foundational-axiom guards.
-- The lower and exactness contracts have no supplied incidence or rank assumptions.

-- A fully expanded restatement checks this large contract by applying the
-- theorem to arbitrary inputs. This avoids expensive higher-order inference
-- in a single type ascription; every original premise and conclusion remains.
namespace CoveringDesigns.Audit18_10_3
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
theorem core_equality_explicit (R : Matrix ι κ ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℕ)
    (hl : Fintype.card ι = 16) (hb : Fintype.card κ = 11)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hrow : ∀ i, (∑ j, E i j) + (δ i : ℝ) = 3) (htotal : ∑ i, δ i = 18)
    (hgram : R * R.transpose = Matrix.diagonal (fun _ => (3 : ℝ)) + E +
      Matrix.of (fun _ _ => (3 : ℝ))) :
    (univ.filter (fun i => δ i = 0)).card = 10 ∧
    (∀ i, δ i = 0 ∨ δ i = 3) ∧
    (∀ i, δ i = 3 → ∀ j, E i j = 0) ∧
    finrank ℝ (LinearMap.ker (Matrix.diagonal (fun _ => (3 : ℝ)) + E).mulVecLin) = 5 ∧
    LinearMap.ker (R * R.transpose).mulVecLin =
      LinearMap.ker (Matrix.diagonal (fun _ => (3 : ℝ)) + E).mulVecLin ∧
    R.rank = 11 := by
  exact C18_10_3.core_equality R E δ hl hb hs hn hz hrow htotal hgram
end CoveringDesigns.Audit18_10_3
#check @CoveringDesigns.C18_10_3.core_equality
#guard_standard_axioms CoveringDesigns.Audit18_10_3.core_equality_explicit
#print axioms CoveringDesigns.Audit18_10_3.core_equality_explicit
#guard_standard_axioms CoveringDesigns.C18_10_3.core_equality
#print axioms CoveringDesigns.C18_10_3.core_equality

#check (@CoveringDesigns.C18_10_3.core_pairing : ∀ {ι : Type u_1} {κ : Type u_2} [inst : Fintype ι] [inst_1 : DecidableEq ι]
  [inst_2 : Fintype κ] [DecidableEq κ] (R : Matrix ι κ ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℕ),
  Fintype.card ι = 16 →
    Fintype.card κ = 11 →
      (∀ (i j : ι), E i j = E j i) →
        (∀ (i j : ι), 0 ≤ E i j) →
          (∀ (i : ι), E i i = 0) →
            (∀ (i : ι), ∑ j : ι, E i j + ↑(δ i) = 3) →
              ∑ i : ι, δ i = 18 →
                (R * R.transpose = (Matrix.diagonal fun (x : ι) => 3) + E + Matrix.of fun (x x_1 : ι) => 3) →
                  ∃ (e : Fin 5 × Bool ⊕ Fin 6 ≃ ι),
                    (∀ (i : Fin 5) (b : Bool), δ (e (Sum.inl (i, b))) = 0) ∧
                      (∀ (i : Fin 6), δ (e (Sum.inr i)) = 3) ∧
                        (∀ (i j : Fin 5), i ≠ j → ∀ (b c : Bool), E (e (Sum.inl (i, b))) (e (Sum.inl (j, c))) = 0) ∧
                          (∀ (i : Fin 5), E (e (Sum.inl (i, Bool.false))) (e (Sum.inl (i, Bool.true))) = 3) ∧
                            (∀ (i : Fin 6) (j : ι), E (e (Sum.inr i)) j = 0) ∧
                              ∀ (i : Fin 5) (j : κ),
                                R (e (Sum.inl (i, Bool.false))) j = R (e (Sum.inl (i, Bool.true))) j)
#guard_standard_axioms CoveringDesigns.C18_10_3.core_pairing
#print axioms CoveringDesigns.C18_10_3.core_pairing

#check (@CoveringDesigns.C18_10_3.core_representatives : ∀ {ι : Type u_1} {κ : Type u_2} [inst : Fintype ι]
  [inst_1 : DecidableEq ι] [inst_2 : Fintype κ] [inst_3 : DecidableEq κ] (R : Matrix ι κ ℝ) (E : Matrix ι ι ℝ)
  (δ : ι → ℕ),
  Fintype.card ι = 16 →
    Fintype.card κ = 11 →
      (∀ (i j : ι), E i j = E j i) →
        (∀ (i j : ι), 0 ≤ E i j) →
          (∀ (i : ι), E i i = 0) →
            (∀ (i : ι), ∑ j : ι, E i j + ↑(δ i) = 3) →
              ∑ i : ι, δ i = 18 →
                (R * R.transpose = (Matrix.diagonal fun (x : ι) => 3) + E + Matrix.of fun (x x_1 : ι) => 3) →
                  ∃ (f : κ ↪ ι),
                    ((Matrix.of fun (i j : κ) => R (f i) j) * Matrix.transpose fun (i j : κ) => R (f i) j) =
                      (Matrix.diagonal fun (x : κ) => 3) + Matrix.of fun (x x_1 : κ) => 3)
#guard_standard_axioms CoveringDesigns.C18_10_3.core_representatives
#print axioms CoveringDesigns.C18_10_3.core_representatives

#check (@CoveringDesigns.C18_10_3.pointSupport_card : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (p : α), (CoveringDesigns.C18_10_3.pointSupport C p).card = CoveringDesigns.degree C p)
#guard_standard_axioms CoveringDesigns.C18_10_3.pointSupport_card
#print axioms CoveringDesigns.C18_10_3.pointSupport_card

#check (@CoveringDesigns.C18_10_3.pointSupport_inter : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (p q : α),
  (CoveringDesigns.C18_10_3.pointSupport C p ∩ CoveringDesigns.C18_10_3.pointSupport C q).card =
    CoveringDesigns.degree (CoveringDesigns.star C p) q)
#guard_standard_axioms CoveringDesigns.C18_10_3.pointSupport_inter
#print axioms CoveringDesigns.C18_10_3.pointSupport_inter

#check (@CoveringDesigns.C18_10_3.row_support : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (H : Finset α) (x : CoveringDesigns.C18_10_3.Outside H),
  CoveringDesigns.BoundaryRank.binarySupport (CoveringDesigns.C18_10_3.rowIncidence C H x) =
    CoveringDesigns.C18_10_3.pointSupport C ↑x)
#guard_standard_axioms CoveringDesigns.C18_10_3.row_support
#print axioms CoveringDesigns.C18_10_3.row_support

#check (@CoveringDesigns.C18_10_3.zero_deficit_intersections : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  {C : CoveringDesigns.Family α} {h g : α},
  h ≠ g →
    (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
      ∀ (x : CoveringDesigns.C18_10_3.Outside {h, g}),
        CoveringDesigns.C18_10_3.rowDeficit C {h, g} x = 0 →
          CoveringDesigns.degree (CoveringDesigns.star C ↑x) h = 3 ∧
            CoveringDesigns.degree (CoveringDesigns.star C ↑x) g = 3)
#guard_standard_axioms CoveringDesigns.C18_10_3.zero_deficit_intersections
#print axioms CoveringDesigns.C18_10_3.zero_deficit_intersections

#check (@CoveringDesigns.C18_10_3.agreeing_high_intersections : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  {C : CoveringDesigns.Family α} {h g : α},
  h ≠ g →
    (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
      ∀ {a b : ↥C},
        CoveringDesigns.C18_10_3.pointSupport C h \ CoveringDesigns.C18_10_3.pointSupport C g = {a} →
          CoveringDesigns.C18_10_3.pointSupport C g \ CoveringDesigns.C18_10_3.pointSupport C h = {b} →
            ∀ (x : CoveringDesigns.C18_10_3.Outside {h, g}),
              CoveringDesigns.C18_10_3.rowDeficit C {h, g} x = 0 ∨ CoveringDesigns.C18_10_3.rowDeficit C {h, g} x = 3 →
                (a ∈ CoveringDesigns.C18_10_3.pointSupport C ↑x ↔ b ∈ CoveringDesigns.C18_10_3.pointSupport C ↑x) →
                  CoveringDesigns.C18_10_3.rowDeficit C {h, g} x = 0 ∧
                    CoveringDesigns.degree (CoveringDesigns.star C ↑x) h = 3 ∧
                      CoveringDesigns.degree (CoveringDesigns.star C ↑x) g = 3)
#guard_standard_axioms CoveringDesigns.C18_10_3.agreeing_high_intersections
#print axioms CoveringDesigns.C18_10_3.agreeing_high_intersections

#check (@CoveringDesigns.C18_10_3.two_high_impossible : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
          ∀ {h g : α},
            h ≠ g →
              CoveringDesigns.degree C h = 7 →
                CoveringDesigns.degree C g = 7 → (∀ (x : α), x ≠ h → x ≠ g → CoveringDesigns.degree C x = 6) → False)
#guard_standard_axioms CoveringDesigns.C18_10_3.two_high_impossible
#print axioms CoveringDesigns.C18_10_3.two_high_impossible

#check (@CoveringDesigns.C18_10_3.lower_bound_17_9_2 : ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α]
  {C : CoveringDesigns.Family α}, Fintype.card α = 17 → CoveringDesigns.IsCover C 9 2 → 6 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C18_10_3.lower_bound_17_9_2
#print axioms CoveringDesigns.C18_10_3.lower_bound_17_9_2

#check (@CoveringDesigns.C18_10_3.degree_ge_six : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 → CoveringDesigns.IsCover C 10 3 → ∀ (p : α), 6 ≤ CoveringDesigns.degree C p)
#guard_standard_axioms CoveringDesigns.C18_10_3.degree_ge_six
#print axioms CoveringDesigns.C18_10_3.degree_ge_six

#check (@CoveringDesigns.C18_10_3.pair_ge_two : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 → ∀ {p q : α}, p ≠ q → 2 ≤ CoveringDesigns.degree (CoveringDesigns.star C p) q)
#guard_standard_axioms CoveringDesigns.C18_10_3.pair_ge_two
#print axioms CoveringDesigns.C18_10_3.pair_ge_two

#check (@CoveringDesigns.C18_10_3.eleven_le_card : ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α]
  {C : CoveringDesigns.Family α}, Fintype.card α = 18 → CoveringDesigns.IsCover C 10 3 → 11 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.C18_10_3.eleven_le_card
#print axioms CoveringDesigns.C18_10_3.eleven_le_card

#check (@CoveringDesigns.C18_10_3.degree_excess_sum : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 → Finset.card C = 11 → ∑ p : α, (CoveringDesigns.degree C p - 6) = 2)
#guard_standard_axioms CoveringDesigns.C18_10_3.degree_excess_sum
#print axioms CoveringDesigns.C18_10_3.degree_excess_sum

#check (@CoveringDesigns.C18_10_3.degree_bounds : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 → ∀ (p : α), 6 ≤ CoveringDesigns.degree C p ∧ CoveringDesigns.degree C p ≤ 8)
#guard_standard_axioms CoveringDesigns.C18_10_3.degree_bounds
#print axioms CoveringDesigns.C18_10_3.degree_bounds

#check (@CoveringDesigns.C18_10_3.degree_profiles : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 →
        (∃ (h : α), CoveringDesigns.degree C h = 8 ∧ ∀ (x : α), x ≠ h → CoveringDesigns.degree C x = 6) ∨
          ∃ (h : α) (g : α),
            h ≠ g ∧
              CoveringDesigns.degree C h = 7 ∧
                CoveringDesigns.degree C g = 7 ∧ ∀ (x : α), x ≠ h → x ≠ g → CoveringDesigns.degree C x = 6)
#guard_standard_axioms CoveringDesigns.C18_10_3.degree_profiles
#print axioms CoveringDesigns.C18_10_3.degree_profiles

#check (@CoveringDesigns.C18_10_3.outside_card : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] (H : Finset α),
  Fintype.card (CoveringDesigns.C18_10_3.Outside H) = Fintype.card α - H.card)
#guard_standard_axioms CoveringDesigns.C18_10_3.outside_card
#print axioms CoveringDesigns.C18_10_3.outside_card

#check (@CoveringDesigns.C18_10_3.pair_self : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α] (C : CoveringDesigns.Family α)
  (p : α), CoveringDesigns.degree (CoveringDesigns.star C p) p = CoveringDesigns.degree C p)
#guard_standard_axioms CoveringDesigns.C18_10_3.pair_self
#print axioms CoveringDesigns.C18_10_3.pair_self

#check (@CoveringDesigns.C18_10_3.pair_sum_all : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {k : ℕ},
  CoveringDesigns.Uniform C k →
    ∀ (p : α), ∑ q : α, CoveringDesigns.degree (CoveringDesigns.star C p) q = k * CoveringDesigns.degree C p)
#guard_standard_axioms CoveringDesigns.C18_10_3.pair_sum_all
#print axioms CoveringDesigns.C18_10_3.pair_sum_all

#check (@CoveringDesigns.C18_10_3.sum_outside : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] (H : Finset α)
  (f : α → ℕ), ∑ x : CoveringDesigns.C18_10_3.Outside H, f ↑x + ∑ x ∈ H, f x = ∑ x : α, f x)
#guard_standard_axioms CoveringDesigns.C18_10_3.sum_outside
#print axioms CoveringDesigns.C18_10_3.sum_outside

#check (@CoveringDesigns.C18_10_3.row_gram_entry : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (H : Finset α) (x y : CoveringDesigns.C18_10_3.Outside H),
  (CoveringDesigns.C18_10_3.rowIncidence C H * (CoveringDesigns.C18_10_3.rowIncidence C H).transpose) x y =
    ↑(CoveringDesigns.degree (CoveringDesigns.star C ↑x) ↑y))
#guard_standard_axioms CoveringDesigns.C18_10_3.row_gram_entry
#print axioms CoveringDesigns.C18_10_3.row_gram_entry

#check (@CoveringDesigns.C18_10_3.row_binary : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (H : Finset α) (x : CoveringDesigns.C18_10_3.Outside H) (B : ↥C),
  CoveringDesigns.C18_10_3.rowIncidence C H x B = 0 ∨ CoveringDesigns.C18_10_3.rowIncidence C H x B = 1)
#guard_standard_axioms CoveringDesigns.C18_10_3.row_binary
#print axioms CoveringDesigns.C18_10_3.row_binary

#check (@CoveringDesigns.C18_10_3.row_sum : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α] {C : CoveringDesigns.Family α}
  {H : Finset α},
  (∀ x ∉ H, CoveringDesigns.degree C x = 6) →
    ∀ (x : CoveringDesigns.C18_10_3.Outside H), ∑ B : ↥C, CoveringDesigns.C18_10_3.rowIncidence C H x B = 6)
#guard_standard_axioms CoveringDesigns.C18_10_3.row_sum
#print axioms CoveringDesigns.C18_10_3.row_sum

#check (@CoveringDesigns.C18_10_3.row_gram : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α] {C : CoveringDesigns.Family α}
  {H : Finset α},
  (∀ x ∉ H, CoveringDesigns.degree C x = 6) →
    CoveringDesigns.C18_10_3.rowIncidence C H * (CoveringDesigns.C18_10_3.rowIncidence C H).transpose =
      (Matrix.diagonal fun (x : CoveringDesigns.C18_10_3.Outside H) => 3) + CoveringDesigns.C18_10_3.rowExcess C H +
        Matrix.of fun (x x_1 : CoveringDesigns.C18_10_3.Outside H) => 3)
#guard_standard_axioms CoveringDesigns.C18_10_3.row_gram
#print axioms CoveringDesigns.C18_10_3.row_gram

#check (@CoveringDesigns.C18_10_3.rowExcess_symm : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (H : Finset α) (x y : CoveringDesigns.C18_10_3.Outside H),
  CoveringDesigns.C18_10_3.rowExcess C H x y = CoveringDesigns.C18_10_3.rowExcess C H y x)
#guard_standard_axioms CoveringDesigns.C18_10_3.rowExcess_symm
#print axioms CoveringDesigns.C18_10_3.rowExcess_symm

#check (@CoveringDesigns.C18_10_3.rowExcess_nonneg : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  {C : CoveringDesigns.Family α} {H : Finset α},
  (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
    ∀ (x y : CoveringDesigns.C18_10_3.Outside H), 0 ≤ CoveringDesigns.C18_10_3.rowExcess C H x y)
#guard_standard_axioms CoveringDesigns.C18_10_3.rowExcess_nonneg
#print axioms CoveringDesigns.C18_10_3.rowExcess_nonneg

#check (@CoveringDesigns.C18_10_3.rowExcess_diag : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (H : Finset α) (x : CoveringDesigns.C18_10_3.Outside H),
  CoveringDesigns.C18_10_3.rowExcess C H x x = 0)
#guard_standard_axioms CoveringDesigns.C18_10_3.rowExcess_diag
#print axioms CoveringDesigns.C18_10_3.rowExcess_diag

#check (@CoveringDesigns.C18_10_3.rowDeficit_add : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  {C : CoveringDesigns.Family α} {H : Finset α},
  (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
    ∀ (x : CoveringDesigns.C18_10_3.Outside H),
      CoveringDesigns.C18_10_3.rowDeficit C H x + 3 * H.card =
        ∑ h ∈ H, CoveringDesigns.degree (CoveringDesigns.star C ↑x) h)
#guard_standard_axioms CoveringDesigns.C18_10_3.rowDeficit_add
#print axioms CoveringDesigns.C18_10_3.rowDeficit_add

#check (@CoveringDesigns.C18_10_3.row_balance : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {H : Finset α},
  Fintype.card α = 18 →
    CoveringDesigns.Uniform C 10 →
      (∀ x ∉ H, CoveringDesigns.degree C x = 6) →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
          ∀ (x : CoveringDesigns.C18_10_3.Outside H),
            ∑ y : CoveringDesigns.C18_10_3.Outside H, CoveringDesigns.C18_10_3.rowExcess C H x y +
                ↑(CoveringDesigns.C18_10_3.rowDeficit C H x) =
              3)
#guard_standard_axioms CoveringDesigns.C18_10_3.row_balance
#print axioms CoveringDesigns.C18_10_3.row_balance

#check (@CoveringDesigns.C18_10_3.rowDeficit_le_three : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {H : Finset α},
  Fintype.card α = 18 →
    CoveringDesigns.Uniform C 10 →
      (∀ x ∉ H, CoveringDesigns.degree C x = 6) →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
          ∀ (x : CoveringDesigns.C18_10_3.Outside H), CoveringDesigns.C18_10_3.rowDeficit C H x ≤ 3)
#guard_standard_axioms CoveringDesigns.C18_10_3.rowDeficit_le_three
#print axioms CoveringDesigns.C18_10_3.rowDeficit_le_three

#check (@CoveringDesigns.C18_10_3.deficit_total_identity : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  CoveringDesigns.Uniform C 10 →
    ∀ (H : Finset α),
      (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
        ∑ x : CoveringDesigns.C18_10_3.Outside H, CoveringDesigns.C18_10_3.rowDeficit C H x +
              3 * Fintype.card (CoveringDesigns.C18_10_3.Outside H) * H.card +
            ∑ h ∈ H, ∑ g ∈ H, CoveringDesigns.degree (CoveringDesigns.star C h) g =
          10 * ∑ h ∈ H, CoveringDesigns.degree C h)
#guard_standard_axioms CoveringDesigns.C18_10_3.deficit_total_identity
#print axioms CoveringDesigns.C18_10_3.deficit_total_identity

#check (@CoveringDesigns.C18_10_3.low_zero_bound : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {H : Finset α},
  Fintype.card α = 18 →
    CoveringDesigns.Uniform C 10 →
      (∀ x ∉ H, CoveringDesigns.degree C x = 6) →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
          2 * Fintype.card (CoveringDesigns.C18_10_3.Outside H) ≤
            2 * Finset.card C +
              (Finset.univ.filter fun x : CoveringDesigns.C18_10_3.Outside H => CoveringDesigns.C18_10_3.rowDeficit C H x = 0).card)
#guard_standard_axioms CoveringDesigns.C18_10_3.low_zero_bound
#print axioms CoveringDesigns.C18_10_3.low_zero_bound

#check (@CoveringDesigns.lower_bound_18_10_3 : ∀ {α : Type u_1} [inst : Fintype α] {C : CoveringDesigns.Family α},
  Fintype.card α = 18 → CoveringDesigns.IsCover C 10 3 → 12 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.lower_bound_18_10_3
#print axioms CoveringDesigns.lower_bound_18_10_3

#check (@CoveringDesigns.indexed_lower_bound_18_10_3 : ∀ {α : Type u_1} {ι : Type u_2} [inst : Fintype α] [inst_1 : Fintype ι]
  (B : ι → Finset α),
  Fintype.card α = 18 →
    (∀ (i : ι), (B i).card = 10) → (∀ (T : Finset α), T.card = 3 → ∃ (i : ι), T ⊆ B i) → 12 ≤ Fintype.card ι)
#guard_standard_axioms CoveringDesigns.indexed_lower_bound_18_10_3
#print axioms CoveringDesigns.indexed_lower_bound_18_10_3

#check (@CoveringDesigns.C18_10_3.deficit_zero_budget : ∀ {ι : Type u_1} [inst : Fintype ι] [DecidableEq ι] (δ : ι → ℕ)
  (cap : ℕ), (∀ (i : ι), δ i ≤ cap) → ∑ i : ι, δ i + cap * (Finset.univ.filter fun i : ι => δ i = 0).card ≤ cap * Fintype.card ι)
#guard_standard_axioms CoveringDesigns.C18_10_3.deficit_zero_budget
#print axioms CoveringDesigns.C18_10_3.deficit_zero_budget

#check (@CoveringDesigns.C18_10_3.one_high_impossible : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
          ∀ {h : α}, CoveringDesigns.degree C h = 8 → (∀ (x : α), x ≠ h → CoveringDesigns.degree C x = 6) → False)
#guard_standard_axioms CoveringDesigns.C18_10_3.one_high_impossible
#print axioms CoveringDesigns.C18_10_3.one_high_impossible

#check (@CoveringDesigns.C18_10_3.high_supports_equal : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  {C : CoveringDesigns.Family α} {h g : α},
  CoveringDesigns.degree C h = 7 →
    CoveringDesigns.degree C g = 7 →
      CoveringDesigns.degree (CoveringDesigns.star C h) g = 7 → CoveringDesigns.star C h = CoveringDesigns.star C g)
#guard_standard_axioms CoveringDesigns.C18_10_3.high_supports_equal
#print axioms CoveringDesigns.C18_10_3.high_supports_equal

#check (@CoveringDesigns.C18_10_3.two_high_deficit_total : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.Uniform C 10 →
      (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
        ∀ {h g : α},
          h ≠ g →
            CoveringDesigns.degree C h = 7 →
              CoveringDesigns.degree C g = 7 →
                ∑ x : CoveringDesigns.C18_10_3.Outside {h, g}, CoveringDesigns.C18_10_3.rowDeficit C {h, g} x +
                    2 * CoveringDesigns.degree (CoveringDesigns.star C h) g =
                  30)
#guard_standard_axioms CoveringDesigns.C18_10_3.two_high_deficit_total
#print axioms CoveringDesigns.C18_10_3.two_high_deficit_total

#check (@CoveringDesigns.C18_10_3.high_seven_deficits : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.Uniform C 10 →
      (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
        ∀ {h g : α},
          h ≠ g →
            CoveringDesigns.degree C h = 7 →
              CoveringDesigns.degree C g = 7 →
                (∀ x ∉ ({h, g} : Finset α), CoveringDesigns.degree C x = 6) →
                  CoveringDesigns.degree (CoveringDesigns.star C h) g = 7 →
                    CoveringDesigns.star C h = CoveringDesigns.star C g ∧
                      ∀ (x : CoveringDesigns.C18_10_3.Outside {h, g}),
                        CoveringDesigns.C18_10_3.rowDeficit C {h, g} x =
                            2 * (CoveringDesigns.degree (CoveringDesigns.star C ↑x) h - 3) ∧
                          CoveringDesigns.C18_10_3.rowDeficit C {h, g} x ≤ 2)
#guard_standard_axioms CoveringDesigns.C18_10_3.high_seven_deficits
#print axioms CoveringDesigns.C18_10_3.high_seven_deficits

#check (@CoveringDesigns.C18_10_3.high_pair_eq_six : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
          ∀ {h g : α},
            h ≠ g →
              CoveringDesigns.degree C h = 7 →
                CoveringDesigns.degree C g = 7 →
                  (∀ x ∉ ({h, g} : Finset α), CoveringDesigns.degree C x = 6) →
                    CoveringDesigns.degree (CoveringDesigns.star C h) g = 6)
#guard_standard_axioms CoveringDesigns.C18_10_3.high_pair_eq_six
#print axioms CoveringDesigns.C18_10_3.high_pair_eq_six

#check (@CoveringDesigns.C18_10_3.saturated_degree_sum : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 →
        ∀ {p q : α},
          p ≠ q →
            CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 →
              CoveringDesigns.degree C p + CoveringDesigns.degree C q ≤ 13)
#guard_standard_axioms CoveringDesigns.C18_10_3.saturated_degree_sum
#print axioms CoveringDesigns.C18_10_3.saturated_degree_sum

#check (@CoveringDesigns.C18_10_3.saturated_low_endpoint : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 →
        ∀ {p q : α},
          p ≠ q →
            CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 →
              CoveringDesigns.degree C p = 6 ∨ CoveringDesigns.degree C q = 6)
#guard_standard_axioms CoveringDesigns.C18_10_3.saturated_low_endpoint
#print axioms CoveringDesigns.C18_10_3.saturated_low_endpoint

#check (@CoveringDesigns.C18_10_3.saturated_local : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 →
        ∀ {p q : α},
          p ≠ q →
            CoveringDesigns.degree C q = 6 →
              CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 →
                CoveringDesigns.degree C p = 6 ∧
                  (∀ (z : α), z ≠ p → z ≠ q → CoveringDesigns.degree (CoveringDesigns.star C q) z ≠ 2) ∧
                    ∃ B ∈ C,
                      ∃ D ∈ C,
                        B ≠ D ∧
                          CoveringDesigns.star (CoveringDesigns.star C p) q = {B, D} ∧
                            B ∪ D = Finset.univ ∧
                              B ∩ D = {p, q} ∧
                                7 ≤
                                  {z ∈ (B \ {p, q}) ×ˢ (D \ {p, q}) |
                                      CoveringDesigns.degree (CoveringDesigns.star C z.1) z.2 = 2}.card)
#guard_standard_axioms CoveringDesigns.C18_10_3.saturated_local
#print axioms CoveringDesigns.C18_10_3.saturated_local

#check (@CoveringDesigns.C18_10_3.pair_filter : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (p q : α), {B ∈ C | {p, q} ⊆ B} = CoveringDesigns.star (CoveringDesigns.star C p) q)
#guard_standard_axioms CoveringDesigns.C18_10_3.pair_filter
#print axioms CoveringDesigns.C18_10_3.pair_filter

#check (@CoveringDesigns.C18_10_3.mem_saturatedEdges_pair : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (C : CoveringDesigns.Family α) {p q : α},
  p ≠ q → ({p, q} ∈ CoveringDesigns.C18_10_3.saturatedEdges C ↔ CoveringDesigns.degree (CoveringDesigns.star C p) q = 2))
#guard_standard_axioms CoveringDesigns.C18_10_3.mem_saturatedEdges_pair
#print axioms CoveringDesigns.C18_10_3.mem_saturatedEdges_pair

#check (@CoveringDesigns.C18_10_3.edge_cases : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {e : Finset α},
  e ∈ CoveringDesigns.C18_10_3.saturatedEdges C →
    ∃ (p : α) (q : α), p ≠ q ∧ e = {p, q} ∧ CoveringDesigns.degree (CoveringDesigns.star C p) q = 2)
#guard_standard_axioms CoveringDesigns.C18_10_3.edge_cases
#print axioms CoveringDesigns.C18_10_3.edge_cases

#check (@CoveringDesigns.C18_10_3.edge_partner : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α} {e : Finset α},
  e ∈ CoveringDesigns.C18_10_3.saturatedEdges C →
    ∀ {p : α}, p ∈ e → ∃ (q : α), p ≠ q ∧ e = {p, q} ∧ CoveringDesigns.degree (CoveringDesigns.star C p) q = 2)
#guard_standard_axioms CoveringDesigns.C18_10_3.edge_partner
#print axioms CoveringDesigns.C18_10_3.edge_partner

#check (@CoveringDesigns.C18_10_3.saturated_endpoints : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 →
        ∀ {p q : α},
          p ≠ q →
            CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 →
              CoveringDesigns.degree C p = 6 ∧ CoveringDesigns.degree C q = 6)
#guard_standard_axioms CoveringDesigns.C18_10_3.saturated_endpoints
#print axioms CoveringDesigns.C18_10_3.saturated_endpoints

#check (@CoveringDesigns.C18_10_3.saturated_no_second : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 →
        ∀ {p q : α},
          p ≠ q →
            CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 →
              ∀ (z : α), z ≠ p → z ≠ q → CoveringDesigns.degree (CoveringDesigns.star C p) z ≠ 2)
#guard_standard_axioms CoveringDesigns.C18_10_3.saturated_no_second
#print axioms CoveringDesigns.C18_10_3.saturated_no_second

#check (@CoveringDesigns.C18_10_3.edges_disjoint : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 → (↑(CoveringDesigns.C18_10_3.saturatedEdges C) : Set (Finset α)).PairwiseDisjoint id)
#guard_standard_axioms CoveringDesigns.C18_10_3.edges_disjoint
#print axioms CoveringDesigns.C18_10_3.edges_disjoint

#check (@CoveringDesigns.C18_10_3.edges_card_le_eight : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 → Finset.card C = 11 → (CoveringDesigns.C18_10_3.saturatedEdges C).card ≤ 8)
#guard_standard_axioms CoveringDesigns.C18_10_3.edges_card_le_eight
#print axioms CoveringDesigns.C18_10_3.edges_card_le_eight

#check (@CoveringDesigns.C18_10_3.all_other_edges_cross : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 →
        ∀ {p q : α},
          p ≠ q →
            CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 →
              ∀ {B D : Finset α},
                B ∈ C →
                  D ∈ C →
                    B ∪ D = Finset.univ →
                      B ∩ D = {p, q} →
                        7 ≤
                            {z ∈ (B \ {p, q}) ×ˢ (D \ {p, q}) |
                                CoveringDesigns.degree (CoveringDesigns.star C z.1) z.2 = 2}.card →
                          (CoveringDesigns.C18_10_3.saturatedEdges C).card = 8 ∧
                            ∀ e ∈ CoveringDesigns.C18_10_3.saturatedEdges C,
                              e ≠ {p, q} → ∃ x ∈ B \ {p, q}, ∃ y ∈ D \ {p, q}, e = {x, y})
#guard_standard_axioms CoveringDesigns.C18_10_3.all_other_edges_cross
#print axioms CoveringDesigns.C18_10_3.all_other_edges_cross

#check (@CoveringDesigns.C18_10_3.supporting_index_unique : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 →
        ∀ A ∈ C,
          ∀ e ∈ CoveringDesigns.C18_10_3.saturatedEdges C,
            ∀ f ∈ CoveringDesigns.C18_10_3.saturatedEdges C, e ⊆ A → f ⊆ A → e = f)
#guard_standard_axioms CoveringDesigns.C18_10_3.supporting_index_unique
#print axioms CoveringDesigns.C18_10_3.supporting_index_unique

#check (@CoveringDesigns.C18_10_3.no_saturated_pair : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 → ∀ {p q : α}, p ≠ q → CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 → False)
#guard_standard_axioms CoveringDesigns.C18_10_3.no_saturated_pair
#print axioms CoveringDesigns.C18_10_3.no_saturated_pair

#check (@CoveringDesigns.C18_10_3.pair_ge_three : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {C : CoveringDesigns.Family α},
  Fintype.card α = 18 →
    CoveringDesigns.IsCover C 10 3 →
      Finset.card C = 11 → ∀ (p q : α), p ≠ q → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C p) q)
#guard_standard_axioms CoveringDesigns.C18_10_3.pair_ge_three
#print axioms CoveringDesigns.C18_10_3.pair_ge_three

#check (@CoveringDesigns.knownBlocks12_18_10_3_distinct : CoveringDesigns.knownBlocks12_18_10_3.Nodup)
#guard_standard_axioms CoveringDesigns.knownBlocks12_18_10_3_distinct
#print axioms CoveringDesigns.knownBlocks12_18_10_3_distinct

#check (@CoveringDesigns.knownCover12_18_10_3_card : Finset.card CoveringDesigns.knownCover12_18_10_3 = 12)
#guard_standard_axioms CoveringDesigns.knownCover12_18_10_3_card
#print axioms CoveringDesigns.knownCover12_18_10_3_card

#check (@CoveringDesigns.knownCover12_18_10_3_uniform : CoveringDesigns.Uniform CoveringDesigns.knownCover12_18_10_3 10)
#guard_standard_axioms CoveringDesigns.knownCover12_18_10_3_uniform
#print axioms CoveringDesigns.knownCover12_18_10_3_uniform

#check (@CoveringDesigns.knownCover12_18_10_3_covers : CoveringDesigns.Covers CoveringDesigns.knownCover12_18_10_3 3)
#guard_standard_axioms CoveringDesigns.knownCover12_18_10_3_covers
#print axioms CoveringDesigns.knownCover12_18_10_3_covers

#check (@CoveringDesigns.knownCover12_18_10_3_isCover : CoveringDesigns.IsCover CoveringDesigns.knownCover12_18_10_3 10 3)
#guard_standard_axioms CoveringDesigns.knownCover12_18_10_3_isCover
#print axioms CoveringDesigns.knownCover12_18_10_3_isCover

#check (@CoveringDesigns.upper_bound_18_10_3 : ∃ (C : CoveringDesigns.Family (Fin 18)),
  CoveringDesigns.IsCover C 10 3 ∧ Finset.card C = 12)
#guard_standard_axioms CoveringDesigns.upper_bound_18_10_3
#print axioms CoveringDesigns.upper_bound_18_10_3

#check (@CoveringDesigns.knownCover12_18_10_3_on_card : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (hv : Fintype.card α = 18), Finset.card (CoveringDesigns.knownCover12_18_10_3_on hv) = 12)
#guard_standard_axioms CoveringDesigns.knownCover12_18_10_3_on_card
#print axioms CoveringDesigns.knownCover12_18_10_3_on_card

#check (@CoveringDesigns.knownCover12_18_10_3_on_isCover : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  (hv : Fintype.card α = 18), CoveringDesigns.IsCover (CoveringDesigns.knownCover12_18_10_3_on hv) 10 3)
#guard_standard_axioms CoveringDesigns.knownCover12_18_10_3_on_isCover
#print axioms CoveringDesigns.knownCover12_18_10_3_on_isCover

#check (@CoveringDesigns.upper_bound_18_10_3_on : ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α],
  Fintype.card α = 18 → ∃ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 10 3 ∧ Finset.card C = 12)
#guard_standard_axioms CoveringDesigns.upper_bound_18_10_3_on
#print axioms CoveringDesigns.upper_bound_18_10_3_on

#check (@CoveringDesigns.covering_number_18_10_3_on : ∀ {α : Type u_1} [inst : Fintype α],
  Fintype.card α = 18 →
    (∃ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 10 3 ∧ Finset.card C = 12) ∧
      ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 10 3 → 12 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.covering_number_18_10_3_on
#print axioms CoveringDesigns.covering_number_18_10_3_on

#check (@CoveringDesigns.covering_number_18_10_3 : (∃ (C : CoveringDesigns.Family (Fin 18)),
    CoveringDesigns.IsCover C 10 3 ∧ Finset.card C = 12) ∧
  ∀ (C : CoveringDesigns.Family (Fin 18)), CoveringDesigns.IsCover C 10 3 → 12 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.covering_number_18_10_3
#print axioms CoveringDesigns.covering_number_18_10_3

#check (@CoveringDesigns.BoundaryRank.restricted_component_pairing : ∀ {ι : Type u_1} {κ : Type u_2} [Fintype ι] [DecidableEq ι]
  [inst : Fintype κ] (G : SimpleGraph ι) (Z : Finset ι) (K : Submodule ℝ (ι → ℝ)),
  (∀ i ∈ Z, ∃ (j : ι), G.Adj i j) →
    (∀ i ∈ Z, ∀ (j : ι), G.Adj i j → j ∈ Z) →
      (∀ x ∈ K, ∀ i ∉ Z, x i = 0) →
        (∀ x ∈ K, ∀ (i j : ι), G.Adj i j → x i + x j = 0) →
          Z.card = 2 * Fintype.card κ →
            Fintype.card κ ≤ Module.finrank ℝ ↥K →
              ∃ (e : κ × Bool ≃ ↥Z), ∀ (i j : κ × Bool), G.Adj ↑(e i) ↑(e j) → i.1 = j.1)
#guard_standard_axioms CoveringDesigns.BoundaryRank.restricted_component_pairing
#print axioms CoveringDesigns.BoundaryRank.restricted_component_pairing

#check (@CoveringDesigns.BoundaryRank.restricted_kernel_pairing : ∀ {ι : Type u_1} {κ : Type u_2} [inst : Fintype ι]
  [inst_1 : DecidableEq ι] [inst_2 : Fintype κ] (ρ : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ),
  0 < ρ →
    (∀ (i j : ι), E i j = E j i) →
      (∀ (i j : ι), 0 ≤ E i j) →
        (∀ (i : ι), E i i = 0) →
          (∀ (i : ι), 0 ≤ δ i) →
            (∀ (i : ι), ∑ j : ι, E i j + δ i = ρ) →
              (∀ (i j : ι), δ i = 0 → δ j ≠ 0 → E i j = 0) →
                (Finset.univ.filter fun i : ι => δ i = 0).card = 2 * Fintype.card κ →
                  Fintype.card κ ≤ Module.finrank ℝ ↥((Matrix.diagonal fun (x : ι) => ρ) + E).mulVecLin.ker →
                    ∃ (e : κ × Bool ≃ ↥(Finset.univ.filter fun i : ι => δ i = 0)),
                      (∀ (i j : κ), i ≠ j → ∀ (b c : Bool), E ↑(e (i, b)) ↑(e (j, c)) = 0) ∧
                        ∀ (i : κ), E ↑(e (i, Bool.false)) ↑(e (i, Bool.true)) = ρ)
#guard_standard_axioms CoveringDesigns.BoundaryRank.restricted_kernel_pairing
#print axioms CoveringDesigns.BoundaryRank.restricted_kernel_pairing

#check (@CoveringDesigns.BoundaryRank.square_duality : ∀ {κ : Type u_1} [inst : Fintype κ] [inst_1 : DecidableEq κ]
  (U : Matrix κ κ ℝ) (r lam : ℝ),
  0 ≤ lam →
    lam < r →
      0 < Fintype.card κ →
        (∀ (i : κ), ∑ j : κ, U i j = r) →
          (U * U.transpose = (Matrix.diagonal fun (x : κ) => r - lam) + Matrix.of fun (x x_1 : κ) => lam) →
            U.det ≠ 0 ∧
              U⁻¹ * U = 1 ∧
                U * U⁻¹ = 1 ∧
                  (∀ (j : κ), ∑ i : κ, U i j = r) ∧
                    U.transpose * U = (Matrix.diagonal fun (x : κ) => r - lam) + Matrix.of fun (x x_1 : κ) => lam)
#guard_standard_axioms CoveringDesigns.BoundaryRank.square_duality
#print axioms CoveringDesigns.BoundaryRank.square_duality

#check (@CoveringDesigns.BoundaryRank.binary_sum : ∀ {κ : Type u_1} [inst : Fintype κ] [DecidableEq κ] (f : κ → ℝ),
  (∀ (j : κ), f j = 0 ∨ f j = 1) → ∑ j : κ, f j = ↑(CoveringDesigns.BoundaryRank.binarySupport f).card)
#guard_standard_axioms CoveringDesigns.BoundaryRank.binary_sum
#print axioms CoveringDesigns.BoundaryRank.binary_sum

#check (@CoveringDesigns.BoundaryRank.binary_dot : ∀ {κ : Type u_1} [inst : Fintype κ] [inst_1 : DecidableEq κ] (f g : κ → ℝ),
  (∀ (j : κ), f j = 0 ∨ f j = 1) →
    (∀ (j : κ), g j = 0 ∨ g j = 1) →
      ∑ j : κ, f j * g j =
        ↑(CoveringDesigns.BoundaryRank.binarySupport f ∩ CoveringDesigns.BoundaryRank.binarySupport g).card)
#guard_standard_axioms CoveringDesigns.BoundaryRank.binary_dot
#print axioms CoveringDesigns.BoundaryRank.binary_dot

#check (@CoveringDesigns.BoundaryRank.two_zero_rows : ∀ {κ : Type u_1} [inst : Fintype κ] [inst_1 : DecidableEq κ]
  (U : Matrix κ κ ℝ),
  Fintype.card κ = 11 →
    (∀ (i j : κ), U i j = 0 ∨ U i j = 1) →
      (∀ (i : κ), ∑ j : κ, U i j = 6) →
        (U * U.transpose = (Matrix.diagonal fun (x : κ) => 3) + Matrix.of fun (x x_1 : κ) => 3) →
          ∀ {a b : κ},
            a ≠ b →
              (Finset.univ.filter fun i : κ => U i a = 0 ∧ U i b = 0).card = 2 ∧
                ∃ (x : κ) (y : κ),
                  x ≠ y ∧
                    U x a = 0 ∧
                      U x b = 0 ∧
                        U y a = 0 ∧
                          U y b = 0 ∧
                            CoveringDesigns.BoundaryRank.binarySupport (U x) ∪
                                CoveringDesigns.BoundaryRank.binarySupport (U y) =
                              Finset.univ \ {a, b})
#guard_standard_axioms CoveringDesigns.BoundaryRank.two_zero_rows
#print axioms CoveringDesigns.BoundaryRank.two_zero_rows

#check (@CoveringDesigns.BoundaryRank.exceptional_support : ∀ {κ : Type u_1} [inst : Fintype κ] [inst_1 : DecidableEq κ]
  (U : Matrix κ κ ℝ),
  Fintype.card κ = 11 →
    (∀ (i j : κ), U i j = 0 ∨ U i j = 1) →
      (∀ (i : κ), ∑ j : κ, U i j = 6) →
        (U * U.transpose = (Matrix.diagonal fun (x : κ) => 3) + Matrix.of fun (x x_1 : κ) => 3) →
          ∀ {a b : κ},
            a ≠ b →
              ∀ (H : Finset κ),
                H.card = 7 →
                  (H ∩ {a, b}).card = 1 →
                    (∀ (i : κ),
                        U i a = 0 → U i b = 0 → (H ∩ CoveringDesigns.BoundaryRank.binarySupport (U i)).card ≤ 3) →
                      ∃ (x : κ) (y : κ),
                        x ≠ y ∧
                          H ∩ CoveringDesigns.BoundaryRank.binarySupport (U x) ∩
                              CoveringDesigns.BoundaryRank.binarySupport (U y) =
                            ∅)
#guard_standard_axioms CoveringDesigns.BoundaryRank.exceptional_support
#print axioms CoveringDesigns.BoundaryRank.exceptional_support

#check (@CoveringDesigns.SupportObstruction.intersection_identity : ∀ {ι : Type u_1} [inst : DecidableEq ι]
  (I A H S T : Finset ι), H ⊆ I → S ∪ T = I \ A → (H ∩ S ∩ T).card + H.card = (H ∩ S).card + (H ∩ T).card + (H ∩ A).card)
#guard_standard_axioms CoveringDesigns.SupportObstruction.intersection_identity
#print axioms CoveringDesigns.SupportObstruction.intersection_identity

#check (@CoveringDesigns.SupportObstruction.empty_of_intersection_bound : ∀ {ι : Type u_1} [inst : DecidableEq ι]
  (I A H S T : Finset ι), H ⊆ I → S ∪ T = I \ A → (H ∩ S).card + (H ∩ T).card + (H ∩ A).card ≤ H.card → H ∩ S ∩ T = ∅)
#guard_standard_axioms CoveringDesigns.SupportObstruction.empty_of_intersection_bound
#print axioms CoveringDesigns.SupportObstruction.empty_of_intersection_bound

#check (@CoveringDesigns.SupportObstruction.uncovered_triple : ∀ {ι : Type u_1} {α : Type u_2} [inst : DecidableEq ι]
  [inst_1 : Fintype ι] [inst_2 : DecidableEq α] (B : ι → Finset α) (h x y : α),
  h ≠ x →
    h ≠ y →
      x ≠ y →
        (Finset.univ.filter fun i : ι => h ∈ B i) ∩ (Finset.univ.filter fun i : ι => x ∈ B i) ∩ (Finset.univ.filter fun i : ι => y ∈ B i) = ∅ →
          (∀ (T : Finset α), T.card = 3 → ∃ (i : ι), T ⊆ B i) → False)
#guard_standard_axioms CoveringDesigns.SupportObstruction.uncovered_triple
#print axioms CoveringDesigns.SupportObstruction.uncovered_triple

#check (@CoveringDesigns.SupportObstruction.single_differences : ∀ {ι : Type u_1} [inst : DecidableEq ι] (H G : Finset ι)
  (n : ℕ),
  H.card = n + 1 →
    G.card = n + 1 →
      (H ∩ G).card = n →
        ∃ (a : ι) (b : ι), a ≠ b ∧ H \ G = {a} ∧ G \ H = {b} ∧ a ∈ H ∧ a ∉ G ∧ b ∈ G ∧ b ∉ H ∧ (H ∩ {a, b}).card = 1)
#guard_standard_axioms CoveringDesigns.SupportObstruction.single_differences
#print axioms CoveringDesigns.SupportObstruction.single_differences

#check (@CoveringDesigns.SupportObstruction.intersections_eq_of_agree : ∀ {ι : Type u_1} [inst : DecidableEq ι]
  (H G S : Finset ι) {a b : ι}, H \ G = {a} → G \ H = {b} → (a ∈ S ↔ b ∈ S) → (S ∩ H).card = (S ∩ G).card)
#guard_standard_axioms CoveringDesigns.SupportObstruction.intersections_eq_of_agree
#print axioms CoveringDesigns.SupportObstruction.intersections_eq_of_agree

#check (@CoveringDesigns.SupportObstruction.empty_of_subtraction_bound : ∀ {ι : Type u_1} [inst : DecidableEq ι]
  (I A H S T : Finset ι), H ⊆ I → S ∪ T = I \ A → (H ∩ S).card + (H ∩ T).card ≤ H.card - (H ∩ A).card → H ∩ S ∩ T = ∅)
#guard_standard_axioms CoveringDesigns.SupportObstruction.empty_of_subtraction_bound
#print axioms CoveringDesigns.SupportObstruction.empty_of_subtraction_bound

#check (@CoveringDesigns.IncidencePacking.packing : ∀ {ε : Type u_1} {ι : Type u_2} [DecidableEq ε] [DecidableEq ι]
  (M : Finset ε) (I : Finset ι) (S : ε → ι → Prop) [inst : DecidableRel S] (r : ℕ),
  (∀ e ∈ M, (Finset.filter (S e) I).card = r) → (∀ i ∈ I, ∀ e ∈ M, ∀ f ∈ M, S e i → S f i → e = f) → r * M.card ≤ I.card)
#guard_standard_axioms CoveringDesigns.IncidencePacking.packing
#print axioms CoveringDesigns.IncidencePacking.packing

#guard_standard_axioms CoveringDesigns.Audit18_10_3.covering_number_explicit
#print axioms CoveringDesigns.Audit18_10_3.covering_number_explicit
#guard_standard_axioms CoveringDesigns.Audit18_10_3.indexed_explicit
#print axioms CoveringDesigns.Audit18_10_3.indexed_explicit

#check (@CoveringDesigns.SupportObstruction.exceptional_count : ∀ {ι : Type u_1} [DecidableEq ι]
    (H G S : Finset ι) {a b : ι}
    (ha : H \ G = {a}) (hb : G \ H = {b}),
    (S ∩ H).card + (S ∩ G).card =
      2 * (S ∩ H ∩ G).card + (if a ∈ S then 1 else 0) +
        (if b ∈ S then 1 else 0))
#guard_standard_axioms CoveringDesigns.SupportObstruction.exceptional_count
#print axioms CoveringDesigns.SupportObstruction.exceptional_count

#check (@CoveringDesigns.SupportObstruction.paired_support_obstruction : ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    (H G : Finset ι)
    (P : Fin 5 → Finset ι) (Q : Fin 6 → Finset ι)
    (hc : Fintype.card ι = 11)
    (hH : H.card = 7) (hG : G.card = 7) (hHG : (H ∩ G).card = 6)
    (hP : ∀ i, (P i).card = 6)
    (hPH : ∀ i, (P i ∩ H).card = 3) (hPG : ∀ i, (P i ∩ G).card = 3)
    (hPQ : ∀ i, (Q i ∩ H).card + (Q i ∩ G).card = 9)
    (hcross : ∀ i j, i ≠ j → (P i ∩ P j).card = 3)
    (hcol : ∀ c, (if c ∈ H then 1 else 0) + (if c ∈ G then 1 else 0) +
      2 * (∑ i, if c ∈ P i then 1 else 0) + (∑ i, if c ∈ Q i then 1 else 0) = 10),
    ∃ i j, i ≠ j ∧ H ∩ P i ∩ P j = ∅)
#guard_standard_axioms CoveringDesigns.SupportObstruction.paired_support_obstruction
#print axioms CoveringDesigns.SupportObstruction.paired_support_obstruction
