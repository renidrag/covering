import CoveringDesigns.C20_11_3

open CoveringDesigns CoveringDesigns.C20_11_3 CoveringDesigns.BoundaryRank
open Finset Matrix Module

set_option linter.unusedVariables false

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.star
#print CoveringDesigns.degree
#print CoveringDesigns.knownCover12_20_11_3
#print CoveringDesigns.knownCover12_20_11_3_on
#print CoveringDesigns.C20_11_3.lowIncidence
#print CoveringDesigns.C20_11_3.lowExcess
#print CoveringDesigns.C20_11_3.highDeficit
#print CoveringDesigns.C20_11_3.onlyBlocks
#print CoveringDesigns.C20_11_3.neitherBlocks
#print CoveringDesigns.BoundaryRank.supportGraph

namespace CoveringDesigns.Audit20_11_3

/-- Exactness with ordinary distinct blocks and all covering conditions exposed. -/
theorem covering_number_explicit {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 20) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 11) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 12) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 11) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 12 ≤ C.card) := by
  obtain ⟨⟨C, hC, hcard⟩, hlower⟩ := covering_number_20_11_3_on hv
  exact ⟨⟨C, hC.1, hC.2, hcard⟩, fun C hu hc => hlower C ⟨hu, hc⟩⟩

end CoveringDesigns.Audit20_11_3

-- Complete public contracts, including every public helper theorem.
-- No rank, degree, saturation or existence premise is added to the public
-- lower-bound or exactness contracts.

-- BoundaryRank/Signless.lean

#check (@CoveringDesigns.BoundaryRank.signless_sum_squares : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ δ : ι → ℝ) (E : Matrix ι ι ℝ)
    (hs : ∀ i j, E i j = E j i)
    (hrow : ∀ i, (∑ j, E i j) + δ i = ρ i) (x : ι → ℝ),
    Star.star x ⬝ᵥ ((Matrix.diagonal ρ + E) *ᵥ x) =
      (∑ i, δ i * (x i)^2) +
        (∑ i, ∑ j, E i j * (x i + x j)^2) / 2)

#check (@CoveringDesigns.BoundaryRank.signless_posSemidef : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ δ : ι → ℝ) (E : Matrix ι ι ℝ)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ i),
    (Matrix.diagonal ρ + E).PosSemidef)

#check (@CoveringDesigns.BoundaryRank.kernel_restrictions : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ δ : ι → ℝ) (E : Matrix ι ι ℝ)
    (hs : ∀ i j, E i j = E j i) (hn : ∀ i j, 0 ≤ E i j)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ i)
    {x : ι → ℝ} (hx : (Matrix.diagonal ρ + E) *ᵥ x = 0),
    (∀ i, 0 < δ i → x i = 0) ∧ (∀ i j, 0 < E i j → x i + x j = 0))

#check (@CoveringDesigns.BoundaryRank.kernel_of_restrictions : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ δ : ι → ℝ) (E : Matrix ι ι ℝ)
    (hn : ∀ i j, 0 ≤ E i j) (hδ : ∀ i, 0 ≤ δ i)
    (hrow : ∀ i, (∑ j, E i j) + δ i = ρ i)
    {x : ι → ℝ} (hd : ∀ i, 0 < δ i → x i = 0)
    (he : ∀ i j, 0 < E i j → x i + x j = 0),
    (Matrix.diagonal ρ + E) *ᵥ x = 0)

#check (@CoveringDesigns.BoundaryRank.ker_add_le_of_posSemidef : ∀ {ι : Type*} [Fintype ι] {A P : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hP : P.PosSemidef),
    LinearMap.ker (A + P).mulVecLin ≤ LinearMap.ker A.mulVecLin)

-- BoundaryRank/Nullity.lean

#check (@CoveringDesigns.BoundaryRank.two_mul_finrank_le_card_of_component_constraints : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) (Z : Finset ι) (K : Submodule ℝ (ι → ℝ))
    (hneigh : ∀ i ∈ Z, ∃ j, G.Adj i j)
    (hzero : ∀ x ∈ K, ∀ i, i ∉ Z → x i = 0)
    (hedge : ∀ x ∈ K, ∀ i j, G.Adj i j → x i + x j = 0),
    2 * finrank ℝ K ≤ Z.card)

set_option maxHeartbeats 2000000 in
#check (@CoveringDesigns.BoundaryRank.two_mul_nullity_le_zero_count : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ),
    2 * finrank ℝ (LinearMap.ker (Matrix.diagonal (fun _ : ι => ρ) + E).mulVecLin) ≤
      (univ.filter fun i => δ i = 0).card)

#check (@CoveringDesigns.BoundaryRank.gram_card_bound : ∀ {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (R : Matrix ι κ ℝ) (ρ : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ)
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    (hgram : R * R.transpose = Matrix.diagonal (fun _ => ρ) + E + P),
    2 * Fintype.card ι ≤ 2 * Fintype.card κ + (univ.filter fun i => δ i = 0).card)

-- C20_11_3/Incidence.lean

#check (@CoveringDesigns.C20_11_3.pair_sum : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {k : ℕ} (hu : Uniform C k) (p : α),
    (∑ q ∈ univ.erase p, degree (star C p) q) = (k - 1) * degree C p)

#check (@CoveringDesigns.C20_11_3.pair_sum_subtype : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {k : ℕ} (hu : Uniform C k) (p : α),
    (∑ q : {q : α // q ≠ p}, degree (star C p) q.val) =
      (k - 1) * degree C p)

#check (@CoveringDesigns.C20_11_3.cross_pair_degree_sum : ∀ {α : Type*} [Fintype α] [DecidableEq α] (C : Family α) (X Y : Finset α),
    (∑ x ∈ X, ∑ y ∈ Y, degree (star C x) y) =
      ∑ B ∈ C, (X ∩ B).card * (Y ∩ B).card)

#check (@CoveringDesigns.C20_11_3.cross_pair_coverage_bound : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {X Y : Finset α}
    (hcover : ∀ x ∈ X, ∀ y ∈ Y, ∃ B ∈ C, x ∈ B ∧ y ∈ B),
    X.card * Y.card ≤ ∑ B ∈ C, (X ∩ B).card * (Y ∩ B).card)

#check (@CoveringDesigns.C20_11_3.mul_le_twenty_five : ∀ {a b : ℕ} (h : a + b ≤ 10),
    a * b ≤ 25)

#check (@CoveringDesigns.C20_11_3.cross_capacity_ten : ∀ {α : Type*} [Fintype α] [DecidableEq α] (X Y B : Finset α) (hXY : Disjoint X Y)
    (hB : B.card ≤ 10),
    (X ∩ B).card * (Y ∩ B).card ≤ 25)

#check (@CoveringDesigns.C20_11_3.lower_bound_19_10_2 : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} (hv : Fintype.card α = 19)
    (hC : IsCover C 10 2),
    6 ≤ C.card)

#check (@CoveringDesigns.C20_11_3.degree_ge_six : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (p : α),
    6 ≤ degree C p)

#check (@CoveringDesigns.C20_11_3.eleven_le_card : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3),
    11 ≤ C.card)

#check (@CoveringDesigns.C20_11_3.degree_excess_sum : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hb : C.card = 11),
    (∑ p, (degree C p - 6)) = 1)

#check (@CoveringDesigns.C20_11_3.degree_six_or_seven : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hb : C.card = 11) (p : α),
    degree C p = 6 ∨ degree C p = 7)

#check (@CoveringDesigns.C20_11_3.degree_profile : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hb : C.card = 11),
    ∃ h, degree C h = 7 ∧ ∀ x, x ≠ h → degree C x = 6)

#check (@CoveringDesigns.C20_11_3.pair_ge_two : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) {p q : α} (hpq : p ≠ q),
    2 ≤ degree (star C p) q)

-- C20_11_3/Rank.lean

#check (@CoveringDesigns.C20_11_3.low_card : ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 20) (h : α),
    Fintype.card (Low h) = 19)

#check (@CoveringDesigns.C20_11_3.lowIncidence_gram_entry : ∀ {α : Type*} [DecidableEq α] (C : Family α) (h : α) (x y : Low h),
    (lowIncidence C h * (lowIncidence C h).transpose) x y =
      (degree (star C x.val) y.val : ℝ))

#check (@CoveringDesigns.C20_11_3.low_gram : ∀ {α : Type*} [DecidableEq α] {C : Family α} {h : α}
    (hlow : ∀ x, x ≠ h → degree C x = 6),
    lowIncidence C h * (lowIncidence C h).transpose =
      Matrix.diagonal (fun _ => (3 : ℝ)) + lowExcess C h +
        Matrix.of (fun _ _ => (3 : ℝ)))

#check (@CoveringDesigns.C20_11_3.lowExcess_symm : ∀ {α : Type*} [DecidableEq α] (C : Family α) (h : α) (x y : Low h),
    lowExcess C h x y = lowExcess C h y x)

#check (@CoveringDesigns.C20_11_3.lowExcess_nonneg : ∀ {α : Type*} [DecidableEq α] {C : Family α} {h : α}
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x y : Low h),
    0 ≤ lowExcess C h x y)

#check (@CoveringDesigns.C20_11_3.lowExcess_diagonal : ∀ {α : Type*} [DecidableEq α] (C : Family α) (h : α) (x : Low h),
    lowExcess C h x x = 0)

#check (@CoveringDesigns.C20_11_3.highDeficit_nonneg : ∀ {α : Type*} [DecidableEq α] {C : Family α} {h : α}
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x : Low h),
    0 ≤ highDeficit C h x)

#check (@CoveringDesigns.C20_11_3.low_row_identity : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {h : α}
    (hv : Fintype.card α = 20) (hu : Uniform C 11)
    (hlow : ∀ x, x ≠ h → degree C x = 6) (x : Low h),
    (∑ y, lowExcess C h x y) + highDeficit C h x = 3)

#check (@CoveringDesigns.C20_11_3.high_deficit_sum : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {h : α}
    (hv : Fintype.card α = 20) (hu : Uniform C 11) (hh : degree C h = 7),
    ∑ x, highDeficit C h x = 13)

#check (@CoveringDesigns.C20_11_3.zero_card_le_fourteen : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (δ : ι → ℝ) (hc : Fintype.card ι = 19)
    (hδ : ∀ i, δ i ≤ 3) (hs : ∑ i, δ i = 13),
    (univ.filter (fun i => δ i = 0)).card ≤ 14)

#check (@CoveringDesigns.C20_11_3.highDeficit_zero_card_le : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {h : α}
    (hv : Fintype.card α = 20) (hu : Uniform C 11)
    (hlow : ∀ x, x ≠ h → degree C x = 6) (hh : degree C h = 7)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y),
    (univ.filter (fun x : Low h => highDeficit C h x = 0)).card ≤ 14)

#check (@CoveringDesigns.C20_11_3.three_ones_posSemidef : ∀ {ι : Type*} [Fintype ι],
    Matrix.PosSemidef (Matrix.of (fun (_ _ : ι) => (3 : ℝ))))

#check (@CoveringDesigns.C20_11_3.low_gram_rank_ge_twelve : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {h : α}
    (hv : Fintype.card α = 20) (hu : Uniform C 11)
    (hlow : ∀ x, x ≠ h → degree C x = 6) (hh : degree C h = 7)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y),
    12 ≤ (lowIncidence C h * (lowIncidence C h).transpose).rank)

#check (@CoveringDesigns.C20_11_3.exists_saturated_pair : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}
    (hv : Fintype.card α = 20) (hC : IsCover C 11 3) (hb : C.card = 11),
    ∃ p q : α, p ≠ q ∧ degree (star C p) q = 2)

-- C20_11_3/SaturatedGeometry.lean

#check (@CoveringDesigns.C20_11_3.saturated_pair_star_eq : ∀ {α : Type*} [DecidableEq α] {C : Family α} {p q : α} {B D : Finset α} (hsat : degree (star C p) q = 2)
    (hB : B ∈ star (star C p) q) (hD : D ∈ star (star C p) q)
    (hBD : B ≠ D),
    star (star C p) q = {B, D})

#check (@CoveringDesigns.C20_11_3.saturated_pair_union : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {p q : α} {B D : Finset α} (hC : Covers C 3) (hpq : p ≠ q)
    (hstar : star (star C p) q = {B, D}),
    B ∪ D = univ)

#check (@CoveringDesigns.C20_11_3.saturated_pair_inter : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {p q : α} {B D : Finset α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q)
    (hstar : star (star C p) q = {B, D}),
    B ∩ D = {p, q})

#check (@CoveringDesigns.C20_11_3.saturated_pair_blocks : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {p q : α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2),
    ∃ B ∈ C, ∃ D ∈ C, B ≠ D ∧ star (star C p) q = {B, D} ∧
      B ∪ D = univ ∧ B ∩ D = {p, q})

#check (@CoveringDesigns.C20_11_3.saturated_pair_geometry : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {p q : α} {B D : Finset α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2)
    (hBC : B ∈ C) (hDC : D ∈ C) (hBD : B ≠ D)
    (hpB : p ∈ B) (hqB : q ∈ B) (hpD : p ∈ D) (hqD : q ∈ D),
    B ∪ D = univ ∧ B ∩ D = {p, q})

#check (@CoveringDesigns.C20_11_3.saturated_partner_of_mem : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {p q : α} {B : Finset α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2)
    (hBC : B ∈ C) (hpB : p ∈ B) (hqB : q ∈ B),
    ∃ D ∈ C, D ≠ B ∧ B ∪ D = univ ∧ B ∩ D = {p, q})

#check (@CoveringDesigns.C20_11_3.other_block_eq_complement : ∀ {α : Type*} [Fintype α] [DecidableEq α] {p q : α} {B D : Finset α} (hunion : B ∪ D = univ)
    (hinter : B ∩ D = {p, q}),
    D = (univ \ B) ∪ {p, q})

#check (@CoveringDesigns.C20_11_3.saturated_partner_eq_complement : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {p q : α} {B : Finset α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2)
    (hBC : B ∈ C) (hpB : p ∈ B) (hqB : q ∈ B),
    let D := (univ \ B) ∪ {p, q}
    D ∈ C ∧ D ≠ B ∧ B ∪ D = univ ∧ B ∩ D = {p, q} ∧
      ∀ E ∈ C, E ≠ B → p ∈ E → q ∈ E → E = D)

#check (@CoveringDesigns.C20_11_3.saturated_residual_geometry : ∀ {α : Type*} [Fintype α] [DecidableEq α] {p q : α} {B D : Finset α} (hpq : p ≠ q)
    (hBcard : B.card = 11) (hDcard : D.card = 11)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p, q}),
    Disjoint (B \ {p, q}) (D \ {p, q}) ∧
      (B \ {p, q}).card = 9 ∧ (D \ {p, q}).card = 9 ∧
      (B \ {p, q}) ∪ (D \ {p, q}) = univ \ {p, q})

-- C20_11_3/SaturatedPartition.lean

#check (@CoveringDesigns.C20_11_3.mem_onlyBlocks : ∀ {α : Type*} [DecidableEq α] {C : Family α} {p q : α} {B : Finset α},
    B ∈ onlyBlocks C p q ↔ B ∈ C ∧ p ∈ B ∧ q ∉ B)

#check (@CoveringDesigns.C20_11_3.mem_neitherBlocks : ∀ {α : Type*} [DecidableEq α] {C : Family α} {p q : α} {B : Finset α},
    B ∈ neitherBlocks C p q ↔ B ∈ C ∧ p ∉ B ∧ q ∉ B)

#check (@CoveringDesigns.C20_11_3.onlyBlocks_card_add_pair : ∀ {α : Type*} [DecidableEq α] (C : Family α) (p q : α),
    (onlyBlocks C p q).card + degree (star C p) q = degree C p)

#check (@CoveringDesigns.C20_11_3.endpoint_sum_partition : ∀ {α : Type*} [DecidableEq α] (C : Family α) (p q : α) (w : Finset α → ℕ),
    (∑ B ∈ C, w B) =
      (∑ B ∈ onlyBlocks C p q, w B) +
      (∑ B ∈ onlyBlocks C q p, w B) +
      (∑ B ∈ neitherBlocks C p q, w B) +
      (∑ B ∈ star (star C p) q, w B))

#check (@CoveringDesigns.C20_11_3.endpoint_card_partition : ∀ {α : Type*} [DecidableEq α] (C : Family α) (p q : α),
    C.card = (onlyBlocks C p q).card + (onlyBlocks C q p).card +
      (neitherBlocks C p q).card + degree (star C p) q)

#check (@CoveringDesigns.C20_11_3.trace_sum : ∀ {α : Type*} [DecidableEq α] [Fintype α] {p q : α} {X Y : Finset α}
    (hdis : Disjoint X Y) (hpart : X ∪ Y = univ \ {p,q}) (B : Finset α),
    (X ∩ B).card + (Y ∩ B).card + (B ∩ {p,q}).card = B.card)

#check (@CoveringDesigns.C20_11_3.trace_sum_only : ∀ {α : Type*} [DecidableEq α] [Fintype α] {p q : α} {X Y B : Finset α}
    (hdis : Disjoint X Y) (hpart : X ∪ Y = univ \ {p,q})
    (hB : B.card = 11) (hp : p ∈ B) (hq : q ∉ B),
    (X ∩ B).card + (Y ∩ B).card = 10)

#check (@CoveringDesigns.C20_11_3.trace_sum_neither : ∀ {α : Type*} [DecidableEq α] [Fintype α] {p q : α} {X Y B : Finset α}
    (hdis : Disjoint X Y) (hpart : X ∪ Y = univ \ {p,q})
    (hB : B.card = 11) (hp : p ∉ B) (hq : q ∉ B),
    (X ∩ B).card + (Y ∩ B).card = 11)

#check (@CoveringDesigns.C20_11_3.trace_product_le : ∀ {a b : ℕ},
    (a+b = 10 → a*b ≤ 25) ∧ (a+b = 11 → a*b ≤ 30))

#check (@CoveringDesigns.C20_11_3.intersection_le_ten : ∀ {α : Type*} [DecidableEq α] {A D : Finset α} {p : α}
    (hA : A.card = 11) (hp : p ∈ A) (hpD : p ∉ D),
    (A ∩ D).card ≤ 10)

#check (@CoveringDesigns.C20_11_3.intersection_sum : ∀ {α : Type*} [DecidableEq α] (A : Finset α) (Q : Family α),
    (∑ D ∈ Q, (A ∩ D).card) = ∑ z ∈ A, degree Q z)

#check (@CoveringDesigns.C20_11_3.endpoint_degree_partition : ∀ {α : Type*} [DecidableEq α] (C : Family α) (p q z : α),
    degree (star C q) z = degree (onlyBlocks C q p) z +
      degree (star (star C p) q) z)

#check (@CoveringDesigns.C20_11_3.residual_pair_eq : ∀ {α : Type*} [DecidableEq α] [Fintype α] {p q z : α} {C : Family α} {B D : Finset α}
    (hstar : star (star C p) q = {B,D}) (hzB : z ∈ B) (hzD : z ∉ D),
    degree (star C q) z = degree (onlyBlocks C q p) z + 1)

#check (@CoveringDesigns.C20_11_3.cross_pair_eq_of_pair_eq : ∀ {α : Type*} [DecidableEq α] {X Y : Finset α} (hdis : Disjoint X Y)
    {a b : α × α} (ha : a ∈ X ×ˢ Y) (hb : b ∈ X ×ˢ Y)
    (he : ({a.1,a.2} : Finset α) = {b.1,b.2}),
    a = b)

#check (@CoveringDesigns.C20_11_3.shared_intersection_sum : ∀ {α : Type*} [DecidableEq α] {C : Family α} {p q : α} {A : Finset α}
    (hA : A.card = 11) (hpA : p ∈ A) (hqA : q ∉ A)
    (hpoint : ∀ z, z ≠ p → z ≠ q → 2 ≤ degree (onlyBlocks C q p) z),
    20 ≤ ∑ D ∈ onlyBlocks C q p, (A ∩ D).card)

-- C20_11_3/SaturatedBudget.lean

#check (@CoveringDesigns.C20_11_3.multiplicity_floor_count : ∀ {γ : Type*} (T : Finset γ) (μ : γ → ℕ)
    (hμ : ∀ t ∈ T, 2 ≤ μ t),
    3 * T.card ≤ (∑ t ∈ T, μ t) + (T.filter (μ · = 2)).card)

#check (@CoveringDesigns.C20_11_3.assignment_card_le : ∀ {β γ : Type*} [DecidableEq β] {P Q : Finset β} {T : Finset γ} (f : γ → β × β)
    (htarget : ∀ t ∈ T, (f t).1 ∈ P ∧ (f t).2 ∈ Q)
    (hinj : Set.InjOn f T),
    T.card ≤ P.card * Q.card)

#check (@CoveringDesigns.C20_11_3.capacity_bound : ∀ {β : Type*} [DecidableEq β] (P Q N : Finset β) (w : β → ℕ)
    (hP : ∀ A ∈ P, w A ≤ 25) (hQ : ∀ D ∈ Q, w D ≤ 25)
    (hN : ∀ D ∈ N, w D ≤ 30),
    (∑ A ∈ P, w A) + (∑ D ∈ Q, w D) + (∑ D ∈ N, w D) ≤
      25 * (P.card + Q.card) + 30 * N.card)

#check (@CoveringDesigns.C20_11_3.capacity_bound_loss16 : ∀ {β : Type*} [DecidableEq β] (P Q N : Finset β) (w : β → ℕ)
    (hP : ∀ A ∈ P, w A ≤ 25) (hQ : ∀ D ∈ Q, w D ≤ 25)
    (hN : ∀ D ∈ N, w D ≤ 30)
    (hloss : ∃ D ∈ Q, w D ≤ 9),
    (∑ A ∈ P, w A) + (∑ D ∈ Q, w D) + (∑ D ∈ N, w D) + 16 ≤
      25 * (P.card + Q.card) + 30 * N.card)

#check (@CoveringDesigns.C20_11_3.cross_count_lower : ∀ {n m S s : ℕ} (hparts : m + n = 5)
    (hcapacity : S ≤ 25 * (n + 4) + 30 * m) (hfloor : 243 ≤ S + s),
    5 * n - 7 ≤ s)

#check (@CoveringDesigns.C20_11_3.no_second_partner_arithmetic : ∀ {n m S s : ℕ} (hparts : m + n = 5)
    (hcapacity : S + 16 ≤ 25 * (n + 4) + 30 * m)
    (hfloor : 243 ≤ S + s) (hassignment : s ≤ 4 * n),
    False)

#check (@CoveringDesigns.C20_11_3.row_partner_bound : ∀ {β : Type*} [DecidableEq β] {Q R : Finset β} (I : β → ℕ)
    (hQ : Q.card = 4) (hRQ : R ⊆ Q)
    (hrow : 20 ≤ ∑ D ∈ Q, I D)
    (hsmall : ∀ D ∈ R, I D = 2) (hcap : ∀ D ∈ Q, I D ≤ 10),
    R.card ≤ 2)

#check (@CoveringDesigns.C20_11_3.assignment_card_le_twice : ∀ {β γ : Type*} [DecidableEq β] {P Q : Finset β} {T : Finset γ}
    (f : γ → β × β) (I : β → β → ℕ)
    (hQ : Q.card = 4)
    (htarget : ∀ t ∈ T, (f t).1 ∈ P ∧ (f t).2 ∈ Q)
    (hinj : Set.InjOn f T)
    (hrow : ∀ A ∈ P, 20 ≤ ∑ D ∈ Q, I A D)
    (hsmall : ∀ t ∈ T, I (f t).1 (f t).2 = 2)
    (hcap : ∀ A ∈ P, ∀ D ∈ Q, I A D ≤ 10),
    T.card ≤ 2 * P.card)

#check (@CoveringDesigns.C20_11_3.final_partner_contradiction : ∀ {n s : ℕ} (hn : n = 4 ∨ n = 5)
    (hlower : 5 * n - 7 ≤ s) (hupper : s ≤ 2 * n),
    False)

-- C20_11_3/SaturatedAssignment.lean

#check (@CoveringDesigns.C20_11_3.residual_not_mem_other : ∀ {α : Type*} [DecidableEq α] {p q x : α} {B D : Finset α}
    (hinter : B ∩ D = {p,q}) (hx : x ∈ B \ {p,q}),
    x ∉ D)

#check (@CoveringDesigns.C20_11_3.cross_partner_exists : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {p q x y : α} {B D : Finset α}
    (hv : Fintype.card α = 20) (hC : IsCover C 11 3)
    (hstar : star (star C p) q = {B,D}) (hinter : B ∩ D = {p,q})
    (hx : x ∈ B \ {p,q}) (hy : y ∈ D \ {p,q})
    (hsat : degree (star C x) y = 2),
    ∃ A ∈ onlyBlocks C p q, ∃ E ∈ onlyBlocks C q p, A ∩ E = {x,y})

#check (@CoveringDesigns.C20_11_3.endpoint_partner_unique :
  ∀ {α : Type*} [DecidableEq α] {C : Family α} {p q x y : α}
    {A E A' E' : Finset α} (hsat : degree (star C x) y = 2)
    (hA : A ∈ onlyBlocks C p q) (hE : E ∈ onlyBlocks C q p)
    (hi : A ∩ E = {x,y})
    (hA' : A' ∈ onlyBlocks C p q) (hE' : E' ∈ onlyBlocks C q p)
    (hi' : A' ∩ E' = {x,y}), A = A' ∧ E = E')

#check (@CoveringDesigns.C20_11_3.exists_cross_assignment : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {p q : α} {B D : Finset α}
    (hv : Fintype.card α = 20) (hC : IsCover C 11 3)
    (hstar : star (star C p) q = {B,D}) (hinter : B ∩ D = {p,q})
    (hdis : Disjoint (B \ {p,q}) (D \ {p,q})),
    let T := ((B \ {p,q}) ×ˢ (D \ {p,q})).filter
      (fun z => degree (star C z.1) z.2 = 2)
    ∃ f : α × α → Finset α × Finset α,
      (∀ z ∈ T, (f z).1 ∈ onlyBlocks C p q ∧
        (f z).2 ∈ onlyBlocks C q p ∧ (f z).1 ∩ (f z).2 = {z.1,z.2}) ∧
      Set.InjOn f (T : Set (α × α)))

-- C20_11_3/SaturatedLoss.lean

#check (@CoveringDesigns.C20_11_3.saturated_residual_complement : ∀ {α : Type*} [Fintype α] [DecidableEq α] {p q : α} {B D : Finset α} (hunion : B ∪ D = univ)
    (hinter : B ∩ D = {p, q}),
    univ \ B = D \ {p, q})

#check (@CoveringDesigns.C20_11_3.second_partner_traces_left : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {p q z : α} {B D : Finset α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q) (hBC : B ∈ C) (hDC : D ∈ C)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p, q})
    (hz : z ∈ B \ {p, q}) (hsat : degree (star C q) z = 2),
    ∃ E ∈ onlyBlocks C q p,
      ((B \ {p, q}) ∩ E).card = 1 ∧ ((D \ {p, q}) ∩ E).card = 9)

#check (@CoveringDesigns.C20_11_3.second_partner_trace : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α} {p q z : α} {B D : Finset α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q) (hBC : B ∈ C) (hDC : D ∈ C)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p, q})
    (hz : z ∈ (B \ {p, q}) ∪ (D \ {p, q}))
    (hsat : degree (star C q) z = 2),
    ∃ E ∈ onlyBlocks C q p,
      ((B \ {p, q}) ∩ E).card * ((D \ {p, q}) ∩ E).card = 9)

-- C20_11_3/Saturated.lean

#check (@CoveringDesigns.C20_11_3.no_saturated_pair_with_degree_six : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}
    (hv : Fintype.card α = 20) (hC : IsCover C 11 3) (hb : C.card = 11)
    {p q : α} (hpq : p ≠ q) (hq6 : degree C q = 6)
    (hsat : degree (star C p) q = 2),
    False)

#check (@CoveringDesigns.C20_11_3.no_saturated_pair : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}
    (hv : Fintype.card α = 20) (hC : IsCover C 11 3) (hb : C.card = 11)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2),
    False)

-- C20_11_3/LowerBound.lean

#check (@CoveringDesigns.lower_bound_20_11_3 : ∀ {α : Type*} [Fintype α] [DecidableEq α]
    {C : Family α} (hv : Fintype.card α = 20) (hC : IsCover C 11 3),
    12 ≤ C.card)

-- C20_11_3/Witness.lean

#check (@CoveringDesigns.knownCover12_20_11_3_card : knownCover12_20_11_3.card = 12)

#check (@CoveringDesigns.knownCover12_20_11_3_uniform : Uniform knownCover12_20_11_3 11)

#check (@CoveringDesigns.knownCover12_20_11_3_covers : Covers knownCover12_20_11_3 3)

#check (@CoveringDesigns.knownCover12_20_11_3_isCover : IsCover knownCover12_20_11_3 11 3)

#check (@CoveringDesigns.upper_bound_20_11_3 : ∃ C : Family (Fin 20), IsCover C 11 3 ∧ C.card = 12)

#check (@CoveringDesigns.knownCover12_20_11_3_on_card : ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 20),
    (knownCover12_20_11_3_on hv).card = 12)

#check (@CoveringDesigns.knownCover12_20_11_3_on_isCover : ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 20),
    IsCover (knownCover12_20_11_3_on hv) 11 3)

#check (@CoveringDesigns.upper_bound_20_11_3_on : ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 20),
    ∃ C : Family α, IsCover C 11 3 ∧ C.card = 12)

-- C20_11_3.lean

#check (@CoveringDesigns.covering_number_20_11_3_on : ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (hv : Fintype.card α = 20),
    (∃ C : Family α, IsCover C 11 3 ∧ C.card = 12) ∧
    (∀ C : Family α, IsCover C 11 3 → 12 ≤ C.card))

#check (@CoveringDesigns.covering_number_20_11_3 : (∃ C : Family (Fin 20), IsCover C 11 3 ∧ C.card = 12) ∧
    (∀ C : Family (Fin 20), IsCover C 11 3 → 12 ≤ C.card))

#check (@CoveringDesigns.Audit20_11_3.covering_number_explicit :
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (hv : Fintype.card α = 20),
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = 11) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 12) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = 11) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 12 ≤ C.card))

#guard_standard_axioms CoveringDesigns.BoundaryRank.signless_sum_squares
#print axioms CoveringDesigns.BoundaryRank.signless_sum_squares
#guard_standard_axioms CoveringDesigns.BoundaryRank.signless_posSemidef
#print axioms CoveringDesigns.BoundaryRank.signless_posSemidef
#guard_standard_axioms CoveringDesigns.BoundaryRank.kernel_restrictions
#print axioms CoveringDesigns.BoundaryRank.kernel_restrictions
#guard_standard_axioms CoveringDesigns.BoundaryRank.kernel_of_restrictions
#print axioms CoveringDesigns.BoundaryRank.kernel_of_restrictions
#guard_standard_axioms CoveringDesigns.BoundaryRank.ker_add_le_of_posSemidef
#print axioms CoveringDesigns.BoundaryRank.ker_add_le_of_posSemidef
#guard_standard_axioms CoveringDesigns.BoundaryRank.two_mul_finrank_le_card_of_component_constraints
#print axioms CoveringDesigns.BoundaryRank.two_mul_finrank_le_card_of_component_constraints
#guard_standard_axioms CoveringDesigns.BoundaryRank.two_mul_nullity_le_zero_count
#print axioms CoveringDesigns.BoundaryRank.two_mul_nullity_le_zero_count
#guard_standard_axioms CoveringDesigns.BoundaryRank.gram_card_bound
#print axioms CoveringDesigns.BoundaryRank.gram_card_bound
#guard_standard_axioms CoveringDesigns.C20_11_3.pair_sum
#print axioms CoveringDesigns.C20_11_3.pair_sum
#guard_standard_axioms CoveringDesigns.C20_11_3.pair_sum_subtype
#print axioms CoveringDesigns.C20_11_3.pair_sum_subtype
#guard_standard_axioms CoveringDesigns.C20_11_3.cross_pair_degree_sum
#print axioms CoveringDesigns.C20_11_3.cross_pair_degree_sum
#guard_standard_axioms CoveringDesigns.C20_11_3.cross_pair_coverage_bound
#print axioms CoveringDesigns.C20_11_3.cross_pair_coverage_bound
#guard_standard_axioms CoveringDesigns.C20_11_3.mul_le_twenty_five
#print axioms CoveringDesigns.C20_11_3.mul_le_twenty_five
#guard_standard_axioms CoveringDesigns.C20_11_3.cross_capacity_ten
#print axioms CoveringDesigns.C20_11_3.cross_capacity_ten
#guard_standard_axioms CoveringDesigns.C20_11_3.lower_bound_19_10_2
#print axioms CoveringDesigns.C20_11_3.lower_bound_19_10_2
#guard_standard_axioms CoveringDesigns.C20_11_3.degree_ge_six
#print axioms CoveringDesigns.C20_11_3.degree_ge_six
#guard_standard_axioms CoveringDesigns.C20_11_3.eleven_le_card
#print axioms CoveringDesigns.C20_11_3.eleven_le_card
#guard_standard_axioms CoveringDesigns.C20_11_3.degree_excess_sum
#print axioms CoveringDesigns.C20_11_3.degree_excess_sum
#guard_standard_axioms CoveringDesigns.C20_11_3.degree_six_or_seven
#print axioms CoveringDesigns.C20_11_3.degree_six_or_seven
#guard_standard_axioms CoveringDesigns.C20_11_3.degree_profile
#print axioms CoveringDesigns.C20_11_3.degree_profile
#guard_standard_axioms CoveringDesigns.C20_11_3.pair_ge_two
#print axioms CoveringDesigns.C20_11_3.pair_ge_two
#guard_standard_axioms CoveringDesigns.C20_11_3.low_card
#print axioms CoveringDesigns.C20_11_3.low_card
#guard_standard_axioms CoveringDesigns.C20_11_3.lowIncidence_gram_entry
#print axioms CoveringDesigns.C20_11_3.lowIncidence_gram_entry
#guard_standard_axioms CoveringDesigns.C20_11_3.low_gram
#print axioms CoveringDesigns.C20_11_3.low_gram
#guard_standard_axioms CoveringDesigns.C20_11_3.lowExcess_symm
#print axioms CoveringDesigns.C20_11_3.lowExcess_symm
#guard_standard_axioms CoveringDesigns.C20_11_3.lowExcess_nonneg
#print axioms CoveringDesigns.C20_11_3.lowExcess_nonneg
#guard_standard_axioms CoveringDesigns.C20_11_3.lowExcess_diagonal
#print axioms CoveringDesigns.C20_11_3.lowExcess_diagonal
#guard_standard_axioms CoveringDesigns.C20_11_3.highDeficit_nonneg
#print axioms CoveringDesigns.C20_11_3.highDeficit_nonneg
#guard_standard_axioms CoveringDesigns.C20_11_3.low_row_identity
#print axioms CoveringDesigns.C20_11_3.low_row_identity
#guard_standard_axioms CoveringDesigns.C20_11_3.high_deficit_sum
#print axioms CoveringDesigns.C20_11_3.high_deficit_sum
#guard_standard_axioms CoveringDesigns.C20_11_3.zero_card_le_fourteen
#print axioms CoveringDesigns.C20_11_3.zero_card_le_fourteen
#guard_standard_axioms CoveringDesigns.C20_11_3.highDeficit_zero_card_le
#print axioms CoveringDesigns.C20_11_3.highDeficit_zero_card_le
#guard_standard_axioms CoveringDesigns.C20_11_3.three_ones_posSemidef
#print axioms CoveringDesigns.C20_11_3.three_ones_posSemidef
#guard_standard_axioms CoveringDesigns.C20_11_3.low_gram_rank_ge_twelve
#print axioms CoveringDesigns.C20_11_3.low_gram_rank_ge_twelve
#guard_standard_axioms CoveringDesigns.C20_11_3.exists_saturated_pair
#print axioms CoveringDesigns.C20_11_3.exists_saturated_pair
#guard_standard_axioms CoveringDesigns.C20_11_3.saturated_pair_star_eq
#print axioms CoveringDesigns.C20_11_3.saturated_pair_star_eq
#guard_standard_axioms CoveringDesigns.C20_11_3.saturated_pair_union
#print axioms CoveringDesigns.C20_11_3.saturated_pair_union
#guard_standard_axioms CoveringDesigns.C20_11_3.saturated_pair_inter
#print axioms CoveringDesigns.C20_11_3.saturated_pair_inter
#guard_standard_axioms CoveringDesigns.C20_11_3.saturated_pair_blocks
#print axioms CoveringDesigns.C20_11_3.saturated_pair_blocks
#guard_standard_axioms CoveringDesigns.C20_11_3.saturated_pair_geometry
#print axioms CoveringDesigns.C20_11_3.saturated_pair_geometry
#guard_standard_axioms CoveringDesigns.C20_11_3.saturated_partner_of_mem
#print axioms CoveringDesigns.C20_11_3.saturated_partner_of_mem
#guard_standard_axioms CoveringDesigns.C20_11_3.other_block_eq_complement
#print axioms CoveringDesigns.C20_11_3.other_block_eq_complement
#guard_standard_axioms CoveringDesigns.C20_11_3.saturated_partner_eq_complement
#print axioms CoveringDesigns.C20_11_3.saturated_partner_eq_complement
#guard_standard_axioms CoveringDesigns.C20_11_3.saturated_residual_geometry
#print axioms CoveringDesigns.C20_11_3.saturated_residual_geometry
#guard_standard_axioms CoveringDesigns.C20_11_3.mem_onlyBlocks
#print axioms CoveringDesigns.C20_11_3.mem_onlyBlocks
#guard_standard_axioms CoveringDesigns.C20_11_3.mem_neitherBlocks
#print axioms CoveringDesigns.C20_11_3.mem_neitherBlocks
#guard_standard_axioms CoveringDesigns.C20_11_3.onlyBlocks_card_add_pair
#print axioms CoveringDesigns.C20_11_3.onlyBlocks_card_add_pair
#guard_standard_axioms CoveringDesigns.C20_11_3.endpoint_sum_partition
#print axioms CoveringDesigns.C20_11_3.endpoint_sum_partition
#guard_standard_axioms CoveringDesigns.C20_11_3.endpoint_card_partition
#print axioms CoveringDesigns.C20_11_3.endpoint_card_partition
#guard_standard_axioms CoveringDesigns.C20_11_3.trace_sum
#print axioms CoveringDesigns.C20_11_3.trace_sum
#guard_standard_axioms CoveringDesigns.C20_11_3.trace_sum_only
#print axioms CoveringDesigns.C20_11_3.trace_sum_only
#guard_standard_axioms CoveringDesigns.C20_11_3.trace_sum_neither
#print axioms CoveringDesigns.C20_11_3.trace_sum_neither
#guard_standard_axioms CoveringDesigns.C20_11_3.trace_product_le
#print axioms CoveringDesigns.C20_11_3.trace_product_le
#guard_standard_axioms CoveringDesigns.C20_11_3.intersection_le_ten
#print axioms CoveringDesigns.C20_11_3.intersection_le_ten
#guard_standard_axioms CoveringDesigns.C20_11_3.intersection_sum
#print axioms CoveringDesigns.C20_11_3.intersection_sum
#guard_standard_axioms CoveringDesigns.C20_11_3.endpoint_degree_partition
#print axioms CoveringDesigns.C20_11_3.endpoint_degree_partition
#guard_standard_axioms CoveringDesigns.C20_11_3.residual_pair_eq
#print axioms CoveringDesigns.C20_11_3.residual_pair_eq
#guard_standard_axioms CoveringDesigns.C20_11_3.cross_pair_eq_of_pair_eq
#print axioms CoveringDesigns.C20_11_3.cross_pair_eq_of_pair_eq
#guard_standard_axioms CoveringDesigns.C20_11_3.shared_intersection_sum
#print axioms CoveringDesigns.C20_11_3.shared_intersection_sum
#guard_standard_axioms CoveringDesigns.C20_11_3.multiplicity_floor_count
#print axioms CoveringDesigns.C20_11_3.multiplicity_floor_count
#guard_standard_axioms CoveringDesigns.C20_11_3.assignment_card_le
#print axioms CoveringDesigns.C20_11_3.assignment_card_le
#guard_standard_axioms CoveringDesigns.C20_11_3.capacity_bound
#print axioms CoveringDesigns.C20_11_3.capacity_bound
#guard_standard_axioms CoveringDesigns.C20_11_3.capacity_bound_loss16
#print axioms CoveringDesigns.C20_11_3.capacity_bound_loss16
#guard_standard_axioms CoveringDesigns.C20_11_3.cross_count_lower
#print axioms CoveringDesigns.C20_11_3.cross_count_lower
#guard_standard_axioms CoveringDesigns.C20_11_3.no_second_partner_arithmetic
#print axioms CoveringDesigns.C20_11_3.no_second_partner_arithmetic
#guard_standard_axioms CoveringDesigns.C20_11_3.row_partner_bound
#print axioms CoveringDesigns.C20_11_3.row_partner_bound
#guard_standard_axioms CoveringDesigns.C20_11_3.assignment_card_le_twice
#print axioms CoveringDesigns.C20_11_3.assignment_card_le_twice
#guard_standard_axioms CoveringDesigns.C20_11_3.final_partner_contradiction
#print axioms CoveringDesigns.C20_11_3.final_partner_contradiction
#guard_standard_axioms CoveringDesigns.C20_11_3.residual_not_mem_other
#print axioms CoveringDesigns.C20_11_3.residual_not_mem_other
#guard_standard_axioms CoveringDesigns.C20_11_3.cross_partner_exists
#print axioms CoveringDesigns.C20_11_3.cross_partner_exists
#guard_standard_axioms CoveringDesigns.C20_11_3.endpoint_partner_unique
#print axioms CoveringDesigns.C20_11_3.endpoint_partner_unique
#guard_standard_axioms CoveringDesigns.C20_11_3.exists_cross_assignment
#print axioms CoveringDesigns.C20_11_3.exists_cross_assignment
#guard_standard_axioms CoveringDesigns.C20_11_3.saturated_residual_complement
#print axioms CoveringDesigns.C20_11_3.saturated_residual_complement
#guard_standard_axioms CoveringDesigns.C20_11_3.second_partner_traces_left
#print axioms CoveringDesigns.C20_11_3.second_partner_traces_left
#guard_standard_axioms CoveringDesigns.C20_11_3.second_partner_trace
#print axioms CoveringDesigns.C20_11_3.second_partner_trace
#guard_standard_axioms CoveringDesigns.C20_11_3.no_saturated_pair_with_degree_six
#print axioms CoveringDesigns.C20_11_3.no_saturated_pair_with_degree_six
#guard_standard_axioms CoveringDesigns.C20_11_3.no_saturated_pair
#print axioms CoveringDesigns.C20_11_3.no_saturated_pair
#guard_standard_axioms CoveringDesigns.lower_bound_20_11_3
#print axioms CoveringDesigns.lower_bound_20_11_3
#guard_standard_axioms CoveringDesigns.knownCover12_20_11_3_card
#print axioms CoveringDesigns.knownCover12_20_11_3_card
#guard_standard_axioms CoveringDesigns.knownCover12_20_11_3_uniform
#print axioms CoveringDesigns.knownCover12_20_11_3_uniform
#guard_standard_axioms CoveringDesigns.knownCover12_20_11_3_covers
#print axioms CoveringDesigns.knownCover12_20_11_3_covers
#guard_standard_axioms CoveringDesigns.knownCover12_20_11_3_isCover
#print axioms CoveringDesigns.knownCover12_20_11_3_isCover
#guard_standard_axioms CoveringDesigns.upper_bound_20_11_3
#print axioms CoveringDesigns.upper_bound_20_11_3
#guard_standard_axioms CoveringDesigns.knownCover12_20_11_3_on_card
#print axioms CoveringDesigns.knownCover12_20_11_3_on_card
#guard_standard_axioms CoveringDesigns.knownCover12_20_11_3_on_isCover
#print axioms CoveringDesigns.knownCover12_20_11_3_on_isCover
#guard_standard_axioms CoveringDesigns.upper_bound_20_11_3_on
#print axioms CoveringDesigns.upper_bound_20_11_3_on
#guard_standard_axioms CoveringDesigns.covering_number_20_11_3_on
#print axioms CoveringDesigns.covering_number_20_11_3_on
#guard_standard_axioms CoveringDesigns.covering_number_20_11_3
#print axioms CoveringDesigns.covering_number_20_11_3
#guard_standard_axioms CoveringDesigns.Audit20_11_3.covering_number_explicit
#print axioms CoveringDesigns.Audit20_11_3.covering_number_explicit
