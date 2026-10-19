import CoveringDesigns.TwoKMinusTwo

open CoveringDesigns CoveringDesigns.TwoKMinusTwo
open Finset Matrix CoveringDesigns.C20_11_3 CoveringDesigns.AffineConstructions
open scoped LinearAlgebra.Projectivization
set_option linter.unusedVariables false

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.degree
#print CoveringDesigns.star
#print CoveringDesigns.minimumPoints
#print CoveringDesigns.C20_11_3.onlyBlocks
#print CoveringDesigns.TwoKMinusTwo.capacity
#print CoveringDesigns.TwoKMinusTwo.Low
#print CoveringDesigns.TwoKMinusTwo.lowIncidence
#print CoveringDesigns.TwoKMinusTwo.excess
#print CoveringDesigns.TwoKMinusTwo.lowExcess
#print CoveringDesigns.TwoKMinusTwo.deficit
#print CoveringDesigns.TwoKMinusTwo.Base
#print CoveringDesigns.TwoKMinusTwo.tetra
#print CoveringDesigns.TwoKMinusTwo.pair
#print CoveringDesigns.TwoKMinusTwo.weight

namespace CoveringDesigns.AuditTwoKMinusTwo

/-- Universal exactness with all ordinary-covering conditions exposed. -/
theorem exactness_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 41 ≤ k) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card = k) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 14) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card = k) →
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) → 14 ≤ C.card) := by
  obtain ⟨⟨C,hC,hcard⟩,hlower⟩ := TwoKMinusTwo.exactness hv hk
  exact ⟨⟨C,hC.1,hC.2,hcard⟩,fun C hu hc => hlower C ⟨hu,hc⟩⟩

/-- The unconditional lower bound adds no structural premise. -/
theorem lower_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k)
    (C : Finset (Finset α)) (hu : ∀ B ∈ C, B.card = k)
    (hc : ∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) :
    14*(k-1) ≤ (k+2)*C.card := by
  classical
  exact TwoKMinusTwo.lower_inequality hv hk ⟨hu,hc⟩

/-- Existence covers every k≥3, independently of the lower-bound range. -/
theorem upper_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) :
    ∃ C : Finset (Finset α), (∀ B ∈ C, B.card = k) ∧
      (∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B) ∧ C.card ≤ 14 := by
  obtain ⟨C,hC,hcard⟩ := TwoKMinusTwo.upper_bound hv hk
  exact ⟨C,hC.1,hC.2,hcard⟩

end CoveringDesigns.AuditTwoKMinusTwo

-- Every public theorem is checked against its full contract below.
-- Expanded statements above also expose the final covering definitions.

-- Arithmetic.lean

#check (@CoveringDesigns.TwoKMinusTwo.product_le_capacity : ∀ {a b k : ℕ} (h : a+b ≤ k),
    a*b ≤ capacity k)

#check (@CoveringDesigns.TwoKMinusTwo.capacity_even : ∀ (r : ℕ),
    capacity (2*r) = r*r)

#check (@CoveringDesigns.TwoKMinusTwo.capacity_odd : ∀ (r : ℕ),
    capacity (2*r+1) = r*(r+1))

#check (@CoveringDesigns.TwoKMinusTwo.capacity_step : ∀ {k : ℕ} (hk : 1 ≤ k),
    capacity k = capacity (k-1) + k/2)

#check (@CoveringDesigns.TwoKMinusTwo.link_capacity_strict : ∀ {k : ℕ} (hk : 9 ≤ k),
    3*capacity (k-1) < (k-2)*(k-2))

#check (@CoveringDesigns.TwoKMinusTwo.endpoint_budget : ∀ {u w r : ℕ} (hu : 4 ≤ u) (hw : 4 ≤ w)
    (hur : u ≤ r) (hwr : w ≤ r),
    u*w+8*r ≤ r*(u+w)+16)

#check (@CoveringDesigns.TwoKMinusTwo.capacity_twelve_impossible : ∀ {k : ℕ} (hk : 17 ≤ k)
    (hs : 3*(k-2)*(k-2)+8*(k/2) ≤ 10*capacity k+16),
    False)

#check (@CoveringDesigns.TwoKMinusTwo.capacity_thirteen_impossible : ∀ {k : ℕ} (hk : 33 ≤ k)
    (hs : 3*(k-2)*(k-2)+8*(k/2) ≤ 11*capacity k+16),
    False)

-- Incidence.lean

#check (@CoveringDesigns.TwoKMinusTwo.cross_capacity : ∀ {α : Type*} [Fintype α] [DecidableEq α] (X Y B : Finset α) (hXY : Disjoint X Y)
    {m : ℕ} (hB : B.card ≤ m),
    (X ∩ B).card * (Y ∩ B).card ≤ capacity m)

#check (@CoveringDesigns.TwoKMinusTwo.link_lower_bound : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α} (hv : Fintype.card α = 2*k-3) (hk : 9 ≤ k)
    (hC : IsCover C (k-1) 2),
    6 ≤ C.card)

#check (@CoveringDesigns.TwoKMinusTwo.degree_ge_six : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α} (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k)
    (hC : IsCover C k 3) (p : α),
    6 ≤ degree C p)

#check (@CoveringDesigns.TwoKMinusTwo.pair_ge_two : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 3 ≤ k) (hC : IsCover C k 3) {p q : α} (hpq : p ≠ q),
    2 ≤ degree (star C p) q)

-- Geometry.lean

#check (@CoveringDesigns.TwoKMinusTwo.saturated_pair_inter : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α} {p q : α} {B D : Finset α} (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hpq : p ≠ q)
    (hstar : star (star C p) q = {B, D}),
    B ∩ D = {p, q})

#check (@CoveringDesigns.TwoKMinusTwo.saturated_pair_blocks : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α} {p q : α} (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2),
    ∃ B ∈ C, ∃ D ∈ C, B ≠ D ∧ star (star C p) q = {B, D} ∧
      B ∪ D = univ ∧ B ∩ D = {p, q})

#check (@CoveringDesigns.TwoKMinusTwo.saturated_pair_geometry : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α} {p q : α} {B D : Finset α} (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2)
    (hBC : B ∈ C) (hDC : D ∈ C) (hBD : B ≠ D)
    (hpB : p ∈ B) (hqB : q ∈ B) (hpD : p ∈ D) (hqD : q ∈ D),
    B ∪ D = univ ∧ B ∩ D = {p, q})

#check (@CoveringDesigns.TwoKMinusTwo.saturated_residual_geometry : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {p q : α} {B D : Finset α} (hpq : p ≠ q)
    (hBcard : B.card = k) (hDcard : D.card = k)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p, q}),
    Disjoint (B \ {p, q}) (D \ {p, q}) ∧
      (B \ {p, q}).card = k-2 ∧ (D \ {p, q}).card = k-2 ∧
      (B \ {p, q}) ∪ (D \ {p, q}) = univ \ {p, q})

#check (@CoveringDesigns.TwoKMinusTwo.cross_partner_exists : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α} {p q x y : α} {B D : Finset α}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) (hC : IsCover C k 3)
    (hstar : star (star C p) q = {B,D}) (hinter : B ∩ D = {p,q})
    (hx : x ∈ B \ {p,q}) (hy : y ∈ D \ {p,q})
    (hsat : degree (star C x) y = 2),
    ∃ A ∈ onlyBlocks C p q, ∃ E ∈ onlyBlocks C q p, A ∩ E = {x,y})

#check (@CoveringDesigns.TwoKMinusTwo.exists_cross_assignment : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α} {p q : α} {B D : Finset α}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) (hC : IsCover C k 3)
    (hstar : star (star C p) q = {B,D}) (hinter : B ∩ D = {p,q})
    (hdis : Disjoint (B \ {p,q}) (D \ {p,q})),
    let T := ((B \ {p,q}) ×ˢ (D \ {p,q})).filter
      (fun z => degree (star C z.1) z.2 = 2)
    ∃ f : α × α → Finset α × Finset α,
      (∀ z ∈ T, (f z).1 ∈ onlyBlocks C p q ∧
        (f z).2 ∈ onlyBlocks C q p ∧ (f z).1 ∩ (f z).2 = {z.1,z.2}) ∧
      Set.InjOn f (T : Set (α × α)))

-- Rank.lean

#check (@CoveringDesigns.TwoKMinusTwo.excess_nonneg : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α}
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x y : α),
    0 ≤ excess C x y)

#check (@CoveringDesigns.TwoKMinusTwo.low_row_le : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 3 ≤ k) (hu : Uniform C k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) (x : Low C),
    (∑ y, lowExcess C x y) ≤ 3)

#check (@CoveringDesigns.TwoKMinusTwo.low_gram : ∀ {α : Type*} [Fintype α] [DecidableEq α] {C : Family α},
    lowIncidence C * (lowIncidence C).transpose =
      Matrix.diagonal (fun _ => (3 : ℝ)) + lowExcess C +
        Matrix.of (fun _ _ => (3 : ℝ)))

#check (@CoveringDesigns.TwoKMinusTwo.low_card_le : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 3 ≤ k) (hu : Uniform C k)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y),
    (minimumPoints C 6).card ≤ 2*C.card)

#check (@CoveringDesigns.TwoKMinusTwo.conditional_rank : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 9 ≤ k) (hC : IsCover C k 3)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y),
    14*(k-1) ≤ (k+2)*C.card)

-- Capacity.lean

#check (@CoveringDesigns.TwoKMinusTwo.endpoint_trace_capacity : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {p q : α} {X Y B : Finset α}
    (hdis : Disjoint X Y) (hpart : X ∪ Y = univ \ {p,q})
    (hB : B.card = k) (hp : p ∈ B) (hq : q ∉ B),
    (X ∩ B).card * (Y ∩ B).card ≤ capacity (k-1))

#check (@CoveringDesigns.TwoKMinusTwo.saturated_capacity : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) (hC : IsCover C k 3)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2),
    3*(k-2)*(k-2)+(k/2)*((onlyBlocks C p q).card+(onlyBlocks C q p).card) ≤
      (C.card-2)*capacity k+(onlyBlocks C p q).card*(onlyBlocks C q p).card)

-- Bounds.lean

#check (@CoveringDesigns.TwoKMinusTwo.saturated_capacity_reduced : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k) (hC : IsCover C k 3)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2)
    (hr : C.card-6 ≤ k/2),
    3*(k-2)*(k-2)+8*(k/2) ≤ (C.card-2)*capacity k+16)

#check (@CoveringDesigns.TwoKMinusTwo.no_saturation_twelve : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 17 ≤ k) (hC : IsCover C k 3)
    (hb : C.card ≤ 12) {p q : α} (hpq : p ≠ q),
    degree (star C p) q ≠ 2)

#check (@CoveringDesigns.TwoKMinusTwo.no_saturation_thirteen : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 33 ≤ k) (hC : IsCover C k 3)
    (hb : C.card ≤ 13) {p q : α} (hpq : p ≠ q),
    degree (star C p) q ≠ 2)

#check (@CoveringDesigns.TwoKMinusTwo.thirteen_le_card : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 20 ≤ k) (hC : IsCover C k 3),
    13 ≤ C.card)

#check (@CoveringDesigns.TwoKMinusTwo.fourteen_le_card : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 41 ≤ k) (hC : IsCover C k 3),
    14 ≤ C.card)

#check (@CoveringDesigns.TwoKMinusTwo.lower_inequality : ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k) (hC : IsCover C k 3),
    14*(k-1) ≤ (k+2)*C.card)

-- Expansion.lean

#check (@CoveringDesigns.TwoKMinusTwo.pad_indexed : ∀ {α ι : Type*} [Fintype α] [Fintype ι]
    (B : ι → Finset α) {k t : ℕ} (hk : k ≤ Fintype.card α)
    (hsize : ∀ i, (B i).card ≤ k)
    (hcover : ∀ T : Finset α, T.card=t → ∃ i, T ⊆ B i),
    ∃ C : Family α, IsCover C k t ∧ C.card ≤ Fintype.card ι)

#check (@CoveringDesigns.TwoKMinusTwo.weighted_expansion : ∀ {β ι : Type*} [Fintype β] [Fintype ι]
    (w : β → ℕ) (B : ι → Finset β) {k t : ℕ}
    (hk : k ≤ ∑ x, w x)
    (hsize : ∀ i, (∑ x ∈ B i, w x) ≤ k)
    (hcover : ∀ T : Finset β, T.card ≤ t → ∃ i, T ⊆ B i),
    ∃ C : Family (Σ x, Fin (w x)), IsCover C k t ∧ C.card ≤ Fintype.card ι)

-- AffineWeights.lean

#check (@CoveringDesigns.TwoKMinusTwo.base_card : Fintype.card Base = 8)

#check (@CoveringDesigns.TwoKMinusTwo.tetra_card : tetra.card=4)

#check (@CoveringDesigns.TwoKMinusTwo.pair_card : pair.card=2)

#check (@CoveringDesigns.TwoKMinusTwo.tetra_not_in_plane : ∀ (p : Direction (ZMod 2) 3) (c : ZMod 2),
    ¬ tetra ⊆ hyperplane p c)

#check (@CoveringDesigns.TwoKMinusTwo.tetra_plane_card : ∀ (p : Direction (ZMod 2) 3) (c : ZMod 2),
    ((hyperplane p c) ∩ tetra).card ≤ 3)

#check (@CoveringDesigns.TwoKMinusTwo.weight_sum : ∀ (a j : ℕ) (hj : j<4),
    (∑ x, weight a j x) = 2*(3+4*a+j)-2)

#check (@CoveringDesigns.TwoKMinusTwo.weight_plane_le : ∀ (a j : ℕ) (hj : j<4)
    (p : Direction (ZMod 2) 3) (c : ZMod 2),
    (∑ x ∈ hyperplane p c, weight a j x) ≤ 3+4*a+j)

-- Construction.lean

#check (@CoveringDesigns.TwoKMinusTwo.small_base_subset : ∀ (T : Finset Base) (hT : T.card ≤ 3),
    ∃ p : Direction (ZMod 2) 3, ∃ c : ZMod 2, T ⊆ hyperplane p c)

#check (@CoveringDesigns.TwoKMinusTwo.upper_bound : ∀ {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k),
    ∃ C : Family α, IsCover C k 3 ∧ C.card ≤ 14)

-- Entry.lean

#check (@CoveringDesigns.TwoKMinusTwo.exactness : ∀ {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α = 2*k-2) (hk : 41 ≤ k),
    (∃ C : Family α, IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family α, IsCover C k 3 → 14 ≤ C.card))

#check (@CoveringDesigns.TwoKMinusTwo.covering_number : ∀ {k : ℕ} (hk : 41 ≤ k),
    (∃ C : Family (Fin (2*k-2)), IsCover C k 3 ∧ C.card = 14) ∧
    (∀ C : Family (Fin (2*k-2)), IsCover C k 3 → 14 ≤ C.card))

#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.product_le_capacity
#print axioms CoveringDesigns.TwoKMinusTwo.product_le_capacity
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.capacity_even
#print axioms CoveringDesigns.TwoKMinusTwo.capacity_even
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.capacity_odd
#print axioms CoveringDesigns.TwoKMinusTwo.capacity_odd
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.capacity_step
#print axioms CoveringDesigns.TwoKMinusTwo.capacity_step
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.link_capacity_strict
#print axioms CoveringDesigns.TwoKMinusTwo.link_capacity_strict
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.endpoint_budget
#print axioms CoveringDesigns.TwoKMinusTwo.endpoint_budget
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.capacity_twelve_impossible
#print axioms CoveringDesigns.TwoKMinusTwo.capacity_twelve_impossible
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.capacity_thirteen_impossible
#print axioms CoveringDesigns.TwoKMinusTwo.capacity_thirteen_impossible
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.cross_capacity
#print axioms CoveringDesigns.TwoKMinusTwo.cross_capacity
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.link_lower_bound
#print axioms CoveringDesigns.TwoKMinusTwo.link_lower_bound
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.degree_ge_six
#print axioms CoveringDesigns.TwoKMinusTwo.degree_ge_six
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.pair_ge_two
#print axioms CoveringDesigns.TwoKMinusTwo.pair_ge_two
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.saturated_pair_inter
#print axioms CoveringDesigns.TwoKMinusTwo.saturated_pair_inter
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.saturated_pair_blocks
#print axioms CoveringDesigns.TwoKMinusTwo.saturated_pair_blocks
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.saturated_pair_geometry
#print axioms CoveringDesigns.TwoKMinusTwo.saturated_pair_geometry
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.saturated_residual_geometry
#print axioms CoveringDesigns.TwoKMinusTwo.saturated_residual_geometry
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.cross_partner_exists
#print axioms CoveringDesigns.TwoKMinusTwo.cross_partner_exists
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.exists_cross_assignment
#print axioms CoveringDesigns.TwoKMinusTwo.exists_cross_assignment
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.excess_nonneg
#print axioms CoveringDesigns.TwoKMinusTwo.excess_nonneg
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.low_row_le
#print axioms CoveringDesigns.TwoKMinusTwo.low_row_le
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.low_gram
#print axioms CoveringDesigns.TwoKMinusTwo.low_gram
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.low_card_le
#print axioms CoveringDesigns.TwoKMinusTwo.low_card_le
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.conditional_rank
#print axioms CoveringDesigns.TwoKMinusTwo.conditional_rank
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.endpoint_trace_capacity
#print axioms CoveringDesigns.TwoKMinusTwo.endpoint_trace_capacity
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.saturated_capacity
#print axioms CoveringDesigns.TwoKMinusTwo.saturated_capacity
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.saturated_capacity_reduced
#print axioms CoveringDesigns.TwoKMinusTwo.saturated_capacity_reduced
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.no_saturation_twelve
#print axioms CoveringDesigns.TwoKMinusTwo.no_saturation_twelve
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.no_saturation_thirteen
#print axioms CoveringDesigns.TwoKMinusTwo.no_saturation_thirteen
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.thirteen_le_card
#print axioms CoveringDesigns.TwoKMinusTwo.thirteen_le_card
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.fourteen_le_card
#print axioms CoveringDesigns.TwoKMinusTwo.fourteen_le_card
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.lower_inequality
#print axioms CoveringDesigns.TwoKMinusTwo.lower_inequality
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.pad_indexed
#print axioms CoveringDesigns.TwoKMinusTwo.pad_indexed
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.weighted_expansion
#print axioms CoveringDesigns.TwoKMinusTwo.weighted_expansion
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.base_card
#print axioms CoveringDesigns.TwoKMinusTwo.base_card
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.tetra_card
#print axioms CoveringDesigns.TwoKMinusTwo.tetra_card
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.pair_card
#print axioms CoveringDesigns.TwoKMinusTwo.pair_card
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.tetra_not_in_plane
#print axioms CoveringDesigns.TwoKMinusTwo.tetra_not_in_plane
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.tetra_plane_card
#print axioms CoveringDesigns.TwoKMinusTwo.tetra_plane_card
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.weight_sum
#print axioms CoveringDesigns.TwoKMinusTwo.weight_sum
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.weight_plane_le
#print axioms CoveringDesigns.TwoKMinusTwo.weight_plane_le
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.small_base_subset
#print axioms CoveringDesigns.TwoKMinusTwo.small_base_subset
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.upper_bound
#print axioms CoveringDesigns.TwoKMinusTwo.upper_bound
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.exactness
#print axioms CoveringDesigns.TwoKMinusTwo.exactness
#guard_standard_axioms CoveringDesigns.TwoKMinusTwo.covering_number
#print axioms CoveringDesigns.TwoKMinusTwo.covering_number
#guard_standard_axioms CoveringDesigns.AuditTwoKMinusTwo.exactness_explicit
#print axioms CoveringDesigns.AuditTwoKMinusTwo.exactness_explicit
#guard_standard_axioms CoveringDesigns.AuditTwoKMinusTwo.lower_explicit
#print axioms CoveringDesigns.AuditTwoKMinusTwo.lower_explicit
#guard_standard_axioms CoveringDesigns.AuditTwoKMinusTwo.upper_explicit
#print axioms CoveringDesigns.AuditTwoKMinusTwo.upper_explicit
