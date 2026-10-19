import CoveringDesigns.Multicover
import CoveringDesigns.Foundations.StandardAxioms

/-! Complete contracts for the indexed foundation and an expanded occurrence-counting cover. -/

namespace CoveringDesigns.Multicover
open Finset
universe u v w

#print Multicover.Uniform
#print Multicover.Covers
#print Multicover.IsCover
#print Multicover.subsetLink
#print Multicover.CoverLower
#print Multicover.bound
#print Multicover.ofFamily
#print Multicover.ofMultiset
#print Multicover.deduplicate

#check (subsetDegree_eq_card : ∀ {α : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq α] (B : ι → Finset α) (X : Finset α),
    indexedSubsetDegree B X = Fintype.card {i // X ⊆ B i})
#check (subsetDegree_empty : ∀ {α : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq α] (B : ι → Finset α),
    indexedSubsetDegree B ∅ = Fintype.card ι)
#check (subsetDegree_singleton : ∀ {α : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq α] (B : ι → Finset α) (p : α),
    indexedSubsetDegree B {p} = indexedDegree B p)
#check (covers_zero_iff : ∀ {α : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq α] (B : ι → Finset α) (lam : ℕ),
    Covers B 0 lam ↔ lam ≤ Fintype.card ι)
#check (covers_multiplicity_zero : ∀ {α : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq α] (B : ι → Finset α) (t : ℕ), Covers B t 0)
#check (covers_one_iff : ∀ {α : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq α] (B : ι → Finset α) (t : ℕ),
    Covers B t 1 ↔ ∀ X : Finset α, X.card = t → ∃ i, X ⊆ B i)
#check (reindex_card : ∀ {ι : Type v} {κ : Type w}
    [Fintype ι] [Fintype κ] (_e : κ ≃ ι), Fintype.card κ = Fintype.card ι)
#check (subsetDegree_reindex : ∀ {α : Type u} {ι : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq α] [Fintype κ] (e : κ ≃ ι) (B : ι → Finset α)
    (X : Finset α), indexedSubsetDegree (B ∘ e) X = indexedSubsetDegree B X)
#check (degree_reindex : ∀ {α : Type u} {ι : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq α] [Fintype κ] (e : κ ≃ ι) (B : ι → Finset α)
    (p : α), indexedDegree (B ∘ e) p = indexedDegree B p)
#check (uniform_reindex : ∀ {α : Type u} {ι : Type v} {κ : Type w}
    (e : κ ≃ ι) (B : ι → Finset α) (k : ℕ), Uniform (B ∘ e) k ↔ Uniform B k)
#check (covers_reindex : ∀ {α : Type u} {ι : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq α] [Fintype κ] (e : κ ≃ ι) (B : ι → Finset α)
    (t lam : ℕ), Covers (B ∘ e) t lam ↔ Covers B t lam)
#check (isCover_reindex : ∀ {α : Type u} {ι : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq α] [Fintype κ] (e : κ ≃ ι) (B : ι → Finset α)
    (k t lam : ℕ), IsCover (B ∘ e) k t lam ↔ IsCover B k t lam)

#check (subsetLink_card : ∀ {α : Type u} {ι : Type v} [DecidableEq α] [Fintype ι]
    (B : ι → Finset α) (X : Finset α),
    Fintype.card {i // X ⊆ B i} = indexedSubsetDegree B X)
#check (subsetLink_uniform : ∀ {α : Type u} {ι : Type v} [DecidableEq α]
    {B : ι → Finset α} {k : ℕ} (_h : Uniform B k) (X : Finset α),
    Uniform (subsetLink B X) (k-X.card))
#check (subsetLink_multiplicity : ∀ {α : Type u} {ι : Type v}
    [DecidableEq α] [Fintype ι] (B : ι → Finset α) (X : Finset α)
    (T : Finset {p : α // p ∉ X}),
    indexedSubsetDegree (subsetLink B X) T =
      indexedSubsetDegree B (X ∪ T.map (Function.Embedding.subtype _)))
#check (subsetLink_isCover : ∀ {α : Type u} {ι : Type v}
    [DecidableEq α] [Fintype ι] {B : ι → Finset α} {k t lam : ℕ}
    (_h : IsCover B k t lam) (X : Finset α) (_hXt : X.card ≤ t),
    IsCover (subsetLink B X) (k-X.card) (t-X.card) lam)
#check (subset_complement_card : ∀ {α : Type u} [DecidableEq α] [Fintype α]
    (X : Finset α), Fintype.card {p : α // p ∉ X} = Fintype.card α-X.card)
#check (multiplicity_ge_of_coverLower : ∀ {α : Type u} {ι : Type v}
    [DecidableEq α] [Fintype α] [Fintype ι] {B : ι → Finset α} {v k t lam i b : ℕ}
    (_hn : Fintype.card α = v) (_h : IsCover B k t lam) (_hi : i ≤ t)
    (_hl : CoverLower.{u,v} (v-i) (k-i) (t-i) lam b) {X : Finset α} (_hX : X.card = i),
    b ≤ indexedSubsetDegree B X)

#check (degree_sum : ∀ {α : Type u} {ι : Type v}
    [Fintype α] [DecidableEq α] [Fintype ι] (B : ι → Finset α),
    (∑ p, indexedDegree B p) = ∑ i, (B i).card)
#check (degree_sum_of_uniform : ∀ {α : Type u} {ι : Type v}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {k : ℕ}
    (_h : Uniform B k), (∑ p, indexedDegree B p) = k*Fintype.card ι)
#check (subsetDegree_sum_of_uniform : ∀ {α : Type u} {ι : Type v}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {k : ℕ}
    (_h : Uniform B k) (r : ℕ),
    (∑ X ∈ (univ : Finset α).powersetCard r, indexedSubsetDegree B X) =
      k.choose r*Fintype.card ι)
#check (bound_of_links : ∀ {α : Type u} {ι : Type v}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {k m : ℕ}
    (_hk : 0 < k) (_hu : Uniform B k)
    (_hl : ∀ p : α, m ≤ Fintype.card {i // ({p} : Finset α) ⊆ B i}),
    Schoenheim.ceilDiv (Fintype.card α*m) k ≤ Fintype.card ι)
#check (lift_lower_bound : ∀ {α : Type u} {ι : Type v}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {v k t lam m : ℕ}
    (_hn : Fintype.card α = v+1) (_h : IsCover B (k+1) (t+1) lam)
    (_hl : CoverLower.{u,v} v k t lam m),
    Schoenheim.ceilDiv ((v+1)*m) (k+1) ≤ Fintype.card ι)

#check (bound_zero : ∀ (lam v k : ℕ), bound lam v k 0 = lam)
#check (bound_succ : ∀ (lam v k t : ℕ),
    bound lam v k (t+1) = Schoenheim.ceilDiv (v*bound lam (v-1) (k-1) t) k)
#check (bound_one_eq : ∀ (v k t : ℕ), bound 1 v k t = Schoenheim.bound v k t)
#check (bound_multiplicity_zero : ∀ (v k t : ℕ), bound 0 v k t = 0)
#check (lower_bound : ∀ {α : Type u} {ι : Type v}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {k t lam : ℕ}
    (_htk : t ≤ k) (_hkv : k ≤ Fintype.card α) (_h : IsCover B k t lam),
    bound lam (Fintype.card α) k t ≤ Fintype.card ι)
#check (schoenheim_coverLower : ∀ {lam v k t : ℕ} (_htk : t ≤ k) (_hkv : k ≤ v),
    CoverLower.{u,v} v k t lam (bound lam v k t))

#check (ofFamily_card : ∀ {α : Type u} (C : Family α), Fintype.card C = C.card)
#check (ofFamily_subsetDegree : ∀ {α : Type u} [DecidableEq α] (C : Family α)
    (X : Finset α), indexedSubsetDegree (ofFamily C) X = HorsleySingh.multiplicity C X)
#check (ofFamily_degree : ∀ {α : Type u} [DecidableEq α] (C : Family α) (p : α),
    indexedDegree (ofFamily C) p = CoveringDesigns.degree C p)
#check (ofFamily_uniform : ∀ {α : Type u} (C : Family α) (k : ℕ),
    Uniform (ofFamily C) k ↔ CoveringDesigns.Uniform C k)
#check (ofFamily_covers_one : ∀ {α : Type u} [DecidableEq α] (C : Family α) (t : ℕ),
    Covers (ofFamily C) t 1 ↔ CoveringDesigns.Covers C t)
#check (ofFamily_isCover_one : ∀ {α : Type u} [DecidableEq α] (C : Family α) (k t : ℕ),
    IsCover (ofFamily C) k t 1 ↔ CoveringDesigns.IsCover C k t)
#check (family_lower_bound : ∀ {α : Type u} [DecidableEq α] [Fintype α]
    {C : Family α} {k t : ℕ} (_htk : t ≤ k) (_hkv : k ≤ Fintype.card α)
    (_h : CoveringDesigns.IsCover C k t), Schoenheim.bound (Fintype.card α) k t ≤ C.card)
#check (deduplicate_card_le : ∀ {α : Type u} [DecidableEq α] {ι : Type v}
    [Fintype ι] (B : ι → Finset α), (deduplicate B).card ≤ Fintype.card ι)
#check (deduplicate_isCover_one : ∀ {α : Type u} [DecidableEq α] {ι : Type v}
    [Fintype ι] (B : ι → Finset α) (k t : ℕ),
    CoveringDesigns.IsCover (deduplicate B) k t ↔ IsCover B k t 1)

#check (ofMultiset_card : ∀ {α : Type u} [DecidableEq α] (M : Multiset (Finset α)),
    Fintype.card M = M.card)
#check (ofMultiset_subsetDegree : ∀ {α : Type u} [DecidableEq α]
    (M : Multiset (Finset α)) (X : Finset α),
    indexedSubsetDegree (ofMultiset M) X = M.countP (X ⊆ ·))
#check (ofMultiset_degree : ∀ {α : Type u} [DecidableEq α]
    (M : Multiset (Finset α)) (p : α), indexedDegree (ofMultiset M) p = M.countP (p ∈ ·))
#check (ofMultiset_uniform : ∀ {α : Type u} [DecidableEq α]
    (M : Multiset (Finset α)) (k : ℕ), Uniform (ofMultiset M) k ↔ ∀ A ∈ M, A.card = k)
#check (ofMultiset_isCover : ∀ {α : Type u} [DecidableEq α]
    (M : Multiset (Finset α)) (k t lam : ℕ), IsCover (ofMultiset M) k t lam ↔
      (∀ A ∈ M, A.card = k) ∧
      (∀ X : Finset α, X.card = t → lam ≤ M.countP (X ⊆ ·)))
#check (multiset_lower_bound : ∀ {α : Type u} [DecidableEq α] [Fintype α]
    {M : Multiset (Finset α)} {k t lam : ℕ} (_htk : t ≤ k) (_hkv : k ≤ Fintype.card α)
    (_hu : ∀ A ∈ M, A.card = k)
    (_hc : ∀ X : Finset α, X.card = t → lam ≤ M.countP (X ⊆ ·)),
    bound lam (Fintype.card α) k t ≤ M.card)

#check (Examples.empty_occurrences : ∀ {α : Type u} [DecidableEq α] (k t : ℕ),
    IsCover (fun i : Fin 0 => (Fin.elim0 i : Finset α)) k t 0)
#check (Examples.repeated_empty : ∀ {α : Type u} [DecidableEq α] (lam : ℕ),
    IsCover (fun _ : Fin lam => (∅ : Finset α)) 0 0 lam)
#check (Examples.empty_points : ∀ (lam : ℕ),
    IsCover (fun _ : Fin lam => (∅ : Finset PEmpty)) 0 0 lam)
#check (Examples.full_copies : ∀ {α : Type u} [DecidableEq α] [Fintype α] (lam t : ℕ),
    IsCover (fun _ : Fin lam => (univ : Finset α)) (Fintype.card α) t lam)
#check (Examples.full_copies_link : ∀ {α : Type u} [DecidableEq α] [Fintype α]
    (lam : ℕ) (X : Finset α),
    Fintype.card {_i : Fin lam // X ⊆ (univ : Finset α)} = lam ∧
      ∀ i, subsetLink (fun _ : Fin lam => (univ : Finset α)) X i = univ)
#check (Examples.empty_subset_link : ∀ {α : Type u} [DecidableEq α]
    {ι : Type v} [Fintype ι] {B : ι → Finset α} {k t lam : ℕ} (_h : IsCover B k t lam),
    Fintype.card {i // (∅ : Finset α) ⊆ B i} = Fintype.card ι ∧
      IsCover (subsetLink B ∅) k t lam)
#check (Examples.strength_zero_link : ∀ {α : Type u} [DecidableEq α]
    {ι : Type v} [Fintype ι] {B : ι → Finset α} {k t lam : ℕ}
    (_h : IsCover B k t lam) {X : Finset α} (_hX : X.card = t),
    IsCover (subsetLink B X) (k-t) 0 lam ∧ lam ≤ indexedSubsetDegree B X)
#check (Examples.deduplication_loses_multiplicity :
    IsCover (fun _ : Fin 2 => (∅ : Finset PEmpty)) 0 0 2 ∧
      ¬ Covers (ofFamily (deduplicate (fun _ : Fin 2 => (∅ : Finset PEmpty)))) 0 2)
#check (Examples.repeated_multiset : ∀ {α : Type u} [DecidableEq α] (lam : ℕ),
    Fintype.card (Multiset.replicate lam (∅ : Finset α)) = lam ∧
      IsCover (ofMultiset (Multiset.replicate lam (∅ : Finset α))) 0 0 lam)
#check (Examples.numerical_values : bound 2 4 3 2 = 4 ∧ bound 2 5 3 2 = 7)
#check (Examples.lower_bound_4_3_2 : ∀ {α : Type u} [DecidableEq α] [Fintype α]
    {ι : Type v} [Fintype ι] {B : ι → Finset α}
    (_hn : Fintype.card α = 4) (_h : IsCover B 3 2 2), 4 ≤ Fintype.card ι)
#check (Examples.lower_bound_5_3_2 : ∀ {α : Type u} [DecidableEq α] [Fintype α]
    {ι : Type v} [Fintype ι] {B : ι → Finset α}
    (_hn : Fintype.card α = 5) (_h : IsCover B 3 2 2), 7 ≤ Fintype.card ι)

end CoveringDesigns.Multicover

namespace CoveringDesigns.AuditMulticover
universe u v
theorem lower_bound_explicit {α : Type u} {ι : Type v}
    [Fintype α] [DecidableEq α] [Fintype ι]
    {B : ι → Finset α} {k t lam : ℕ}
    (htk : t ≤ k) (hkv : k ≤ Fintype.card α)
    (hu : ∀ i, (B i).card = k)
    (hc : ∀ X : Finset α, X.card = t →
      lam ≤ ((Finset.univ : Finset ι).filter (fun i => X ⊆ B i)).card) :
    Multicover.bound lam (Fintype.card α) k t ≤ Fintype.card ι :=
  Multicover.lower_bound htk hkv ⟨hu, hc⟩
end CoveringDesigns.AuditMulticover

-- Transitive foundational axiom guards for every public theorem.
#guard_standard_axioms CoveringDesigns.Multicover.subsetDegree_eq_card
#print axioms CoveringDesigns.Multicover.subsetDegree_eq_card
#guard_standard_axioms CoveringDesigns.Multicover.subsetDegree_empty
#print axioms CoveringDesigns.Multicover.subsetDegree_empty
#guard_standard_axioms CoveringDesigns.Multicover.subsetDegree_singleton
#print axioms CoveringDesigns.Multicover.subsetDegree_singleton
#guard_standard_axioms CoveringDesigns.Multicover.covers_zero_iff
#print axioms CoveringDesigns.Multicover.covers_zero_iff
#guard_standard_axioms CoveringDesigns.Multicover.covers_multiplicity_zero
#print axioms CoveringDesigns.Multicover.covers_multiplicity_zero
#guard_standard_axioms CoveringDesigns.Multicover.covers_one_iff
#print axioms CoveringDesigns.Multicover.covers_one_iff
#guard_standard_axioms CoveringDesigns.Multicover.reindex_card
#print axioms CoveringDesigns.Multicover.reindex_card
#guard_standard_axioms CoveringDesigns.Multicover.subsetDegree_reindex
#print axioms CoveringDesigns.Multicover.subsetDegree_reindex
#guard_standard_axioms CoveringDesigns.Multicover.degree_reindex
#print axioms CoveringDesigns.Multicover.degree_reindex
#guard_standard_axioms CoveringDesigns.Multicover.uniform_reindex
#print axioms CoveringDesigns.Multicover.uniform_reindex
#guard_standard_axioms CoveringDesigns.Multicover.covers_reindex
#print axioms CoveringDesigns.Multicover.covers_reindex
#guard_standard_axioms CoveringDesigns.Multicover.isCover_reindex
#print axioms CoveringDesigns.Multicover.isCover_reindex
#guard_standard_axioms CoveringDesigns.Multicover.subsetLink_card
#print axioms CoveringDesigns.Multicover.subsetLink_card
#guard_standard_axioms CoveringDesigns.Multicover.subsetLink_uniform
#print axioms CoveringDesigns.Multicover.subsetLink_uniform
#guard_standard_axioms CoveringDesigns.Multicover.subsetLink_multiplicity
#print axioms CoveringDesigns.Multicover.subsetLink_multiplicity
#guard_standard_axioms CoveringDesigns.Multicover.subsetLink_isCover
#print axioms CoveringDesigns.Multicover.subsetLink_isCover
#guard_standard_axioms CoveringDesigns.Multicover.subset_complement_card
#print axioms CoveringDesigns.Multicover.subset_complement_card
#guard_standard_axioms CoveringDesigns.Multicover.multiplicity_ge_of_coverLower
#print axioms CoveringDesigns.Multicover.multiplicity_ge_of_coverLower
#guard_standard_axioms CoveringDesigns.Multicover.degree_sum
#print axioms CoveringDesigns.Multicover.degree_sum
#guard_standard_axioms CoveringDesigns.Multicover.degree_sum_of_uniform
#print axioms CoveringDesigns.Multicover.degree_sum_of_uniform
#guard_standard_axioms CoveringDesigns.Multicover.subsetDegree_sum_of_uniform
#print axioms CoveringDesigns.Multicover.subsetDegree_sum_of_uniform
#guard_standard_axioms CoveringDesigns.Multicover.bound_of_links
#print axioms CoveringDesigns.Multicover.bound_of_links
#guard_standard_axioms CoveringDesigns.Multicover.lift_lower_bound
#print axioms CoveringDesigns.Multicover.lift_lower_bound
#guard_standard_axioms CoveringDesigns.Multicover.bound_zero
#print axioms CoveringDesigns.Multicover.bound_zero
#guard_standard_axioms CoveringDesigns.Multicover.bound_succ
#print axioms CoveringDesigns.Multicover.bound_succ
#guard_standard_axioms CoveringDesigns.Multicover.bound_one_eq
#print axioms CoveringDesigns.Multicover.bound_one_eq
#guard_standard_axioms CoveringDesigns.Multicover.bound_multiplicity_zero
#print axioms CoveringDesigns.Multicover.bound_multiplicity_zero
#guard_standard_axioms CoveringDesigns.Multicover.lower_bound
#print axioms CoveringDesigns.Multicover.lower_bound
#guard_standard_axioms CoveringDesigns.Multicover.schoenheim_coverLower
#print axioms CoveringDesigns.Multicover.schoenheim_coverLower
#guard_standard_axioms CoveringDesigns.Multicover.ofFamily_card
#print axioms CoveringDesigns.Multicover.ofFamily_card
#guard_standard_axioms CoveringDesigns.Multicover.ofFamily_subsetDegree
#print axioms CoveringDesigns.Multicover.ofFamily_subsetDegree
#guard_standard_axioms CoveringDesigns.Multicover.ofFamily_degree
#print axioms CoveringDesigns.Multicover.ofFamily_degree
#guard_standard_axioms CoveringDesigns.Multicover.ofFamily_uniform
#print axioms CoveringDesigns.Multicover.ofFamily_uniform
#guard_standard_axioms CoveringDesigns.Multicover.ofFamily_covers_one
#print axioms CoveringDesigns.Multicover.ofFamily_covers_one
#guard_standard_axioms CoveringDesigns.Multicover.ofFamily_isCover_one
#print axioms CoveringDesigns.Multicover.ofFamily_isCover_one
#guard_standard_axioms CoveringDesigns.Multicover.family_lower_bound
#print axioms CoveringDesigns.Multicover.family_lower_bound
#guard_standard_axioms CoveringDesigns.Multicover.deduplicate_card_le
#print axioms CoveringDesigns.Multicover.deduplicate_card_le
#guard_standard_axioms CoveringDesigns.Multicover.deduplicate_isCover_one
#print axioms CoveringDesigns.Multicover.deduplicate_isCover_one
#guard_standard_axioms CoveringDesigns.Multicover.ofMultiset_card
#print axioms CoveringDesigns.Multicover.ofMultiset_card
#guard_standard_axioms CoveringDesigns.Multicover.ofMultiset_subsetDegree
#print axioms CoveringDesigns.Multicover.ofMultiset_subsetDegree
#guard_standard_axioms CoveringDesigns.Multicover.ofMultiset_degree
#print axioms CoveringDesigns.Multicover.ofMultiset_degree
#guard_standard_axioms CoveringDesigns.Multicover.ofMultiset_uniform
#print axioms CoveringDesigns.Multicover.ofMultiset_uniform
#guard_standard_axioms CoveringDesigns.Multicover.ofMultiset_isCover
#print axioms CoveringDesigns.Multicover.ofMultiset_isCover
#guard_standard_axioms CoveringDesigns.Multicover.multiset_lower_bound
#print axioms CoveringDesigns.Multicover.multiset_lower_bound
#guard_standard_axioms CoveringDesigns.Multicover.Examples.empty_occurrences
#print axioms CoveringDesigns.Multicover.Examples.empty_occurrences
#guard_standard_axioms CoveringDesigns.Multicover.Examples.repeated_empty
#print axioms CoveringDesigns.Multicover.Examples.repeated_empty
#guard_standard_axioms CoveringDesigns.Multicover.Examples.empty_points
#print axioms CoveringDesigns.Multicover.Examples.empty_points
#guard_standard_axioms CoveringDesigns.Multicover.Examples.full_copies
#print axioms CoveringDesigns.Multicover.Examples.full_copies
#guard_standard_axioms CoveringDesigns.Multicover.Examples.full_copies_link
#print axioms CoveringDesigns.Multicover.Examples.full_copies_link
#guard_standard_axioms CoveringDesigns.Multicover.Examples.empty_subset_link
#print axioms CoveringDesigns.Multicover.Examples.empty_subset_link
#guard_standard_axioms CoveringDesigns.Multicover.Examples.strength_zero_link
#print axioms CoveringDesigns.Multicover.Examples.strength_zero_link
#guard_standard_axioms CoveringDesigns.Multicover.Examples.deduplication_loses_multiplicity
#print axioms CoveringDesigns.Multicover.Examples.deduplication_loses_multiplicity
#guard_standard_axioms CoveringDesigns.Multicover.Examples.repeated_multiset
#print axioms CoveringDesigns.Multicover.Examples.repeated_multiset
#guard_standard_axioms CoveringDesigns.Multicover.Examples.numerical_values
#print axioms CoveringDesigns.Multicover.Examples.numerical_values
#guard_standard_axioms CoveringDesigns.Multicover.Examples.lower_bound_4_3_2
#print axioms CoveringDesigns.Multicover.Examples.lower_bound_4_3_2
#guard_standard_axioms CoveringDesigns.Multicover.Examples.lower_bound_5_3_2
#print axioms CoveringDesigns.Multicover.Examples.lower_bound_5_3_2
#guard_standard_axioms CoveringDesigns.AuditMulticover.lower_bound_explicit
#print axioms CoveringDesigns.AuditMulticover.lower_bound_explicit
