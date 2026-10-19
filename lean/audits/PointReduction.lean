import CoveringDesigns.PointReduction
import CoveringDesigns.Foundations.StandardAxioms

/-! Full public contracts and transitive foundational-axiom guards. -/
namespace CoveringDesigns.PointReduction
open Finset
universe u v w

#print pullback
#print indexedSubsetDegree
#print Multicover.IsCover
#print Multicover.CoverLower

-- Basic
#check (mem_pullback : ∀ {α : Type u} {β : Type v} [DecidableEq α] [Fintype β] (e : β ↪ α) (A : Finset α) (x : β),
  x ∈ pullback e A ↔ e x ∈ A)

#check (pullback_card_le : ∀ {α : Type u} {β : Type v} [DecidableEq α] [Fintype β] (e : β ↪ α) (A : Finset α),
  (pullback e A).card ≤ A.card)

#check (exists_padding : ∀ {α : Type u} {β : Type v} {ι : Type w} [DecidableEq α] [Fintype β] (e : β ↪ α) (B : ι → Finset α) {k : ℕ}
    (hu : Multicover.Uniform B k) (hk : k ≤ Fintype.card β),
  ∃ B' : ι → Finset β, Multicover.Uniform B' k ∧
      ∀ i, pullback e (B i) ⊆ B' i)

#check (multiplicity_le : ∀ {α : Type u} {β : Type v} {ι : Type w} [DecidableEq α] [DecidableEq β] [Fintype β] [Fintype ι] (e : β ↪ α) (B : ι → Finset α)
    (B' : ι → Finset β) (hp : ∀ i, pullback e (B i) ⊆ B' i) (T : Finset β),
  indexedSubsetDegree B (T.map e) ≤ indexedSubsetDegree B' T)

#check (isCover_of_padding : ∀ {α : Type u} {β : Type v} {ι : Type w} [DecidableEq α] [DecidableEq β] [Fintype β] [Fintype ι] (e : β ↪ α)
    {B : ι → Finset α} {B' : ι → Finset β} {k t lam : ℕ}
    (h : Multicover.IsCover B k t lam) (hu : Multicover.Uniform B' k)
    (hp : ∀ i, pullback e (B i) ⊆ B' i),
  Multicover.IsCover B' k t lam)

#check (reduce_along : ∀ {α : Type u} {β : Type v} {ι : Type w} [DecidableEq α] [DecidableEq β] [Fintype β] [Fintype ι] (e : β ↪ α) {B : ι → Finset α} {k t lam : ℕ}
    (h : Multicover.IsCover B k t lam) (hk : k ≤ Fintype.card β),
  ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam ∧
      (∀ i, pullback e (B i) ⊆ B' i) ∧
      ∀ T : Finset β, indexedSubsetDegree B (T.map e) ≤ indexedSubsetDegree B' T)

#check (reduce_points : ∀ {α : Type u} {β : Type v} {ι : Type w} [DecidableEq α] [DecidableEq β] [Fintype β] [Fintype α] [Fintype ι] {B : ι → Finset α} {k t lam : ℕ}
    (h : Multicover.IsCover B k t lam) (hk : k ≤ Fintype.card β)
    (hv : Fintype.card β ≤ Fintype.card α),
  ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam)

#check (uniform_full : ∀ {β : Type v} {ι : Type w} [Fintype β] {B : ι → Finset β} {k : ℕ}
    (hu : Multicover.Uniform B k) (hk : k=Fintype.card β),
  ∀ i, B i=univ)

#check (reduce_points_explicit : ∀ {α : Type u} {β : Type v} {ι : Type w} [DecidableEq α] [DecidableEq β] [Fintype β] [Fintype α] [Fintype ι]
    {B : ι → Finset α} {k t lam : ℕ}
    (hu : ∀ i, (B i).card=k)
    (hc : ∀ T : Finset α, T.card=t → lam ≤ (univ.filter (fun i => T ⊆ B i)).card)
    (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α),
  ∃ B' : ι → Finset β, (∀ i, (B' i).card=k) ∧
      ∀ T : Finset β, T.card=t → lam ≤ (univ.filter (fun i => T ⊆ B' i)).card)

-- Bounds
#check (coverLower_mono : ∀ {v₀ v₁ k t lam L : ℕ}
    (hk : k ≤ v₀) (hv : v₀ ≤ v₁)
    (hl : Multicover.CoverLower.{u,w} v₀ k t lam L),
  Multicover.CoverLower.{u,w} v₁ k t lam L)

#check (exists_cover_le : ∀ {α : Type u} {β : Type v} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι]
    {k t lam b : ℕ} (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α)
    (h : ∃ B : ι → Finset α, Multicover.IsCover B k t lam ∧ Fintype.card ι ≤ b),
  ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam ∧ Fintype.card ι ≤ b)

#check (exists_cover_exact : ∀ {α : Type u} {β : Type v} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι]
    {k t lam b : ℕ} (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α)
    (h : ∃ B : ι → Finset α, Multicover.IsCover B k t lam ∧ Fintype.card ι=b),
  ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam ∧ Fintype.card ι=b)

-- Family
#check (family_reduce_points : ∀ {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {C : Family α} {k t : ℕ} (h : IsCover C k t)
    (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α),
  ∃ D : Family β, IsCover D k t ∧ D.card ≤ C.card)

#check (family_lower_mono : ∀ {v₀ v₁ k t L : ℕ} (hk : k ≤ v₀) (hv : v₀ ≤ v₁)
    (hl : ∀ {β : Type u} [Fintype β] [DecidableEq β] {D : Family β},
      Fintype.card β=v₀ → IsCover D k t → L ≤ D.card)
    {α : Type u} [Fintype α] [DecidableEq α] {C : Family α}
    (hn : Fintype.card α=v₁) (h : IsCover C k t),
  L ≤ C.card)

-- Examples
namespace Examples
#check (identity_reduction : ∀ {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {k t lam : ℕ}
    (h : Multicover.IsCover B k t lam) (hk : k ≤ Fintype.card α),
  ∃ B' : ι → Finset α, Multicover.IsCover B' k t lam ∧ B'=B)

#check (strength_zero : ∀ {α : Type u} {β : Type v} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι]
    {B : ι → Finset α} {k lam : ℕ} (h : Multicover.IsCover B k 0 lam)
    (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α),
  ∃ B' : ι → Finset β, Multicover.IsCover B' k 0 lam ∧ lam ≤ Fintype.card ι)

#check (zero_multiplicity : ∀ {α : Type u} {β : Type v} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι]
    {B : ι → Finset α} {k t : ℕ} (hu : Multicover.Uniform B k)
    (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α),
  ∃ B' : ι → Finset β, Multicover.IsCover B' k t 0)

#check (empty_reduction : ∃ B' : Fin 0 → Finset (Fin 0), Multicover.IsCover B' 0 0 0)

#check (triples_multiplicity : ∀ (T : Finset (Fin 4)),
  indexedSubsetDegree triples T=4-T.card)

#check (triples_cover : Multicover.IsCover triples 3 2 2)

#check (four_repeated_triples : ∃ B' : Fin 4 → Finset (Fin 3), Multicover.IsCover B' 3 2 2 ∧
      (∀ i, B' i=univ) ∧ Fintype.card (Fin 4)=4 ∧
      ∀ T : Finset (Fin 3), indexedSubsetDegree B' T=4)

end Examples

end CoveringDesigns.PointReduction

#guard_standard_axioms
  CoveringDesigns.PointReduction.mem_pullback
  CoveringDesigns.PointReduction.pullback_card_le
  CoveringDesigns.PointReduction.exists_padding
  CoveringDesigns.PointReduction.multiplicity_le
  CoveringDesigns.PointReduction.isCover_of_padding
  CoveringDesigns.PointReduction.reduce_along
  CoveringDesigns.PointReduction.reduce_points
  CoveringDesigns.PointReduction.uniform_full
  CoveringDesigns.PointReduction.reduce_points_explicit
  CoveringDesigns.PointReduction.coverLower_mono
  CoveringDesigns.PointReduction.exists_cover_le
  CoveringDesigns.PointReduction.exists_cover_exact
  CoveringDesigns.PointReduction.family_reduce_points
  CoveringDesigns.PointReduction.family_lower_mono
  CoveringDesigns.PointReduction.Examples.identity_reduction
  CoveringDesigns.PointReduction.Examples.strength_zero
  CoveringDesigns.PointReduction.Examples.zero_multiplicity
  CoveringDesigns.PointReduction.Examples.empty_reduction
  CoveringDesigns.PointReduction.Examples.triples_multiplicity
  CoveringDesigns.PointReduction.Examples.triples_cover
  CoveringDesigns.PointReduction.Examples.four_repeated_triples

#print axioms CoveringDesigns.PointReduction.mem_pullback
#print axioms CoveringDesigns.PointReduction.pullback_card_le
#print axioms CoveringDesigns.PointReduction.exists_padding
#print axioms CoveringDesigns.PointReduction.multiplicity_le
#print axioms CoveringDesigns.PointReduction.isCover_of_padding
#print axioms CoveringDesigns.PointReduction.reduce_along
#print axioms CoveringDesigns.PointReduction.reduce_points
#print axioms CoveringDesigns.PointReduction.uniform_full
#print axioms CoveringDesigns.PointReduction.reduce_points_explicit
#print axioms CoveringDesigns.PointReduction.coverLower_mono
#print axioms CoveringDesigns.PointReduction.exists_cover_le
#print axioms CoveringDesigns.PointReduction.exists_cover_exact
#print axioms CoveringDesigns.PointReduction.family_reduce_points
#print axioms CoveringDesigns.PointReduction.family_lower_mono
#print axioms CoveringDesigns.PointReduction.Examples.identity_reduction
#print axioms CoveringDesigns.PointReduction.Examples.strength_zero
#print axioms CoveringDesigns.PointReduction.Examples.zero_multiplicity
#print axioms CoveringDesigns.PointReduction.Examples.empty_reduction
#print axioms CoveringDesigns.PointReduction.Examples.triples_multiplicity
#print axioms CoveringDesigns.PointReduction.Examples.triples_cover
#print axioms CoveringDesigns.PointReduction.Examples.four_repeated_triples
