import CoveringDesigns.Multicover.Basic
import Mathlib.Data.Fintype.EquivFin

/-! Occurrence-preserving restriction and padding, independent of affine geometry.
The standard transformation is used in Horsley–Singh §4. Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.PointReduction
open Finset
universe u v w
variable {α : Type u} {β : Type v} {ι : Type w}
  [DecidableEq α] [DecidableEq β] [Fintype β]

def pullback (e : β ↪ α) (A : Finset α) : Finset β := univ.filter (fun x => e x ∈ A)

omit [DecidableEq β] in
@[simp] theorem mem_pullback (e : β ↪ α) (A : Finset α) (x : β) :
    x ∈ pullback e A ↔ e x ∈ A := by simp [pullback]

omit [DecidableEq β] in
theorem pullback_card_le (e : β ↪ α) (A : Finset α) : (pullback e A).card ≤ A.card := by
  have he : (pullback e A).map e ⊆ A := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact (mem_pullback e A y).mp hy
  simpa only [card_map] using card_le_card he

omit [DecidableEq β] in
/-- Padding is chosen separately for each occurrence, without identifying equal blocks. -/
theorem exists_padding (e : β ↪ α) (B : ι → Finset α) {k : ℕ}
    (hu : Multicover.Uniform B k) (hk : k ≤ Fintype.card β) :
    ∃ B' : ι → Finset β, Multicover.Uniform B' k ∧
      ∀ i, pullback e (B i) ⊆ B' i := by
  have hp (i : ι) : ∃ U : Finset β, pullback e (B i) ⊆ U ∧ U.card=k := by
    obtain ⟨U, hU, _, hc⟩ := exists_subsuperset_card_eq (subset_univ (pullback e (B i)))
      ((pullback_card_le e (B i)).trans_eq (hu i)) (by simpa using hk)
    exact ⟨U, hU, hc⟩
  choose B' hs hc using hp
  exact ⟨B', hc, hs⟩

/-- Containment alone gives monotonicity of every indexed subset multiplicity. -/
theorem multiplicity_le [Fintype ι] (e : β ↪ α) (B : ι → Finset α)
    (B' : ι → Finset β) (hp : ∀ i, pullback e (B i) ⊆ B' i) (T : Finset β) :
    indexedSubsetDegree B (T.map e) ≤ indexedSubsetDegree B' T := by
  unfold indexedSubsetDegree
  apply card_le_card
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  intro x hx
  exact hp i ((mem_pullback e (B i) x).mpr (hi (mem_map.mpr ⟨x, hx, rfl⟩)))

theorem isCover_of_padding [Fintype ι] (e : β ↪ α)
    {B : ι → Finset α} {B' : ι → Finset β} {k t lam : ℕ}
    (h : Multicover.IsCover B k t lam) (hu : Multicover.Uniform B' k)
    (hp : ∀ i, pullback e (B i) ⊆ B' i) : Multicover.IsCover B' k t lam := by
  refine ⟨hu, fun T ht => ?_⟩
  exact (h.2 (T.map e) (by simpa using ht)).trans (multiplicity_le e B B' hp T)

/-- Reduction along a supplied embedding, with the same occurrence type and all counts. -/
theorem reduce_along [Fintype ι] (e : β ↪ α) {B : ι → Finset α} {k t lam : ℕ}
    (h : Multicover.IsCover B k t lam) (hk : k ≤ Fintype.card β) :
    ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam ∧
      (∀ i, pullback e (B i) ⊆ B' i) ∧
      ∀ T : Finset β, indexedSubsetDegree B (T.map e) ≤ indexedSubsetDegree B' T := by
  obtain ⟨B', hu, hp⟩ := exists_padding e B h.1 hk
  exact ⟨B', isCover_of_padding e h hu hp, hp, multiplicity_le e B B' hp⟩

/-- Point-count reduction for all natural multiplicities, including zero.
The occurrence type is literally unchanged; no injectivity premise is needed. -/
theorem reduce_points [Fintype α] [Fintype ι] {B : ι → Finset α} {k t lam : ℕ}
    (h : Multicover.IsCover B k t lam) (hk : k ≤ Fintype.card β)
    (hv : Fintype.card β ≤ Fintype.card α) :
    ∃ B' : ι → Finset β, Multicover.IsCover B' k t lam := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hv
  obtain ⟨B', hB', _, _⟩ := reduce_along e h hk
  exact ⟨B', hB'⟩

omit [DecidableEq β] in
/-- A full-size block on the target contains every target point. -/
theorem uniform_full {B : ι → Finset β} {k : ℕ}
    (hu : Multicover.Uniform B k) (hk : k=Fintype.card β) : ∀ i, B i=univ := by
  intro i
  exact eq_of_subset_of_card_le (subset_univ _) (by simp [hu i, hk])

/-- Expanded contract states uniformity, coverage and the retained occurrence type. -/
theorem reduce_points_explicit [Fintype α] [Fintype ι]
    {B : ι → Finset α} {k t lam : ℕ}
    (hu : ∀ i, (B i).card=k)
    (hc : ∀ T : Finset α, T.card=t → lam ≤ (univ.filter (fun i => T ⊆ B i)).card)
    (hk : k ≤ Fintype.card β) (hv : Fintype.card β ≤ Fintype.card α) :
    ∃ B' : ι → Finset β, (∀ i, (B' i).card=k) ∧
      ∀ T : Finset β, T.card=t → lam ≤ (univ.filter (fun i => T ⊆ B' i)).card :=
  reduce_points ⟨hu, hc⟩ hk hv

end CoveringDesigns.PointReduction
