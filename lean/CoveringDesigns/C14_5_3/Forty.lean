import CoveringDesigns.C14_5_3.Completion

/-! The original lower bound forty precedes irredundancy and every special
block argument. All covers here retain occurrence indices. -/
namespace CoveringDesigns.C14_5_3
open Finset
open LabelledCliques (extensions)
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

theorem exact_of_capacity {B : ι → Finset α} {k t : ℕ}
    (hB : Multicover.IsCover B k t 1)
    (he : k.choose t * Fintype.card ι = (Fintype.card α).choose t) :
    ExactDesign.IsDesign B k t 1 := by
  refine ⟨hB.1, ?_⟩
  have hs : (∑ T ∈ (univ : Finset α).powersetCard t, 1) =
      ∑ T ∈ (univ : Finset α).powersetCard t, indexedSubsetDegree B T := by
    rw [Multicover.subsetDegree_sum_of_uniform hB.1, he]
    simp
  have hp (T : Finset α) (hT : T ∈ (univ : Finset α).powersetCard t) :
      1 ≤ indexedSubsetDegree B T := hB.2 T (mem_powersetCard.mp hT).2
  intro T hT
  exact ((sum_eq_sum_iff_of_le hp).mp hs T (mem_powersetCard_univ.mpr hT)).symm

theorem point_floor {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (x : α) : 13 ≤ indexedDegree B x := by
  have h := Multicover.multiplicity_ge_of_coverLower hv hB (i := 1) (by omega)
    (Multicover.schoenheim_coverLower (by decide) (by decide)) (X := {x}) (by simp)
  norm_num [Multicover.bound, Schoenheim.ceilDiv, Multicover.subsetDegree_singleton] at h
  exact h

theorem pair_floor {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {P : Finset α} (hP : P.card = 2) :
    4 ≤ indexedSubsetDegree B P := by
  have h := Multicover.multiplicity_ge_of_coverLower hv hB (i := 2) (by omega)
    (Multicover.schoenheim_coverLower (by decide) (by decide)) hP
  norm_num [Multicover.bound, Schoenheim.ceilDiv] at h
  exact h

theorem minimum_link_exact {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {x : α} (hx : indexedDegree B x = 13) :
    ExactDesign.IsDesign (Multicover.subsetLink B {x}) 4 2 1 := by
  have hc : Multicover.IsCover (Multicover.subsetLink B {x}) 4 2 1 := by
    simpa using Multicover.subsetLink_isCover hB {x} (by simp)
  apply exact_of_capacity hc
  rw [Multicover.subsetLink_card, Multicover.subsetDegree_singleton, hx,
    Multicover.subset_complement_card, card_singleton, hv]
  decide

def residualBlocks (B : ι → Finset α) (x : α) :
    {i // x ∉ B i} → Finset {p : α // p ∉ ({x} : Finset α)} :=
  fun i => (B i.val).subtype (· ∉ ({x} : Finset α))

theorem residual_card (B : ι → Finset α) (x : α) :
    Fintype.card {i // x ∉ B i} = Fintype.card ι - indexedDegree B x := by
  rw [Fintype.card_subtype_compl (fun i => x ∈ B i)]
  simp [Fintype.card_subtype, indexedDegree]

theorem residual_uniform {B : ι → Finset α} (hB : Multicover.Uniform B 5) (x : α) :
    Multicover.Uniform (residualBlocks B x) 5 := by
  intro i
  rw [residualBlocks, card_subtype]
  have he : (B i.val).filter (· ∉ ({x} : Finset α)) = B i.val := by
    apply filter_eq_self.mpr
    intro p hp
    simp only [mem_singleton]
    intro he
    subst p
    exact i.property hp
  rw [he, hB]

/-- Actual blocks avoiding the point cover every noncollinear triple of its link. -/
theorem residual_completion {B : ι → Finset α}
    (hB : Multicover.IsCover B 5 3 1) (x : α) :
    IsCompletion (Multicover.subsetLink B {x}) (residualBlocks B x) := by
  classical
  refine ⟨residual_uniform hB.1 x, ?_⟩
  intro T hT
  have ht := mem_filter.mp hT
  have hcard := (mem_powersetCard.mp ht.1).2
  let T' := T.map (Function.Embedding.subtype _)
  have hcard' : T'.card = 3 := by simp [T', hcard]
  obtain ⟨i, hi⟩ := (Multicover.covers_one_iff B 3).mp hB.2 T' hcard'
  have hmiss : x ∉ B i := by
    intro hxi
    have hs : T ⊆ Multicover.subsetLink B {x} ⟨i, by simpa using hxi⟩ := by
      intro p hp
      apply mem_subtype.mpr
      exact hi (mem_map.mpr ⟨p, hp, rfl⟩)
    have hp := (multiplicity_pos_iff (Multicover.subsetLink B {x}) T).mpr
      ⟨⟨i, by simpa using hxi⟩, hs⟩
    omega
  apply Nat.succ_le_of_lt
  apply (multiplicity_pos_iff _ T).mpr
  refine ⟨⟨i, hmiss⟩, ?_⟩
  intro p hp
  apply mem_subtype.mpr
  exact hi (mem_map.mpr ⟨p, hp, rfl⟩)

theorem lower_bound_40 {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) : 40 ≤ Fintype.card ι := by
  by_contra hn
  have hs := Multicover.degree_sum_of_uniform hB.1
  have hex : ∃ x : α, indexedDegree B x = 13 := by
    by_contra hh
    push Not at hh
    have hl := sum_le_sum (s := (univ : Finset α))
      (fun x _ => show 14 ≤ indexedDegree B x by have := point_floor hv hB x; have := hh x; omega)
    simp only [sum_const, card_univ, Nat.nsmul_eq_mul, hv, hs] at hl
    omega
  obtain ⟨x, hx⟩ := hex
  have h := completion_at_least_27
    (by rw [Multicover.subset_complement_card, card_singleton, hv])
    (minimum_link_exact hv hB hx) (residual_completion hB x)
  rw [residual_card, hx] at h
  omega

/-- A private t-subset for each actual occurrence; stronger than injectivity. -/
def Irredundant (B : ι → Finset α) (t : ℕ) : Prop :=
  ∀ i, ∃ T : Finset α, T.card = t ∧ T ⊆ B i ∧ ∀ j, T ⊆ B j → j = i

theorem forty_irredundant {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) (hn : Fintype.card ι = 40) :
    Irredundant B 3 := by
  classical
  intro i
  by_contra hh
  push Not at hh
  let D := fun j : {j : ι // j ≠ i} => B j.val
  have hD : Multicover.IsCover D 5 3 1 := by
    refine ⟨fun j => hB.1 j.val, (Multicover.covers_one_iff D 3).mpr ?_⟩
    intro T ht
    obtain ⟨j, hj⟩ := (Multicover.covers_one_iff B 3).mp hB.2 T ht
    by_cases hji : j = i
    · subst j
      obtain ⟨j, hj, hji⟩ := hh T ht hj
      exact ⟨⟨j, hji⟩, hj⟩
    · exact ⟨⟨j, hji⟩, hj⟩
  have hd : Fintype.card {j : ι // j ≠ i} = 39 := by
    rw [Fintype.card_subtype_compl (fun j => j = i)]
    simp [Fintype.card_subtype, hn]
  have := lower_bound_40 hv hD
  rw [hd] at this
  omega

theorem Irredundant.injective {B : ι → Finset α} {t : ℕ} (hB : Irredundant B t) :
    Function.Injective B := by
  intro i j hij
  obtain ⟨T, ht, hi, hu⟩ := hB i
  exact (hu j (hij ▸ hi)).symm

theorem Irredundant.private_multiplicity {B : ι → Finset α} {t : ℕ}
    (hB : Irredundant B t) (i : ι) :
    ∃ T : Finset α, T.card = t ∧ T ⊆ B i ∧ indexedSubsetDegree B T = 1 := by
  obtain ⟨T, ht, hi, hu⟩ := hB i
  exact ⟨T, ht, hi, (multiplicity_one_iff B T).mpr ⟨i, hi, hu⟩⟩

theorem tight_extensions {B : ι → Finset α} {k m : ℕ}
    (hB : Multicover.Uniform B k) (S : Finset α)
    (hf : ∀ T ∈ extensions S, m ≤ indexedSubsetDegree B T)
    (he : (k-S.card) * indexedSubsetDegree B S = (Fintype.card α-S.card) * m) :
    ∀ T ∈ extensions S, indexedSubsetDegree B T = m := by
  have hs : (∑ T ∈ extensions S, m) = ∑ T ∈ extensions S, indexedSubsetDegree B T := by
    rw [LabelledCliques.extension_sum hB, he]
    simp [LabelledCliques.card_extensions]
  intro T hT
  exact ((sum_eq_sum_iff_of_le hf).mp hs T hT).symm

theorem minimum_pair_exact {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {x : α} (hx : indexedDegree B x = 13)
    {P : Finset α} (hP : P.card = 2) (hxP : x ∈ P) : indexedSubsetDegree B P = 4 := by
  apply tight_extensions hB.1 {x}
  · intro T hT
    apply pair_floor hv hB
    have := (LabelledCliques.mem_extensions.mp hT).2
    simpa using this
  · simp [Multicover.subsetDegree_singleton, hx, hv]
  · exact LabelledCliques.mem_extensions.mpr ⟨by simpa using hxP, by simpa using hP⟩

theorem minimum_triple_exact {B : ι → Finset α} (hv : Fintype.card α = 14)
    (hB : Multicover.IsCover B 5 3 1) {x : α} (hx : indexedDegree B x = 13)
    {T : Finset α} (hT : T.card = 3) (hxT : x ∈ T) : indexedSubsetDegree B T = 1 := by
  have hc : (T.erase x).card = 2 := by rw [card_erase_of_mem hxT, hT]
  obtain ⟨y, hy⟩ := card_pos.mp (show 0 < (T.erase x).card by omega)
  have hxy := (mem_erase.mp hy).1.symm
  let P : Finset α := {x,y}
  have hP : P.card = 2 := by simp [P, hxy]
  have hPT : P ⊆ T := by simp only [P, insert_subset_iff, singleton_subset_iff]; exact ⟨hxT, (mem_erase.mp hy).2⟩
  apply tight_extensions hB.1 P
  · intro U hU
    apply hB.2
    have := (LabelledCliques.mem_extensions.mp hU).2
    omega
  · rw [hP, minimum_pair_exact hv hB hx hP (by simp [P]), hv]
  · exact LabelledCliques.mem_extensions.mpr ⟨hPT, by omega⟩

end CoveringDesigns.C14_5_3
