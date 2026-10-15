import CoveringDesigns.C11_5_2.Geometry.Representatives

/-! Intrinsic statements of the Stanton properties used in GPPT Sections 4–5.
The finite proofs inspect the displayed representatives; generic relabelling
then makes each statement independent of the chosen coordinates. -/

namespace CoveringDesigns.StantonGeometry

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def shortPoints (C : Family α) : Finset α := univ.filter (IsShortPoint C)
def couples (C : Family α) : Family α :=
  ((univ : Finset α).powersetCard 2).filter (IsCouple C)
def fullBlocks (C : Family α) : Family α := C.filter fun B => ¬ IsShortBlock C B

structure Facts (C : Family α) : Prop where
  short_exists : ∃ B ∈ C, IsShortBlock C B
  short_unique : ∀ B ∈ C, ∀ D ∈ C, IsShortBlock C B → IsShortBlock C D → B = D
  short_points_card : (shortPoints C).card = 3
  couples_card : (couples C).card = 4
  point_partition : ∀ x, IsShortPoint C x ∨ ∃ y, x ≠ y ∧ IsCouple C {x, y}
  couple_no_short : ∀ x y, IsCouple C {x, y} → ¬ IsShortPoint C x ∧ ¬ IsShortPoint C y
  spouse_unique : ∀ x y z, IsCouple C {x, y} → IsCouple C {x, z} → y = z
  short_members : ∀ B ∈ C, IsShortBlock C B →
    ∀ x ∈ B, IsShortPoint C x ∨ degree C x = 4
  free_in_short : ∀ x, degree C x = 4 → ∀ B ∈ C, IsShortBlock C B → x ∈ B
  full_pair_cover : ∀ x y, x ≠ y → ¬ IsShortPoint C x →
    ∃ B ∈ fullBlocks C, x ∈ B ∧ y ∈ B
  full_couples : ∀ B ∈ fullBlocks C, coupleCount C B = 2
  full_intersection : ∀ B ∈ fullBlocks C, ∀ D ∈ fullBlocks C, B ≠ D →
    IsCouple C (B ∩ D) ∨ ∃ x, IsShortPoint C x ∧ B ∩ D = {x}
  short_full_meet : ∀ S ∈ C, IsShortBlock C S → ∀ B ∈ fullBlocks C,
    ∃ x, IsShortPoint C x ∧ x ∈ S ∧ x ∈ B
  couple_full_count : ∀ x y, IsCouple C {x, y} → multiplicity (fullBlocks C) {x, y} = 3
  split_couple_short : ∀ x y, IsCouple C {x, y} → ∀ B ∈ C,
    x ∈ B → y ∉ B → IsShortBlock C B
  two_short_points : ∀ B ∈ C, ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
    IsShortPoint C x → IsShortPoint C y → IsShortBlock C B
  multiplicity_two_short : ∀ x y, x ≠ y → multiplicity C {x, y} = 2 →
    ∃ B ∈ C, IsShortBlock C B ∧ x ∈ B ∧ y ∈ B
  multiplicity_two_free : ∀ x y, x ≠ y → multiplicity C {x, y} = 2 →
    degree C x = 4 ∨ degree C y = 4
  full_pair_count_ne_two : ∀ x y, x ≠ y → multiplicity (fullBlocks C) {x, y} ≠ 2
  short_two_full : ∀ x, IsShortPoint C x →
    ∃ B ∈ fullBlocks C, ∃ D ∈ fullBlocks C, B ≠ D ∧ B ∩ D = {x}

omit [Fintype α] [Fintype β] in
theorem fullBlocks_relabel (e : α ≃ β) (C : Family α) :
    fullBlocks (relabel e C) = relabel e (fullBlocks C) := by
  unfold fullBlocks relabel
  rw [filter_map]
  congr 1
  ext B
  simp only [mem_filter]
  change (B ∈ C ∧ ¬ IsShortBlock (relabel e C) (B.map e.toEmbedding)) ↔ _
  simp

theorem shortPoints_relabel (e : α ≃ β) (C : Family α) :
    shortPoints (relabel e C) = (shortPoints C).map e.toEmbedding := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp [shortPoints]

theorem couples_relabel (e : α ≃ β) (C : Family α) :
    couples (relabel e C) = relabel e (couples C) := by
  unfold couples relabel
  rw [← (map_univ_equiv e), powersetCard_map, filter_map]
  congr 1
  ext K
  simp only [mem_filter]
  change (K ∈ univ.powersetCard 2 ∧ IsCouple (relabel e C) (K.map e.toEmbedding)) ↔ _
  simp

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
private theorem forall_points (e : α ≃ β) (P : β → Prop) :
    (∀ x, P x) ↔ ∀ x, P (e x) := e.surjective.forall

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
private theorem exists_points (e : α ≃ β) (P : β → Prop) :
    (∃ x, P x) ↔ ∃ x, P (e x) := e.surjective.exists

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
private theorem forall_blocks (e : α ≃ β) (P : Finset β → Prop) :
    (∀ B, P B) ↔ ∀ B : Finset α, P (B.map e.toEmbedding) :=
  (Equiv.finsetCongr e).surjective.forall

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
private theorem exists_blocks (e : α ≃ β) (P : Finset β → Prop) :
    (∃ B, P B) ↔ ∃ B : Finset α, P (B.map e.toEmbedding) :=
  (Equiv.finsetCongr e).surjective.exists

omit [Fintype α] [Fintype β] in
@[simp] theorem multiplicity_pair_relabel (e : α ≃ β) (C : Family α) (x y : α) :
    multiplicity (relabel e C) {e x, e y} = multiplicity C {x, y} := by
  simpa only [map_insert, map_singleton, Equiv.coe_toEmbedding] using
    multiplicity_relabel e C {x, y}

omit [Fintype α] [Fintype β] in
@[simp] theorem isCouple_pair_relabel (e : α ≃ β) (C : Family α) (x y : α) :
    IsCouple (relabel e C) {e x, e y} ↔ IsCouple C {x, y} := by
  simpa only [map_insert, map_singleton, Equiv.coe_toEmbedding] using
    isCouple_relabel e C {x, y}

omit [Fintype α] [Fintype β] in
private theorem map_eq_singleton (e : α ≃ β) (B : Finset α) (x : α) :
    B.map e.toEmbedding = {e x} ↔ B = {x} := by
  change B.map e.toEmbedding = ({x} : Finset α).map e.toEmbedding ↔ _
  exact map_inj

theorem Facts.relabel {C : Family α} (h : Facts C) (e : α ≃ β) : Facts (relabel e C) := by
  constructor
  all_goals first
    | simpa only [shortPoints_relabel, card_map] using h.short_points_card
    | simpa only [couples_relabel, relabel_card] using h.couples_card
    | skip
  all_goals simp only [forall_blocks e, exists_blocks e, forall_points e, exists_points e,
    fullBlocks_relabel, mem_relabel, mem_map_equiv, Equiv.symm_apply_apply,
    isShortBlock_relabel, isShortPoint_relabel, degree_relabel, coupleCount_relabel,
    isCouple_pair_relabel, multiplicity_pair_relabel, ← map_inter,
    isCouple_relabel, map_eq_singleton, ne_eq, map_inj, e.injective.eq_iff]
  · exact h.short_exists
  · exact h.short_unique
  · exact h.point_partition
  · exact h.couple_no_short
  · exact h.spouse_unique
  · exact h.short_members
  · exact h.free_in_short
  · exact h.full_pair_cover
  · exact h.full_couples
  · exact h.full_intersection
  · exact h.short_full_meet
  · exact h.couple_full_count
  · exact h.split_couple_short
  · exact h.two_short_points
  · exact h.multiplicity_two_short
  · exact h.multiplicity_two_free
  · exact h.full_pair_count_ne_two
  · exact h.short_two_full

theorem Facts.two_full_couple {C : Family α} (h : Facts C) (x y : α) (hxy : x ≠ y)
    {B D : Finset α} (hB : B ∈ fullBlocks C) (hD : D ∈ fullBlocks C)
    (hBD : B ≠ D) (hxB : x ∈ B) (hyB : y ∈ B) (hxD : x ∈ D) (hyD : y ∈ D) :
    IsCouple C {x, y} := by
  have hs : ({x, y} : Finset α) ⊆ B ∩ D := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨mem_inter.mpr ⟨hxB, hxD⟩, mem_inter.mpr ⟨hyB, hyD⟩⟩
  rcases h.full_intersection B hB D hD hBD with hk | ⟨z, _, he⟩
  · have he : ({x, y} : Finset α) = B ∩ D :=
      eq_of_subset_of_card_le hs (by rw [hk.1]; simp [hxy])
    rwa [he]
  · have hx : x = z := mem_singleton.mp (he ▸ mem_inter.mpr ⟨hxB, hxD⟩)
    have hy : y = z := mem_singleton.mp (he ▸ mem_inter.mpr ⟨hyB, hyD⟩)
    exact False.elim (hxy (hx.trans hy.symm))

section FixedChecks
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 512

theorem representative_facts (tag : Bool) : Facts (stantonRepresentative tag) := by
  constructor
  all_goals cases tag <;> decide +kernel

end FixedChecks

#guard_standard_axioms Facts.relabel representative_facts

end CoveringDesigns.StantonGeometry
