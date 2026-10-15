import CoveringDesigns.C13_7_4.Structural.Basic
import CoveringDesigns.C13_7_4.Structural.GPPTGeometry
import CoveringDesigns.C13_7_4.Structural.SwapObstruction

/-! Structural exclusions for aligned ordinary minimum links.
The normal-form extraction is separate from the matching obstructions here. -/

namespace CoveringDesigns.C13Structural

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace FiveIntersectionMatching

variable {C : Family α} {r : α}

/-- Four disjoint intersection pairs with no common point after deletion
exclude both alternatives in the structural GPPT theorem. -/
theorem not_minimum_four (M : FiveIntersectionMatching C r 4)
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    (hcommon : ∀ x, (∀ j, x ∈ M.block j) → x = r) : degree C r ≠ 15 := by
  intro hr
  rcases minimum_geometry (by rw [complement_point_card, hn])
    (link_isCover hC r) (by rw [link_card, hr]) with hG | hG
  · obtain ⟨G⟩ := hG
    have := G.matching_le_three M.toLink
    omega
  · obtain ⟨G⟩ := hG
    exact M.not_exceptional hcommon G

/-- Three pairs suffice if all endpoints meet two local degree-seven points. -/
theorem not_minimum_three (M : FiveIntersectionMatching C r 3)
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    (hcommon : ∀ x, (∀ j, x ∈ M.block j) → x = r)
    (p q : α) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : degree (star C p) r = 7) (hq : degree (star C q) r = 7)
    (hroots : ∀ j, p ∈ M.block j ∨ q ∈ M.block j) : degree C r ≠ 15 := by
  intro hr
  rcases minimum_geometry (by rw [complement_point_card, hn])
    (link_isCover hC r) (by rw [link_card, hr]) with hG | hG
  · obtain ⟨G⟩ := hG
    let p' : {x : α // x ≠ r} := ⟨p, hpr⟩
    let q' : {x : α // x ≠ r} := ⟨q, hqr⟩
    have hp' : degree (link C r) p' = 7 := by
      rw [degree_link, pair_degree_comm]
      exact hp
    have hq' : degree (link C r) q' = 7 := by
      rw [degree_link, pair_degree_comm]
      exact hq
    have hh : ∀ j, p' ∈ M.toLink.block j ∨ q' ∈ M.toLink.block j := by
      intro j
      simpa [toLink, deletedBlock, p', q'] using hroots j
    have := G.matching_le_two_of_degree_seven M.toLink p' q' hp' hq' hh
    omega
  · obtain ⟨G⟩ := hG
    exact M.not_exceptional hcommon G

end FiveIntersectionMatching

/-- In a minimum point's star, two distinct global blocks meet at most five times. -/
theorem minimum_global_block_inter_le_five {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) {r : α}
    (hr : degree C r = 15) {B D : Finset α}
    (hB : B ∈ C) (hD : D ∈ C) (hrB : r ∈ B) (hrD : r ∈ D) (hne : B ≠ D) :
    (B ∩ D).card ≤ 5 := by
  let B' := B.subtype (· ≠ r)
  let D' := D.subtype (· ≠ r)
  have hB' : B' ∈ link C r := mem_image.mpr ⟨B, mem_filter.mpr ⟨hB, hrB⟩, rfl⟩
  have hD' : D' ∈ link C r := mem_image.mpr ⟨D, mem_filter.mpr ⟨hD, hrD⟩, rfl⟩
  have hne' : B' ≠ D' := fun he => hne ((subtype_ne_inj hrB hrD).mp he)
  have hh := minimum_block_inter_le_four
    (by rw [complement_point_card, hn]) (link_isCover hC r)
    (by rw [link_card, hr]) hB' hD' hne'
  rw [subtype_ne_inter_card hrB hrD] at hh
  omega

/-- All twelve private full blocks forced by a single spouse swap occur. -/
def HasSwappedPrivateRows (C : Family α) (e : SwapPoint ↪ α) : Prop :=
  ∀ i b, (swappedPrivateBlock i b).map e ∈ C

def embeddedCompanionMatching {C : Family α} (e : SwapPoint ↪ α)
    (hprivate : HasSwappedPrivateRows C e) (k : Fin 3) :
    FiveIntersectionMatching C (e (swapCompanion k)) 4 :=
  embeddedFiveMatching e (swapCompanion k) (companionMatchingBlock k)
    (companionMatchingBlock_injective k)
    (fun _ => hprivate _ _) (companionMatchingBlock_through k)
    (companionMatchingBlock_inter k)

def embeddedSpouseMatching {C : Family α} (e : SwapPoint ↪ α)
    (hprivate : HasSwappedPrivateRows C e) (v : Fin 4) (b : Bool) (hv : v ≠ 0) :
    FiveIntersectionMatching C (e (swapSpouse v b)) 3 :=
  embeddedFiveMatching e (swapSpouse v b) (spouseMatchingBlock v b)
    (spouseMatchingBlock_injective v b)
    (fun _ => hprivate _ _) (spouseMatchingBlock_through v b hv)
    (spouseMatchingBlock_inter v b)

theorem swapped_companion_not_minimum {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    (e : SwapPoint ↪ α) (hprivate : HasSwappedPrivateRows C e) (k : Fin 3) :
    degree C (e (swapCompanion k)) ≠ 15 := by
  apply (embeddedCompanionMatching e hprivate k).not_minimum_four hn hC
  exact embedded_common (by decide : 0 < 4) e (swapCompanion k)
    (companionMatchingBlock k) (companionMatchingBlock_common k)

theorem swapped_degree_seven_spouse_not_minimum {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    (e : SwapPoint ↪ α) (hprivate : HasSwappedPrivateRows C e)
    (v : Fin 4) (b : Bool) (hv : v ≠ 0)
    (hp : degree (star C (e (swapRoot false))) (e (swapSpouse v b)) = 7)
    (hq : degree (star C (e (swapRoot true))) (e (swapSpouse v b)) = 7) :
    degree C (e (swapSpouse v b)) ≠ 15 := by
  let M := embeddedSpouseMatching e hprivate v b hv
  apply M.not_minimum_three hn hC
    (embedded_common (by decide : 0 < 3) e (swapSpouse v b)
      (spouseMatchingBlock v b) (spouseMatchingBlock_common v b hv))
    (e (swapRoot false)) (e (swapRoot true))
  · intro h
    have he := e.injective h
    simp [swapRoot, swapSpouse] at he
  · intro h
    have he := e.injective h
    simp [swapRoot, swapSpouse] at he
  · exact hp
  · exact hq
  · intro j
    simpa [M, embeddedSpouseMatching, embeddedFiveMatching] using
      spouseMatchingBlock_roots v b j

/-- A fourth pair of common rows supplements the three private pairs. -/
theorem swapped_spouse_not_minimum_of_extra_pair {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    (e : SwapPoint ↪ α) (hprivate : HasSwappedPrivateRows C e)
    (v : Fin 4) (b : Bool) (hv : v ≠ 0) (B D : Finset SwapPoint)
    (hB : B.map e ∈ C) (hD : D.map e ∈ C)
    (hBroots : ∀ a, swapRoot a ∈ B) (hDroots : ∀ a, swapRoot a ∈ D)
    (hBD : B ≠ D) (hinter : (B ∩ D).card = 5)
    (hrB : swapSpouse v b ∈ B) (hrD : swapSpouse v b ∈ D) :
    degree C (e (swapSpouse v b)) ≠ 15 := by
  let M := embeddedSpouseMatching e hprivate v b hv
  have hBM : ∀ j, B.map e ≠ M.block j := by
    intro j h
    exact ne_swappedPrivateBlock_of_roots B hBroots
      (j.1, spouseOrientation j.1 v b) j.2 ((Finset.map_injective e) h)
  have hDM : ∀ j, D.map e ≠ M.block j := by
    intro j h
    exact ne_swappedPrivateBlock_of_roots D hDroots
      (j.1, spouseOrientation j.1 v b) j.2 ((Finset.map_injective e) h)
  have hBD' : B.map e ≠ D.map e := fun h => hBD ((Finset.map_injective e) h)
  have hinter' : (B.map e ∩ D.map e).card = 5 := by
    rw [← map_inter, card_map, hinter]
  have hrB' : e (swapSpouse v b) ∈ B.map e := mem_map.mpr ⟨_, hrB, rfl⟩
  have hrD' : e (swapSpouse v b) ∈ D.map e := mem_map.mpr ⟨_, hrD, rfl⟩
  have hcommon : ∀ x, (∀ j, x ∈ M.block j) → x = e (swapSpouse v b) :=
    embedded_common (by decide : 0 < 3) e (swapSpouse v b)
      (spouseMatchingBlock v b) (spouseMatchingBlock_common v b hv)
  let N := M.extend (B.map e) (D.map e) hB hD hrB' hrD' hBD' hBM hDM hinter'
  exact N.not_minimum_four hn hC
    (M.extend_common hcommon _ _ hB hD hrB' hrD' hBD' hBM hDM hinter')

/-- An addition in the own-spine completion supplies the extra pair. -/
theorem swapped_addition_not_minimum {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    (e : SwapPoint ↪ α) (hprivate : HasSwappedPrivateRows C e)
    (hcommon : ∀ i, (swappedCommonBlock i).map e ∈ C)
    (R : Finset (Fin 4 × Bool)) (hR : R.card = 2)
    (hown : (swappedOwnBlock (R.image Sum.inr)).map e ∈ C)
    (v : Fin 4) (b : Bool) (hv : v ≠ 0) (hvr : (v, b) ∈ R) :
    degree C (e (swapSpouse v b)) ≠ 15 := by
  obtain ⟨i, hi⟩ := additions_in_common R hR
  apply swapped_spouse_not_minimum_of_extra_pair hn hC e hprivate v b hv
    (swappedOwnBlock (R.image Sum.inr)) (swappedCommonBlock i)
    hown (hcommon i) (swappedOwnBlock_roots _) (swappedCommonBlock_roots i)
    (swappedOwnBlock_ne_common _ i) (swappedOwnBlock_common_inter_card R hR i hi)
    (swappedOwnBlock_addition R hvr)
  cases b <;> simp [swappedCommonBlock, swapSpouse, swapRoot, commonTrace, hi (v, _) hvr]

/-- The foreign completed row supplies the extra pair for the x-points. -/
theorem swapped_foreign_spouse_not_minimum {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    (e : SwapPoint ↪ α) (hprivate : HasSwappedPrivateRows C e)
    (hcommon : ∀ i, (swappedCommonBlock i).map e ∈ C)
    (hforeign : swappedForeignBlock.map e ∈ C)
    (v : Fin 4) (hv : v ≠ 0) : degree C (e (swapSpouse v false)) ≠ 15 := by
  obtain ⟨i, hinter, hr, hne⟩ := foreign_common_extra_pair v hv
  exact swapped_spouse_not_minimum_of_extra_pair hn hC e hprivate v false hv
    swappedForeignBlock (swappedCommonBlock i) hforeign (hcommon i)
    swappedForeignBlock_roots (swappedCommonBlock_roots i) hne hinter
    (mem_inter.mp hr).1 (mem_inter.mp hr).2

/-- The forced rows shared by the multiplicity-eight and multiplicity-nine forms. -/
structure AlignedSwapRows (C : Family α) (e : SwapPoint ≃ α)
    (R : Finset (Fin 4 × Bool)) : Prop where
  private_mem : HasSwappedPrivateRows C e.toEmbedding
  common_mem : ∀ i, (swappedCommonBlock i).map e.toEmbedding ∈ C
  own_mem : (swappedOwnBlock (R.image Sum.inr)).map e.toEmbedding ∈ C
  additions_card : R.card = 2

def swappedExceptionalPoints : Finset SwapPoint :=
  {swapRoot false, swapRoot true, swapSpouse 0 false, swapSpouse 0 true}

theorem swappedExceptionalPoints_card : swappedExceptionalPoints.card = 4 := by decide +kernel

/-- The geometry confines all minimum points to the two roots and swapped pair. -/
theorem swapped_minimum_card_le_four {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    (e : SwapPoint ≃ α) (hprivate : HasSwappedPrivateRows C e.toEmbedding)
    (hspouse : ∀ v b, v ≠ 0 → degree C (e (swapSpouse v b)) ≠ 15) :
    (minimumPoints C 15).card ≤ 4 := by
  have hsub : minimumPoints C 15 ⊆ swappedExceptionalPoints.map e.toEmbedding := by
    intro x hx
    have hd := (mem_filter.mp hx).2
    obtain ⟨z, rfl⟩ := e.surjective x
    apply mem_map.mpr
    refine ⟨z, ?_, rfl⟩
    rcases z with a | (k | ⟨v, b⟩)
    · cases a <;> simp [swappedExceptionalPoints, swapRoot]
    · exact False.elim (swapped_companion_not_minimum hn hC e.toEmbedding hprivate k hd)
    · by_cases hv : v = 0
      · subst v
        cases b <;> simp [swappedExceptionalPoints, swapSpouse]
      · exact False.elim (hspouse v b hv hd)
  have hh := card_le_card hsub
  simpa [card_map, swappedExceptionalPoints_card] using hh

/-- One spouse-swap obstruction excludes both multiplicities eight and nine.
The degree-seven side condition records the degrees read from the two
completed-spine decompositions, only at y-points outside the additions. -/
theorem spouse_swap_impossible {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) (hb : C.card ≤ 29)
    (e : SwapPoint ≃ α) (R : Finset (Fin 4 × Bool)) (H : AlignedSwapRows C e R)
    (hforeign : swappedForeignBlock.map e.toEmbedding ∈ C)
    (hlow : ∀ v, v ≠ 0 → (v, true) ∉ R →
      degree (star C (e (swapRoot false))) (e (swapSpouse v true)) = 7 ∧
      degree (star C (e (swapRoot true))) (e (swapSpouse v true)) = 7) : False := by
  have hh := swapped_minimum_card_le_four hn hC e H.private_mem
    (fun v b hv => by
      cases b with
      | false =>
        exact swapped_foreign_spouse_not_minimum hn hC e.toEmbedding
          H.private_mem H.common_mem hforeign v hv
      | true =>
        by_cases hr : (v, true) ∈ R
        · exact swapped_addition_not_minimum hn hC e.toEmbedding H.private_mem
            H.common_mem R H.additions_card H.own_mem v true hv hr
        · exact swapped_degree_seven_spouse_not_minimum hn hC e.toEmbedding
            H.private_mem v true hv (hlow v hv hr).1 (hlow v hv hr).2)
  have hl := five_minimum_points hn hC hb
  omega

/-- Identical private cores force every third point to be nonminimum. -/
theorem identical_private_point_not_minimum {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    (e : SwapPoint ↪ α)
    (hrows : ∀ i b, (identicalPrivateBlock i b).map e ∈ C) (z : TracePoint) :
    degree C (e (Sum.inr z)) ≠ 15 := by
  intro hz
  obtain ⟨i, hi⟩ := privateTrace_covers_points z
  have hmem (b : Bool) : e (Sum.inr z) ∈ (identicalPrivateBlock i b).map e :=
    mem_map.mpr ⟨_, identicalPrivateBlock_through i z hi b, rfl⟩
  have hne : (identicalPrivateBlock i false).map e ≠
      (identicalPrivateBlock i true).map e := by
    intro he
    exact identicalPrivateBlock_ne i ((Finset.map_injective e) he)
  have hh := minimum_global_block_inter_le_five hn hC hz
    (hrows i false) (hrows i true) (hmem false) (hmem true) hne
  rw [← map_inter, card_map, identicalPrivateBlock_inter] at hh
  omega

/-- The identical-core gluing is impossible with at most twenty-nine blocks. -/
theorem identical_private_cores_impossible {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) (hb : C.card ≤ 29)
    (e : SwapPoint ≃ α)
    (hrows : ∀ i b, (identicalPrivateBlock i b).map e.toEmbedding ∈ C) : False := by
  have hsub : minimumPoints C 15 ⊆ ({swapRoot false, swapRoot true} : Finset SwapPoint).map
      e.toEmbedding := by
    intro x hx
    have hd := (mem_filter.mp hx).2
    obtain ⟨z, rfl⟩ := e.surjective x
    apply mem_map.mpr
    refine ⟨z, ?_, rfl⟩
    rcases z with b | z
    · cases b <;> simp [swapRoot]
    · exact False.elim (identical_private_point_not_minimum hn hC e.toEmbedding hrows z hd)
  have hh := card_le_card hsub
  have hl := five_minimum_points hn hC hb
  simp [swapRoot] at hh
  omega

#guard_standard_axioms FiveIntersectionMatching.not_minimum_four
  FiveIntersectionMatching.not_minimum_three minimum_global_block_inter_le_five
  swapped_companion_not_minimum swapped_degree_seven_spouse_not_minimum
  swapped_addition_not_minimum swapped_foreign_spouse_not_minimum
  swapped_minimum_card_le_four spouse_swap_impossible
  identical_private_point_not_minimum identical_private_cores_impossible

end CoveringDesigns.C13Structural
