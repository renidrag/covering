import CoveringDesigns.C12_6_3.Structural.Frames
import CoveringDesigns.C12_6_3.Structural.Templates
import CoveringDesigns.C12_6_3.Structural.ShortSymmetry
import Mathlib.Logic.Equiv.Fin.Basic
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Structural counting for GPPT Lemma 5.8.  These lemmas concern the three
short traces after a triplicate triple of degree-seven roots is separated.
They do not assert that an arbitrary covering has already been normalized.
The normalization and the application to all coverings are separate steps.
-/

namespace CoveringDesigns.GPPTStructural

open Finset

variable {α : Type*} [DecidableEq α]

/-- A five-point short trace containing `x` covers at most four pairs between
two disjoint sets of sizes two and six.  Missing a point of the two-set lowers
the capacity to three. -/
theorem short_cross_capacity (x : α) (Y Z W : Finset α)
    (hY : Y.card = 2) (hdis : Disjoint Y Z) (hxY : x ∉ Y) (hxZ : x ∉ Z)
    (hW : W.card = 5) (hxW : x ∈ W) :
    (W ∩ Y).card * (W ∩ Z).card ≤ 4 ∧
      ((W ∩ Y).card ≤ 1 → (W ∩ Y).card * (W ∩ Z).card ≤ 3) := by
  have hf : (W ∩ Y).card ≤ 2 := (card_le_card inter_subset_right).trans_eq hY
  have hd : Disjoint (W ∩ Y) (W ∩ Z) := by
    apply disjoint_left.mpr
    intro y hy hz
    exact disjoint_left.mp hdis (mem_inter.mp hy).2 (mem_inter.mp hz).2
  have hsub : (W ∩ Y) ∪ (W ∩ Z) ⊆ W.erase x := by
    intro y hy
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨hyW, hyY⟩ := mem_inter.mp hy
      exact mem_erase.mpr ⟨fun he => hxY (he ▸ hyY), hyW⟩
    · obtain ⟨hyW, hyZ⟩ := mem_inter.mp hy
      exact mem_erase.mpr ⟨fun he => hxZ (he ▸ hyZ), hyW⟩
  have hs : (W ∩ Y).card + (W ∩ Z).card ≤ 4 := by
    have hh := card_le_card hsub
    rw [card_union_of_disjoint hd, card_erase_of_mem hxW, hW] at hh
    exact hh
  have hcases : (W ∩ Y).card = 0 ∨ (W ∩ Y).card = 1 ∨ (W ∩ Y).card = 2 := by omega
  rcases hcases with he | he | he
  · simp [he]
  · rw [he] at hs ⊢
    omega
  · rw [he] at hs ⊢
    omega

/-- If twelve cross pairs are covered by three short traces, all three
four-pair capacity bounds are attained. -/
theorem common_short_saturation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : α) (Y Z : Finset α) (W : ι → Finset α)
    (hi : Fintype.card ι = 3) (hY : Y.card = 2) (hZ : Z.card = 6)
    (hdis : Disjoint Y Z) (hxY : x ∉ Y) (hxZ : x ∉ Z)
    (hW : ∀ i, (W i).card = 5) (hxW : ∀ i, x ∈ W i)
    (hcover : ∀ y ∈ Y, ∀ z ∈ Z, ∃ i, y ∈ W i ∧ z ∈ W i) :
    ∀ i, (W i ∩ Y).card * (W i ∩ Z).card = 4 := by
  have hsub : Y ×ˢ Z ⊆ univ.biUnion (fun i : ι => (W i ∩ Y) ×ˢ (W i ∩ Z)) := by
    intro yz hyz
    obtain ⟨hy, hz⟩ := mem_product.mp hyz
    obtain ⟨i, hiy, hiz⟩ := hcover yz.1 hy yz.2 hz
    apply mem_biUnion.mpr
    exact ⟨i, mem_univ i, mem_product.mpr ⟨mem_inter.mpr ⟨hiy, hy⟩,
      mem_inter.mpr ⟨hiz, hz⟩⟩⟩
  have htotal := (card_le_card hsub).trans card_biUnion_le
  simp only [card_product, hY, hZ] at htotal
  have hcap (i : ι) := (short_cross_capacity x Y Z (W i) hY hdis hxY hxZ
    (hW i) (hxW i)).1
  have hsum : (∑ _i : ι, (4 : ℕ)) = 12 := by simp [hi]
  intro i
  by_contra he
  have hlt : (W i ∩ Y).card * (W i ∩ Z).card < 4 := by
    have hh := hcap i
    omega
  have hs := sum_lt_sum (s := (univ : Finset ι)) (fun j _ => hcap j)
    ⟨i, mem_univ i, hlt⟩
  rw [hsum] at hs
  omega

/-- GPPT's Case 2 forcing step: if a point is short for all three roots,
its two triad-mates occur in every short trace. -/
theorem common_short_mates_forced {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : α) (Y Z : Finset α) (W : ι → Finset α)
    (hi : Fintype.card ι = 3) (hY : Y.card = 2) (hZ : Z.card = 6)
    (hdis : Disjoint Y Z) (hxY : x ∉ Y) (hxZ : x ∉ Z)
    (hW : ∀ i, (W i).card = 5) (hxW : ∀ i, x ∈ W i)
    (hcover : ∀ y ∈ Y, ∀ z ∈ Z, ∃ i, y ∈ W i ∧ z ∈ W i) :
    ∀ i, Y ⊆ W i := by
  have hsat := common_short_saturation x Y Z W hi hY hZ hdis hxY hxZ hW hxW hcover
  intro i
  have hc := short_cross_capacity x Y Z (W i) hY hdis hxY hxZ (hW i) (hxW i)
  have hle : (W i ∩ Y).card ≤ 2 := (card_le_card inter_subset_right).trans_eq hY
  have hge : 2 ≤ (W i ∩ Y).card := by
    by_contra hn
    have hh := hc.2 (by omega)
    rw [hsat i] at hh
    omega
  have he : W i ∩ Y = Y := eq_of_subset_of_card_le inter_subset_right (by omega)
  intro y hy
  have hm : y ∈ W i ∩ Y := by rwa [he]
  exact (mem_inter.mp hm).1

/-- Two five-point traces containing a fixed pair can cover six other points
only by partitioning those six points into two triples. -/
theorem two_short_traces_partition (P Z U V : Finset α)
    (hP : P.card = 2) (hZ : Z.card = 6) (hdis : Disjoint P Z)
    (hU : U.card = 5) (hV : V.card = 5) (hPU : P ⊆ U) (hPV : P ⊆ V)
    (hcover : Z ⊆ U ∪ V) :
    (U ∩ Z).card = 3 ∧ (V ∩ Z).card = 3 ∧
      Disjoint (U ∩ Z) (V ∩ Z) ∧ (U ∩ Z) ∪ (V ∩ Z) = Z := by
  have hcap (W : Finset α) (hW : W.card = 5) (hPW : P ⊆ W) :
      (W ∩ Z).card ≤ 3 := by
    have hd : Disjoint P (W ∩ Z) := hdis.mono_right inter_subset_right
    have hs : P ∪ (W ∩ Z) ⊆ W := union_subset hPW inter_subset_left
    have hh := card_le_card hs
    rw [card_union_of_disjoint hd, hP, hW] at hh
    omega
  have he : (U ∩ Z) ∪ (V ∩ Z) = Z := by
    apply Subset.antisymm
    · exact union_subset inter_subset_right inter_subset_right
    · intro z hz
      rcases mem_union.mp (hcover hz) with hu | hv
      · exact mem_union_left _ (mem_inter.mpr ⟨hu, hz⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨hv, hz⟩)
  have huc := hcap U hU hPU
  have hvc := hcap V hV hPV
  have hc := card_union_add_card_inter (U ∩ Z) (V ∩ Z)
  rw [he, hZ] at hc
  have hzero : ((U ∩ Z) ∩ (V ∩ Z)).card = 0 := by omega
  exact ⟨by omega, by omega, disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hzero), he⟩

/-- In a triad partitioned between two short traces, after their selected
points are removed exactly one nonselected addition remains. -/
theorem partitioned_triad_one_addition (T Z U V : Finset α) (u v : α)
    (hT : T.card = 3) (hTZ : T ⊆ Z) (hcover : Z ⊆ U ∪ V)
    (hdis : Disjoint (U ∩ Z) (V ∩ Z))
    (huU : u ∈ U) (huT : u ∈ T) (hvV : v ∈ V) (hvT : v ∈ T) :
    ((U ∩ T).erase u).card + ((V ∩ T).erase v).card = 1 := by
  have hd : Disjoint (U ∩ T) (V ∩ T) := by
    apply hdis.mono
    · exact inter_subset_inter_left hTZ
    · exact inter_subset_inter_left hTZ
  have he : (U ∩ T) ∪ (V ∩ T) = T := by
    apply Subset.antisymm
    · exact union_subset inter_subset_right inter_subset_right
    · intro t ht
      rcases mem_union.mp (hcover (hTZ ht)) with hu | hv
      · exact mem_union_left _ (mem_inter.mpr ⟨hu, ht⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨hv, ht⟩)
  have hsum : (U ∩ T).card + (V ∩ T).card = 3 := by
    rw [← card_union_of_disjoint hd, he, hT]
  have hum : u ∈ U ∩ T := mem_inter.mpr ⟨huU, huT⟩
  have hvm : v ∈ V ∩ T := mem_inter.mpr ⟨hvV, hvT⟩
  have hupos : 0 < (U ∩ T).card := card_pos.mpr ⟨u, hum⟩
  have hvpos : 0 < (V ∩ T).card := card_pos.mpr ⟨v, hvm⟩
  rw [card_erase_of_mem hum, card_erase_of_mem hvm]
  omega

namespace TriplicateFrame

variable [Fintype α] {C : Family α} (F : TriplicateFrame C)

theorem triad_eq_of_mem {i j : Fin 3} {x : α}
    (hi : x ∈ F.common.triad i) (hj : x ∈ F.common.triad j) : i = j := by
  by_contra hn
  exact disjoint_left.mp (F.common.pairwise_disjoint hn) hi hj

theorem selected_injective (r : Fin 3) : Function.Injective (F.row r).selected := by
  intro i j he
  exact F.triad_eq_of_mem (F.row r |>.selected_mem i) (he ▸ (F.row r).selected_mem j)

/-- The two additions to a short trace, beyond its three selected points. -/
def additions (r : Fin 3) : Finset α :=
  (F.row r).shortTrace \ univ.image (F.row r).selected

theorem additions_card (r : Fin 3) : (F.additions r).card = 2 := by
  rw [additions, card_sdiff_of_subset (F.row r).selected_subset,
    (F.row r).shortTrace_card, card_image_of_injective _ (F.selected_injective r)]
  rfl

theorem mem_selected_iff {x : α} {j : Fin 3} (hx : x ∈ F.common.triad j)
    (r : Fin 3) : x ∈ univ.image (F.row r).selected ↔ x = (F.row r).selected j := by
  constructor
  · intro hm
    obtain ⟨i, _, he⟩ := mem_image.mp hm
    have hij := F.triad_eq_of_mem ((he ▸ (F.row r).selected_mem i)) hx
    simpa [hij] using he.symm
  · intro he
    exact mem_image.mpr ⟨j, mem_univ _, he.symm⟩

theorem mem_markedRow_iff {x : α} {j : Fin 3} (hx : x ∈ F.common.triad j)
    (r i : Fin 3) :
    x ∈ StantonGeometry.markedRow F.common.triad (F.row r).selected i ↔
      (i = j ∧ x = (F.row r).selected j) ∨
        (i ≠ j ∧ x ≠ (F.row r).selected j) := by
  simp only [StantonGeometry.markedRow, mem_union, mem_singleton, mem_biUnion,
    mem_erase, mem_univ, and_true, mem_sdiff]
  constructor
  · rintro (he | ⟨k, hki, hxT, hxs⟩)
    · have hij := F.triad_eq_of_mem (he ▸ (F.row r).selected_mem i) hx
      exact Or.inl ⟨hij, by simpa [hij] using he⟩
    · have hkj := F.triad_eq_of_mem hxT hx
      subst k
      exact Or.inr ⟨Ne.symm hki, by simpa using hxs⟩
  · rintro (⟨rfl, he⟩ | ⟨hij, hxs⟩)
    · exact Or.inl he
    · exact Or.inr ⟨j, Ne.symm hij, hx, hxs⟩

/-- Fifteen formal block positions: three common blocks, then three full
and one short block at each root. -/
def blockAt : Fin 3 ⊕ (Fin 3 × Option (Fin 3)) → Finset α
  | .inl j => univ.image F.roots ∪ F.common.triad j
  | .inr (r, none) => insert (F.roots r) (F.row r).shortTrace
  | .inr (r, some j) => insert (F.roots r)
      (StantonGeometry.markedRow F.common.triad (F.row r).selected j)

theorem blockAt_image : univ.image F.blockAt = C := by
  conv_rhs => rw [F.blocks_eq]
  ext B
  simp only [mem_image, mem_union, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with j | ⟨r, _ | j⟩
    · exact Or.inl (Or.inl ⟨j, rfl⟩)
    · exact Or.inr ⟨r, rfl⟩
    · exact Or.inl (Or.inr ⟨r, j, rfl⟩)
  · rintro ((⟨j, rfl⟩ | ⟨r, j, rfl⟩) | ⟨r, rfl⟩)
    · exact ⟨.inl j, rfl⟩
    · exact ⟨.inr (r, some j), rfl⟩
    · exact ⟨.inr (r, none), rfl⟩

/-- The hypothesis of fifteen distinct blocks certifies that the fifteen
structural positions name different blocks. -/
theorem blockAt_injective (hC : C.card = 15) : Function.Injective F.blockAt := by
  have hh : (univ.image F.blockAt).card = (univ : Finset (Fin 3 ⊕ (Fin 3 × Option (Fin 3)))).card := by
    rw [F.blockAt_image, hC]
    decide +kernel
  have hi := card_image_iff.mp hh
  exact fun i j he => hi (mem_univ i) (mem_univ j) he

theorem degree_eq_index_sum (hC : C.card = 15) (x : α) :
    degree C x = ∑ i, if x ∈ F.blockAt i then 1 else 0 := by
  conv_lhs => rw [← F.blockAt_image]
  unfold degree star
  rw [filter_image, card_image_of_injective _ (F.blockAt_injective hC)]
  simp only [card_eq_sum_ones, sum_filter]

theorem not_mem_roots_of_mem_triad {x : α} {j : Fin 3}
    (hx : x ∈ F.common.triad j) : x ∉ univ.image F.roots := by
  exact fun hr => disjoint_left.mp (F.common.disjoint_root j) hr hx

theorem mem_triad_iff {x : α} {j : Fin 3} (hx : x ∈ F.common.triad j)
    (i : Fin 3) : x ∈ F.common.triad i ↔ i = j := by
  exact ⟨fun hi => F.triad_eq_of_mem hi hx, fun he => he ▸ hx⟩

theorem row_incidence_count {x : α} {j : Fin 3} (hx : x ∈ F.common.triad j)
    (r : Fin 3) :
    (∑ i : Fin 3, if x ∈ StantonGeometry.markedRow
        F.common.triad (F.row r).selected i then 1 else 0) +
      (if x ∈ (F.row r).shortTrace then 1 else 0) =
        2 + (if x ∈ F.additions r then 1 else 0) := by
  have hs := F.mem_selected_iff hx r
  simp only [F.mem_markedRow_iff hx]
  by_cases he : x = (F.row r).selected j
  · have hxW := (F.row r).selected_subset (hs.mpr he)
    have hxW' : (F.row r).selected j ∈ (F.row r).shortTrace := he ▸ hxW
    simp [he, hxW', additions]
  · have hn : x ∉ univ.image (F.row r).selected := fun h => he (hs.mp h)
    have hf : (univ.filter fun i : Fin 3 => i ≠ j) = univ.erase j := by
      ext i
      simp
    have hc : (univ.filter fun i : Fin 3 => i ≠ j).card = 2 := by
      rw [hf, card_erase_of_mem (mem_univ j)]
      rfl
    have hsum : (∑ i : Fin 3, if i ≠ j then (1 : ℕ) else 0) = 2 := by
      simpa only [card_eq_sum_ones, sum_filter] using hc
    simp only [ne_eq, he, and_false, false_or, not_false_eq_true, and_true,
      additions, mem_sdiff, hn, hsum]

/-- Every outside point has baseline degree seven. Any additional incidence
is exactly a nonselected occurrence in one of the three short traces. -/
theorem degree_eq_seven_additions (hC : C.card = 15) {x : α} {j : Fin 3}
    (hx : x ∈ F.common.triad j) :
    degree C x = 7 + ∑ r : Fin 3, if x ∈ F.additions r then 1 else 0 := by
  have hn := F.not_mem_roots_of_mem_triad hx
  have hroot (r : Fin 3) : x ≠ F.roots r := by
    intro he
    exact hn (mem_image.mpr ⟨r, mem_univ _, he.symm⟩)
  rw [F.degree_eq_index_sum hC, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [blockAt, mem_union, hn, false_or, F.mem_triad_iff hx,
    Fintype.sum_option, mem_insert, hroot, false_or]
  rw [sum_ite_eq']
  simp only [mem_univ, ite_true]
  have hs := Finset.sum_congr (s₁ := univ) rfl (fun r _ => F.row_incidence_count hx r)
  simp only [sum_add_distrib] at hs
  have hr : (∑ r : Fin 3, (2 : ℕ)) = 6 := by decide +kernel
  rw [hr] at hs
  simp only [sum_add_distrib]
  omega

/-- When `x` is selected by all three rows, a triple consisting of `x`,
a triad-mate, and a point in another triad can occur only in a short block. -/
theorem common_short_cross_covered (hC : IsCover C 6 3) {x : α} {j : Fin 3}
    (hx : x ∈ F.common.triad j) (hsel : ∀ r, (F.row r).selected j = x)
    {y z : α} (hy : y ∈ F.common.triad j) (hyx : y ≠ x)
    (hzT : z ∉ F.common.triad j) (hzR : z ∉ univ.image F.roots) :
    ∃ r, y ∈ (F.row r).shortTrace ∧ z ∈ (F.row r).shortTrace := by
  have hxR := F.not_mem_roots_of_mem_triad hx
  have hyR := F.not_mem_roots_of_mem_triad hy
  have hxz : x ≠ z := fun he => hzT (he ▸ hx)
  have hyz : y ≠ z := fun he => hzT (he ▸ hy)
  have ht : ({x, y, z} : Finset α).card = 3 := by
    simp [Ne.symm hyx, hxz, hyz]
  obtain ⟨B, hB, hs⟩ := hC.2 {x, y, z} ht
  have hxB : x ∈ B := hs (by simp)
  have hyB : y ∈ B := hs (by simp)
  have hzB : z ∈ B := hs (by simp)
  rw [F.blocks_eq] at hB
  rcases mem_union.mp hB with hB | hB
  · rcases mem_union.mp hB with hB | hB
    · obtain ⟨k, _, rfl⟩ := mem_image.mp hB
      have hxk : x ∈ F.common.triad k := (mem_union.mp hxB).resolve_left hxR
      have hkj := F.triad_eq_of_mem hxk hx
      have hzk : z ∈ F.common.triad k := (mem_union.mp hzB).resolve_left hzR
      exact (hzT (hkj ▸ hzk)).elim
    · obtain ⟨r, _, hB⟩ := mem_biUnion.mp hB
      obtain ⟨k, _, rfl⟩ := mem_image.mp hB
      have hxr : x ≠ F.roots r := fun he => hxR (mem_image.mpr ⟨r, mem_univ _, he.symm⟩)
      have hyr : y ≠ F.roots r := fun he => hyR (mem_image.mpr ⟨r, mem_univ _, he.symm⟩)
      have hxm := (F.mem_markedRow_iff hx r k).mp ((mem_insert.mp hxB).resolve_left hxr)
      have hym := (F.mem_markedRow_iff hy r k).mp ((mem_insert.mp hyB).resolve_left hyr)
      rw [hsel r] at hxm hym
      rcases hxm with ⟨hkj, _⟩ | ⟨_, hxx⟩
      · rcases hym with ⟨_, hyx'⟩ | ⟨hnkj, _⟩
        · exact (hyx hyx').elim
        · exact (hnkj hkj).elim
      · exact (hxx rfl).elim
  · obtain ⟨r, _, rfl⟩ := mem_image.mp hB
    refine ⟨r, ?_, ?_⟩
    · exact (mem_insert.mp hyB).resolve_left
        (fun he => hyR (mem_image.mpr ⟨r, mem_univ _, he.symm⟩))
    · exact (mem_insert.mp hzB).resolve_left
        (fun he => hzR (mem_image.mpr ⟨r, mem_univ _, he.symm⟩))

/-- GPPT Case 2: the six available additions are exactly the two mates of the
common selected point, repeated once in each short trace. -/
theorem additions_eq_common_mates (hn : Fintype.card α = 12)
    (hC : IsCover C 6 3) {x : α} {j : Fin 3}
    (hx : x ∈ F.common.triad j) (hsel : ∀ r, (F.row r).selected j = x) :
    ∀ r, F.additions r = (F.common.triad j).erase x := by
  let Y := (F.common.triad j).erase x
  let Z := univ \ (univ.image F.roots ∪ F.common.triad j)
  have hY : Y.card = 2 := by
    rw [card_erase_of_mem hx, F.common.triad_card]
  have hR : (univ.image F.roots).card = 3 := by
    rw [card_image_of_injective _ F.roots_injective]
    rfl
  have hZ : Z.card = 6 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hn,
      card_union_of_disjoint (F.common.disjoint_root j), hR, F.common.triad_card]
  have hd : Disjoint Y Z := by
    apply disjoint_left.mpr
    intro y hy hz
    exact (mem_sdiff.mp hz).2 (mem_union_right _ (mem_of_mem_erase hy))
  have hxY : x ∉ Y := notMem_erase x _
  have hxZ : x ∉ Z := by
    intro hz
    exact (mem_sdiff.mp hz).2 (mem_union_right _ hx)
  have hxW (r : Fin 3) : x ∈ (F.row r).shortTrace := by
    apply (F.row r).selected_subset
    exact mem_image.mpr ⟨j, mem_univ _, hsel r⟩
  have hcov : ∀ y ∈ Y, ∀ z ∈ Z, ∃ r,
      y ∈ (F.row r).shortTrace ∧ z ∈ (F.row r).shortTrace := by
    intro y hy z hz
    have hznot := (mem_sdiff.mp hz).2
    exact F.common_short_cross_covered hC hx hsel (mem_of_mem_erase hy)
      (mem_erase.mp hy).1 (fun hzT => hznot (mem_union_right _ hzT))
      (fun hzR => hznot (mem_union_left _ hzR))
  have hforce := common_short_mates_forced x Y Z (fun r => (F.row r).shortTrace)
    (by rfl) hY hZ hd hxY hxZ (fun r => (F.row r).shortTrace_card) hxW hcov
  intro r
  symm
  apply eq_of_subset_of_card_le
  · intro y hy
    refine mem_sdiff.mpr ⟨hforce r hy, ?_⟩
    intro hym
    have he := (F.mem_selected_iff (mem_of_mem_erase hy) r).mp hym
    rw [hsel r] at he
    exact (mem_erase.mp hy).1 he
  · rw [F.additions_card, hY]

/-- All six points in the two other triads have minimum degree in Case 2. -/
theorem other_triad_degree_seven (hn : Fintype.card α = 12)
    (hC : IsCover C 6 3) (hc : C.card = 15) {x : α} {j k : Fin 3}
    (hx : x ∈ F.common.triad j) (hsel : ∀ r, (F.row r).selected j = x)
    (hkj : k ≠ j) {y : α} (hy : y ∈ F.common.triad k) : degree C y = 7 := by
  have he := F.additions_eq_common_mates hn hC hx hsel
  have hyn : y ∉ (F.common.triad j).erase x := by
    intro hm
    exact hkj (F.triad_eq_of_mem hy (mem_of_mem_erase hm))
  rw [F.degree_eq_seven_additions hc hy]
  simp only [he, hyn, ite_false, sum_const_zero, Nat.add_zero]

/-- There are six nonselected short-trace occurrences in the whole frame. -/
theorem additions_total : ∑ r : Fin 3, (F.additions r).card = 6 := by
  simp only [F.additions_card]
  decide +kernel

theorem pair_degree_eq_index_sum (hC : C.card = 15) (x y : α) :
    degree (star C x) y = ∑ i, if x ∈ F.blockAt i ∧ y ∈ F.blockAt i then 1 else 0 := by
  conv_lhs => rw [← F.blockAt_image]
  unfold degree star
  rw [filter_filter, filter_image, card_image_of_injective _ (F.blockAt_injective hC)]
  simp only [card_eq_sum_ones, sum_filter]

private theorem sum_other_indices (j : Fin 3) :
    (∑ i : Fin 3, if i ≠ j then (1 : ℕ) else 0) = 2 := by
  have hf : (univ.filter fun i : Fin 3 => i ≠ j) = univ.erase j := by
    ext i
    simp
  have hc : (univ.filter fun i : Fin 3 => i ≠ j).card = 2 := by
    rw [hf, card_erase_of_mem (mem_univ j)]
    rfl
  simpa only [card_eq_sum_ones, sum_filter] using hc

/-- A selected point repeated in two rows forces its two triad-mates to occur
together at least five times: once in the common block and twice in each row. -/
theorem repeated_selection_mates_pair_ge_five (hc : C.card = 15)
    {j r s : Fin 3} (hrs : r ≠ s) {x y z : α}
    (hy : y ∈ F.common.triad j) (hz : z ∈ F.common.triad j)
    (hyx : y ≠ x) (hzx : z ≠ x)
    (hr : (F.row r).selected j = x) (hs : (F.row s).selected j = x) :
    5 ≤ degree (star C y) z := by
  let g : Fin 3 → ℕ := fun a =>
    (if y ∈ (F.row a).shortTrace ∧ z ∈ (F.row a).shortTrace then 1 else 0) +
    ∑ i : Fin 3, if y ∈ StantonGeometry.markedRow F.common.triad (F.row a).selected i ∧
      z ∈ StantonGeometry.markedRow F.common.triad (F.row a).selected i then 1 else 0
  have hrow (a : Fin 3) (ha : (F.row a).selected j = x) : 2 ≤ g a := by
    have hsum : (∑ i : Fin 3,
        if y ∈ StantonGeometry.markedRow F.common.triad (F.row a).selected i ∧
          z ∈ StantonGeometry.markedRow F.common.triad (F.row a).selected i then 1 else 0) = 2 := by
      simp only [F.mem_markedRow_iff hy, F.mem_markedRow_iff hz, ha,
        ne_eq, hyx, hzx, not_false_eq_true, and_false, false_or, and_true, and_self]
      exact sum_other_indices j
    dsimp only [g]
    rw [hsum]
    omega
  have hsum : 4 ≤ ∑ a, g a := by
    have hh : ∑ a ∈ ({r, s} : Finset (Fin 3)), g a ≤ ∑ a, g a :=
      sum_le_sum_of_subset (subset_univ _)
    rw [sum_pair hrs] at hh
    have hgr := hrow r hr
    have hgs := hrow s hs
    omega
  have hyR := F.not_mem_roots_of_mem_triad hy
  have hzR := F.not_mem_roots_of_mem_triad hz
  have hyr (a : Fin 3) : y ≠ F.roots a := fun he =>
    hyR (mem_image.mpr ⟨a, mem_univ _, he.symm⟩)
  have hzr (a : Fin 3) : z ≠ F.roots a := fun he =>
    hzR (mem_image.mpr ⟨a, mem_univ _, he.symm⟩)
  have he : degree (star C y) z = 1 + ∑ a, g a := by
    rw [F.pair_degree_eq_index_sum hc, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [blockAt, mem_union, hyR, hzR, false_or, F.mem_triad_iff hy,
      F.mem_triad_iff hz, and_self, Fintype.sum_option, mem_insert, hyr, hzr, false_or]
    rw [sum_ite_eq']
    simp only [mem_univ, ite_true]
    rfl
  omega

/-- A triad whose points all have minimum degree has three distinct selected
points. A repetition would violate the degree bound in a minimum point's link. -/
theorem column_injective_of_minimum (hn : Fintype.card α = 12)
    (hC : IsCover C 6 3) (hc : C.card = 15) (j : Fin 3)
    (hd : ∀ y ∈ F.common.triad j, degree C y = 7) :
    Function.Injective fun r => (F.row r).selected j := by
  intro r s he
  by_contra hrs
  let x := (F.row r).selected j
  have hx : x ∈ F.common.triad j := (F.row r).selected_mem j
  have htwo : ((F.common.triad j).erase x).card = 2 := by
    rw [card_erase_of_mem hx, F.common.triad_card]
  obtain ⟨y, z, hyz, hm⟩ := card_eq_two.mp htwo
  have hym : y ∈ (F.common.triad j).erase x := by rw [hm]; simp
  have hzm : z ∈ (F.common.triad j).erase x := by rw [hm]; simp
  have hlo := F.repeated_selection_mates_pair_ge_five hc hrs
    (mem_of_mem_erase hym) (mem_of_mem_erase hzm) (mem_erase.mp hym).1
    (mem_erase.mp hzm).1 rfl he.symm
  have hhi := structural_degree_bound
    (by rw [complement_point_card, hn]) (link_isCover hC y)
    (by rw [link_card, hd y (mem_of_mem_erase hym)])
    (⟨z, Ne.symm hyz⟩ : {q : α // q ≠ y})
  rw [degree_link] at hhi
  change degree (star C y) z ≤ 4 at hhi
  omega

/-- The two nonconstant columns are injective in GPPT Case 2. -/
theorem other_column_injective (hn : Fintype.card α = 12)
    (hC : IsCover C 6 3) (hc : C.card = 15) {x : α} {j k : Fin 3}
    (hx : x ∈ F.common.triad j) (hsel : ∀ r, (F.row r).selected j = x)
    (hkj : k ≠ j) : Function.Injective fun r => (F.row r).selected k := by
  exact F.column_injective_of_minimum hn hC hc k
    (fun _ hy => F.other_triad_degree_seven hn hC hc hx hsel hkj hy)

/-- A minimum point selected by two rows must be selected by the third row
as well. The common block is short in its link, so short-point symmetry forces
all three roots to select it. -/
theorem minimum_selected_twice_all (hn : Fintype.card α = 12)
    (hC : IsCover C 6 3) (hc : C.card ≤ 15) {j r s : Fin 3} (hrs : r ≠ s)
    {x : α} (hx : x ∈ F.common.triad j) (hd : degree C x = 7)
    (hr : (F.row r).selected j = x) (hs : (F.row s).selected j = x) :
    ∀ t, (F.row t).selected j = x := by
  have hxR := F.not_mem_roots_of_mem_triad hx
  have hroot (a : Fin 3) : F.roots a ≠ x := fun he =>
    hxR (mem_image.mpr ⟨a, mem_univ _, he⟩)
  have hshort (a : Fin 3) (ha : (F.row a).selected j = x) :
      StantonGeometry.IsShortPoint (link C x) ⟨F.roots a, hroot a⟩ := by
    have hh := ((F.row a).selected_iff ⟨x, (hroot a).symm⟩).mp
      (mem_image.mpr ⟨j, mem_univ _, ha⟩)
    exact minimum_short_symmetry hn hC (F.root_degree a) hd (hroot a) hh
  let B := univ.image F.roots ∪ F.common.triad j
  let S := B.subtype (· ≠ x)
  have hB : B ∈ C := by
    rw [← F.blockAt_image]
    exact mem_image.mpr ⟨.inl j, mem_univ _, rfl⟩
  have hS : S ∈ link C x :=
    mem_image.mpr ⟨B, mem_filter.mpr ⟨hB, mem_union_right _ hx⟩, rfl⟩
  have hmem (a : Fin 3) : (⟨F.roots a, hroot a⟩ : {q : α // q ≠ x}) ∈ S :=
    mem_subtype.mpr (mem_union_left _ (mem_image.mpr ⟨a, mem_univ _, rfl⟩))
  have hfacts := StantonGeometry.geometry_facts
    (by rw [complement_point_card, hn]) (link_isCover hC x) (by rw [link_card, hd])
  have hsr : StantonGeometry.IsShortBlock (link C x) S :=
    hfacts.two_short_points S hS _ (hmem r) _ (hmem s)
      (fun he => hrs (F.roots_injective (congrArg Subtype.val he))) (hshort r hr) (hshort s hs)
  intro t
  have ht := minimum_in_short_block_is_short hn hC hc hd (F.root_degree t)
    (hroot t).symm hsr (hmem t)
  have hsx := minimum_short_symmetry hn hC hd (F.root_degree t) (hroot t).symm ht
  exact ((F.mem_selected_iff hx t).mp
    (((F.row t).selected_iff ⟨x, (hroot t).symm⟩).mpr hsx)).symm

/-- In a nonconstant repeated column, all three points have degree above seven
(GPPT Case 3). For the repeated selected point this uses short-point symmetry;
for its mates it uses the five-fold pair obstruction. -/
theorem repeated_column_no_minimum (hn : Fintype.card α = 12)
    (hC : IsCover C 6 3) (hc : C.card = 15) (j : Fin 3)
    (hrepeat : ¬ Function.Injective fun r => (F.row r).selected j)
    (hnonconstant : ¬ ∃ x, ∀ r, (F.row r).selected j = x) :
    ∀ y ∈ F.common.triad j, degree C y ≠ 7 := by
  classical
  obtain ⟨r, s, he, hrs⟩ : ∃ r s, (F.row r).selected j = (F.row s).selected j ∧ r ≠ s := by
    by_contra! h
    exact hrepeat h
  let x := (F.row r).selected j
  have hx : x ∈ F.common.triad j := (F.row r).selected_mem j
  intro y hy hdy
  by_cases hyx : y = x
  · subst y
    exact hnonconstant ⟨x, F.minimum_selected_twice_all hn hC (by omega) hrs hx hdy rfl he.symm⟩
  · have hym : y ∈ (F.common.triad j).erase x := mem_erase.mpr ⟨hyx, hy⟩
    have hcard : (((F.common.triad j).erase x).erase y).card = 1 := by
      rw [card_erase_of_mem hym, card_erase_of_mem hx, F.common.triad_card]
    obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (((F.common.triad j).erase x).erase y).card by omega)
    have hzy : z ≠ y := (mem_erase.mp hz).1
    have hz' := mem_of_mem_erase hz
    have hlo := F.repeated_selection_mates_pair_ge_five hc hrs hy
      (mem_of_mem_erase hz') hyx (mem_erase.mp hz').1 rfl he.symm
    have hhi := minimum_pair_degree_le_four hn hC hdy hzy
    omega

/-- Count the nonselected occurrences of a point in the three short traces. -/
def extraCount (x : α) : ℕ := ∑ r : Fin 3, if x ∈ F.additions r then 1 else 0

/-- The excess incidences assigned to one triad. -/
def triadExcess (j : Fin 3) : ℕ := ∑ r : Fin 3, (F.additions r ∩ F.common.triad j).card

theorem triadExcess_eq_sum (j : Fin 3) :
    F.triadExcess j = ∑ x ∈ F.common.triad j, F.extraCount x := by
  have hc (r : Fin 3) : (F.additions r ∩ F.common.triad j).card =
      ∑ x ∈ F.common.triad j, if x ∈ F.additions r then 1 else 0 := by
    rw [← sum_filter, filter_mem_eq_inter, inter_comm]
    simp only [sum_const, Nat.nsmul_eq_mul, Nat.mul_one]
  simp only [triadExcess, hc, extraCount]
  exact sum_comm

theorem triadExcess_total : ∑ j : Fin 3, F.triadExcess j = 6 := by
  have hr (r : Fin 3) : ∑ j : Fin 3, (F.additions r ∩ F.common.triad j).card = 2 := by
    have hd : (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
        (fun j => F.additions r ∩ F.common.triad j) := by
      intro i _ j _ hij
      exact (F.common.pairwise_disjoint hij).mono inter_subset_right inter_subset_right
    have he : univ.biUnion (fun j => F.additions r ∩ F.common.triad j) = F.additions r := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨j, _, hj⟩ := mem_biUnion.mp hx
        exact (mem_inter.mp hj).1
      · intro x hx
        have hxW := (mem_sdiff.mp hx).1
        have hxR : x ∉ univ.image F.roots := fun hm =>
          disjoint_left.mp (F.short_disjoint_roots r) hm hxW
        have hspan : x ∈ univ.image F.roots ∪ univ.biUnion F.common.triad := by
          rw [F.common.spans]
          exact mem_univ _
        obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp ((mem_union.mp hspan).resolve_left hxR)
        exact mem_biUnion.mpr ⟨j, hj, mem_inter.mpr ⟨hx, hxj⟩⟩
    rw [← card_biUnion hd, he, F.additions_card]
  simp only [triadExcess]
  rw [sum_comm]
  simp only [hr]
  decide +kernel

theorem extraCount_pos_of_nonminimum (hc : C.card = 15) {x : α} {j : Fin 3}
    (hx : x ∈ F.common.triad j) (hd : degree C x ≠ 7) : 1 ≤ F.extraCount x := by
  have he := F.degree_eq_seven_additions hc hx
  change degree C x = 7 + F.extraCount x at he
  omega

theorem triadExcess_ge_three_of_no_minimum (hc : C.card = 15) (j : Fin 3)
    (hd : ∀ x ∈ F.common.triad j, degree C x ≠ 7) : 3 ≤ F.triadExcess j := by
  rw [F.triadExcess_eq_sum]
  have hh := sum_le_sum (s := F.common.triad j) (fun x hx =>
    F.extraCount_pos_of_nonminimum hc hx (hd x hx))
  simpa only [sum_const, Nat.nsmul_eq_mul, F.common.triad_card, Nat.mul_one] using hh

theorem repeated_column_excess_ge_three (hn : Fintype.card α = 12)
    (hC : IsCover C 6 3) (hc : C.card = 15) (j : Fin 3)
    (hrepeat : ¬ Function.Injective fun r => (F.row r).selected j)
    (hnonconstant : ¬ ∃ x, ∀ r, (F.row r).selected j = x) : 3 ≤ F.triadExcess j :=
  F.triadExcess_ge_three_of_no_minimum hc j
    (F.repeated_column_no_minimum hn hC hc j hrepeat hnonconstant)

/-- A degree-seven outside point appears in a short trace precisely when that
row selects it. -/
theorem minimum_mem_shortTrace_iff (hc : C.card = 15) {x : α} {j : Fin 3}
    (hx : x ∈ F.common.triad j) (hd : degree C x = 7) (r : Fin 3) :
    x ∈ (F.row r).shortTrace ↔ x = (F.row r).selected j := by
  constructor
  · intro hxW
    by_contra he
    have hxA : x ∈ F.additions r := mem_sdiff.mpr
      ⟨hxW, fun hm => he ((F.mem_selected_iff hx r).mp hm)⟩
    have hle : (if x ∈ F.additions r then 1 else 0) ≤ F.extraCount x := by
      exact single_le_sum (f := fun a => if x ∈ F.additions a then 1 else 0)
        (fun _ _ => Nat.zero_le _) (mem_univ r)
    have hdeg := F.degree_eq_seven_additions hc hx
    change degree C x = 7 + F.extraCount x at hdeg
    rw [if_pos hxA] at hle
    omega
  · intro he
    exact (F.row r).selected_subset ((F.mem_selected_iff hx r).mpr he)

/-- If a column uses only two selected values, a triple containing both and
a point outside that triad must occur in a short block. -/
theorem two_selected_cross_covered (hC : IsCover C 6 3) {x y : α} {j : Fin 3}
    (hx : x ∈ F.common.triad j) (hy : y ∈ F.common.triad j) (hxy : x ≠ y)
    (hsel : ∀ r, (F.row r).selected j = x ∨ (F.row r).selected j = y)
    {z : α} (hzT : z ∉ F.common.triad j) (hzR : z ∉ univ.image F.roots) :
    ∃ r, x ∈ (F.row r).shortTrace ∧ y ∈ (F.row r).shortTrace ∧
      z ∈ (F.row r).shortTrace := by
  have hxR := F.not_mem_roots_of_mem_triad hx
  have hyR := F.not_mem_roots_of_mem_triad hy
  have hxz : x ≠ z := fun he => hzT (he ▸ hx)
  have hyz : y ≠ z := fun he => hzT (he ▸ hy)
  obtain ⟨B, hB, hs⟩ := hC.2 {x, y, z} (by simp [hxy, hxz, hyz])
  have hxB : x ∈ B := hs (by simp)
  have hyB : y ∈ B := hs (by simp)
  have hzB : z ∈ B := hs (by simp)
  rw [F.blocks_eq] at hB
  rcases mem_union.mp hB with hB | hB
  · rcases mem_union.mp hB with hB | hB
    · obtain ⟨k, _, rfl⟩ := mem_image.mp hB
      have hxk := (mem_union.mp hxB).resolve_left hxR
      have hzk := (mem_union.mp hzB).resolve_left hzR
      exact (hzT (F.triad_eq_of_mem hxk hx ▸ hzk)).elim
    · obtain ⟨r, _, hB⟩ := mem_biUnion.mp hB
      obtain ⟨k, _, rfl⟩ := mem_image.mp hB
      have hxr : x ≠ F.roots r := fun he => hxR (mem_image.mpr ⟨r, mem_univ _, he.symm⟩)
      have hyr : y ≠ F.roots r := fun he => hyR (mem_image.mpr ⟨r, mem_univ _, he.symm⟩)
      have hxm := (F.mem_markedRow_iff hx r k).mp ((mem_insert.mp hxB).resolve_left hxr)
      have hym := (F.mem_markedRow_iff hy r k).mp ((mem_insert.mp hyB).resolve_left hyr)
      rcases hsel r with he | he
      · rw [he] at hxm hym
        rcases hxm with ⟨hk, _⟩ | ⟨_, hn⟩
        · rcases hym with ⟨_, hyx⟩ | ⟨hn, _⟩
          · exact (hxy hyx.symm).elim
          · exact (hn hk).elim
        · exact (hn rfl).elim
      · rw [he] at hxm hym
        rcases hym with ⟨hk, _⟩ | ⟨_, hn⟩
        · rcases hxm with ⟨_, hxy'⟩ | ⟨hn, _⟩
          · exact (hxy hxy').elim
          · exact (hn hk).elim
        · exact (hn rfl).elim
  · obtain ⟨r, _, rfl⟩ := mem_image.mp hB
    refine ⟨r, ?_, ?_, ?_⟩
    · exact (mem_insert.mp hxB).resolve_left
        (fun he => hxR (mem_image.mpr ⟨r, mem_univ _, he.symm⟩))
    · exact (mem_insert.mp hyB).resolve_left
        (fun he => hyR (mem_image.mpr ⟨r, mem_univ _, he.symm⟩))
    · exact (mem_insert.mp hzB).resolve_left
        (fun he => hzR (mem_image.mpr ⟨r, mem_univ _, he.symm⟩))

theorem extraCount_le_triadExcess {x : α} {j : Fin 3}
    (hx : x ∈ F.common.triad j) : F.extraCount x ≤ F.triadExcess j := by
  rw [F.triadExcess_eq_sum]
  exact single_le_sum (fun _ _ => Nat.zero_le _) hx

theorem minimum_of_triadExcess_zero (hc : C.card = 15) {j : Fin 3}
    (hj : F.triadExcess j = 0) {x : α} (hx : x ∈ F.common.triad j) :
    degree C x = 7 := by
  have he := F.degree_eq_seven_additions hc hx
  have hh := F.extraCount_le_triadExcess hx
  change degree C x = 7 + F.extraCount x at he
  omega

theorem triadExcess_ge_four (hc : C.card = 15) {j : Fin 3}
    (hd : ∀ x ∈ F.common.triad j, degree C x ≠ 7)
    {x : α} (hx : x ∈ F.common.triad j) (hex : 2 ≤ F.extraCount x) :
    4 ≤ F.triadExcess j := by
  have hsum := sum_le_sum (s := (F.common.triad j).erase x)
    (fun y hy => F.extraCount_pos_of_nonminimum hc (mem_of_mem_erase hy)
      (hd y (mem_of_mem_erase hy)))
  simp only [sum_const, Nat.nsmul_eq_mul, Nat.mul_one,
    card_erase_of_mem hx, F.common.triad_card] at hsum
  have he := sum_erase_add (F.common.triad j) F.extraCount hx
  rw [← F.triadExcess_eq_sum] at he
  omega

/-- A repeated nonconstant column requires four extra incidences if another
column has no extras: its three selected minimum points force the repeated
column's two selected values into every short trace. -/
theorem repeated_column_excess_ge_four_of_zero (hn : Fintype.card α = 12)
    (hC : IsCover C 6 3) (hc : C.card = 15) {j k : Fin 3} (hjk : j ≠ k)
    (hrepeat : ¬ Function.Injective fun r => (F.row r).selected j)
    (hnonconstant : ¬ ∃ x, ∀ r, (F.row r).selected j = x)
    (hk : F.triadExcess k = 0) : 4 ≤ F.triadExcess j := by
  obtain ⟨r, s, he, hrs⟩ : ∃ r s, (F.row r).selected j = (F.row s).selected j ∧ r ≠ s := by
    by_contra! h
    exact hrepeat h
  let x := (F.row r).selected j
  obtain ⟨t, ht⟩ : ∃ t, (F.row t).selected j ≠ x := by
    by_contra! hall
    exact hnonconstant ⟨x, hall⟩
  let y := (F.row t).selected j
  have hrt : r ≠ t := fun h => ht (h ▸ rfl)
  have hst : s ≠ t := fun h => ht (h ▸ he.symm)
  have hcases (a : Fin 3) : a = r ∨ a = s ∨ a = t := by omega
  have hx : x ∈ F.common.triad j := (F.row r).selected_mem j
  have hy : y ∈ F.common.triad j := (F.row t).selected_mem j
  have hxy : x ≠ y := Ne.symm ht
  have hsel (a : Fin 3) : (F.row a).selected j = x ∨ (F.row a).selected j = y := by
    rcases hcases a with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl he.symm
    · exact Or.inr rfl
  have hmin (z : α) (hz : z ∈ F.common.triad k) : degree C z = 7 :=
    F.minimum_of_triadExcess_zero hc hk hz
  have hi := F.column_injective_of_minimum hn hC hc k hmin
  have hforce (a : Fin 3) : y ∈ (F.row a).shortTrace := by
    let z := (F.row a).selected k
    have hz : z ∈ F.common.triad k := (F.row a).selected_mem k
    obtain ⟨b, _, hyb, hzb⟩ := F.two_selected_cross_covered hC hx hy hxy hsel
      (fun hzj => hjk (F.triad_eq_of_mem hzj hz)) (F.not_mem_roots_of_mem_triad hz)
    have hab := hi ((F.minimum_mem_shortTrace_iff hc hz (hmin z hz) b).mp hzb)
    exact hab ▸ hyb
  have hyr : y ∈ F.additions r := mem_sdiff.mpr ⟨hforce r, fun hm =>
    ht ((F.mem_selected_iff hy r).mp hm)⟩
  have hys : y ∈ F.additions s := mem_sdiff.mpr ⟨hforce s, fun hm =>
    ht (((F.mem_selected_iff hy s).mp hm).trans he.symm)⟩
  have htwo : 2 ≤ F.extraCount y := by
    have hh := sum_le_sum_of_subset (f := fun a => if y ∈ F.additions a then (1 : ℕ) else 0)
      (show ({r, s} : Finset (Fin 3)) ⊆ univ from subset_univ _)
    rw [sum_pair hrs, if_pos hyr, if_pos hys] at hh
    exact hh
  exact F.triadExcess_ge_four hc (F.repeated_column_no_minimum hn hC hc j hrepeat hnonconstant)
    hy htwo

/-- In GPPT Case 3 there can be only one repeated column. -/
theorem other_columns_injective_of_repeated (hn : Fintype.card α = 12)
    (hC : IsCover C 6 3) (hc : C.card = 15)
    (hnonconstant : ∀ j, ¬ ∃ x, ∀ r, (F.row r).selected j = x)
    {j : Fin 3} (hrepeat : ¬ Function.Injective fun r => (F.row r).selected j) :
    ∀ k, k ≠ j → Function.Injective fun r => (F.row r).selected k := by
  intro k hkj
  by_contra hk
  have hthird : ∀ a b : Fin 3, a ≠ b → ∃ c, c ≠ a ∧ c ≠ b := by decide +kernel
  obtain ⟨l, hlj, hlk⟩ := hthird j k hkj.symm
  have hall : (univ : Finset (Fin 3)) = {j, k, l} := by
    ext a
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    omega
  have htotal := F.triadExcess_total
  rw [hall, sum_insert (by simp [Ne.symm hkj, Ne.symm hlj]), sum_pair (Ne.symm hlk)] at htotal
  have hj3 := F.repeated_column_excess_ge_three hn hC hc j hrepeat (hnonconstant j)
  have hk3 := F.repeated_column_excess_ge_three hn hC hc k hk (hnonconstant k)
  have hl0 : F.triadExcess l = 0 := by omega
  have hj4 := F.repeated_column_excess_ge_four_of_zero hn hC hc (Ne.symm hlj)
    hrepeat (hnonconstant j) hl0
  omega

/-- Two distinct nonminimum points in a triad require two extra incidences. -/
theorem triadExcess_ge_two_of_pair (hc : C.card = 15) {j : Fin 3} {x y : α}
    (hx : x ∈ F.common.triad j) (hy : y ∈ F.common.triad j) (hxy : x ≠ y)
    (hdx : degree C x ≠ 7) (hdy : degree C y ≠ 7) : 2 ≤ F.triadExcess j := by
  have hs : ({x, y} : Finset α) ⊆ F.common.triad j := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hx, hy⟩
  have hh := sum_le_sum_of_subset (f := F.extraCount) hs
  rw [sum_pair hxy, ← F.triadExcess_eq_sum] at hh
  have h1 := F.extraCount_pos_of_nonminimum hc hx hdx
  have h2 := F.extraCount_pos_of_nonminimum hc hy hdy
  omega

/-- One of the two repeated rows selects a minimum point in another column.
Otherwise those four distinct selected points and the first triad would
require at least seven of the six available extra incidences. -/
theorem exists_minimum_selected_other_column (hn : Fintype.card α = 12)
    (hC : IsCover C 6 3) (hc : C.card = 15)
    (hnonconstant : ∀ j, ¬ ∃ x, ∀ r, (F.row r).selected j = x)
    {j r s : Fin 3} (hrs : r ≠ s)
    (he : (F.row r).selected j = (F.row s).selected j) :
    ∃ k, k ≠ j ∧ (degree C ((F.row r).selected k) = 7 ∨
      degree C ((F.row s).selected k) = 7) := by
  have hr : ¬ Function.Injective fun a => (F.row a).selected j := fun hi => hrs (hi he)
  have hi := F.other_columns_injective_of_repeated hn hC hc hnonconstant hr
  have hj3 := F.repeated_column_excess_ge_three hn hC hc j hr (hnonconstant j)
  by_contra! hnone
  have hlo (k : Fin 3) : 2 + (if k = j then 1 else 0) ≤ F.triadExcess k := by
    by_cases hkj : k = j
    · simpa [hkj] using hj3
    · have hnon := hnone k hkj
      have hh := F.triadExcess_ge_two_of_pair hc ((F.row r).selected_mem k)
        ((F.row s).selected_mem k) (fun h => hrs (hi k hkj h)) hnon.1 hnon.2
      simpa [hkj] using hh
  have hsum := sum_le_sum (s := univ) (fun k _ => hlo k)
  have heq : (∑ k : Fin 3, (2 + if k = j then 1 else 0 : ℕ)) = 7 := by
    simp [sum_add_distrib]
  rw [heq, F.triadExcess_total] at hsum
  omega

/-- The point positions in Figure 4: roots first, then each triad in root order. -/
private def pointCode : Fin 3 ⊕ (Fin 3 × Fin 3) ≃ Fin 12 :=
  (Equiv.sumCongr (Equiv.refl (Fin 3)) finProdFinEquiv).trans finSumFinEquiv

private def pointAt : Fin 3 ⊕ (Fin 3 × Fin 3) → α
  | .inl r => F.roots r
  | .inr (j, r) => (F.row r).selected j

private theorem pointAt_injective
    (hi : ∀ j, Function.Injective fun r => (F.row r).selected j) :
    Function.Injective F.pointAt := by
  intro a b he
  rcases a with r | ⟨j, r⟩ <;> rcases b with s | ⟨k, s⟩ <;> dsimp only [pointAt] at he
  · exact congrArg Sum.inl (F.roots_injective he)
  · have hs := (F.row s).selected_mem k
    have hr : F.roots r ∈ univ.image F.roots := mem_image.mpr ⟨r, mem_univ _, rfl⟩
    exact (disjoint_left.mp (F.common.disjoint_root k) hr (he ▸ hs)).elim
  · have hr := (F.row r).selected_mem j
    have hs : F.roots s ∈ univ.image F.roots := mem_image.mpr ⟨s, mem_univ _, rfl⟩
    exact (disjoint_left.mp (F.common.disjoint_root j) hs (he ▸ hr)).elim
  · have hjk := F.triad_eq_of_mem ((F.row r).selected_mem j) (he ▸ (F.row s).selected_mem k)
    subst k
    have hrs := hi j he
    subst s
    rfl

private theorem pointAt_bijective (hn : Fintype.card α = 12)
    (hi : ∀ j, Function.Injective fun r => (F.row r).selected j) :
    Function.Bijective F.pointAt := by
  have hf := F.pointAt_injective hi
  have hs : univ.image F.pointAt = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_image_of_injective _ hf]
    simp [hn]
  exact ⟨hf, fun x => by
    have hx : x ∈ univ.image F.pointAt := by rw [hs]; exact mem_univ _
    obtain ⟨i, _, hi⟩ := mem_image.mp hx
    exact ⟨i, hi⟩⟩

/-- In Case 1, the three selected points in each triad give canonical Figure 4
coordinates. This is only a relabelling, with no restriction on the covering. -/
noncomputable def injectiveCoordinates (hn : Fintype.card α = 12)
    (hi : ∀ j, Function.Injective fun r => (F.row r).selected j) : α ≃ Fin 12 :=
  (Equiv.ofBijective F.pointAt (F.pointAt_bijective hn hi)).symm.trans pointCode

private theorem injectiveCoordinates_pointAt (hn : Fintype.card α = 12)
    (hi : ∀ j, Function.Injective fun r => (F.row r).selected j)
    (a : Fin 3 ⊕ (Fin 3 × Fin 3)) :
    F.injectiveCoordinates hn hi (F.pointAt a) = pointCode a := by
  exact congrArg pointCode ((Equiv.ofBijective F.pointAt (F.pointAt_bijective hn hi)).symm_apply_apply a)

private def figure4Roots : Finset (Fin 12) :=
  univ.image fun r : Fin 3 => pointCode (.inl r)

private def figure4Triads (j : Fin 3) : Finset (Fin 12) :=
  univ.image fun r : Fin 3 => pointCode (.inr (j, r))

private theorem figure4_core_formula : figure4Core =
    (univ.image fun j => figure4Roots ∪ figure4Triads j) ∪
    (univ.biUnion fun r : Fin 3 => univ.image fun j =>
      insert (pointCode (.inl r))
        (StantonGeometry.markedRow figure4Triads
          (fun k => pointCode (.inr (k, r))) j)) := by
  decide +kernel

private theorem figure4_spine_formula : ∀ r : Fin 3,
    figure4Spine r = insert (pointCode (.inl r))
      (univ.image fun j : Fin 3 => pointCode (.inr (j, r))) := by
  decide +kernel

private theorem injectiveCoordinates_roots (hn : Fintype.card α = 12)
    (hi : ∀ j, Function.Injective fun r => (F.row r).selected j) :
    (univ.image F.roots).map (F.injectiveCoordinates hn hi).toEmbedding = figure4Roots := by
  simp only [map_eq_image, image_image, Function.comp_def, figure4Roots]
  congr 1
  funext r
  exact F.injectiveCoordinates_pointAt hn hi (.inl r)

private theorem injectiveCoordinates_triads (hn : Fintype.card α = 12)
    (hi : ∀ j, Function.Injective fun r => (F.row r).selected j) (j : Fin 3) :
    (F.common.triad j).map (F.injectiveCoordinates hn hi).toEmbedding = figure4Triads j := by
  have he : univ.image (fun r => (F.row r).selected j) = F.common.triad j := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨r, _, rfl⟩ := mem_image.mp hx
      exact (F.row r).selected_mem j
    · rw [card_image_of_injective _ (hi j), F.common.triad_card]
      rfl
  rw [← he, map_eq_image, image_image]
  congr 1
  funext r
  exact F.injectiveCoordinates_pointAt hn hi (.inr (j, r))

omit [Fintype α] in
private theorem markedRow_map {β : Type*} [DecidableEq β]
    (e : α ≃ β) (T : Fin 3 → Finset α) (s : Fin 3 → α) (j : Fin 3) :
    (StantonGeometry.markedRow T s j).map e.toEmbedding =
      StantonGeometry.markedRow (fun k => (T k).map e.toEmbedding) (e ∘ s) j := by
  simp only [StantonGeometry.markedRow, map_eq_image, image_union, biUnion_image,
    image_sdiff _ _ e.toEmbedding.injective, image_singleton, Function.comp_def,
    Equiv.toEmbedding_apply]

/-- GPPT Lemma 5.8, Case 1: if no selected point is repeated in a triad,
the covering is a completion of Figure 4 in explicit coordinates. -/
theorem injective_isFigure4Completion (hn : Fintype.card α = 12)
    (hi : ∀ j, Function.Injective fun r => (F.row r).selected j) :
    IsFigure4Completion (relabel (F.injectiveCoordinates hn hi) C) := by
  let e := F.injectiveCoordinates hn hi
  let B : Fin 3 → Finset (Fin 12) := fun r =>
    (insert (F.roots r) (F.row r).shortTrace).map e.toEmbedding
  apply (isFigure4Completion_iff_extensions _).mpr
  refine ⟨B, ?_, ?_⟩
  · intro r
    constructor
    · rw [figure4_spine_formula r]
      intro x hx
      rcases mem_insert.mp hx with he | hx
      · subst x
        exact mem_map.mpr ⟨F.roots r, mem_insert_self _ _,
          F.injectiveCoordinates_pointAt hn hi (.inl r)⟩
      · obtain ⟨j, _, rfl⟩ := mem_image.mp hx
        exact mem_map.mpr ⟨(F.row r).selected j,
          mem_insert_of_mem ((F.row r).selected_subset (mem_image.mpr ⟨j, mem_univ _, rfl⟩)),
          F.injectiveCoordinates_pointAt hn hi (.inr (j, r))⟩
    · rw [card_map, card_insert_of_notMem (F.row r).root_not_mem_shortTrace,
        (F.row r).shortTrace_card]
  · have hroots (r : Fin 3) : e (F.roots r) = pointCode (.inl r) :=
      F.injectiveCoordinates_pointAt hn hi (.inl r)
    have hselected (r j : Fin 3) : e ((F.row r).selected j) = pointCode (.inr (j, r)) :=
      F.injectiveCoordinates_pointAt hn hi (.inr (j, r))
    have htriad (k : Fin 3) : (F.common.triad k).map e.toEmbedding = figure4Triads k :=
      F.injectiveCoordinates_triads hn hi k
    unfold relabel
    conv_lhs => arg 2; rw [F.blocks_eq]
    rw [map_union, map_union, figure4_core_formula]
    have hcommon : ((univ.image fun j => univ.image F.roots ∪ F.common.triad j).map
        (Finset.mapEmbedding e.toEmbedding).toEmbedding) =
          univ.image fun j => figure4Roots ∪ figure4Triads j := by
      rw [map_eq_image, image_image]
      congr 1
      funext j
      change (univ.image F.roots ∪ F.common.triad j).map e.toEmbedding = _
      rw [map_union, F.injectiveCoordinates_roots hn hi, F.injectiveCoordinates_triads hn hi]
    have hfull : ((univ.biUnion fun r => univ.image fun j =>
        insert (F.roots r) (StantonGeometry.markedRow F.common.triad (F.row r).selected j)).map
        (Finset.mapEmbedding e.toEmbedding).toEmbedding) =
        univ.biUnion fun r : Fin 3 => univ.image fun j =>
          insert (pointCode (.inl r)) (StantonGeometry.markedRow figure4Triads
            (fun k => pointCode (.inr (k, r))) j) := by
      simp only [map_eq_image, biUnion_image, image_image, Function.comp_def]
      congr 1
      funext r
      congr 1
      funext j
      change (insert (F.roots r) (StantonGeometry.markedRow F.common.triad (F.row r).selected j)).map e.toEmbedding = _
      rw [map_insert]
      simp only [Equiv.toEmbedding_apply]
      rw [hroots, markedRow_map]
      simp only [htriad, Function.comp_def, hselected]
    have hshort : ((univ.image fun r => insert (F.roots r) (F.row r).shortTrace).map
        (Finset.mapEmbedding e.toEmbedding).toEmbedding) = univ.image B := by
      rw [map_eq_image, image_image]
      rfl
    rw [hcommon, hfull, hshort]

omit [DecidableEq α] [Fintype α] in
/-- Case 1 in the same isomorphism-invariant form as the GPPT reduction. -/
theorem injective_isomorphicTemplateCompletion {D : Family (Fin 12)}
    (G : TriplicateFrame D)
    (hi : ∀ j, Function.Injective fun r => (G.row r).selected j) :
    IsomorphicTemplateCompletion D := by
  have hh := figure4Completion_isomorphicTemplateCompletion
    (G.injective_isFigure4Completion (by simp) hi)
  obtain ⟨E, hE, e, he⟩ := hh
  refine ⟨E, hE, (G.injectiveCoordinates (by simp) hi).trans e, ?_⟩
  rw [← relabel_trans]
  exact he

end TriplicateFrame

#guard_standard_axioms short_cross_capacity common_short_saturation common_short_mates_forced
  two_short_traces_partition partitioned_triad_one_addition
  TriplicateFrame.additions_card TriplicateFrame.degree_eq_seven_additions
  TriplicateFrame.additions_total TriplicateFrame.additions_eq_common_mates
  TriplicateFrame.other_triad_degree_seven TriplicateFrame.injective_isFigure4Completion
  TriplicateFrame.injective_isomorphicTemplateCompletion
  TriplicateFrame.repeated_selection_mates_pair_ge_five
  TriplicateFrame.column_injective_of_minimum TriplicateFrame.other_column_injective
  TriplicateFrame.minimum_selected_twice_all TriplicateFrame.repeated_column_no_minimum
  TriplicateFrame.triadExcess_total TriplicateFrame.repeated_column_excess_ge_three
  TriplicateFrame.minimum_mem_shortTrace_iff TriplicateFrame.two_selected_cross_covered
  TriplicateFrame.repeated_column_excess_ge_four_of_zero
  TriplicateFrame.other_columns_injective_of_repeated
  TriplicateFrame.exists_minimum_selected_other_column

end CoveringDesigns.GPPTStructural
