import CoveringDesigns.C12_6_3.Structural.Triplicate
import CoveringDesigns.C12_6_3.Structural.ShortSymmetry

/-!
The final contradiction in GPPT Lemma 5.8, Case 3.  The repeated column and
the two injective columns determine the incidences needed in a minimum
point's link.  The argument counts only the fifteen structural block
positions of that actual frame; the short-trace additions remain arbitrary.
-/

set_option maxHeartbeats 1000000

namespace CoveringDesigns.GPPTStructural

open Finset StantonGeometry

variable {α : Type*} [DecidableEq α] [Fintype α] {C : Family α}

omit [Fintype α] in
private theorem link_pair_filter (D : Family α) (a : α)
    (u v : {q : α // q ≠ a}) :
    multiplicity (link D a) {u, v} =
      (D.filter fun B => a ∈ B ∧ u.val ∈ B ∧ v.val ∈ B).card := by
  have he := congrArg Finset.card (commonBlocks_liftBlock D a {u, v})
  rw [card_image_of_injective _ (liftBlock_injective a)] at he
  simpa only [commonBlocks, multiplicity, liftBlock, map_insert, map_singleton,
    Function.Embedding.subtype_apply, insert_subset_iff, singleton_subset_iff] using he

private theorem fullBlocks_link_erase (D : Family α) (a : α) (S : Finset α)
    (haS : a ∈ S) (hf : Facts (link D a))
    (hs : IsShortBlock (link D a) (S.subtype (· ≠ a))) :
    fullBlocks (link D a) = link (D.erase S) a := by
  ext B
  constructor
  · intro hB
    obtain ⟨hB, hn⟩ := mem_filter.mp hB
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hB
    obtain ⟨hEC, haE⟩ := mem_filter.mp hE
    refine mem_image.mpr ⟨E, mem_filter.mpr ⟨mem_erase.mpr ⟨?_, hEC⟩, haE⟩, rfl⟩
    intro he
    exact hn (he ▸ hs)
  · intro hB
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hB
    obtain ⟨hEC, haE⟩ := mem_filter.mp hE
    obtain ⟨hES, hEC⟩ := mem_erase.mp hEC
    have hE : E.subtype (· ≠ a) ∈ link D a :=
      mem_image.mpr ⟨E, mem_filter.mpr ⟨hEC, haE⟩, rfl⟩
    refine mem_filter.mpr ⟨hE, fun hshort => ?_⟩
    have he := hf.short_unique _ hE _ hs.1 hshort hs
    have he' := congrArg (liftBlock a) he
    rw [liftBlock_subtype a haE, liftBlock_subtype a haS] at he'
    exact hES he'

namespace TriplicateFrame

private theorem filter_card_indices (F : TriplicateFrame C) (hc : C.card = 15)
    (P : Finset α → Prop) [DecidablePred P] :
    (C.filter P).card = (univ.filter fun i => P (F.blockAt i)).card := by
  conv_lhs => rw [← F.blockAt_image]
  rw [filter_image, card_image_of_injective _ (F.blockAt_injective hc)]

private theorem root_not_mem_markedRow (F : TriplicateFrame C) (t r j : Fin 3) :
    F.roots t ∉ markedRow F.common.triad (F.row r).selected j := by
  have hr : F.roots t ∈ univ.image F.roots := mem_image.mpr ⟨t, mem_univ _, rfl⟩
  have ht (k : Fin 3) : F.roots t ∉ F.common.triad k :=
    fun h => disjoint_left.mp (F.common.disjoint_root k) hr h
  intro h
  rcases mem_union.mp h with h | h
  · exact ht j ((mem_singleton.mp h) ▸ (F.row r).selected_mem j)
  · obtain ⟨k, _, hk⟩ := mem_biUnion.mp h
    exact ht k (mem_sdiff.mp hk).1

private theorem root_mem_noncommon (F : TriplicateFrame C) (t r : Fin 3)
    (j : Option (Fin 3)) : F.roots t ∈ F.blockAt (.inr (r, j)) ↔ t = r := by
  have hne : (F.roots t = F.roots r) ↔ t = r := F.roots_injective.eq_iff
  cases j with
  | none =>
    have hn : F.roots t ∉ (F.row r).shortTrace := fun h =>
      disjoint_left.mp (F.short_disjoint_roots r)
        (mem_image.mpr ⟨t, mem_univ _, rfl⟩) h
    simp only [blockAt, mem_insert, hne, hn, or_false]
  | some j =>
    simp only [blockAt, mem_insert, hne, F.root_not_mem_markedRow, or_false]

/-- A minimum point has no nonselected occurrence in a short trace. -/
private theorem minimum_not_mem_additions (F : TriplicateFrame C) (hc : C.card = 15)
    {a : α} {j : Fin 3} (ha : a ∈ F.common.triad j) (hd : degree C a = 7)
    (r : Fin 3) : a ∉ F.additions r := by
  have he := F.degree_eq_seven_additions hc ha
  have hs : (∑ s : Fin 3, if a ∈ F.additions s then 1 else 0) = 0 := by omega
  have hr : (if a ∈ F.additions r then 1 else 0) ≤
      ∑ s : Fin 3, if a ∈ F.additions s then 1 else 0 :=
    single_le_sum (f := fun s : Fin 3 => if a ∈ F.additions s then (1 : ℕ) else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ r)
  rw [hs] at hr
  intro hm
  simp [hm] at hr

/-- GPPT Figure 7 is impossible: two rows agree in column zero, the third
differs, the other columns are injective, and row zero selects a minimum
point in column one.  Stanton geometry in that point's link gives the
contradiction, without any assumptions on the remaining short additions. -/
theorem repeated_column_minimum_selected_contradiction (F : TriplicateFrame C)
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hc : C.card = 15)
    (h10 : (F.row 1).selected 0 = (F.row 0).selected 0)
    (h20 : (F.row 2).selected 0 ≠ (F.row 0).selected 0)
    (hi1 : Function.Injective fun r => (F.row r).selected 1)
    (hi2 : Function.Injective fun r => (F.row r).selected 2)
    (hmin : degree C ((F.row 0).selected 1) = 7) : False := by
  let a := (F.row 0).selected 1
  let x := (F.row 0).selected 0
  let b := (F.row 0).selected 2
  let y := (F.row 2).selected 0
  have haT : a ∈ F.common.triad 1 := (F.row 0).selected_mem 1
  have hxT : x ∈ F.common.triad 0 := (F.row 0).selected_mem 0
  have hbT : b ∈ F.common.triad 2 := (F.row 0).selected_mem 2
  have hyT : y ∈ F.common.triad 0 := (F.row 2).selected_mem 0
  have hyx : y ≠ x := h20
  have hyErase : y ∈ (F.common.triad 0).erase x := mem_erase.mpr ⟨hyx, hyT⟩
  have hzcard : (((F.common.triad 0).erase x).erase y).card = 1 := by
    rw [card_erase_of_mem hyErase, card_erase_of_mem hxT, F.common.triad_card]
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (((F.common.triad 0).erase x).erase y).card by omega)
  have hzy : z ≠ y := (mem_erase.mp hz).1
  have hzx : z ≠ x := (mem_erase.mp (mem_of_mem_erase hz)).1
  have hzT : z ∈ F.common.triad 0 := mem_of_mem_erase (mem_of_mem_erase hz)
  have hroot {u : α} {k : Fin 3} (hu : u ∈ F.common.triad k) (r : Fin 3) :
      u ≠ F.roots r := fun he => F.not_mem_roots_of_mem_triad hu
        (mem_image.mpr ⟨r, mem_univ _, he.symm⟩)
  have hax : a ≠ x := fun he => by
    have hh := F.triad_eq_of_mem haT (he ▸ hxT)
    omega
  have hab : a ≠ b := fun he => by
    have hh := F.triad_eq_of_mem haT (he ▸ hbT)
    omega
  have hay : a ≠ y := fun he => by
    have hh := F.triad_eq_of_mem haT (he ▸ hyT)
    omega
  have haz : a ≠ z := fun he => by
    have hh := F.triad_eq_of_mem haT (he ▸ hzT)
    omega
  have hxb : x ≠ b := fun he => by
    have hh := F.triad_eq_of_mem hxT (he ▸ hbT)
    omega
  have hasel (r : Fin 3) : a = (F.row r).selected 1 ↔ r = 0 := by
    exact ⟨fun he => (hi1 he).symm, fun he => he ▸ rfl⟩
  have hbsel (r : Fin 3) : b = (F.row r).selected 2 ↔ r = 0 := by
    exact ⟨fun he => (hi2 he).symm, fun he => he ▸ rfl⟩
  have hxsel (r : Fin 3) : x = (F.row r).selected 0 ↔ r ≠ 2 := by
    fin_cases r <;> simp [x, h10, Ne.symm h20]
  have hysel (r : Fin 3) : y = (F.row r).selected 0 ↔ r = 2 := by
    fin_cases r <;> simp [y, h10, h20]
  have hzsel (r : Fin 3) : z ≠ (F.row r).selected 0 := by
    fin_cases r
    · exact hzx
    · change z ≠ (F.row 1).selected 0
      rw [h10]
      exact hzx
    · exact hzy
  have hashort (r : Fin 3) : a ∈ (F.row r).shortTrace ↔ r = 0 := by
    constructor
    · intro ha
      have hsel : a ∈ univ.image (F.row r).selected := by
        by_contra hh
        exact F.minimum_not_mem_additions hc haT hmin r (mem_sdiff.mpr ⟨ha, hh⟩)
      exact (hasel r).mp ((F.mem_selected_iff haT r).mp hsel)
    · rintro rfl
      exact (F.row 0).selected_subset (mem_image.mpr ⟨1, mem_univ _, rfl⟩)
  have hxshort : x ∈ (F.row 0).shortTrace :=
    (F.row 0).selected_subset (mem_image.mpr ⟨0, mem_univ _, rfl⟩)
  have hbshort : b ∈ (F.row 0).shortTrace :=
    (F.row 0).selected_subset (mem_image.mpr ⟨2, mem_univ _, rfl⟩)
  let iS : Fin 3 ⊕ (Fin 3 × Option (Fin 3)) := .inr (0, none)
  let iB : Fin 3 ⊕ (Fin 3 × Option (Fin 3)) := .inr (1, some 0)
  let iD : Fin 3 ⊕ (Fin 3 × Option (Fin 3)) := .inr (0, some 1)
  let iE : Fin 3 ⊕ (Fin 3 × Option (Fin 3)) := .inr (1, some 2)
  have hpair (i : Fin 3 ⊕ (Fin 3 × Option (Fin 3))) :
      a ∈ F.blockAt i ∧ x ∈ F.blockAt i ∧ b ∈ F.blockAt i ↔ i = iS ∨ i = iB := by
    rcases i with k | ⟨r, _ | k⟩
    · fin_cases k <;>
        simp [blockAt, F.not_mem_roots_of_mem_triad haT, F.not_mem_roots_of_mem_triad hxT,
          F.not_mem_roots_of_mem_triad hbT, F.mem_triad_iff haT, F.mem_triad_iff hxT,
          F.mem_triad_iff hbT, iS, iB]
    · fin_cases r <;>
        simp [blockAt, hroot haT, hroot hxT, hroot hbT, hashort, hxshort, hbshort, iS, iB]
    · simp only [blockAt, mem_insert, hroot haT, hroot hxT, hroot hbT, false_or,
        F.mem_markedRow_iff haT, F.mem_markedRow_iff hxT, F.mem_markedRow_iff hbT,
        hasel, hxsel, hbsel]
      fin_cases r <;> fin_cases k <;> simp [iS, iB, hasel, hxsel, hbsel]
  have hmates (i : Fin 3 ⊕ (Fin 3 × Option (Fin 3))) :
      (a ∈ F.blockAt i ∧ y ∈ F.blockAt i ∧ z ∈ F.blockAt i) ∧ i ≠ iS ↔
        i = iD ∨ i = iE := by
    rcases i with k | ⟨r, _ | k⟩
    · fin_cases k <;>
        simp [blockAt, F.not_mem_roots_of_mem_triad haT, F.not_mem_roots_of_mem_triad hyT,
          F.not_mem_roots_of_mem_triad hzT, F.mem_triad_iff haT, F.mem_triad_iff hyT,
          F.mem_triad_iff hzT, iS, iD, iE]
    · fin_cases r <;>
        simp [blockAt, hroot haT, hroot hyT, hroot hzT, hashort, iS, iD, iE]
    · simp only [blockAt, mem_insert, hroot haT, hroot hyT, hroot hzT, false_or,
        F.mem_markedRow_iff haT, F.mem_markedRow_iff hyT, F.mem_markedRow_iff hzT,
        hasel, hysel, hzsel]
      fin_cases r <;> fin_cases k <;> simp [iS, iD, iE, hasel, hysel, hzsel]
  let x' : {q : α // q ≠ a} := ⟨x, hax.symm⟩
  let b' : {q : α // q ≠ a} := ⟨b, hab.symm⟩
  let y' : {q : α // q ≠ a} := ⟨y, hay.symm⟩
  let z' : {q : α // q ≠ a} := ⟨z, haz.symm⟩
  let S := F.blockAt iS
  have haS : a ∈ S := by simpa [S, iS, blockAt, hroot haT] using (hashort 0).mpr rfl
  have hf := geometry_facts (by rw [complement_point_card, hn])
    (link_isCover hC a) (by rw [link_card]; exact hmin)
  have hcount : multiplicity (link C a) {x', b'} = 2 := by
    rw [link_pair_filter, F.filter_card_indices hc]
    have he : (univ.filter fun i => a ∈ F.blockAt i ∧ x ∈ F.blockAt i ∧ b ∈ F.blockAt i) =
        {iS, iB} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      exact hpair i
    change (univ.filter fun i => a ∈ F.blockAt i ∧ x ∈ F.blockAt i ∧ b ∈ F.blockAt i).card = 2
    rw [he]
    decide +kernel
  have hrootShort : IsShortPoint (link C a) ⟨F.roots 0, (hroot haT 0).symm⟩ := by
    apply minimum_short_symmetry hn hC (F.root_degree 0) hmin (hroot haT 0).symm
    exact ((F.row 0).selected_iff ⟨a, hroot haT 0⟩).mp
      (mem_image.mpr ⟨1, mem_univ _, rfl⟩)
  have hshortS : IsShortBlock (link C a) (S.subtype (· ≠ a)) := by
    obtain ⟨B, hBL, hBshort, hxB, hbB⟩ := hf.multiplicity_two_short x' b'
      (fun he => hxb (congrArg Subtype.val he)) hcount
    obtain ⟨D, hDL, hDshort, hrD⟩ := hrootShort.2
    have hrB : (⟨F.roots 0, (hroot haT 0).symm⟩ : {q : α // q ≠ a}) ∈ B := by
      rw [hf.short_unique B hBL D hDL hBshort hDshort]
      exact hrD
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hBL
    obtain ⟨hEC, haE⟩ := mem_filter.mp hE
    rw [← F.blockAt_image] at hEC
    obtain ⟨i, _, rfl⟩ := mem_image.mp hEC
    rcases (hpair i).mp ⟨haE, mem_subtype.mp hxB, mem_subtype.mp hbB⟩ with hi | hi
    · simpa only [hi] using hBshort
    · have hr := (F.root_mem_noncommon 0 1 (some 0)).mp
        (show F.roots 0 ∈ F.blockAt (.inr (1, some 0)) by
          simpa only [hi] using mem_subtype.mp hrB)
      omega
  have hfullCount : multiplicity (fullBlocks (link C a)) {y', z'} = 2 := by
    rw [fullBlocks_link_erase C a S haS hf hshortS, link_pair_filter]
    have he : ((C.erase S).filter fun B => a ∈ B ∧ y ∈ B ∧ z ∈ B) =
        C.filter (fun B => (a ∈ B ∧ y ∈ B ∧ z ∈ B) ∧ B ≠ S) := by
      ext B
      simp [and_assoc, and_left_comm, and_comm]
    change ((C.erase S).filter fun B => a ∈ B ∧ y ∈ B ∧ z ∈ B).card = 2
    rw [he, F.filter_card_indices hc]
    have hiS (i) : F.blockAt i ≠ S ↔ i ≠ iS :=
      not_congr (F.blockAt_injective hc).eq_iff
    have hi : (univ.filter fun i =>
        (a ∈ F.blockAt i ∧ y ∈ F.blockAt i ∧ z ∈ F.blockAt i) ∧ F.blockAt i ≠ S) =
        {iD, iE} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, hiS]
      exact hmates i
    rw [hi]
    decide +kernel
  exact hf.full_pair_count_ne_two y' z'
    (fun he => hzy (congrArg Subtype.val he).symm) hfullCount

#guard_standard_axioms repeated_column_minimum_selected_contradiction

end TriplicateFrame

end CoveringDesigns.GPPTStructural
