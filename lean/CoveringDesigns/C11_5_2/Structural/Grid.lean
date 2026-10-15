import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega
import CoveringDesigns.Foundations.StandardAxioms

/-! The four cells of two distinct partitions of a six-point set into triples. -/

namespace CoveringDesigns.StantonStructural

open Finset

variable {α : Type*} [DecidableEq α]

/-- The two singleton cells and two pair cells, with either orientation of `W`. -/
structure GridCells (X T W : Finset α) where
  s : α
  t : α
  C : Finset α
  D : Finset α
  pairwise_disjoint : List.Pairwise Disjoint [{s}, {t}, C, D]
  C_card : C.card = 2
  D_card : D.card = 2
  span : {s, t} ∪ (C ∪ D) = X
  T_eq : T = {s} ∪ C
  T_compl_eq : X \ T = {t} ∪ D
  W_eq_or : (W = {s} ∪ D ∧ X \ W = {t} ∪ C) ∨
    (W = {t} ∪ C ∧ X \ W = {s} ∪ D)

namespace GridCells

variable {X T W : Finset α} (G : GridCells X T W)

theorem s_mem_X : G.s ∈ X := by
  simpa only [G.span] using (show G.s ∈ {G.s, G.t} ∪ (G.C ∪ G.D) by simp)

theorem t_mem_X : G.t ∈ X := by
  simpa only [G.span] using (show G.t ∈ {G.s, G.t} ∪ (G.C ∪ G.D) by simp)

theorem C_subset : G.C ⊆ X := by
  intro x hx
  rw [← G.span]
  simp [hx]

theorem D_subset : G.D ⊆ X := by
  intro x hx
  rw [← G.span]
  simp [hx]

end GridCells

private theorem cells_of_single_intersection {X T W : Finset α}
    (hX : X.card = 6) (hT : T ⊆ X) (hW : W ⊆ X)
    (hTc : T.card = 3) (hWc : W.card = 3) (hi : (T ∩ W).card = 1) :
    Nonempty (GridCells X T W) := by
  have hu : (T ∪ W).card = 5 := by
    have hh := card_union_add_card_inter T W
    omega
  have ho : (X \ (T ∪ W)).card = 1 := by
    rw [card_sdiff_of_subset (union_subset hT hW), hX, hu]
  obtain ⟨s, hs⟩ := card_eq_one.mp hi
  obtain ⟨t, ht⟩ := card_eq_one.mp ho
  have hC : (T \ W).card = 2 := by
    have hh := card_sdiff_add_card_inter T W
    omega
  have hD : (W \ T).card = 2 := by
    have hh := card_sdiff_add_card_inter W T
    rw [inter_comm W T] at hh
    omega
  have hd : List.Pairwise Disjoint [T ∩ W, X \ (T ∪ W), T \ W, W \ T] := by
    simp only [List.pairwise_cons, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp only [disjoint_left, mem_inter, mem_sdiff, mem_union]
    tauto
  have hspan : {s, t} ∪ ((T \ W) ∪ (W \ T)) = X := by
    have hp : ({s, t} : Finset α) = {s} ∪ {t} := by simp
    rw [hp, ← hs, ← ht]
    ext x
    have hxT : x ∈ T → x ∈ X := fun hx => hT hx
    have hxW : x ∈ W → x ∈ X := fun hx => hW hx
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  have hTeq : T = {s} ∪ (T \ W) := by
    rw [← hs, union_comm]
    exact (sdiff_union_inter T W).symm
  have hWeq : W = {s} ∪ (W \ T) := by
    rw [← hs, inter_comm T W, union_comm]
    exact (sdiff_union_inter W T).symm
  have hTcompl : X \ T = {t} ∪ (W \ T) := by
    rw [← ht]
    ext x
    have hxW : x ∈ W → x ∈ X := fun hx => hW hx
    simp only [mem_union, mem_sdiff]
    tauto
  have hWcompl : X \ W = {t} ∪ (T \ W) := by
    rw [← ht]
    ext x
    have hxT : x ∈ T → x ∈ X := fun hx => hT hx
    simp only [mem_union, mem_sdiff]
    tauto
  refine ⟨{
    s := s, t := t, C := T \ W, D := W \ T
    pairwise_disjoint := ?_
    C_card := hC, D_card := hD, span := hspan
    T_eq := hTeq, T_compl_eq := hTcompl
    W_eq_or := Or.inl ⟨hWeq, hWcompl⟩ }⟩
  simpa only [hs, ht] using hd

/-- Distinct triple partitions have the four-cell pattern `1,2,2,1`. -/
theorem exists_grid_cells {X T W : Finset α}
    (hX : X.card = 6) (hT : T ⊆ X) (hW : W ⊆ X)
    (hTc : T.card = 3) (hWc : W.card = 3)
    (hne : W ≠ T) (hne' : W ≠ X \ T) : Nonempty (GridCells X T W) := by
  have hcT : (X \ T).card = 3 := by
    rw [card_sdiff_of_subset hT, hX, hTc]
  have hcW : (X \ W).card = 3 := by
    rw [card_sdiff_of_subset hW, hX, hWc]
  have hi_le : (T ∩ W).card ≤ 3 := (card_le_card inter_subset_left).trans_eq hTc
  have hi_zero : (T ∩ W).card ≠ 0 := by
    intro he
    have hempty : T ∩ W = ∅ := card_eq_zero.mp he
    have hsub : W ⊆ X \ T := by
      intro x hx
      refine mem_sdiff.mpr ⟨hW hx, ?_⟩
      intro hxT
      have hxI : x ∈ T ∩ W := mem_inter.mpr ⟨hxT, hx⟩
      rw [hempty] at hxI
      simp at hxI
    exact hne' (eq_of_subset_of_card_le hsub (by omega))
  have hi_three : (T ∩ W).card ≠ 3 := by
    intro he
    have heT : T ∩ W = T := eq_of_subset_of_card_le inter_subset_left (by omega)
    have hsub : T ⊆ W := by rw [← heT]; exact inter_subset_right
    exact hne (eq_of_subset_of_card_le hsub (by omega)).symm
  have hi_cases : (T ∩ W).card = 1 ∨ (T ∩ W).card = 2 := by omega
  rcases hi_cases with hi | hi
  · exact cells_of_single_intersection hX hT hW hTc hWc hi
  · have he : T ∩ (X \ W) = T \ W := by
      ext x
      have hxT : x ∈ T → x ∈ X := fun hx => hT hx
      simp only [mem_inter, mem_sdiff]
      tauto
    have hi' : (T ∩ (X \ W)).card = 1 := by
      rw [he]
      have hh := card_sdiff_add_card_inter T W
      omega
    obtain ⟨G⟩ := cells_of_single_intersection hX hT sdiff_subset hTc hcW hi'
    refine ⟨{
      s := G.s, t := G.t, C := G.C, D := G.D
      pairwise_disjoint := G.pairwise_disjoint
      C_card := G.C_card, D_card := G.D_card, span := G.span
      T_eq := G.T_eq, T_compl_eq := G.T_compl_eq
      W_eq_or := ?_ }⟩
    rcases G.W_eq_or with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨by simpa only [Finset.sdiff_sdiff_eq_self hW] using h2, h1⟩
    · exact Or.inl ⟨by simpa only [Finset.sdiff_sdiff_eq_self hW] using h2, h1⟩

#guard_standard_axioms exists_grid_cells

end CoveringDesigns.StantonStructural
