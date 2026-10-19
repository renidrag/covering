import CoveringDesigns.C20_11_3.SaturatedAssignment
import CoveringDesigns.TwoKMinusTwo.Incidence

/-! Saturated geometry retains actual blocks and full exclusive parts.
No converse from intersection size to saturation is asserted. -/
namespace CoveringDesigns.TwoKMinusCGeneral
open Finset C20_11_3 TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α] {c k : ℕ}
variable {C : Family α} {p q : α} {B D : Finset α}

theorem saturated_pair_inter_card (hv : Fintype.card α+c=2*k)
    (hC : IsCover C k 3) (hpq : p ≠ q)
    (hstar : star (star C p) q = {B,D}) : (B ∩ D).card=c := by
  have hB : B ∈ star (star C p) q := by rw [hstar]; simp
  have hD : D ∈ star (star C p) q := by rw [hstar]; simp
  have hb := hC.1 B (mem_filter.mp (mem_filter.mp hB).1).1
  have hd := hC.1 D (mem_filter.mp (mem_filter.mp hD).1).1
  have hi := card_union_add_card_inter B D
  rw [saturated_pair_union hC.2 hpq hstar, card_univ, hb, hd] at hi
  omega

/-- Two distinct actual blocks, their star, union, intersection and exclusive sizes. -/
theorem saturated_pair_blocks (hv : Fintype.card α+c=2*k)
    (hC : IsCover C k 3) (hpq : p ≠ q) (hsat : degree (star C p) q=2) :
    ∃ B ∈ C, ∃ D ∈ C, B ≠ D ∧ star (star C p) q={B,D} ∧
      B ∪ D=univ ∧ (B ∩ D).card=c ∧
      (B \ D).card=k-c ∧ (D \ B).card=k-c := by
  obtain ⟨B,D,hBD,hstar⟩ := card_eq_two.mp hsat
  have hB : B ∈ star (star C p) q := by rw [hstar]; simp
  have hD : D ∈ star (star C p) q := by rw [hstar]; simp
  have hBC := (mem_filter.mp (mem_filter.mp hB).1).1
  have hDC := (mem_filter.mp (mem_filter.mp hD).1).1
  have hi := saturated_pair_inter_card hv hC hpq hstar
  refine ⟨B,hBC,D,hDC,hBD,hstar,saturated_pair_union hC.2 hpq hstar,hi,?_,?_⟩
  · have he := card_sdiff_add_card_inter B D
    rw [hi,hC.1 B hBC] at he
    omega
  · have he := card_sdiff_add_card_inter D B
    rw [inter_comm D B,hi,hC.1 D hDC] at he
    omega

/-- Orientation into endpoint classes is forced by the two actual supporting blocks. -/
theorem oriented_blocks_unique {x y : α} {A E A' E' : Finset α}
    (hA : A ∈ onlyBlocks C p q) (hE : E ∈ onlyBlocks C q p)
    (hA' : A' ∈ onlyBlocks C p q) (hE' : E' ∈ onlyBlocks C q p)
    (hs : star (star C x) y={A,E}) (hs' : star (star C x) y={A',E'}) :
    A=A' ∧ E=E' := by
  have he : ({A,E} : Family α)={A',E'} := hs.symm.trans hs'
  have ha : A=A' := by
    have hm : A ∈ ({A',E'} : Family α) := by rw [← he]; simp
    rcases mem_insert.mp hm with h | h
    · exact h
    · have hh := mem_singleton.mp h
      exact ((mem_onlyBlocks.mp hE').2.2 (hh ▸ (mem_onlyBlocks.mp hA).2.1)).elim
  have hd : E=E' := by
    have hm : E ∈ ({A',E'} : Family α) := by rw [← he]; simp
    rcases mem_insert.mp hm with h | h
    · exact ((mem_onlyBlocks.mp hA').2.2 (h ▸ (mem_onlyBlocks.mp hE).2.1)).elim
    · exact mem_singleton.mp h
  exact ⟨ha,hd⟩
theorem cross_partner_exists {C : Family α} {p q x y : α} {B D : Finset α}
    (hv : Fintype.card α+c=2*k) (hC : IsCover C k 3)
    (hstar : star (star C p) q = {B,D})
    (hx : x ∈ B \ D) (hy : y ∈ D \ B)
    (hsat : degree (star C x) y = 2) :
    ∃ A ∈ onlyBlocks C p q, ∃ E ∈ onlyBlocks C q p, star (star C x) y={A,E} ∧
      (A ∩ E).card=c ∧ ({x,y} : Finset α) ⊆ A ∩ E := by
  have hxD : x ∉ D := (mem_sdiff.mp hx).2
  have hyB : y ∉ B := (mem_sdiff.mp hy).2
  have hxy : x ≠ y := by intro h; subst y; exact hxD (mem_sdiff.mp hy).1
  obtain ⟨A,hAC,E,hEC,_hAE,hAEStar,hunion,hAEinter,_,_⟩ :=
    saturated_pair_blocks hv hC hxy hsat
  have hAs : A ∈ star (star C x) y := by rw [hAEStar]; simp
  have hEs : E ∈ star (star C x) y := by rw [hAEStar]; simp
  have hxA := (mem_filter.mp (mem_filter.mp hAs).1).2
  have hyA := (mem_filter.mp hAs).2
  have hxE := (mem_filter.mp (mem_filter.mp hEs).1).2
  have hyE := (mem_filter.mp hEs).2
  have hsub : ({x,y} : Finset α) ⊆ A ∩ E := by simp [insert_subset_iff,hxA,hyA,hxE,hyE]
  have hnotboth (F : Finset α) (hFC : F ∈ C) (hxF : x ∈ F) (hyF : y ∈ F) :
      ¬ (p ∈ F ∧ q ∈ F) := by
    intro hh
    have hF : F ∈ star (star C p) q := by simp [star,hFC,hh.1,hh.2]
    rw [hstar] at hF
    rcases mem_insert.mp hF with hFB | hFD
    · subst F; exact hyB hyF
    · have hFD := mem_singleton.mp hFD
      subst F; exact hxD hxF
  have hpU : p ∈ A ∪ E := by rw [hunion]; simp
  have hqU : q ∈ A ∪ E := by rw [hunion]; simp
  by_cases hpA : p ∈ A
  · have hqA : q ∉ A := fun h => hnotboth A hAC hxA hyA ⟨hpA,h⟩
    have hqE := (mem_union.mp hqU).resolve_left hqA
    have hpE : p ∉ E := fun h => hnotboth E hEC hxE hyE ⟨h,hqE⟩
    exact ⟨A,mem_onlyBlocks.mpr ⟨hAC,hpA,hqA⟩,
      E,mem_onlyBlocks.mpr ⟨hEC,hqE,hpE⟩,hAEStar,hAEinter,hsub⟩
  · have hpE := (mem_union.mp hpU).resolve_left hpA
    have hqE : q ∉ E := fun h => hnotboth E hEC hxE hyE ⟨hpE,h⟩
    have hqA := (mem_union.mp hqU).resolve_right hqE
    exact ⟨E,mem_onlyBlocks.mpr ⟨hEC,hpE,hqE⟩,
      A,mem_onlyBlocks.mpr ⟨hAC,hqA,hpA⟩,by simpa [pair_comm] using hAEStar,
      by simpa [inter_comm] using hAEinter,by simpa [inter_comm] using hsub⟩


end CoveringDesigns.TwoKMinusCGeneral
