import CoveringDesigns.C12_6_3.Structural.MinimumPairs

/-! GPPT Corollary 5.3 and Lemma 5.4. A minimum point in another minimum
point's short block is short there, and this short-point relation is symmetric.
The symmetry proof transports two blocks with singleton intersection between
links and applies the intrinsic Stanton intersection properties. -/

namespace CoveringDesigns

open Finset StantonGeometry

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace StantonGeometry

/-- Any singleton intersection of two different blocks identifies a short
point. This includes an intersection involving the unique short block. -/
theorem Facts.short_of_singleton_intersection {C : Family α} (h : Facts C)
    {B D : Finset α} (hB : B ∈ C) (hD : D ∈ C) (hBD : B ≠ D)
    {x : α} (hinter : B ∩ D = {x}) : IsShortPoint C x := by
  have hpoint {y : α} (hyB : y ∈ B) (hyD : y ∈ D) : y = x := by
    exact mem_singleton.mp (hinter ▸ mem_inter.mpr ⟨hyB, hyD⟩)
  by_cases hsB : IsShortBlock C B
  · by_cases hsD : IsShortBlock C D
    · exact False.elim (hBD (h.short_unique B hB D hD hsB hsD))
    · obtain ⟨y, hy, hyB, hyD⟩ := h.short_full_meet B hB hsB D (mem_filter.mpr ⟨hD, hsD⟩)
      exact hpoint hyB hyD ▸ hy
  · by_cases hsD : IsShortBlock C D
    · obtain ⟨y, hy, hyD, hyB⟩ := h.short_full_meet D hD hsD B (mem_filter.mpr ⟨hB, hsB⟩)
      exact hpoint hyB hyD ▸ hy
    · rcases h.full_intersection B (mem_filter.mpr ⟨hB, hsB⟩)
        D (mem_filter.mpr ⟨hD, hsD⟩) hBD with hk | ⟨y, hy, he⟩
      · have hc := hk.1
        rw [hinter, card_singleton] at hc
        omega
      · have heq : y = x := singleton_injective (he.symm.trans hinter)
        exact heq ▸ hy

end StantonGeometry

namespace GPPTStructural

/-- GPPT Corollary 5.3: a minimum point in a minimum root's short block is
short in the induced cover. -/
theorem minimum_in_short_block_is_short {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card ≤ 15)
    {p q : α} (hp : degree C p = 7) (hq : degree C q = 7) (hpq : p ≠ q)
    {B : Finset {x : α // x ≠ p}} (hB : IsShortBlock (link C p) B)
    (hqB : (⟨q, hpq.symm⟩ : {x : α // x ≠ p}) ∈ B) :
    IsShortPoint (link C p) ⟨q, hpq.symm⟩ := by
  refine ⟨?_, B, hB.1, hB, hqB⟩
  rw [degree_link]
  exact minimum_pair_degree_three hn hC hb hp hq hpq

/-- Two blocks meeting only in q after deleting p meet only in p after
deleting q. This transport is independent of covering or classification. -/
theorem swap_link_singleton_intersection {C : Family α} {p q : α} (hpq : p ≠ q)
    {B D : Finset {x : α // x ≠ p}}
    (hB : B ∈ link C p) (hD : D ∈ link C p) (hBD : B ≠ D)
    (hinter : B ∩ D = {(⟨q, hpq.symm⟩ : {x : α // x ≠ p})}) :
    ∃ E ∈ link C q, ∃ F ∈ link C q, E ≠ F ∧
      E ∩ F = {(⟨p, hpq⟩ : {x : α // x ≠ q})} := by
  obtain ⟨E, hE, rfl⟩ := mem_image.mp hB
  obtain ⟨F, hF, rfl⟩ := mem_image.mp hD
  obtain ⟨hEC, hpE⟩ := mem_filter.mp hE
  obtain ⟨hFC, hpF⟩ := mem_filter.mp hF
  have hqEF : (⟨q, hpq.symm⟩ : {x : α // x ≠ p}) ∈
      E.subtype (· ≠ p) ∩ F.subtype (· ≠ p) := by rw [hinter]; simp
  have hqE : q ∈ E := mem_subtype.mp (mem_inter.mp hqEF).1
  have hqF : q ∈ F := mem_subtype.mp (mem_inter.mp hqEF).2
  refine ⟨E.subtype (· ≠ q), mem_image.mpr ⟨E, mem_filter.mpr ⟨hEC, hqE⟩, rfl⟩,
    F.subtype (· ≠ q), mem_image.mpr ⟨F, mem_filter.mpr ⟨hFC, hqF⟩, rfl⟩, ?_, ?_⟩
  · intro he
    have he' := congrArg (liftBlock q) he
    rw [liftBlock_subtype q hqE, liftBlock_subtype q hqF] at he'
    exact hBD (congrArg (Finset.subtype (· ≠ p)) he')
  · ext x
    simp only [mem_inter, mem_subtype, mem_singleton, Subtype.ext_iff]
    constructor
    · rintro ⟨hxE, hxF⟩
      by_contra hxp
      let y : {y : α // y ≠ p} := ⟨x.val, hxp⟩
      have hy : y ∈ E.subtype (· ≠ p) ∩ F.subtype (· ≠ p) :=
        mem_inter.mpr ⟨mem_subtype.mpr hxE, mem_subtype.mpr hxF⟩
      rw [hinter] at hy
      have hxy : x.val = q := congrArg Subtype.val (mem_singleton.mp hy)
      exact x.property hxy
    · intro he
      simpa only [he] using And.intro hpE hpF

/-- GPPT Lemma 5.4: shortness between two degree-seven points is symmetric.
The argument needs only their two Stanton links, regardless of total blocks. -/
theorem minimum_short_symmetry {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    {p q : α} (hp : degree C p = 7) (hq : degree C q = 7) (hpq : p ≠ q)
    (hs : IsShortPoint (link C p) ⟨q, hpq.symm⟩) :
    IsShortPoint (link C q) ⟨p, hpq⟩ := by
  have hP := geometry_facts (by rw [complement_point_card, hn])
    (link_isCover hC p) (by rw [link_card, hp])
  have hQ := geometry_facts (by rw [complement_point_card, hn])
    (link_isCover hC q) (by rw [link_card, hq])
  obtain ⟨B, hB, D, hD, hBD, hinter⟩ := hP.short_two_full ⟨q, hpq.symm⟩ hs
  obtain ⟨E, hE, F, hF, hEF, hinter'⟩ := swap_link_singleton_intersection hpq
    (mem_filter.mp hB).1 (mem_filter.mp hD).1 hBD hinter
  exact hQ.short_of_singleton_intersection hE hF hEF hinter'

theorem minimum_short_iff {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3)
    {p q : α} (hp : degree C p = 7) (hq : degree C q = 7) (hpq : p ≠ q) :
    IsShortPoint (link C p) ⟨q, hpq.symm⟩ ↔ IsShortPoint (link C q) ⟨p, hpq⟩ :=
  ⟨minimum_short_symmetry hn hC hp hq hpq,
    minimum_short_symmetry hn hC hq hp hpq.symm⟩

#guard_standard_axioms Facts.short_of_singleton_intersection minimum_in_short_block_is_short
  swap_link_singleton_intersection minimum_short_symmetry minimum_short_iff

end GPPTStructural

end CoveringDesigns
