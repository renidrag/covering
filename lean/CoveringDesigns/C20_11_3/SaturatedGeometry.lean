import CoveringDesigns.Foundations.Links

/-!
Actual-block geometry of a saturated pair in a (20,11,3) covering.
Only the forward implication from multiplicity two to complementary blocks
is used. No classification or finite covering search enters these proofs.
-/

namespace CoveringDesigns.C20_11_3

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {C : Family α} {p q : α} {B D : Finset α}

omit [Fintype α] in
/-- The two named, distinct blocks exhaust a pair-star of cardinality two. -/
theorem saturated_pair_star_eq
    (hsat : degree (star C p) q = 2)
    (hB : B ∈ star (star C p) q) (hD : D ∈ star (star C p) q)
    (hBD : B ≠ D) : star (star C p) q = {B, D} := by
  have hsub : ({B, D} : Finset (Finset α)) ⊆ star (star C p) q := by
    intro A hA
    rcases mem_insert.mp hA with rfl | hA
    · exact hB
    · have : A = D := mem_singleton.mp hA
      subst A
      exact hD
  apply (eq_of_subset_of_card_le hsub _).symm
  simpa only [show (star (star C p) q).card = 2 from hsat,
    card_pair hBD] using (le_refl 2)

/-- Coverage forces the union of the two blocks through a saturated pair. -/
theorem saturated_pair_union (hC : Covers C 3) (hpq : p ≠ q)
    (hstar : star (star C p) q = {B, D}) : B ∪ D = univ := by
  have hB : B ∈ star (star C p) q := by rw [hstar]; simp
  have hpB : p ∈ B := (mem_filter.mp (mem_filter.mp hB).1).2
  have hqB : q ∈ B := (mem_filter.mp hB).2
  apply eq_univ_of_forall
  intro z
  by_cases hzp : z = p
  · subst z
    exact mem_union_left _ hpB
  by_cases hzq : z = q
  · subst z
    exact mem_union_left _ hqB
  have hcard : ({p, q, z} : Finset α).card = 3 := by
    simp [hpq, Ne.symm hzp, Ne.symm hzq]
  obtain ⟨A, hAC, hT⟩ := hC {p, q, z} hcard
  have hA : A ∈ star (star C p) q := by
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hAC, hT (by simp)⟩, hT (by simp)⟩
  rw [hstar] at hA
  have hzA : z ∈ A := hT (by simp)
  rcases mem_insert.mp hA with rfl | hA
  · exact mem_union_left _ hzA
  · have : A = D := mem_singleton.mp hA
    subst A
    exact mem_union_right _ hzA

/-- On twenty points, the two size-eleven blocks intersect exactly in the
pair. This is not a converse to saturation. -/
theorem saturated_pair_inter (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q)
    (hstar : star (star C p) q = {B, D}) : B ∩ D = {p, q} := by
  have hB : B ∈ star (star C p) q := by rw [hstar]; simp
  have hD : D ∈ star (star C p) q := by rw [hstar]; simp
  have hBC : B ∈ C := (mem_filter.mp (mem_filter.mp hB).1).1
  have hDC : D ∈ C := (mem_filter.mp (mem_filter.mp hD).1).1
  have hpB : p ∈ B := (mem_filter.mp (mem_filter.mp hB).1).2
  have hpD : p ∈ D := (mem_filter.mp (mem_filter.mp hD).1).2
  have hqB : q ∈ B := (mem_filter.mp hB).2
  have hqD : q ∈ D := (mem_filter.mp hD).2
  have hsub : ({p, q} : Finset α) ⊆ B ∩ D := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_inter.mpr ⟨hpB, hpD⟩
    · have : x = q := mem_singleton.mp hx
      subst x
      exact mem_inter.mpr ⟨hqB, hqD⟩
  have hcount := card_union_add_card_inter B D
  rw [saturated_pair_union hC.2 hpq hstar, card_univ, hv,
    hC.1 B hBC, hC.1 D hDC] at hcount
  apply (eq_of_subset_of_card_le hsub _).symm
  rw [card_pair hpq]
  omega

/-- A saturated pair supplies two distinct actual covering blocks. -/
theorem saturated_pair_blocks (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2) :
    ∃ B ∈ C, ∃ D ∈ C, B ≠ D ∧ star (star C p) q = {B, D} ∧
      B ∪ D = univ ∧ B ∩ D = {p, q} := by
  obtain ⟨B, D, hBD, hstar⟩ := card_eq_two.mp hsat
  have hB : B ∈ star (star C p) q := by rw [hstar]; simp
  have hD : D ∈ star (star C p) q := by rw [hstar]; simp
  refine ⟨B, (mem_filter.mp (mem_filter.mp hB).1).1,
    D, (mem_filter.mp (mem_filter.mp hD).1).1, hBD, hstar,
    saturated_pair_union hC.2 hpq hstar, saturated_pair_inter hv hC hpq hstar⟩

/-- Geometry with two already named blocks, for later cross-pair counting. -/
theorem saturated_pair_geometry (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2)
    (hBC : B ∈ C) (hDC : D ∈ C) (hBD : B ≠ D)
    (hpB : p ∈ B) (hqB : q ∈ B) (hpD : p ∈ D) (hqD : q ∈ D) :
    B ∪ D = univ ∧ B ∩ D = {p, q} := by
  have hB : B ∈ star (star C p) q :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨hBC, hpB⟩, hqB⟩
  have hD : D ∈ star (star C p) q :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨hDC, hpD⟩, hqD⟩
  have hstar := saturated_pair_star_eq hsat hB hD hBD
  exact ⟨saturated_pair_union hC.2 hpq hstar,
    saturated_pair_inter hv hC hpq hstar⟩

/-- The partner of a specified containing block is another actual block. -/
theorem saturated_partner_of_mem (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2)
    (hBC : B ∈ C) (hpB : p ∈ B) (hqB : q ∈ B) :
    ∃ D ∈ C, D ≠ B ∧ B ∪ D = univ ∧ B ∩ D = {p, q} := by
  obtain ⟨U, hUC, V, hVC, hUV, hstar, hunion, hinter⟩ :=
    saturated_pair_blocks hv hC hpq hsat
  have hB : B ∈ star (star C p) q :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨hBC, hpB⟩, hqB⟩
  rw [hstar] at hB
  rcases mem_insert.mp hB with hBU | hBV
  · subst U
    exact ⟨V, hVC, Ne.symm hUV, hunion, hinter⟩
  · have hBV : B = V := mem_singleton.mp hBV
    subst V
    exact ⟨U, hUC, hUV, by simpa [union_comm] using hunion,
      by simpa [inter_comm] using hinter⟩

/-- The other block is forced by the union and intersection equations. -/
theorem other_block_eq_complement (hunion : B ∪ D = univ)
    (hinter : B ∩ D = {p, q}) : D = (univ \ B) ∪ {p, q} := by
  ext x
  constructor
  · intro hxD
    by_cases hxB : x ∈ B
    · apply mem_union_right
      rw [← hinter]
      exact mem_inter.mpr ⟨hxB, hxD⟩
    · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_univ _, hxB⟩)
  · intro hx
    rcases mem_union.mp hx with hx | hx
    · have hxU : x ∈ B ∪ D := by rw [hunion]; simp
      exact (mem_union.mp hxU).resolve_left (mem_sdiff.mp hx).2
    · rw [← hinter] at hx
      exact (mem_inter.mp hx).2

/-- Saturation and one containing block determine its unique actual partner
by a complement formula. -/
theorem saturated_partner_eq_complement (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2)
    (hBC : B ∈ C) (hpB : p ∈ B) (hqB : q ∈ B) :
    let D := (univ \ B) ∪ {p, q}
    D ∈ C ∧ D ≠ B ∧ B ∪ D = univ ∧ B ∩ D = {p, q} ∧
      ∀ E ∈ C, E ≠ B → p ∈ E → q ∈ E → E = D := by
  obtain ⟨D, hDC, hDB, hunion, hinter⟩ :=
    saturated_partner_of_mem hv hC hpq hsat hBC hpB hqB
  have hDformula := other_block_eq_complement hunion hinter
  dsimp only
  rw [← hDformula]
  refine ⟨hDC, hDB, hunion, hinter, ?_⟩
  intro E hEC hEB hpE hqE
  have hgeometry := saturated_pair_geometry hv hC hpq hsat hBC hEC
    (Ne.symm hEB) hpB hqB hpE hqE
  exact (other_block_eq_complement hgeometry.1 hgeometry.2).trans hDformula.symm

/-- Removing the saturated pair leaves two complementary nine-sets. -/
theorem saturated_residual_geometry (hpq : p ≠ q)
    (hBcard : B.card = 11) (hDcard : D.card = 11)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p, q}) :
    Disjoint (B \ {p, q}) (D \ {p, q}) ∧
      (B \ {p, q}).card = 9 ∧ (D \ {p, q}).card = 9 ∧
      (B \ {p, q}) ∪ (D \ {p, q}) = univ \ {p, q} := by
  have hpB : ({p, q} : Finset α) ⊆ B := by rw [← hinter]; exact inter_subset_left
  have hpD : ({p, q} : Finset α) ⊆ D := by rw [← hinter]; exact inter_subset_right
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro x hxB hxD
    have hx : x ∈ B ∩ D := mem_inter.mpr
      ⟨(mem_sdiff.mp hxB).1, (mem_sdiff.mp hxD).1⟩
    rw [hinter] at hx
    exact (mem_sdiff.mp hxB).2 hx
  · rw [card_sdiff_of_subset hpB, hBcard, card_pair hpq]
  · rw [card_sdiff_of_subset hpD, hDcard, card_pair hpq]
  · ext x
    have hxU : x ∈ B ∪ D := by rw [hunion]; simp
    simp only [mem_union, mem_sdiff, mem_univ, true_and]
    constructor
    · rintro (⟨_, hx⟩ | ⟨_, hx⟩) <;> exact hx
    · intro hx
      rcases mem_union.mp hxU with hxB | hxD
      · exact Or.inl ⟨hxB, hx⟩
      · exact Or.inr ⟨hxD, hx⟩

end CoveringDesigns.C20_11_3
