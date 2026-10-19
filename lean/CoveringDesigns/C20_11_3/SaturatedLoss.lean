import CoveringDesigns.C20_11_3.SaturatedGeometry
import CoveringDesigns.C20_11_3.SaturatedPartition

/-!
A second saturated partner of the degree-six endpoint forces an actual
endpoint-only block with traces one and nine. This is the geometric source
of the sixteen-unit capacity loss, without an assumed trace configuration.
-/

namespace CoveringDesigns.C20_11_3

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {C : Family α} {p q z : α} {B D : Finset α}

/-- Removing one of the two endpoint blocks leaves the other residual side. -/
theorem saturated_residual_complement (hunion : B ∪ D = univ)
    (hinter : B ∩ D = {p, q}) : univ \ B = D \ {p, q} := by
  ext x
  simp only [mem_sdiff, mem_univ, true_and]
  constructor
  · intro hxB
    have hxU : x ∈ B ∪ D := by rw [hunion]; simp
    refine ⟨(mem_union.mp hxU).resolve_left hxB, ?_⟩
    intro hxpair
    rw [← hinter] at hxpair
    exact hxB (mem_inter.mp hxpair).1
  · rintro ⟨hxD, hxpair⟩ hxB
    apply hxpair
    rw [← hinter]
    exact mem_inter.mpr ⟨hxB, hxD⟩

/-- On the first residual side, saturation with q forces traces one and nine
in an actual block containing q and omitting p. -/
theorem second_partner_traces_left (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q) (hBC : B ∈ C) (hDC : D ∈ C)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p, q})
    (hz : z ∈ B \ {p, q}) (hsat : degree (star C q) z = 2) :
    ∃ E ∈ onlyBlocks C q p,
      ((B \ {p, q}) ∩ E).card = 1 ∧ ((D \ {p, q}) ∩ E).card = 9 := by
  have hzB := (mem_sdiff.mp hz).1
  have hzpair := (mem_sdiff.mp hz).2
  have hzq : z ≠ q := by intro h; exact hzpair (by simp [h])
  have hzp : z ≠ p := by intro h; exact hzpair (by simp [h])
  have hqB : q ∈ B := by
    have hq : q ∈ B ∩ D := by rw [hinter]; simp
    exact (mem_inter.mp hq).1
  obtain ⟨E, hEC, _, hBEunion, hBEinter⟩ :=
    saturated_partner_of_mem hv hC (Ne.symm hzq) hsat hBC hqB hzB
  have hE : E = (D \ {p, q}) ∪ {q, z} := by
    rw [other_block_eq_complement hBEunion hBEinter,
      saturated_residual_complement hunion hinter]
  have hqE : q ∈ E := by rw [hE]; simp
  have hpE : p ∉ E := by rw [hE]; simp [hpq, Ne.symm hzp]
  have hgeo := saturated_residual_geometry hpq (hC.1 B hBC) (hC.1 D hDC)
    hunion hinter
  have hleft : (B \ {p, q}) ∩ E = {z} := by
    ext x
    simp only [mem_inter, mem_singleton]
    constructor
    · rintro ⟨hxB, hxE⟩
      rw [hE] at hxE
      rcases mem_union.mp hxE with hxD | hxqz
      · exact (disjoint_left.mp hgeo.1 hxB hxD).elim
      · rcases mem_insert.mp hxqz with hxq | hxz
        · subst x
          exact ((mem_sdiff.mp hxB).2 (by simp)).elim
        · exact mem_singleton.mp hxz
    · intro hxz
      subst x
      exact ⟨hz, by rw [hE]; simp⟩
  have hright : (D \ {p, q}) ∩ E = D \ {p, q} := by
    apply inter_eq_left.mpr
    intro x hx
    rw [hE]
    exact mem_union_left _ hx
  refine ⟨E, mem_onlyBlocks.mpr ⟨hEC, hqE, hpE⟩, ?_, ?_⟩
  · rw [hleft, card_singleton]
  · rw [hright]
    exact hgeo.2.2.1

/-- Either residual location of a second saturated partner forces a trace
product of nine in the same actual q-only block family. -/
theorem second_partner_trace (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hpq : p ≠ q) (hBC : B ∈ C) (hDC : D ∈ C)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p, q})
    (hz : z ∈ (B \ {p, q}) ∪ (D \ {p, q}))
    (hsat : degree (star C q) z = 2) :
    ∃ E ∈ onlyBlocks C q p,
      ((B \ {p, q}) ∩ E).card * ((D \ {p, q}) ∩ E).card = 9 := by
  rcases mem_union.mp hz with hzB | hzD
  · obtain ⟨E, hE, hleft, hright⟩ :=
      second_partner_traces_left hv hC hpq hBC hDC hunion hinter hzB hsat
    exact ⟨E, hE, by rw [hleft, hright]⟩
  · obtain ⟨E, hE, hleft, hright⟩ := second_partner_traces_left hv hC hpq hDC hBC
      (by simpa [union_comm] using hunion)
      (by simpa [inter_comm] using hinter) hzD hsat
    exact ⟨E, hE, by rw [hleft, hright]⟩

end CoveringDesigns.C20_11_3
