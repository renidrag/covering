import CoveringDesigns.C13_7_4.Structural.Basic
import CoveringDesigns.C13_7_4.Structural.GPPTGeometry

/-! A pair of minimum points cannot have multiplicity ten.
The exceptional GPPT pair propagates to the other root; every point outside
the resulting triple would then violate GPPT's minimum-pair theorem. -/

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem exceptional_at_degree_ten {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    {p q : α} (hp : degree C p = 15) (hpq : p ≠ q)
    (hd : degree (star C p) q = 10) : Nonempty (ExceptionalGeometry (link C p)) := by
  rcases minimum_geometry
      (by rw [complement_point_card, hn] : Fintype.card {x : α // x ≠ p} = 12)
      (link_isCover hC p) (by rw [link_card, hp]) with ho | he
  · obtain ⟨G⟩ := ho
    have hbound := G.degree_le_nine ⟨q, hpq.symm⟩
    rw [degree_link, hd] at hbound
    omega
  · exact he

omit [Fintype α] in
private theorem exceptional_high_pair_degree {D : Family α}
    (G : ExceptionalGeometry D) {p q : α} (hp : p ∈ G.high) (hq : q ∈ G.high) :
    degree (star D p) q = 10 := by
  have he : star (star D p) q = star D p := by
    ext A
    simp only [star, mem_filter]
    constructor
    · rintro ⟨h, _⟩
      exact h
    · rintro ⟨hA, hpA⟩
      exact ⟨⟨hA, hpA⟩, G.high_columns A hA p hp hpA hq⟩
  change (star (star D p) q).card = 10
  rw [he]
  exact G.degree_high p hp

/-- Multiplicity ten between two degree-fifteen points is impossible in a
cover with at most twenty-nine blocks. -/
theorem minimum_pair_ne_ten {C : Family α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) (hb : C.card ≤ 29)
    {p q : α} (hp : degree C p = 15) (hq : degree C q = 15) (hpq : p ≠ q) :
    degree (star C p) q ≠ 10 := by
  intro hten
  obtain ⟨Gp⟩ := exceptional_at_degree_ten hn hC hp hpq hten
  obtain ⟨Gq⟩ := exceptional_at_degree_ten hn hC hq hpq.symm
    (by rwa [pair_degree_comm])
  let q' : {x : α // x ≠ p} := ⟨q, hpq.symm⟩
  let p' : {x : α // x ≠ q} := ⟨p, hpq⟩
  have hqH : q' ∈ Gp.high := (Gp.degree_eq_ten_iff q').mp (by rwa [degree_link])
  have hpH : p' ∈ Gq.high := (Gq.degree_eq_ten_iff p').mp (by
    rw [degree_link, pair_degree_comm]
    exact hten)
  obtain ⟨r', hrH, hrne⟩ := exists_mem_ne (by rw [Gp.high_card]; decide) q'
  have hrp : r'.val ≠ p := r'.property
  have hrq : r'.val ≠ q := fun h => hrne (Subtype.ext h)
  let r'' : {x : α // x ≠ q} := ⟨r'.val, hrq⟩
  have hGp : Gp.high = {q', r'} := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hqH
      · exact mem_singleton.mp hx ▸ hrH
    · rw [Gp.high_card, card_pair hrne.symm]
  have htriple : containmentCount C {p, q, r'.val} = 10 := by
    have h := exceptional_high_pair_degree Gp hqH hrH
    rw [← containmentCount_pair, containmentCount_link] at h
    simpa [q'] using h
  have hQr : degree (star (link C q) p') r'' = 10 := by
    rw [← containmentCount_pair, containmentCount_link]
    simpa [p', r'', insert_comm] using htriple
  have hrHq : r'' ∈ Gq.high := by
    by_contra hr
    have hh := Gq.high_low p' hpH r'' hr
    omega
  have hGq : Gq.high = {p', r''} := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hpH
      · exact mem_singleton.mp hx ▸ hrHq
    · rw [Gq.high_card, card_pair (show p' ≠ r'' from fun h =>
        hrp (congrArg Subtype.val h).symm)]
  have hminsub : minimumPoints C 15 ⊆ {p, q, r'.val} := by
    intro x hx
    by_contra hout
    have hxmin : degree C x = 15 := (mem_filter.mp hx).2
    have hxp : x ≠ p := fun h => hout (mem_insert.mpr (Or.inl h))
    have hxq : x ≠ q := fun h => hout (mem_insert_of_mem (mem_insert.mpr (Or.inl h)))
    have hxr : x ≠ r'.val := fun h => hout (mem_insert_of_mem
      (mem_insert_of_mem (mem_singleton.mpr h)))
    let xp : {y : α // y ≠ p} := ⟨x, hxp⟩
    let xq : {y : α // y ≠ q} := ⟨x, hxq⟩
    have hxpH : xp ∉ Gp.high := by
      rw [hGp]
      simp only [mem_insert, mem_singleton]
      rintro (h | h)
      · exact hxq (congrArg Subtype.val h)
      · exact hxr (congrArg Subtype.val h)
    have hxqH : xq ∉ Gq.high := by
      rw [hGq]
      simp only [mem_insert, mem_singleton]
      rintro (h | h)
      · exact hxp (congrArg Subtype.val h)
      · exact hxr (congrArg Subtype.val h)
    have hpx : degree (star C p) x = 7 := by
      have h := Gp.degree_low xp hxpH
      rwa [degree_link] at h
    have hqx : degree (star C q) x = 7 := by
      have h := Gq.degree_low xq hxqH
      rwa [degree_link] at h
    have hfour : containmentCount C {p, q, x} = 4 := by
      have h := Gp.high_low q' hqH xp hxpH
      rw [← containmentCount_pair, containmentCount_link] at h
      simpa [q', xp] using h
    have hthree := minimum_triple_count hn hC hxmin hxp hxq hpq
      (by rwa [pair_degree_comm]) (by rwa [pair_degree_comm])
    have hthree' : containmentCount C {p, q, x} = 3 := by
      have he : ({x, p, q} : Finset α) = {p, q, x} := by
        ext z
        simp [or_left_comm, or_comm]
      rwa [he] at hthree
    omega
  have hmany := five_minimum_points hn hC hb
  have hfew := card_le_card hminsub
  have hsmall : ({p, q, r'.val} : Finset α).card = 3 := by
    simp [hpq, hrp.symm, hrq.symm]
  omega

#guard_standard_axioms minimum_pair_ne_ten

end CoveringDesigns.C13Structural
