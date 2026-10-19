import CoveringDesigns.C20_11_3.Incidence
import CoveringDesigns.TwoKMinusTwo.Arithmetic

/-! Variable-parameter elementary pair-link floor. -/
namespace CoveringDesigns.TwoKMinusTwo
open Finset C20_11_3
variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

theorem cross_capacity (X Y B : Finset α) (hXY : Disjoint X Y)
    {m : ℕ} (hB : B.card ≤ m) : (X ∩ B).card * (Y ∩ B).card ≤ capacity m := by
  apply product_le_capacity
  have hd : Disjoint (X ∩ B) (Y ∩ B) :=
    hXY.mono inter_subset_left inter_subset_left
  rw [← card_union_of_disjoint hd]
  exact (card_le_card (union_subset inter_subset_right inter_subset_right)).trans hB

private theorem link_degree_ge_two {C : Family α} (hv : Fintype.card α = 2*k-3) (hk : 9 ≤ k)
    (hC : IsCover C (k-1) 2) (p : α) : 2 ≤ degree C p := by
  have hb := one_cover_bound (link_isCover (k := k-2)
    (by simpa [show k-2+1=k-1 by omega] using hC) p)
  rw [complement_point_card, hv, link_card] at hb
  have hsub : k-2+2=k := by omega
  have hpoints : 2*k-3-1+4=2*k := by omega
  by_contra hn
  have hm := Nat.mul_le_mul_left (k-2) (show degree C p ≤ 1 by omega)
  nlinarith

/-- The degree-two branch of the elementary pair-link obstruction. -/
private theorem link_degree_two_impossible {C : Family α}
    (hv : Fintype.card α = 2*k-3) (hk : 9 ≤ k) (hC : IsCover C (k-1) 2) (hb : C.card ≤ 5)
    {p : α} (hp : degree C p = 2) : False := by
  obtain ⟨A, B, hAB, hs⟩ := card_eq_two.mp hp
  have hAstar : A ∈ star C p := by rw [hs]; simp
  have hBstar : B ∈ star C p := by rw [hs]; simp
  obtain ⟨hAC, hpA⟩ := mem_filter.mp hAstar
  obtain ⟨hBC, hpB⟩ := mem_filter.mp hBstar
  have hAc := hC.1 A hAC
  have hBc := hC.1 B hBC
  have hU : A ∪ B = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hzp : z = p
    · subst z
      exact mem_union_left _ hpA
    · obtain ⟨D, hDC, hpz⟩ := hC.2 {p, z} (card_pair (Ne.symm hzp))
      have hDs : D ∈ star C p := mem_filter.mpr ⟨hDC, hpz (by simp)⟩
      have hzD : z ∈ D := hpz (by simp)
      rw [hs] at hDs
      rcases mem_insert.mp hDs with hDA | hDB
      · exact mem_union_left _ (hDA ▸ hzD)
      · exact mem_union_right _ ((mem_singleton.mp hDB) ▸ hzD)
  have hIc : (A ∩ B).card = 1 := by
    have hi := card_union_add_card_inter A B
    rw [hU, card_univ, hv, hAc, hBc] at hi
    omega
  have hI : A ∩ B = {p} := by
    symm
    apply eq_of_subset_of_card_le
    · exact singleton_subset_iff.mpr (mem_inter.mpr ⟨hpA, hpB⟩)
    · simp [hIc]
  let X := A.erase p
  let Y := B.erase p
  have hX : X.card = k-2 := by simp [X, card_erase_of_mem hpA, hAc, Nat.sub_sub]
  have hY : Y.card = k-2 := by simp [Y, card_erase_of_mem hpB, hBc, Nat.sub_sub]
  have hXY : Disjoint X Y := by
    apply disjoint_left.mpr
    intro z hzX hzY
    have hzI : z ∈ A ∩ B :=
      mem_inter.mpr ⟨(mem_erase.mp hzX).2, (mem_erase.mp hzY).2⟩
    rw [hI] at hzI
    exact (mem_erase.mp hzX).1 (mem_singleton.mp hzI)
  have hnotA {y : α} (hy : y ∈ Y) : y ∉ A := by
    intro hyA
    have hyI := mem_inter.mpr ⟨hyA, (mem_erase.mp hy).2⟩
    rw [hI] at hyI
    exact (mem_erase.mp hy).1 (mem_singleton.mp hyI)
  have hnotB {x : α} (hx : x ∈ X) : x ∉ B := by
    intro hxB
    have hxI := mem_inter.mpr ⟨(mem_erase.mp hx).2, hxB⟩
    rw [hI] at hxI
    exact (mem_erase.mp hx).1 (mem_singleton.mp hxI)
  let D := C \ {A, B}
  have hDcard : D.card ≤ 3 := by
    have hsub : ({A, B} : Family α) ⊆ C := by
      intro E hE
      rcases mem_insert.mp hE with rfl | hE
      · exact hAC
      · simpa only [mem_singleton.mp hE] using hBC
    have he := card_sdiff_add_card_eq_card hsub
    have htwo : ({A, B} : Family α).card = 2 := by simp [hAB]
    change D.card + ({A, B} : Family α).card = C.card at he
    rw [htwo] at he
    omega
  have hcover : ∀ x ∈ X, ∀ y ∈ Y, ∃ E ∈ D, x ∈ E ∧ y ∈ E := by
    intro x hx y hy
    have hxy : x ≠ y := by
      intro he
      subst y
      exact (disjoint_left.mp hXY) hx hy
    obtain ⟨E, hEC, hxyE⟩ := hC.2 {x, y} (by simp [hxy])
    have hxE : x ∈ E := hxyE (by simp)
    have hyE : y ∈ E := hxyE (by simp)
    have hEA : E ≠ A := by intro he; exact hnotA hy (he ▸ hyE)
    have hEB : E ≠ B := by intro he; exact hnotB hx (he ▸ hxE)
    exact ⟨E, mem_sdiff.mpr ⟨hEC, by simp [hEA, hEB]⟩, hxE, hyE⟩
  have hcapacity : (∑ E ∈ D, (X ∩ E).card * (Y ∩ E).card) ≤ capacity (k-1) * D.card := by
    calc
      _ ≤ ∑ _E ∈ D, capacity (k-1) := by
        apply sum_le_sum
        intro E hE
        exact cross_capacity X Y E hXY (by
          rw [hC.1 E (mem_sdiff.mp hE).1])
      _ = _ := by simp [Nat.mul_comm]
  have hbound := cross_pair_coverage_bound hcover
  rw [hX, hY] at hbound
  have hcap := Nat.mul_le_mul_left (capacity (k-1)) hDcard
  have hstrict := link_capacity_strict hk
  nlinarith

/-- Every ordinary pair-cover of 2k-3 points by (k-1)-point blocks needs six blocks. -/
theorem link_lower_bound {C : Family α} (hv : Fintype.card α = 2*k-3) (hk : 9 ≤ k)
    (hC : IsCover C (k-1) 2) : 6 ≤ C.card := by
  by_contra hsmall
  have hb : C.card ≤ 5 := by omega
  have hdeg (p : α) : 3 ≤ degree C p := by
    have hl := link_degree_ge_two hv hk hC p
    by_contra hh
    exact link_degree_two_impossible hv hk hC hb (p := p) (by omega)
  have hi := incidence_lower_bound hC.1 hdeg
  rw [hv] at hi
  have hh := Nat.mul_le_mul_left (k-1) hb
  have hs : k-1+1=k := by omega
  have ht : 2*k-3+3=2*k := by omega
  nlinarith

/-- The elementary pair-link bound applied to each actual point link. -/
theorem degree_ge_six {C : Family α} (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k)
    (hC : IsCover C k 3) (p : α) : 6 ≤ degree C p := by
  have hl := link_lower_bound
    (by rw [complement_point_card, hv]; omega : Fintype.card {q : α // q ≠ p} = 2*k-3)
    hk (link_isCover (k := k-1) (by simpa [Nat.sub_add_cancel (show 1 ≤ k by omega)] using hC) p)
  simpa only [link_card] using hl


theorem pair_ge_two {C : Family α} (hv : Fintype.card α = 2*k-2)
    (hk : 3 ≤ k) (hC : IsCover C k 3) {p q : α} (hpq : p ≠ q) :
    2 ≤ degree (star C p) q := by
  let q' : {q : α // q ≠ p} := ⟨q, hpq.symm⟩
  have hc : IsCover C (k-2+1+1) 3 := by
    simpa [show k-2+1+1=k by omega] using hC
  have hl := one_cover_bound (link_isCover (link_isCover hc p) q')
  rw [complement_point_card, complement_point_card, hv, link_card, degree_link] at hl
  have hs : k-2+2=k := by omega
  have ht : 2*k-2-1-1+4=2*k := by omega
  by_contra hn
  have hm := Nat.mul_le_mul_left (k-2) (show degree (star C p) q ≤ 1 by omega)
  nlinarith

end CoveringDesigns.TwoKMinusTwo
