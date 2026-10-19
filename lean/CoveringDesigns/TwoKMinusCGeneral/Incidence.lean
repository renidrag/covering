import CoveringDesigns.C20_11_3.Incidence
import CoveringDesigns.TwoKMinusTwo.Incidence
import CoveringDesigns.TwoKMinusCGeneral.Arithmetic

/-! Variable-parameter elementary pair-link floor. -/
namespace CoveringDesigns.TwoKMinusCGeneral
open Finset C20_11_3 TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α] {c k : ℕ}

private theorem link_degree_ge_two {C : Family α} (hv : Fintype.card α+c+1=2*k) (hc : 2 ≤ c) (hk : 8*c ≤ k+7)
    (hC : IsCover C (k-1) 2) (p : α) : 2 ≤ degree C p := by
  have hb := one_cover_bound (link_isCover (k := k-2)
    (by simpa [show k-2+1=k-1 by omega] using hC) p)
  rw [complement_point_card, link_card] at hb
  have hsub : k-2+2=k := by omega
  have hpoints : Fintype.card α-1+c+2=2*k := by omega
  by_contra hn
  have hm := Nat.mul_le_mul_left (k-2) (show degree C p ≤ 1 by omega)
  nlinarith

/-- The degree-two branch of the elementary pair-link obstruction. -/
private theorem link_degree_two_impossible {C : Family α}
    (hv : Fintype.card α+c+1=2*k) (hc : 2 ≤ c) (hk : 8*c ≤ k+7) (hC : IsCover C (k-1) 2) (hb : C.card ≤ 5)
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
  have hIc : (A ∩ B).card = c-1 := by
    have hi := card_union_add_card_inter A B
    rw [hU, card_univ, hAc, hBc] at hi
    omega
  let X := A \ B
  let Y := B \ A
  have hX : X.card = k-c := by
    have he := card_sdiff_add_card_inter A B
    rw [hIc, hAc] at he
    change X.card + (c-1) = k-1 at he
    omega
  have hY : Y.card = k-c := by
    have he := card_sdiff_add_card_inter B A
    rw [inter_comm B A, hIc, hBc] at he
    change Y.card + (c-1) = k-1 at he
    omega
  have hXY : Disjoint X Y := by
    apply disjoint_left.mpr
    intro z hzX hzY
    exact (mem_sdiff.mp hzX).2 (mem_sdiff.mp hzY).1
  have hnotA {y : α} (hy : y ∈ Y) : y ∉ A := (mem_sdiff.mp hy).2
  have hnotB {x : α} (hx : x ∈ X) : x ∉ B := (mem_sdiff.mp hx).2
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
  have hstrict := TwoKMinusCGeneral.link_capacity_strict hc hk
  nlinarith

/-- General pair-link floor, including its degree-two alternative. -/
theorem link_lower_bound {C : Family α} (hv : Fintype.card α+c+1=2*k) (hc : 2 ≤ c) (hk : 8*c ≤ k+7)
    (hC : IsCover C (k-1) 2) : 6 ≤ C.card := by
  by_contra hsmall
  have hb : C.card ≤ 5 := by omega
  have hdeg (p : α) : 3 ≤ degree C p := by
    have hl := link_degree_ge_two hv hc hk hC p
    by_contra hh
    exact link_degree_two_impossible hv hc hk hC hb (p := p) (by omega)
  have hi := incidence_lower_bound hC.1 hdeg
  have hh := Nat.mul_le_mul_left (k-1) hb
  have hs : k-1+1=k := by omega
  have ht : Fintype.card α+c+1=2*k := hv
  nlinarith

/-- Six actual blocks through every point under the sufficient link threshold. -/
theorem degree_ge_six {C : Family α} (hv : Fintype.card α+c=2*k)
    (hc : 2 ≤ c) (hk : 8*c ≤ k+7) (hC : IsCover C k 3) (p : α) :
    6 ≤ degree C p := by
  have hl := link_lower_bound
    (by rw [complement_point_card]; omega : Fintype.card {q : α // q ≠ p}+c+1=2*k)
    hc hk (link_isCover (k := k-1)
      (by simpa [Nat.sub_add_cancel (show 1 ≤ k by omega)] using hC) p)
  simpa only [link_card] using hl

/-- Pair floor from the ordinary double link; no small-family assumption. -/
theorem pair_ge_two {C : Family α} (hv : Fintype.card α+c=2*k)
    (hc : 2 ≤ c) (hck : c<k) (hC : IsCover C k 3) {p q : α} (hpq : p ≠ q) :
    2 ≤ degree (star C p) q := by
  let q' : {q : α // q ≠ p} := ⟨q, hpq.symm⟩
  have hC' : IsCover C (k-2+1+1) 3 := by
    simpa [show k-2+1+1=k by omega] using hC
  have hl := one_cover_bound (link_isCover (link_isCover hC' p) q')
  rw [complement_point_card, complement_point_card, link_card, degree_link] at hl
  have hs : k-2+2=k := by omega
  have ht : Fintype.card α-1-1+c+2=2*k := by omega
  by_contra hn
  have hm := Nat.mul_le_mul_left (k-2) (show degree (star C p) q ≤ 1 by omega)
  nlinarith

end CoveringDesigns.TwoKMinusCGeneral
