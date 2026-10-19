import CoveringDesigns.Foundations.Bounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod

/-!
The elementary incidence part of the proof of `C(20,11,3) = 12`.

The six-block bound for `(19,10,2)` is proved directly: a degree-two point
splits the other points into two nine-sets, whose 81 cross-pairs cannot be
covered by three ten-point blocks. No other numerical covering result or
classification is imported.
-/

namespace CoveringDesigns.C20_11_3

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Pair multiplicity counts actual ordinary blocks containing both points. -/
abbrev pairDegree (C : Family α) (p q : α) : ℕ := degree (star C p) q

/-- Counting companions in all blocks through one point. -/
theorem pair_sum {C : Family α} {k : ℕ} (hu : Uniform C k) (p : α) :
    (∑ q ∈ univ.erase p, degree (star C p) q) = (k - 1) * degree C p := by
  have hstar : Uniform (star C p) k := fun B hB => hu B (mem_filter.mp hB).1
  have hs := degree_sum_of_uniform hstar
  have hself : degree (star C p) p = degree C p := by
    simp [degree, star, filter_filter]
  have he := sum_erase_add (univ : Finset α) (fun q => degree (star C p) q)
    (mem_univ p)
  change (∑ q, degree (star C p) q) = k * degree C p at hs
  rw [hself, hs] at he
  rw [Nat.sub_mul, one_mul]
  omega

/-- The same companion count indexed by the point-complement subtype. -/
theorem pair_sum_subtype {C : Family α} {k : ℕ} (hu : Uniform C k) (p : α) :
    (∑ q : {q : α // q ≠ p}, degree (star C p) q.val) =
      (k - 1) * degree C p := by
  rw [← pair_sum hu p]
  apply sum_bij (fun q _ => q.val)
  · intro q _
    exact mem_erase.mpr ⟨q.property, mem_univ _⟩
  · intro q _ r _ hqr
    exact Subtype.ext hqr
  · intro q hq
    exact ⟨⟨q, (mem_erase.mp hq).1⟩, mem_univ _, rfl⟩
  · intro q _
    rfl

/-- Exchanging the cross-pair and actual-block sums. -/
theorem cross_pair_degree_sum (C : Family α) (X Y : Finset α) :
    (∑ x ∈ X, ∑ y ∈ Y, degree (star C x) y) =
      ∑ B ∈ C, (X ∩ B).card * (Y ∩ B).card := by
  have hp (x y : α) : degree (star C x) y =
      ∑ B ∈ C, if x ∈ B ∧ y ∈ B then 1 else 0 := by
    simp only [degree, star, card_eq_sum_ones, sum_filter]
    apply sum_congr rfl
    intro B _
    split_ifs <;> simp_all
  simp_rw [hp]
  simp_rw [sum_comm (s := Y) (t := C)]
  rw [sum_comm]
  apply sum_congr rfl
  intro B hB
  have hi (T : Finset α) : (T ∩ B).card = ∑ x ∈ T, if x ∈ B then 1 else 0 := by
    have he : T ∩ B = T.filter (· ∈ B) := by ext; simp
    rw [he, card_eq_sum_ones, sum_filter]
  rw [hi X, hi Y, sum_mul]
  apply sum_congr rfl
  intro x hx
  rw [mul_sum]
  apply sum_congr rfl
  intro y hy
  split_ifs <;> simp_all

/-- A union bound on capacities for any supplied cover of a rectangle. -/
theorem cross_pair_coverage_bound {C : Family α} {X Y : Finset α}
    (hcover : ∀ x ∈ X, ∀ y ∈ Y, ∃ B ∈ C, x ∈ B ∧ y ∈ B) :
    X.card * Y.card ≤ ∑ B ∈ C, (X ∩ B).card * (Y ∩ B).card := by
  have hs : X ×ˢ Y ⊆ C.biUnion (fun B => (X ∩ B) ×ˢ (Y ∩ B)) := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    obtain ⟨B, hB, hxb, hyb⟩ := hcover x hx y hy
    exact mem_biUnion.mpr ⟨B, hB,
      mem_product.mpr ⟨mem_inter.mpr ⟨hx, hxb⟩, mem_inter.mpr ⟨hy, hyb⟩⟩⟩
  have hb := (card_le_card hs).trans card_biUnion_le
  simpa only [card_product] using hb

/-- Elementary integer capacity of a ten-point block crossing two sides. -/
theorem mul_le_twenty_five {a b : ℕ} (h : a + b ≤ 10) : a * b ≤ 25 := by
  have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
      a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 := by omega
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega

/-- A ten-point block supplies at most 25 cross-pairs between disjoint sides. -/
theorem cross_capacity_ten (X Y B : Finset α) (hXY : Disjoint X Y)
    (hB : B.card ≤ 10) : (X ∩ B).card * (Y ∩ B).card ≤ 25 := by
  apply mul_le_twenty_five
  have hd : Disjoint (X ∩ B) (Y ∩ B) :=
    hXY.mono inter_subset_left inter_subset_left
  rw [← card_union_of_disjoint hd]
  exact (card_le_card (union_subset inter_subset_right inter_subset_right)).trans hB

private theorem degree_ge_two_19 {C : Family α} (hv : Fintype.card α = 19)
    (hC : IsCover C 10 2) (p : α) : 2 ≤ degree C p := by
  have hb := one_cover_bound (link_isCover hC p)
  rw [complement_point_card, hv, link_card] at hb
  omega

/-- The degree-two branch of the elementary `(19,10,2)` obstruction. -/
private theorem degree_two_19_impossible {C : Family α}
    (hv : Fintype.card α = 19) (hC : IsCover C 10 2) (hb : C.card ≤ 5)
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
  have hX : X.card = 9 := by simp [X, card_erase_of_mem hpA, hAc]
  have hY : Y.card = 9 := by simp [Y, card_erase_of_mem hpB, hBc]
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
  have hcapacity : (∑ E ∈ D, (X ∩ E).card * (Y ∩ E).card) ≤ 25 * D.card := by
    calc
      _ ≤ ∑ _E ∈ D, 25 := by
        apply sum_le_sum
        intro E hE
        exact cross_capacity_ten X Y E hXY (by
          rw [hC.1 E (mem_sdiff.mp hE).1])
      _ = _ := by simp [Nat.mul_comm]
  have hbound := cross_pair_coverage_bound hcover
  rw [hX, hY] at hbound
  omega

/-- Every ordinary pair-cover of nineteen points by ten-point blocks needs six blocks. -/
theorem lower_bound_19_10_2 {C : Family α} (hv : Fintype.card α = 19)
    (hC : IsCover C 10 2) : 6 ≤ C.card := by
  by_contra hsmall
  have hb : C.card ≤ 5 := by omega
  have hdeg (p : α) : 3 ≤ degree C p := by
    have hl := degree_ge_two_19 hv hC p
    by_contra hh
    exact degree_two_19_impossible hv hC hb (p := p) (by omega)
  have hi := incidence_lower_bound hC.1 hdeg
  rw [hv] at hi
  omega

/-- The elementary nineteen-point bound applied to each actual point link. -/
theorem degree_ge_six {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (p : α) : 6 ≤ degree C p := by
  have hl := lower_bound_19_10_2
    (by rw [complement_point_card, hv] : Fintype.card {q : α // q ≠ p} = 19)
    (link_isCover hC p)
  simpa only [link_card] using hl

/-- The incidence total already excludes ten or fewer blocks. -/
theorem eleven_le_card {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) : 11 ≤ C.card := by
  have hi := incidence_lower_bound hC.1 (degree_ge_six hv hC)
  rw [hv] at hi
  omega

/-- Eleven blocks leave one incidence above the pointwise degree-six floor. -/
theorem degree_excess_sum {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hb : C.card = 11) :
    (∑ p, (degree C p - 6)) = 1 := by
  have hs := degree_sum_of_uniform hC.1
  rw [hb] at hs
  have he : (∑ p, (degree C p - 6)) + 120 = 121 := by
    calc
      _ = ∑ p, ((degree C p - 6) + 6) := by simp [sum_add_distrib, hv]
      _ = ∑ p, degree C p := sum_congr rfl fun p _ =>
        Nat.sub_add_cancel (degree_ge_six hv hC p)
      _ = _ := hs
  omega

/-- Every point has degree six or seven when the family has eleven blocks. -/
theorem degree_six_or_seven {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hb : C.card = 11) (p : α) :
    degree C p = 6 ∨ degree C p = 7 := by
  have hl := degree_ge_six hv hC p
  have hu : degree C p - 6 ≤ ∑ q, (degree C q - 6) :=
    single_le_sum (f := fun q => degree C q - 6)
      (fun _ _ => Nat.zero_le _) (mem_univ p)
  rw [degree_excess_sum hv hC hb] at hu
  omega

/-- There is a unique high point: its degree is seven, and every other degree is six. -/
theorem degree_profile {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) (hb : C.card = 11) :
    ∃ h, degree C h = 7 ∧ ∀ x, x ≠ h → degree C x = 6 := by
  have hex : ∃ h, degree C h = 7 := by
    by_contra hno
    have hall (p : α) : degree C p = 6 := by
      rcases degree_six_or_seven hv hC hb p with h | h
      · exact h
      · exact False.elim (hno ⟨p, h⟩)
    have he := degree_excess_sum hv hC hb
    simp [hall] at he
  obtain ⟨h, hh⟩ := hex
  refine ⟨h, hh, ?_⟩
  intro x hxh
  have hu : (∑ p ∈ ({x, h} : Finset α), (degree C p - 6)) ≤
      ∑ p, (degree C p - 6) := sum_le_sum_of_subset (subset_univ _)
  simp [hxh, hh, degree_excess_sum hv hC hb] at hu
  have hl := degree_ge_six hv hC x
  omega

/-- Covering all eighteen third points requires at least two blocks through a pair. -/
theorem pair_ge_two {C : Family α} (hv : Fintype.card α = 20)
    (hC : IsCover C 11 3) {p q : α} (hpq : p ≠ q) :
    2 ≤ degree (star C p) q := by
  let q' : {q : α // q ≠ p} := ⟨q, hpq.symm⟩
  have hl := one_cover_bound (link_isCover (link_isCover hC p) q')
  rw [complement_point_card, complement_point_card, hv, link_card, degree_link] at hl
  change 20 - 1 - 1 ≤ 9 * degree (star C p) q at hl
  omega

end CoveringDesigns.C20_11_3
