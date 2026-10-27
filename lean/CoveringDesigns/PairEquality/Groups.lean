import CoveringDesigns.PairEquality.Basic

/-! The star-complement groups in Füredi's equality argument. -/

namespace CoveringDesigns.PairEquality
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace Internal

/-- The star complement includes its centre and excludes its other neighbours. -/
def starGroup (H : Finset (Finset I)) (x : I) : Finset I :=
  univ.filter (fun y => y = x ∨ codegree H x y = 0)

@[simp] theorem mem_starGroup {H : Finset (Finset I)} {x y : I} :
    y ∈ starGroup H x ↔ y = x ∨ codegree H x y = 0 := by simp [starGroup]

private theorem codegree_self (H : Finset (Finset I)) (x : I) :
    codegree H x x = degree H x := by simp [codegree,degree]

private theorem codegree_zero {H : Finset (Finset I)} {x y : I} :
    codegree H x y = 0 ↔ ∀ E ∈ H, x ∈ E → y ∉ E := by
  simp [codegree,card_eq_zero,filter_eq_empty_iff]

private theorem pair_count (H : Finset (Finset I)) (S : Finset I) (x : I) :
    (∑ y ∈ S, codegree H x y) =
      ∑ E ∈ H.filter (x ∈ ·), (S ∩ E).card := by
  simp only [codegree,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro E hE
  by_cases hx : x ∈ E
  · simp [hx, ← sum_filter, filter_mem_eq_inter]
  · simp [hx]

variable {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ}
variable (h : PositiveUnitLoads q H w)
include h

private theorem thin_star {x y : I} (hx : degree H x = q) (hxy : x ≠ y) :
    codegree H x y ≤ 1 := by
  apply card_le_one.mpr
  intro E hE F hF
  obtain ⟨hE,hxE,hyE⟩ := mem_filter.mp hE
  obtain ⟨hF,hxF,hyF⟩ := mem_filter.mp hF
  by_contra hEF
  have hi := h.saturated_intersection hE (h.saturated_of_degree hx hE hxE) hF hEF
  exact hxy (card_le_one.mp hi.le x (mem_inter.mpr ⟨hxE,hxF⟩)
    y (mem_inter.mpr ⟨hyE,hyF⟩))

private theorem pair_split {x : I} (hx : degree H x = q) (S : Finset I) :
    (∑ y ∈ S, codegree H x y) =
      (S \ starGroup H x).card + if x ∈ S then q else 0 := by
  have term (y : I) : codegree H x y =
      (if y ∉ starGroup H x then 1 else 0) + if y = x then q else 0 := by
    by_cases he : y = x
    · subst y
      simp [codegree_self,hx]
    · have hc := (thin_star h) hx (Ne.symm he)
      by_cases hz : codegree H x y = 0 <;> simp [he,hz] <;> omega
  simp_rw [term]
  rw [sum_add_distrib]
  have hs : (∑ y ∈ S, if y ∉ starGroup H x then 1 else 0) =
      (S \ starGroup H x).card := by
    rw [← sum_filter, ← card_eq_sum_ones]
    congr 1
    ext y
    simp
  rw [hs,sum_ite_eq']

theorem starGroup_card {x : I} (hx : degree H x = q) : (starGroup H x).card = q := by
  have he := pair_count H univ x
  rw [(pair_split h) hx] at he
  simp only [mem_univ,ite_true,univ_inter] at he
  have he' : (univ \ starGroup H x).card + q = degree H x * (q+1) := by
    simpa [sum_congr rfl (fun E hE => h.uniform E (mem_filter.mp hE).1),degree] using he
  have hc := card_sdiff_add_card_eq_card (subset_univ (starGroup H x))
  rw [card_univ,h.coordinates] at hc
  rw [hx] at he'
  nlinarith

theorem starGroup_codegree {x y : I} (hx : degree H x = q) (hxy : x ≠ y) :
    codegree H x y = if y ∈ starGroup H x then 0 else 1 := by
  have hc := thin_star h hx hxy
  by_cases he : codegree H x y = 0 <;> simp [Ne.symm hxy,he] <;> omega

theorem starGroup_transversal {x : I} (hx : degree H x = q)
    {E : Finset I} (hE : E ∈ H) : (E ∩ starGroup H x).card = 1 := by
  by_cases hxE : x ∈ E
  · have eq : E ∩ starGroup H x = {x} := by
      ext y
      simp only [mem_inter,mem_starGroup,mem_singleton]
      constructor
      · rintro ⟨hy,he | hz⟩
        · exact he
        · exact False.elim ((codegree_zero.mp hz E hE hxE) hy)
      · rintro rfl
        exact ⟨hxE,Or.inl rfl⟩
    rw [eq,card_singleton]
  · have he := pair_count H E x
    rw [(pair_split h) hx E,ite_eq_right hxE,add_zero] at he
    have hs : (∑ F ∈ H.filter (x ∈ ·), (E ∩ F).card) = q := by
      have ht (F : Finset I) (hF : F ∈ H.filter (x ∈ ·)) : (E ∩ F).card = 1 := by
        obtain ⟨hF,hxF⟩ := mem_filter.mp hF
        rw [inter_comm]
        exact h.saturated_intersection hF (h.saturated_of_degree hx hF hxF) hE
          (fun eq => hxE (eq ▸ hxF))
      rw [sum_congr rfl ht]
      simpa [degree] using hx
    rw [hs] at he
    have hc := card_sdiff_add_card_inter E (starGroup H x)
    rw [he,h.uniform E hE] at hc
    omega

private theorem group_subset {x y : I} (hx : degree H x = q)
    (hy : y ∈ starGroup H x) : starGroup H x ⊆ starGroup H y := by
  intro z hz
  rw [mem_starGroup]
  by_cases hzy : z = y
  · exact Or.inl hzy
  · right
    rw [codegree_zero]
    intro E hE hyE hzE
    have hi := (starGroup_transversal h) hx hE
    exact hzy (card_le_one.mp hi.le z (mem_inter.mpr ⟨hzE,hz⟩)
      y (mem_inter.mpr ⟨hyE,hy⟩))

theorem starGroup_equal_or_disjoint {x y : I} (hx : degree H x = q)
    (hy : degree H y = q) : starGroup H x = starGroup H y ∨
      Disjoint (starGroup H x) (starGroup H y) := by
  by_cases hyx : y ∈ starGroup H x
  · exact Or.inl (eq_of_subset_of_card_le ((group_subset h) hx hyx)
      (by rw [(starGroup_card h) hx,(starGroup_card h) hy]))
  · right
    have hs : (∑ z ∈ starGroup H x, codegree H y z) = q := by
      rw [pair_count]
      have ht (E : Finset I) (hE : E ∈ H.filter (y ∈ ·)) :
          (starGroup H x ∩ E).card = 1 := by
        rw [inter_comm]
        exact (starGroup_transversal h) hx (mem_filter.mp hE).1
      rw [sum_congr rfl ht]
      simpa [degree] using hy
    have hall (z : I) (hz : z ∈ starGroup H x) : codegree H y z = 1 := by
      have hc : (∑ z ∈ starGroup H x, codegree H y z) =
          ∑ _z ∈ starGroup H x, 1 := by simpa [(starGroup_card h) hx] using hs
      exact (sum_eq_sum_iff_of_le (fun z hz => (thin_star h) hy
        (fun he => hyx (he.symm ▸ hz)))).mp hc z hz
    apply disjoint_left.mpr
    intro z hz hz'
    rcases mem_starGroup.mp hz' with he | he
    · exact hyx (he ▸ hz)
    · have := hall z hz
      omega

end Internal
end CoveringDesigns.PairEquality
