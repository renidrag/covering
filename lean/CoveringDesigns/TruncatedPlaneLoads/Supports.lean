import CoveringDesigns.TruncatedPlaneLoads.Incidence

/-! Classification of small supports meeting every core edge. -/

namespace CoveringDesigns.TruncatedPlaneLoads
open Finset
variable {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable {q : ℕ} (P : Plane q V G)

namespace Plane
include P

def extra (i : G) (a : V) : Finset V := insert a (P.groupSet i)

@[simp] theorem mem_extra (i : G) (a x : V) :
    x ∈ P.extra i a ↔ x = a ∨ P.group x = i := by simp [extra]

theorem extra_size {i : G} {a : V} (ha : P.group a ≠ i) :
    (P.extra i a).card = q+1 := by simp [extra, ha]

theorem extra_core_meet {E : Finset V} (hE : E ∈ P.core) (i : G) (a : V) :
    (P.extra i a ∩ E).Nonempty := by
  obtain ⟨x, hx⟩ := card_pos.mp (by rw [P.transversal E hE i]; omega :
    0 < (E.filter (P.group · = i)).card)
  exact ⟨x, mem_inter.mpr ⟨(P.mem_extra i a x).mpr (Or.inr (mem_filter.mp hx).2),
    (mem_filter.mp hx).1⟩⟩

theorem extra_not_core (hq : 2 ≤ q) {i : G} {a : V} : P.extra i a ∉ P.core := by
  intro h
  have hh := P.transversal (P.extra i a) h i
  have le : (P.groupSet i).card ≤ ((P.extra i a).filter (P.group · = i)).card := by
    apply card_le_card
    intro x hx
    simp only [mem_filter, mem_extra, mem_groupSet] at *
    exact ⟨Or.inr hx, hx⟩
  rw [P.groupSet_card, hh] at le
  omega

theorem extra_intersection {i j : G} {a b : V} (hij : i ≠ j) :
    (P.extra i a ∩ P.extra j b).Nonempty ↔ P.group a = j ∨ P.group b = i ∨ a = b := by
  simp only [nonempty_iff_ne_empty]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h
    rcases mem_inter.mp hx with ⟨hx, hy⟩
    simp only [mem_extra] at hx hy
    rcases hx with rfl | hx <;> rcases hy with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · subst x
      exact Or.inr (Or.inl hx)
    · exact False.elim (hij (hx.symm.trans h))
  · intro h
    apply nonempty_iff_ne_empty.mp
    rcases h with h | h | h
    · exact ⟨a, by simp [h]⟩
    · exact ⟨b, by simp [h]⟩
    · subst b
      exact ⟨a, by simp⟩

private theorem star_sum (S : Finset V) {c : V} (hc : c ∉ S) :
    (∑ E ∈ P.core.filter (c ∈ ·), (E ∩ S).card) =
      (S.filter (P.group · ≠ P.group c)).card := by
  have hcount (y : V) (hy : y ∈ S) :
      ((P.core.filter (c ∈ ·)).filter (y ∈ ·)).card =
        if P.group y = P.group c then 0 else 1 := by
    have hne : c ≠ y := by intro h; subst y; exact hc hy
    simpa only [filter_filter, and_comm, eq_comm] using P.codegree c y hne
  calc
    _ = ∑ y ∈ S, ((P.core.filter (c ∈ ·)).filter (y ∈ ·)).card := by
      simp only [card_eq_sum_ones, sum_filter, mem_inter]
      rw [sum_comm]
      apply sum_congr rfl
      intro E hE
      rw [← sum_filter]
      by_cases hcE : c ∈ E <;> simp [hcE, inter_comm]
    _ = _ := by
      rw [sum_congr rfl hcount]
      simp only [card_eq_sum_ones, sum_filter]
      apply sum_congr rfl
      intro y hy
      by_cases h : P.group y = P.group c <;> simp [h]

private theorem star_bound {S : Finset V}
    (hmeet : ∀ E ∈ P.core, (E ∩ S).Nonempty) {c : V} (hc : c ∉ S) :
    q ≤ (S.filter (P.group · ≠ P.group c)).card := by
  calc
    q = ∑ _E ∈ P.core.filter (c ∈ ·), 1 := by simp [P.degree]
    _ ≤ ∑ E ∈ P.core.filter (c ∈ ·), (E ∩ S).card := by
      apply sum_le_sum
      intro E hE
      exact card_pos.mpr (hmeet E (mem_filter.mp hE).1)
    _ = _ := P.star_sum S hc

private theorem star_exact {S : Finset V}
    (hmeet : ∀ E ∈ P.core, (E ∩ S).Nonempty) {c : V} (hc : c ∉ S)
    (hs : (S.filter (P.group · ≠ P.group c)).card = q)
    {E : Finset V} (hE : E ∈ P.core) (hcE : c ∈ E) : (E ∩ S).card = 1 := by
  have hle : ∀ F ∈ P.core.filter (c ∈ ·), 1 ≤ (F ∩ S).card :=
    fun F hF => card_pos.mpr (hmeet F (mem_filter.mp hF).1)
  have heq : (∑ _F ∈ P.core.filter (c ∈ ·), 1) =
      ∑ F ∈ P.core.filter (c ∈ ·), (F ∩ S).card := by
    rw [P.star_sum S hc, hs]
    simp [P.degree]
  exact ((sum_eq_sum_iff_of_le hle).mp heq E (mem_filter.mpr ⟨hE, hcE⟩)).symm

/-- Every support of size q+1 meeting the core is a core edge or a full
group with one outside coordinate. -/
theorem support_classification (hq : 2 ≤ q) {S : Finset V} (hs : S.card = q+1)
    (hmeet : ∀ E ∈ P.core, (E ∩ S).Nonempty) :
    S ∈ P.core ∨ ∃ i a, P.group a ≠ i ∧ S = P.extra i a := by
  by_cases hfull : ∃ i, P.groupSet i ⊆ S
  · obtain ⟨i, hi⟩ := hfull
    have hc : (S \ P.groupSet i).card = 1 := by
      rw [card_sdiff_of_subset hi, hs, P.groupSet_card]
      omega
    obtain ⟨a, ha⟩ := card_eq_one.mp hc
    have ham : a ∈ S \ P.groupSet i := by rw [ha]; simp
    refine Or.inr ⟨i, a, ?_, ?_⟩
    · simpa only [mem_groupSet] using (mem_sdiff.mp ham).2
    · have hu := sdiff_union_of_subset hi
      rw [ha] at hu
      simpa [extra, singleton_union] using hu.symm
  · have small (i : G) : (S.filter (P.group · = i)).card ≤ 1 := by
      have hn : ¬ P.groupSet i ⊆ S := fun h => hfull ⟨i,h⟩
      obtain ⟨c, hc, hcS⟩ := not_subset.mp hn
      have hb := P.star_bound hmeet hcS
      have hg : P.group c = i := (P.mem_groupSet i c).mp hc
      rw [hg] at hb
      simp only [ne_eq] at hb
      have he := card_filter_add_card_filter_not (s := S) (p := fun x => P.group x = i)
      omega
    have one (i : G) : (S.filter (P.group · = i)).card = 1 := by
      have ht : (∑ j : G, (S.filter (P.group · = j)).card) = ∑ _j : G, 1 := by
        calc
          _ = S.card := by
            simp only [card_eq_sum_ones, sum_filter]
            rw [sum_comm]
            simp
          _ = _ := by simp [hs, P.groups_card]
      exact (sum_eq_sum_iff_of_le (fun j _ => small j)).mp ht i (mem_univ _)
    obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < S.card)
    have hnot : ¬ S ⊆ S.filter (P.group · = P.group x) := by
      intro h
      have hle := card_le_card h
      rw [one, hs] at hle
      omega
    obtain ⟨y, hy, hny⟩ := not_subset.mp hnot
    have hg : P.group x ≠ P.group y := by
      intro h
      exact hny (mem_filter.mpr ⟨hy, h.symm⟩)
    obtain ⟨E, hE, hxE, hyE⟩ := P.join hg
    have hxy : x ≠ y := fun h => hg (congrArg P.group h)
    have htwo : 2 ≤ (E ∩ S).card := by
      calc
        2 = ({x,y} : Finset V).card := by simp [hxy]
        _ ≤ (E ∩ S).card := card_le_card (s := {x,y}) (by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl <;> simp [hxE, hyE, hx, hy])
    have hsub : E ⊆ S := by
      intro c hcE
      by_contra hc
      have hsplit := card_filter_add_card_filter_not
        (s := S) (p := fun z => P.group z = P.group c)
      have he := P.star_exact hmeet hc (by
        rw [one, hs] at hsplit
        simpa only [ne_eq] using (show (S.filter (fun z => ¬ P.group z = P.group c)).card = q by omega)) hE hcE
      omega
    have eq : E = S := eq_of_subset_of_card_le hsub (by rw [P.core_size hE, hs])
    exact Or.inl (eq ▸ hE)

end Plane
end CoveringDesigns.TruncatedPlaneLoads
