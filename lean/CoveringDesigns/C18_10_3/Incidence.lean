import CoveringDesigns.TwoKMinusTwo.Incidence

/-! Point links and the exhaustive excess-two profiles on eighteen actual points.
Formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.C18_10_3
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem lower_bound_17_9_2 {C : Family α} (hv : Fintype.card α = 17)
    (hC : IsCover C 9 2) : 6 ≤ C.card :=
  TwoKMinusTwo.link_lower_bound (k := 10) hv (by decide) hC

theorem degree_ge_six {C : Family α} (hv : Fintype.card α = 18)
    (hC : IsCover C 10 3) (p : α) : 6 ≤ degree C p :=
  TwoKMinusTwo.degree_ge_six (k := 10) hv (by decide) hC p

theorem pair_ge_two {C : Family α} (hv : Fintype.card α = 18)
    (hC : IsCover C 10 3) {p q : α} (hpq : p ≠ q) :
    2 ≤ degree (star C p) q :=
  TwoKMinusTwo.pair_ge_two (k := 10) hv (by decide) hC hpq

theorem eleven_le_card {C : Family α} (hv : Fintype.card α = 18)
    (hC : IsCover C 10 3) : 11 ≤ C.card := by
  have hi := incidence_lower_bound hC.1 (degree_ge_six hv hC)
  rw [hv] at hi
  omega

theorem degree_excess_sum {C : Family α} (hv : Fintype.card α = 18)
    (hC : IsCover C 10 3) (hb : C.card = 11) :
    (∑ p, (degree C p - 6)) = 2 := by
  have hs := degree_sum_of_uniform hC.1
  rw [hb] at hs
  have he : (∑ p, (degree C p - 6)) + 108 = 110 := by
    calc
      _ = ∑ p, ((degree C p - 6) + 6) := by simp [sum_add_distrib, hv]
      _ = ∑ p, degree C p := sum_congr rfl fun p _ =>
        Nat.sub_add_cancel (degree_ge_six hv hC p)
      _ = _ := hs
  omega

theorem degree_bounds {C : Family α} (hv : Fintype.card α = 18)
    (hC : IsCover C 10 3) (hb : C.card = 11) (p : α) :
    6 ≤ degree C p ∧ degree C p ≤ 8 := by
  have hl := degree_ge_six hv hC p
  have hu := single_le_sum (f := fun q => degree C q - 6)
    (fun _ _ => Nat.zero_le _) (mem_univ p)
  rw [degree_excess_sum hv hC hb] at hu
  omega

/-- The disjunction retains actual, distinct high point labels. -/
theorem degree_profiles {C : Family α} (hv : Fintype.card α = 18)
    (hC : IsCover C 10 3) (hb : C.card = 11) :
    (∃ h, degree C h = 8 ∧ ∀ x, x ≠ h → degree C x = 6) ∨
    (∃ h g, h ≠ g ∧ degree C h = 7 ∧ degree C g = 7 ∧
      ∀ x, x ≠ h → x ≠ g → degree C x = 6) := by
  have hs := degree_excess_sum hv hC hb
  have hl := degree_ge_six hv hC
  have hu := degree_bounds hv hC hb
  by_cases he : ∃ h, degree C h = 8
  · obtain ⟨h, hh⟩ := he
    refine Or.inl ⟨h, hh, ?_⟩
    intro x hxh
    have hx := sum_le_sum_of_subset (f := fun p => degree C p - 6)
      (subset_univ ({x,h} : Finset α))
    simp [hxh, hh, hs] at hx
    have := hl x
    omega
  · have he7 : ∃ h, degree C h = 7 := by
      by_contra hn
      have hall : ∀ x, degree C x = 6 := by
        intro x
        have := hu x
        have h7 : degree C x ≠ 7 := fun h => hn ⟨x,h⟩
        have h8 : degree C x ≠ 8 := fun h => he ⟨x,h⟩
        omega
      simp [hall] at hs
    obtain ⟨h, hh⟩ := he7
    have heg : ∃ g, g ≠ h ∧ degree C g = 7 := by
      by_contra hn
      have hall : ∀ x, x ≠ h → degree C x = 6 := by
        intro x hxh
        have := hu x
        have h7 : degree C x ≠ 7 := fun h => hn ⟨x,hxh,h⟩
        have h8 : degree C x ≠ 8 := fun h => he ⟨x,h⟩
        omega
      have ht : (∑ x, (degree C x - 6)) = degree C h - 6 := by
        apply sum_eq_single h
        · intro x _ hxh
          simp [hall x hxh]
        · simp
      omega
    obtain ⟨g, hgh, hg⟩ := heg
    refine Or.inr ⟨h,g,hgh.symm,hh,hg,?_⟩
    intro x hxh hxg
    have hx := sum_le_sum_of_subset (f := fun p => degree C p - 6)
      (subset_univ ({x,h,g} : Finset α))
    simp [hxh,hxg,hgh.symm,hh,hg,hs] at hx
    have := hl x
    omega

end CoveringDesigns.C18_10_3
