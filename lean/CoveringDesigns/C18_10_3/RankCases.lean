import CoveringDesigns.C18_10_3.LowRows
import CoveringDesigns.BoundaryRank.DeficitCharging

/-! The one-high profile, all high-pair multiplicities, and the equality
case. At multiplicity seven equality of high supports supplies even deficits. -/
namespace CoveringDesigns.C18_10_3
open Finset Matrix
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem deficit_zero_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (δ : ι → ℕ) (cap : ℕ) (hcap : ∀ i, δ i ≤ cap) :
    (∑ i, δ i) + cap*(univ.filter (fun i => δ i = 0)).card ≤ cap*Fintype.card ι := by
  have hp := DeficitCharging.sum_le_mul_positive univ δ cap (fun i _ => hcap i)
  have hc := card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun i => δ i = 0)
  simp only [card_univ] at hc
  simp only [Nat.pos_iff_ne_zero] at hp
  nlinarith

theorem one_high_impossible {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    {h : α} (hh : degree C h = 8) (hlow : ∀ x, x ≠ h → degree C x = 6) : False := by
  have hlo : ∀ x, x ∉ ({h} : Finset α) → degree C x = 6 := by simpa using hlow
  have hc : Fintype.card (Outside ({h} : Finset α)) = 17 := by rw [outside_card,hv,card_singleton]
  have ht := deficit_total_identity hC.1 ({h} : Finset α) hpair
  simp only [sum_singleton,card_singleton,pair_self,hh,hc] at ht
  have hz := low_zero_bound hv hC.1 hlo hpair
  rw [hc,hb] at hz
  have hd := deficit_zero_budget (rowDeficit C {h}) 3 (rowDeficit_le_three hv hC.1 hlo hpair)
  rw [hc] at hd
  omega

/-- Equal full multiplicity identifies the two high supports as actual block
sets. It does not identify their distinct actual point labels. -/
theorem high_supports_equal {C : Family α} {h g : α}
    (hh : degree C h = 7) (hg : degree C g = 7)
    (hm : degree (star C h) g = 7) : star C h = star C g := by
  have h1 : star (star C h) g = star C h :=
    eq_of_subset_of_card_le (filter_subset _ _) (by change degree C h ≤ degree (star C h) g; omega)
  have hsub : star (star C h) g ⊆ star C g := by
    intro B hB
    obtain ⟨hB,hgB⟩ := mem_filter.mp hB
    exact mem_filter.mpr ⟨(mem_filter.mp hB).1,hgB⟩
  have h2 : star (star C h) g = star C g :=
    eq_of_subset_of_card_le hsub (by change degree C g ≤ degree (star C h) g; omega)
  exact h1.symm.trans h2

theorem two_high_deficit_total {C : Family α}
    (hv : Fintype.card α = 18) (hu : Uniform C 10)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    {h g : α} (hne : h ≠ g) (hh : degree C h = 7) (hg : degree C g = 7) :
    (∑ x : Outside ({h,g} : Finset α), rowDeficit C {h,g} x) +
      2*degree (star C h) g = 30 := by
  have hc : Fintype.card (Outside ({h,g} : Finset α)) = 16 := by rw [outside_card,hv,card_pair hne]
  have ht := deficit_total_identity hu ({h,g} : Finset α) hpair
  simp [hne,pair_self,hh,hg,hc,pair_degree_comm C g h] at ht
  omega

/-- At high-pair multiplicity seven every deficit is even and at most two. -/
theorem high_seven_deficits {C : Family α}
    (hv : Fintype.card α = 18) (hu : Uniform C 10)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    {h g : α} (hne : h ≠ g) (hh : degree C h = 7) (hg : degree C g = 7)
    (hlow : ∀ x, x ∉ ({h,g} : Finset α) → degree C x = 6)
    (hm : degree (star C h) g = 7) :
    star C h = star C g ∧ ∀ x : Outside ({h,g} : Finset α),
      rowDeficit C {h,g} x = 2*(degree (star C x.val) h - 3) ∧ rowDeficit C {h,g} x ≤ 2 := by
  have he := high_supports_equal hh hg hm
  refine ⟨he,?_⟩
  intro x
  have hmu : degree (star C x.val) h = degree (star C x.val) g := by
    rw [pair_degree_comm C x.val h,he,pair_degree_comm C g x.val]
  have hd : rowDeficit C {h,g} x = 2*(degree (star C x.val) h - 3) := by
    simp [rowDeficit,hne,← hmu,two_mul]
  have hcap := rowDeficit_le_three hv hu hlow hpair x
  exact ⟨hd,by omega⟩

/-- Multiplicities three, four and five contradict the cap-three budget;
seven contradicts the even cap-two budget. Six is the sole remaining case. -/
theorem high_pair_eq_six {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    {h g : α} (hne : h ≠ g) (hh : degree C h = 7) (hg : degree C g = 7)
    (hlow : ∀ x, x ∉ ({h,g} : Finset α) → degree C x = 6) :
    degree (star C h) g = 6 := by
  have hc : Fintype.card (Outside ({h,g} : Finset α)) = 16 := by rw [outside_card,hv,card_pair hne]
  have ht := two_high_deficit_total hv hC.1 hpair hne hh hg
  have hz := low_zero_bound hv hC.1 hlow hpair
  rw [hc,hb] at hz
  have hd := deficit_zero_budget (rowDeficit C {h,g}) 3 (rowDeficit_le_three hv hC.1 hlow hpair)
  rw [hc] at hd
  have hmle : degree (star C h) g ≤ 7 := by
    have hh' := card_filter_le (star C h) (fun B => g ∈ B)
    change degree (star C h) g ≤ degree C h at hh'
    omega
  by_cases hm : degree (star C h) g = 7
  · have htwo := high_seven_deficits hv hC.1 hpair hne hh hg hlow hm
    have hd2 := deficit_zero_budget (rowDeficit C {h,g}) 2 (fun x => (htwo.2 x).2)
    rw [hc] at hd2
    omega
  · omega

end CoveringDesigns.C18_10_3
