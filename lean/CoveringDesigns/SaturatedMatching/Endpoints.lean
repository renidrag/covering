import CoveringDesigns.SaturatedMatching.Split
import Mathlib.Tactic.IntervalCases

/-! Endpoint consequences of actual saturated geometry at k=31,32.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset C20_11_3 TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {C : Family α} {p q : α} {k : ℕ}

namespace Split
variable (s : Split C p q k)
include s

theorem endpoint_floor (hv : Fintype.card α = 2*k-2) (hk : 9 ≤ k)
    (hC : IsCover C k 3) : 4 ≤ s.P.card ∧ 4 ≤ s.Q.card := by
  have hp := onlyBlocks_card_add_pair C p q
  have hq := onlyBlocks_card_add_pair C q p
  rw [s.saturated] at hp
  rw [pair_degree_comm C q p,s.saturated] at hq
  have hpd := TwoKMinusTwo.degree_ge_six hv hk hC p
  have hqd := TwoKMinusTwo.degree_ge_six hv hk hC q
  change s.P.card+2=degree C p at hp
  change s.Q.card+2=degree C q at hq
  omega

/-- The second-partner loss excludes every second saturated mate before
using the refined bound or any global separation conclusion. -/
theorem no_second_partner (hv : Fintype.card α = 2*k-2)
    (hk : k = 31 ∨ k = 32) (hC : IsCover C k 3) (hb : C.card = 13) :
    ∀ z, z ≠ p → z ≠ q → degree (star C q) z ≠ 2 := by
  intro z hzp hzq hsat
  have hkl : 9 ≤ k := by omega
  have hk3 : 3 ≤ k := by omega
  obtain ⟨hp,hq⟩ := s.endpoint_floor hv hkl hC
  have hparts := s.parts
  rw [hb] at hparts
  have hple : s.P.card ≤ 7 := by omega
  have hqle : s.Q.card ≤ 7 := by omega
  have hprod : s.P.card*s.Q.card ≤ 49 := by nlinarith
  have hcross := (s.cross_card_le hv hk3 hC).trans hprod
  have hbudget := s.exact_budget hv hk3 hC
  have hz : z ∈ s.X ∪ s.Y := by rw [s.geometry.2.2.2]; simp [hzp,hzq]
  obtain ⟨E,hE,hw⟩ := second_partner_trace hv hk3 hC s.endpoints
    s.left_mem s.right_mem s.union_eq s.inter_eq hz hsat
  have hcap := s.cap_Q hE
  have hl := s.loss_at hC (mem_onlyBlocks.mp hE).1
  change s.weight E = k-2 at hw
  rw [hcap,hw] at hl
  rcases hk with hk | hk <;> subst k <;>
    norm_num [capacity] at hbudget hl <;> omega

/-- After the no-second-partner theorem, the initial endpoint capacity
leaves only (4,4),(4,5),(5,4) at k=31, and (4,4) at k=32. -/
theorem endpoint_counts (hv : Fintype.card α = 2*k-2)
    (hk : k = 31 ∨ k = 32) (hC : IsCover C k 3) (hb : C.card = 13) :
    (s.P.card = 4 ∧ s.Q.card = 4) ∨
      (k = 31 ∧ s.P.card = 4 ∧ s.Q.card = 5) ∨
      (k = 31 ∧ s.P.card = 5 ∧ s.Q.card = 4) := by
  obtain ⟨hp,hq⟩ := s.endpoint_floor hv (by omega) hC
  have hparts := s.parts
  rw [hb] at hparts
  have hcap := saturated_capacity hv (by omega) hC s.endpoints s.saturated
  change 3*(k-2)*(k-2)+(k/2)*(s.P.card+s.Q.card) ≤
    (C.card-2)*capacity k+s.P.card*s.Q.card at hcap
  rw [hb] at hcap
  have hple : s.P.card ≤ 7 := by omega
  have hqle : s.Q.card ≤ 7 := by omega
  generalize ha : s.P.card = a at *
  generalize hc : s.Q.card = c at *
  rcases hk with hk | hk <;> subst k <;>
    interval_cases a <;> interval_cases c <;> norm_num [capacity] at * <;> omega

/-- The refined shared-block bound removes both mixed cases and k=32.
Any surviving saturated pair has k=31, two degree-six endpoints, and at
most eight saturated residual cross-pairs. -/
theorem surviving_counts (hv : Fintype.card α = 2*k-2)
    (hk : k = 31 ∨ k = 32) (hC : IsCover C k 3) (hb : C.card = 13) :
    k = 31 ∧ s.P.card = 4 ∧ s.Q.card = 4 ∧
      degree C p = 6 ∧ degree C q = 6 ∧ s.crosses.card ≤ 8 := by
  have hn := s.no_second_partner hv hk hC hb
  have hns := s.swap.no_second_partner hv hk hC hb
  obtain ⟨hp,hq⟩ := s.endpoint_floor hv (by omega) hC
  have hr := s.refined_bound hv (by omega) hC (by omega) hn
  have hrs := s.swap.refined_bound hv (by omega) hC
    (by simpa only [swap_Q] using (show 2 ≤ s.P.card by omega)) hns
  simp only [swap_crosses,swap_P,swap_Q] at hrs
  have he := s.exact_budget hv (by omega) hC
  have hparts := s.parts
  rw [hb] at hparts
  have hpd := onlyBlocks_card_add_pair C p q
  have hqd := onlyBlocks_card_add_pair C q p
  rw [s.saturated] at hpd
  rw [pair_degree_comm C q p,s.saturated] at hqd
  change s.P.card+2=degree C p at hpd
  change s.Q.card+2=degree C q at hqd
  rcases s.endpoint_counts hv hk hC hb with ⟨hP,hQ⟩ | ⟨hk,hP,hQ⟩ | ⟨hk,hP,hQ⟩
  · rcases hk with hk | hk <;> subst k <;>
      simp only [hP,hQ] at hr hrs he hparts hpd hqd
    · norm_num [capacity] at hr hrs he
      exact ⟨rfl,hP,hQ,by omega,by omega,by omega⟩
    · norm_num [capacity] at hr hrs he
      omega
  · subst k
    simp only [hP,hQ] at hr hrs he hparts
    norm_num [capacity] at hr hrs he
    omega
  · subst k
    simp only [hP,hQ] at hr hrs he hparts
    norm_num [capacity] at hr hrs he
    omega

end Split

/-- Saturation is impossible at (62,32,3), using actual triple coverage. -/
theorem no_saturation_32 (hv : Fintype.card α = 62)
    (hC : IsCover C 32 3) (hb : C.card = 13) (hpq : p ≠ q) :
    degree (star C p) q ≠ 2 := by
  intro hs
  obtain ⟨s⟩ := Split.exists_of_saturated (k := 32) (by simpa using hv) (by omega) hC hpq hs
  have hh := s.surviving_counts (by simpa using hv) (Or.inr rfl) hC hb
  omega

end CoveringDesigns.SaturatedMatching
