import CoveringDesigns.C20_11_3.Incidence
import CoveringDesigns.C20_11_3.SaturatedAssignment
import CoveringDesigns.C20_11_3.SaturatedBudget
import CoveringDesigns.C20_11_3.SaturatedLoss

/-!
The shared-block obstruction. Cross-pairs first force many saturated pairs.
A second saturated partner of the degree-six endpoint would lose sixteen
units of capacity. The same four endpoint blocks therefore meet each
residual point twice, and restrict every row of the actual pairing map.
-/
namespace CoveringDesigns.C20_11_3
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The counting contradiction with the degree-six endpoint already oriented. -/
theorem no_saturated_pair_with_degree_six {C : Family α}
    (hv : Fintype.card α = 20) (hC : IsCover C 11 3) (hb : C.card = 11)
    {p q : α} (hpq : p ≠ q) (hq6 : degree C q = 6)
    (hsat : degree (star C p) q = 2) : False := by
  classical
  obtain ⟨B,hBC,D,hDC,hBD,hstar,hunion,hinter⟩ :=
    saturated_pair_blocks hv hC hpq hsat
  let X := B \ {p,q}
  let Y := D \ {p,q}
  let P := onlyBlocks C p q
  let Q := onlyBlocks C q p
  let N := neitherBlocks C p q
  let w : Finset α → ℕ := fun A => (X ∩ A).card * (Y ∩ A).card
  let S := ∑ A ∈ C, w A
  let T := (X ×ˢ Y).filter (fun z => degree (star C z.1) z.2 = 2)
  obtain ⟨hdis,hX,hY,hpart⟩ := saturated_residual_geometry hpq
    (hC.1 B hBC) (hC.1 D hDC) hunion hinter
  change Disjoint X Y at hdis
  change X.card = 9 at hX
  change Y.card = 9 at hY
  change X ∪ Y = univ \ {p,q} at hpart
  have hQ : Q.card = 4 := by
    have h := onlyBlocks_card_add_pair C q p
    rw [pair_degree_comm C q p,hsat,hq6] at h
    change Q.card + 2 = 6 at h
    omega
  have hn : P.card = 4 ∨ P.card = 5 := by
    have h := onlyBlocks_card_add_pair C p q
    rw [hsat] at h
    change P.card + 2 = degree C p at h
    have hd := degree_six_or_seven hv hC hb p
    omega
  have hparts : N.card + P.card = 5 := by
    have h := endpoint_card_partition C p q
    change C.card = P.card + Q.card + N.card + degree (star C p) q at h
    rw [hb,hQ,hsat] at h
    omega
  have hPcap : ∀ A ∈ P, w A ≤ 25 := by
    intro A hA
    obtain ⟨hAC,hpA,hqA⟩ := mem_onlyBlocks.mp hA
    exact trace_product_le.1 (trace_sum_only hdis hpart (hC.1 A hAC) hpA hqA)
  have hQcap : ∀ A ∈ Q, w A ≤ 25 := by
    intro A hA
    obtain ⟨hAC,hqA,hpA⟩ := mem_onlyBlocks.mp hA
    exact trace_product_le.1 (trace_sum_only hdis
      (by simpa [pair_comm] using hpart) (hC.1 A hAC) hqA hpA)
  have hNcap : ∀ A ∈ N, w A ≤ 30 := by
    intro A hA
    obtain ⟨hAC,hpA,hqA⟩ := mem_neitherBlocks.mp hA
    exact trace_product_le.2 (trace_sum_neither hdis hpart (hC.1 A hAC) hpA hqA)
  have hwB : w B = 0 := by
    have he : Y ∩ B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzY,hzB⟩ := mem_inter.mp hz
      exact residual_not_mem_other (B := D) (D := B) (by simpa [inter_comm] using hinter) hzY hzB
    simp [w,he]
  have hwD : w D = 0 := by
    have he : X ∩ D = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzX,hzD⟩ := mem_inter.mp hz
      exact residual_not_mem_other hinter hzX hzD
    simp [w,he]
  have hS : S = (∑ A ∈ P, w A) + (∑ A ∈ Q, w A) + (∑ A ∈ N, w A) := by
    dsimp only [S]
    rw [endpoint_sum_partition C p q w,hstar]
    simp [hwB,hwD,hBD,P,Q,N]
  have hcapacity : S ≤ 25 * (P.card + 4) + 30 * N.card := by
    rw [hS,← hQ]
    exact capacity_bound P Q N w hPcap hQcap hNcap
  have hfloor : 243 ≤ S + T.card := by
    have h := multiplicity_floor_count (X ×ˢ Y)
      (fun z => degree (star C z.1) z.2) (by
        intro z hz
        obtain ⟨hzX,hzY⟩ := mem_product.mp hz
        apply pair_ge_two hv hC
        intro he
        exact disjoint_left.mp hdis hzX (he.symm ▸ hzY))
    have he : (∑ z ∈ X ×ˢ Y, degree (star C z.1) z.2) = S := by
      rw [sum_product]
      exact cross_pair_degree_sum C X Y
    rw [he,card_product,hX,hY] at h
    exact h
  obtain ⟨f,hf,hinj⟩ := exists_cross_assignment hv hC hstar hinter hdis
  change ∀ z ∈ T, (f z).1 ∈ P ∧ (f z).2 ∈ Q ∧
    (f z).1 ∩ (f z).2 = {z.1,z.2} at hf
  change Set.InjOn f (T : Set (α × α)) at hinj
  have htarget : ∀ z ∈ T, (f z).1 ∈ P ∧ (f z).2 ∈ Q :=
    fun z hz => ⟨(hf z hz).1,(hf z hz).2.1⟩
  have hfirst : T.card ≤ 4 * P.card := by
    have h := assignment_card_le f htarget hinj
    simpa [hQ,Nat.mul_comm] using h
  have hnotsecond (z : α) (hz : z ∈ X ∪ Y) : degree (star C q) z ≠ 2 := by
    intro hs
    obtain ⟨E,hEQ,hwE⟩ := second_partner_trace hv hC hpq hBC hDC hunion hinter hz hs
    have hcap := capacity_bound_loss16 P Q N w hPcap hQcap hNcap
      ⟨E,hEQ,by exact Nat.le_of_eq hwE⟩
    rw [← hS,hQ] at hcap
    exact no_second_partner_arithmetic hparts hcap hfloor hfirst
  have hpoint (z : α) (hzp : z ≠ p) (hzq : z ≠ q) : 2 ≤ degree Q z := by
    have hz : z ∈ X ∪ Y := by rw [hpart]; simp [hzp,hzq]
    have hμ := pair_ge_two hv hC hzq.symm
    have hne := hnotsecond z hz
    have hthree : 3 ≤ degree (star C q) z := by omega
    rcases mem_union.mp hz with hzX | hzY
    · have he := residual_pair_eq hstar (mem_sdiff.mp hzX).1
        (residual_not_mem_other hinter hzX)
      change degree (star C q) z = degree Q z + 1 at he
      omega
    · have hs : star (star C p) q = {D,B} := by simpa [pair_comm] using hstar
      have he := residual_pair_eq hs (mem_sdiff.mp hzY).1
        (residual_not_mem_other (B := D) (D := B) (by simpa [inter_comm] using hinter) hzY)
      change degree (star C q) z = degree Q z + 1 at he
      omega
  have hrow : ∀ A ∈ P, 20 ≤ ∑ E ∈ Q, (A ∩ E).card := by
    intro A hA
    obtain ⟨hAC,hpA,hqA⟩ := mem_onlyBlocks.mp hA
    exact shared_intersection_sum (hC.1 A hAC) hpA hqA hpoint
  have hsmall : ∀ z ∈ T, ((f z).1 ∩ (f z).2).card = 2 := by
    intro z hz
    rw [(hf z hz).2.2]
    apply card_pair
    obtain ⟨hzX,hzY⟩ := mem_product.mp (mem_filter.mp hz).1
    intro he
    exact disjoint_left.mp hdis hzX (he.symm ▸ hzY)
  have hcap : ∀ A ∈ P, ∀ E ∈ Q, (A ∩ E).card ≤ 10 := by
    intro A hA E hE
    obtain ⟨hAC,hpA,_⟩ := mem_onlyBlocks.mp hA
    exact intersection_le_ten (hC.1 A hAC) hpA (mem_onlyBlocks.mp hE).2.2
  have hlast := assignment_card_le_twice f (fun A E => (A ∩ E).card)
    hQ htarget hinj hrow hsmall hcap
  exact final_partner_contradiction hn (cross_count_lower hparts hcapacity hfloor) hlast

/-- No saturated pair can occur in an eleven-block (20,11,3) covering. -/
theorem no_saturated_pair {C : Family α}
    (hv : Fintype.card α = 20) (hC : IsCover C 11 3) (hb : C.card = 11)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2) : False := by
  obtain ⟨h,hh,hlow⟩ := degree_profile hv hC hb
  by_cases hqh : q = h
  · have hph : p ≠ h := by simpa [hqh] using hpq
    apply no_saturated_pair_with_degree_six hv hC hb hpq.symm (hlow p hph)
    simpa [pair_degree_comm] using hsat
  · exact no_saturated_pair_with_degree_six hv hC hb hpq (hlow q hqh) hsat

end CoveringDesigns.C20_11_3
