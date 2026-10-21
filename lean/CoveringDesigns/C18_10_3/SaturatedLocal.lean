import CoveringDesigns.C18_10_3.Incidence
import CoveringDesigns.SaturatedMatching.Counting
import CoveringDesigns.SaturatedMatching.Geometry

/-! Actual-index capacities, the twelve-unit loss, and rounding on every
assignment fibre. The conclusion retains the local residual partition. -/
namespace CoveringDesigns.C18_10_3
open Finset C20_11_3
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The support union rules out two high endpoints and every degree-eight endpoint. -/
theorem saturated_degree_sum {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2) :
    degree C p + degree C q ≤ 13 := by
  have hi := card_union_add_card_inter (star C p) (star C q)
  have he : star C p ∩ star C q = star (star C p) q := by
    ext A
    simp [star, and_assoc, and_left_comm, and_comm]
  have hu : (star C p ∪ star C q).card ≤ C.card :=
    card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  rw [he] at hi
  change _ + degree (star C p) q = degree C p + degree C q at hi
  omega

/-- Every edge has a low endpoint. -/
theorem saturated_low_endpoint {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2) :
    degree C p = 6 ∨ degree C q = 6 := by
  have hh := saturated_degree_sum hv hC hb hpq hsat
  have hp := degree_ge_six hv hC p
  have hq := degree_ge_six hv hC q
  omega

/-- A low endpoint has no second partner; the other endpoint is also low.
At least seven other saturated edges cross the retained partition. -/
theorem saturated_local {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    {p q : α} (hpq : p ≠ q) (hq6 : degree C q = 6)
    (hsat : degree (star C p) q = 2) :
    degree C p = 6 ∧
    (∀ z, z ≠ p → z ≠ q → degree (star C q) z ≠ 2) ∧
    ∃ B ∈ C, ∃ D ∈ C, B ≠ D ∧ star (star C p) q = {B,D} ∧
      B ∪ D = univ ∧ B ∩ D = {p,q} ∧
      7 ≤ (((B \ {p,q}) ×ˢ (D \ {p,q})).filter
        (fun z => degree (star C z.1) z.2 = 2)).card := by
  classical
  obtain ⟨B,hBC,D,hDC,hBD,hstar,hunion,hinter⟩ :=
    TwoKMinusTwo.saturated_pair_blocks (k := 10) hv (by decide) hC hpq hsat
  let X := B \ {p,q}
  let Y := D \ {p,q}
  let P := onlyBlocks C p q
  let Q := onlyBlocks C q p
  let N := neitherBlocks C p q
  let w : Finset α → ℕ := fun A => (X ∩ A).card * (Y ∩ A).card
  let S := ∑ A ∈ C, w A
  let T := (X ×ˢ Y).filter (fun z => degree (star C z.1) z.2 = 2)
  obtain ⟨hdis,hX,hY,hpart⟩ := TwoKMinusTwo.saturated_residual_geometry hpq
    (hC.1 B hBC) (hC.1 D hDC) hunion hinter
  change Disjoint X Y at hdis
  change X.card = 8 at hX
  change Y.card = 8 at hY
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
    have hd := saturated_degree_sum hv hC hb hpq hsat
    have hl := degree_ge_six hv hC p
    omega
  have hparts : N.card + P.card = 5 := by
    have h := endpoint_card_partition C p q
    change C.card = P.card + Q.card + N.card + degree (star C p) q at h
    rw [hb,hQ,hsat] at h
    omega
  have hPcap : ∀ A ∈ P, w A ≤ 20 := by
    intro A hA
    obtain ⟨hAC,hpA,hqA⟩ := mem_onlyBlocks.mp hA
    exact TwoKMinusTwo.endpoint_trace_capacity (k := 10) hdis hpart (hC.1 A hAC) hpA hqA
  have hQcap : ∀ A ∈ Q, w A ≤ 20 := by
    intro A hA
    obtain ⟨hAC,hqA,hpA⟩ := mem_onlyBlocks.mp hA
    exact TwoKMinusTwo.endpoint_trace_capacity (k := 10) hdis
      (by simpa [pair_comm] using hpart) (hC.1 A hAC) hqA hpA
  have hNcap : ∀ A ∈ N, w A ≤ 25 := by
    intro A hA
    exact TwoKMinusTwo.cross_capacity X Y A hdis (hC.1 A (mem_neitherBlocks.mp hA).1).le
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
  have hcapacity : S ≤ 20 * (P.card + 4) + 25 * N.card := by
    rw [hS]
    have hp := sum_le_sum hPcap
    have hq := sum_le_sum hQcap
    have hn := sum_le_sum hNcap
    simp only [sum_const, Nat.nsmul_eq_mul, hQ] at hp hq hn
    omega
  have hfloor : 192 ≤ S + T.card := by
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
  obtain ⟨f,hf,hinj⟩ := TwoKMinusTwo.exists_cross_assignment (k := 10) hv (by decide) hC hstar hinter hdis
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
    obtain ⟨E,hEQ,hwE⟩ := SaturatedMatching.second_partner_trace
      (k := 10) hv (by decide) hC hpq hBC hDC hunion hinter hz hs
    have hloss := SaturatedMatching.capacity_loss_at Q w (fun _ => 20) hQcap hEQ
    change w E = 8 at hwE
    rw [hwE] at hloss
    have hp := sum_le_sum hPcap
    have hn := sum_le_sum hNcap
    simp only [sum_const, Nat.nsmul_eq_mul, hQ] at hp hn hloss
    have hcap : S + 12 ≤ 20*(P.card+4)+25*N.card := by rw [hS]; omega
    omega
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
  have hrow : ∀ A ∈ P, 18 ≤ ∑ E ∈ Q, (A ∩ E).card := by
    intro A hA
    obtain ⟨hAC,hpA,hqA⟩ := mem_onlyBlocks.mp hA
    exact SaturatedMatching.shared_intersection_sum (hC.1 A hAC) hpA hqA hpoint
  have hsmall : ∀ z ∈ T, ((f z).1 ∩ (f z).2).card = 2 := by
    intro z hz
    rw [(hf z hz).2.2]
    apply card_pair
    obtain ⟨hzX,hzY⟩ := mem_product.mp (mem_filter.mp hz).1
    intro he
    exact disjoint_left.mp hdis hzX (he.symm ▸ hzY)
  have hcap : ∀ A ∈ P, ∀ E ∈ Q, (A ∩ E).card ≤ 9 := by
    intro A hA E hE
    obtain ⟨hAC,hpA,_⟩ := mem_onlyBlocks.mp hA
    exact SaturatedMatching.intersection_le_pred (hC.1 A hAC) hpA (mem_onlyBlocks.mp hE).2.2
  have hfibre := SaturatedMatching.assignment_fibre_bound f (fun A E => (A ∩ E).card)
    (k := 10) (by decide) (by omega) htarget hinj hrow hsmall hcap
  have hlast : T.card ≤ 2 * P.card := by
    rw [card_eq_sum_card_fiberwise (f := fun z => (f z).1)
      (s := T) (t := P) (fun z hz => (htarget z hz).1)]
    calc
      _ ≤ ∑ _A ∈ P, 2 := sum_le_sum fun A hA => by
        have hh := hfibre A hA
        rw [hQ] at hh
        omega
      _ = _ := by simp [Nat.mul_comm]
  have hn4 : P.card = 4 := by omega
  have hp6 : degree C p = 6 := by
    have hh := onlyBlocks_card_add_pair C p q
    change P.card + degree (star C p) q = degree C p at hh
    omega
  refine ⟨hp6, ?_, B,hBC,D,hDC,hBD,hstar,hunion,hinter,?_⟩
  · intro z hzp hzq
    exact hnotsecond z (by rw [hpart]; simp [hzp,hzq])
  · change 7 ≤ T.card
    omega

end CoveringDesigns.C18_10_3
