import CoveringDesigns.TwoKMinusTwo.Geometry
import CoveringDesigns.TwoKMinusTwo.Incidence
import CoveringDesigns.C20_11_3.SaturatedBudget

/-! Parameterised capacity of a saturated pair, using actual endpoint blocks. -/
namespace CoveringDesigns.TwoKMinusTwo
open Finset C20_11_3
variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

theorem endpoint_trace_capacity {p q : α} {X Y B : Finset α}
    (hdis : Disjoint X Y) (hpart : X ∪ Y = univ \ {p,q})
    (hB : B.card = k) (hp : p ∈ B) (hq : q ∉ B) :
    (X ∩ B).card * (Y ∩ B).card ≤ capacity (k-1) := by
  have hi : B ∩ {p,q} = {p} := by ext x; simp; aesop
  have h := trace_sum hdis hpart B
  rw [hi, card_singleton, hB] at h
  apply product_le_capacity
  omega

/-- The bare obstruction needs only k≥3; degree floors enter later. -/
theorem saturated_capacity {C : Family α}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) (hC : IsCover C k 3)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2) :
    3*(k-2)*(k-2)+(k/2)*((onlyBlocks C p q).card+(onlyBlocks C q p).card) ≤
      (C.card-2)*capacity k+(onlyBlocks C p q).card*(onlyBlocks C q p).card := by
  classical
  obtain ⟨B,hBC,D,hDC,hBD,hstar,hunion,hinter⟩ :=
    saturated_pair_blocks hv hk hC hpq hsat
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
  change X.card = k-2 at hX
  change Y.card = k-2 at hY
  change X ∪ Y = univ \ {p,q} at hpart
  have hPcap : ∀ A ∈ P, w A ≤ capacity (k-1) := by
    intro A hA
    obtain ⟨hAC,hpA,hqA⟩ := mem_onlyBlocks.mp hA
    exact endpoint_trace_capacity hdis hpart (hC.1 A hAC) hpA hqA
  have hQcap : ∀ A ∈ Q, w A ≤ capacity (k-1) := by
    intro A hA
    obtain ⟨hAC,hqA,hpA⟩ := mem_onlyBlocks.mp hA
    exact endpoint_trace_capacity hdis
      (by simpa [pair_comm] using hpart) (hC.1 A hAC) hqA hpA
  have hNcap : ∀ A ∈ N, w A ≤ capacity k := by
    intro A hA
    obtain ⟨hAC,hpA,hqA⟩ := mem_neitherBlocks.mp hA
    exact cross_capacity X Y A hdis (hC.1 A hAC).le
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
  have hcapacity : S ≤ capacity (k-1)*(P.card+Q.card) + capacity k*N.card := by
    rw [hS]
    have hp := sum_le_sum (s := P) hPcap
    have hq := sum_le_sum (s := Q) hQcap
    have hn := sum_le_sum (s := N) hNcap
    simp only [sum_const, Nat.nsmul_eq_mul] at hp hq hn
    nlinarith
  have hfloor : 3*(k-2)*(k-2) ≤ S + T.card := by
    have h := multiplicity_floor_count (X ×ˢ Y)
      (fun z => degree (star C z.1) z.2) (by
        intro z hz
        obtain ⟨hzX,hzY⟩ := mem_product.mp hz
        apply pair_ge_two hv hk hC
        intro he
        exact disjoint_left.mp hdis hzX (he.symm ▸ hzY))
    have he : (∑ z ∈ X ×ˢ Y, degree (star C z.1) z.2) = S := by
      rw [sum_product]
      exact cross_pair_degree_sum C X Y
    rw [he,card_product,hX,hY] at h
    simpa [Nat.mul_assoc] using h
  obtain ⟨f,hf,hinj⟩ := exists_cross_assignment hv hk hC hstar hinter hdis
  change ∀ z ∈ T, (f z).1 ∈ P ∧ (f z).2 ∈ Q ∧
    (f z).1 ∩ (f z).2 = {z.1,z.2} at hf
  change Set.InjOn f (T : Set (α × α)) at hinj
  have htarget : ∀ z ∈ T, (f z).1 ∈ P ∧ (f z).2 ∈ Q :=
    fun z hz => ⟨(hf z hz).1,(hf z hz).2.1⟩
  have hfirst : T.card ≤ P.card*Q.card := assignment_card_le f htarget hinj
  have hp := endpoint_card_partition C p q
  change C.card = P.card+Q.card+N.card+degree (star C p) q at hp
  rw [hsat] at hp
  have hsum : C.card-2=P.card+Q.card+N.card := by omega
  change 3*(k-2)*(k-2)+(k/2)*(P.card+Q.card) ≤
    (C.card-2)*capacity k+P.card*Q.card
  rw [hsum]
  have hstep := capacity_step (show 1 ≤ k by omega)
  nlinarith

end CoveringDesigns.TwoKMinusTwo
