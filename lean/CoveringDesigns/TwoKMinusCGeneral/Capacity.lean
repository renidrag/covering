import CoveringDesigns.TwoKMinusCGeneral.Assignment
import CoveringDesigns.TwoKMinusCGeneral.Incidence
import CoveringDesigns.C20_11_3.SaturatedBudget

/-! Parameterised capacity of a saturated pair, using actual endpoint blocks. -/
namespace CoveringDesigns.TwoKMinusCGeneral
open Finset C20_11_3 TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α] {c k : ℕ}

theorem endpoint_trace_capacity {p : α} {X Y B : Finset α}
    (hdis : Disjoint X Y) (hout : p ∉ X ∪ Y)
    (hB : B.card=k) (hp : p ∈ B) :
    (X ∩ B).card*(Y ∩ B).card ≤ capacity (k-1) := by
  apply product_le_capacity
  rw [← card_union_of_disjoint (hdis.mono inter_subset_left inter_subset_left)]
  have hsub : (X ∩ B) ∪ (Y ∩ B) ⊆ B.erase p := by
    intro z hz
    have hzB : z ∈ B := (union_subset inter_subset_right inter_subset_right) hz
    have hzXY : z ∈ X ∪ Y := (union_subset_union inter_subset_left inter_subset_left) hz
    exact mem_erase.mpr ⟨by intro h; subst z; exact hout hzXY,hzB⟩
  simpa [card_erase_of_mem hp,hB] using card_le_card hsub

/-- Capacity of a saturated pair, independent of a point-degree or block-budget assumption. -/
theorem saturated_capacity {C : Family α}
    (hv : Fintype.card α+c=2*k) (hc : 2≤c) (hck : c<k) (hC : IsCover C k 3)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2) :
    3*(k-c)*(k-c)+(k/2)*((onlyBlocks C p q).card+(onlyBlocks C q p).card) ≤
      (C.card-2)*capacity k+capacity c*(onlyBlocks C p q).card*(onlyBlocks C q p).card := by
  classical
  obtain ⟨B,hBC,D,hDC,hBD,hstar,_hunion,_hinter,hX,hY⟩ :=
    saturated_pair_blocks hv hC hpq hsat
  let X := B \ D
  let Y := D \ B
  let P := onlyBlocks C p q
  let Q := onlyBlocks C q p
  let N := neitherBlocks C p q
  let w : Finset α → ℕ := fun A => (X ∩ A).card * (Y ∩ A).card
  let S := ∑ A ∈ C, w A
  let T := (X ×ˢ Y).filter (fun z => degree (star C z.1) z.2 = 2)
  have hdis : Disjoint X Y := by
    apply disjoint_left.mpr
    intro z hzX hzY
    exact (mem_sdiff.mp hzX).2 (mem_sdiff.mp hzY).1
  change X.card = k-c at hX
  change Y.card = k-c at hY
  have hBs : B ∈ star (star C p) q := by rw [hstar]; simp
  have hDs : D ∈ star (star C p) q := by rw [hstar]; simp
  have hpB := (mem_filter.mp (mem_filter.mp hBs).1).2
  have hpD := (mem_filter.mp (mem_filter.mp hDs).1).2
  have hqB := (mem_filter.mp hBs).2
  have hqD := (mem_filter.mp hDs).2
  have hpout : p ∉ X ∪ Y := by simp [X,Y,hpB,hpD]
  have hqout : q ∉ X ∪ Y := by simp [X,Y,hqB,hqD]
  have hPcap : ∀ A ∈ P, w A ≤ capacity (k-1) := by
    intro A hA
    obtain ⟨hAC,hpA,hqA⟩ := mem_onlyBlocks.mp hA
    exact endpoint_trace_capacity hdis hpout (hC.1 A hAC) hpA
  have hQcap : ∀ A ∈ Q, w A ≤ capacity (k-1) := by
    intro A hA
    obtain ⟨hAC,hqA,hpA⟩ := mem_onlyBlocks.mp hA
    exact endpoint_trace_capacity hdis hqout (hC.1 A hAC) hqA
  have hNcap : ∀ A ∈ N, w A ≤ capacity k := by
    intro A hA
    obtain ⟨hAC,hpA,hqA⟩ := mem_neitherBlocks.mp hA
    exact cross_capacity X Y A hdis (hC.1 A hAC).le
  have hwB : w B = 0 := by
    have he : Y ∩ B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzY,hzB⟩ := mem_inter.mp hz
      exact (mem_sdiff.mp hzY).2 hzB
    simp [w,he]
  have hwD : w D = 0 := by
    have he : X ∩ D = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzX,hzD⟩ := mem_inter.mp hz
      exact (mem_sdiff.mp hzX).2 hzD
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
  have hfloor : 3*(k-c)*(k-c) ≤ S + T.card := by
    have h := multiplicity_floor_count (X ×ˢ Y)
      (fun z => degree (star C z.1) z.2) (by
        intro z hz
        obtain ⟨hzX,hzY⟩ := mem_product.mp hz
        apply TwoKMinusCGeneral.pair_ge_two hv hc hck hC
        intro he
        exact disjoint_left.mp hdis hzX (he.symm ▸ hzY))
    have he : (∑ z ∈ X ×ˢ Y, degree (star C z.1) z.2) = S := by
      rw [sum_product]
      exact cross_pair_degree_sum C X Y
    rw [he,card_product,hX,hY] at h
    simpa [Nat.mul_assoc] using h
  have hfirst : T.card ≤ capacity c*P.card*Q.card :=
    saturated_cross_card_le hv hC hstar
  have hp := endpoint_card_partition C p q
  change C.card = P.card+Q.card+N.card+degree (star C p) q at hp
  rw [hsat] at hp
  have hsum : C.card-2=P.card+Q.card+N.card := by omega
  change 3*(k-c)*(k-c)+(k/2)*(P.card+Q.card) ≤
    (C.card-2)*capacity k+capacity c*P.card*Q.card
  rw [hsum]
  have hstep := capacity_step (show 1 ≤ k by omega)
  nlinarith

end CoveringDesigns.TwoKMinusCGeneral
