import CoveringDesigns.TwoKMinusCGeneral.Geometry
import CoveringDesigns.C20_11_3.SaturatedBudget

/-! A simultaneous actual-block assignment with bounded, possibly nontrivial fibres. -/
namespace CoveringDesigns.TwoKMinusCGeneral
open Finset C20_11_3 TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α] {c k : ℕ}

/-- Only nonempty fibres inherit intersection size c. Extra intersection points
outside the exclusive parts reduce the available trace capacity. -/
theorem exists_cross_assignment {C : Family α} {p q : α} {B D : Finset α}
    (hv : Fintype.card α+c=2*k) (hC : IsCover C k 3)
    (hstar : star (star C p) q={B,D}) :
    let T := ((B \ D) ×ˢ (D \ B)).filter (fun z => degree (star C z.1) z.2=2)
    ∃ f : α × α → Finset α × Finset α,
      (∀ z ∈ T, (f z).1 ∈ onlyBlocks C p q ∧ (f z).2 ∈ onlyBlocks C q p ∧
        star (star C z.1) z.2={(f z).1,(f z).2} ∧
        ((f z).1 ∩ (f z).2).card=c ∧
        ({z.1,z.2} : Finset α) ⊆ (f z).1 ∩ (f z).2) ∧
      (∀ a, (T.filter (fun z => f z=a)).card ≤ capacity c) := by
  classical
  dsimp only
  let X := B \ D
  let Y := D \ B
  let T := (X ×ˢ Y).filter (fun z => degree (star C z.1) z.2=2)
  have hex (z : α × α) : ∃ a : Finset α × Finset α,
      z ∈ T → a.1 ∈ onlyBlocks C p q ∧ a.2 ∈ onlyBlocks C q p ∧
        star (star C z.1) z.2={a.1,a.2} ∧ (a.1 ∩ a.2).card=c ∧
        ({z.1,z.2} : Finset α) ⊆ a.1 ∩ a.2 := by
    by_cases hz : z ∈ T
    · obtain ⟨hz',hs⟩ := mem_filter.mp hz
      obtain ⟨hx,hy⟩ := mem_product.mp hz'
      obtain ⟨A,hA,E,hE,hst,hi,hsub⟩ := cross_partner_exists hv hC hstar hx hy hs
      exact ⟨(A,E),fun _ => ⟨hA,hE,hst,hi,hsub⟩⟩
    · exact ⟨(∅,∅),fun h => (hz h).elim⟩
  choose f hf using hex
  refine ⟨f,hf,?_⟩
  intro a
  let U := T.filter (fun z => f z=a)
  by_cases hU : U.Nonempty
  · obtain ⟨z,hz⟩ := hU
    obtain ⟨hzT,hza⟩ := mem_filter.mp hz
    have hcard : (a.1 ∩ a.2).card=c := by rw [← hza]; exact (hf z hzT).2.2.2.1
    have hsub : U ⊆ (X ∩ (a.1 ∩ a.2)) ×ˢ (Y ∩ (a.1 ∩ a.2)) := by
      intro t ht
      obtain ⟨htT,hta⟩ := mem_filter.mp ht
      have hxy := mem_product.mp (mem_filter.mp htT).1
      have hh : ({t.1,t.2} : Finset α) ⊆ a.1 ∩ a.2 := by
        rw [← hta]; exact (hf t htT).2.2.2.2
      exact mem_product.mpr ⟨mem_inter.mpr ⟨hxy.1,hh (by simp)⟩,
        mem_inter.mpr ⟨hxy.2,hh (by simp)⟩⟩
    have hdis : Disjoint X Y := by
      apply disjoint_left.mpr
      intro t htX htY
      exact (mem_sdiff.mp htX).2 (mem_sdiff.mp htY).1
    exact (card_le_card hsub).trans (by
      rw [card_product]
      exact cross_capacity X Y (a.1 ∩ a.2) hdis hcard.le)
  · have he : U=∅ := not_nonempty_iff_eq_empty.mp hU
    change U.card ≤ _
    simp [he]

/-- Summing the bounded fibres into actual endpoint block pairs. -/
theorem saturated_cross_card_le {C : Family α} {p q : α} {B D : Finset α}
    (hv : Fintype.card α+c=2*k) (hC : IsCover C k 3)
    (hstar : star (star C p) q={B,D}) :
    (((B \ D) ×ˢ (D \ B)).filter (fun z => degree (star C z.1) z.2=2)).card ≤
      capacity c*(onlyBlocks C p q).card*(onlyBlocks C q p).card := by
  classical
  obtain ⟨f,hf,hfib⟩ := exists_cross_assignment hv hC hstar
  let T := ((B \ D) ×ˢ (D \ B)).filter (fun z => degree (star C z.1) z.2=2)
  have hmaps : Set.MapsTo f T ((onlyBlocks C p q) ×ˢ (onlyBlocks C q p)) := by
    intro z hz
    exact mem_product.mpr ⟨(hf z hz).1,(hf z hz).2.1⟩
  change T.card ≤ _
  rw [card_eq_sum_card_fiberwise hmaps]
  calc
    _ ≤ ∑ _a ∈ (onlyBlocks C p q) ×ˢ (onlyBlocks C q p), capacity c :=
      sum_le_sum (fun a _ => hfib a)
    _ = _ := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end CoveringDesigns.TwoKMinusCGeneral
