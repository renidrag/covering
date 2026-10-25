import CoveringDesigns.SevenBlock.Degrees

/-! Literal occurrence traces and the complementary-choice agreement count.
No local coordinate equivalences are silently identified. -/
namespace CoveringDesigns.C19_9_3
open Finset SevenBlock
universe u v
variable {V : Type u} {I : Type v} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

/-- Mapping a link column back to the parent gives the actual intersection
of supports, on the original occurrence labels. -/
theorem literal_link_trace (B : I → Finset V) (x : V)
    (y : {y : V // y ∉ ({x} : Finset V)}) :
    (pointSupport (Multicover.subsetLink B {x}) y).map
      (Function.Embedding.subtype _) = pointSupport B x ∩ pointSupport B y.val := by
  ext i
  simp only [mem_map, mem_pointSupport, Multicover.subsetLink, mem_subtype, mem_inter]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ⟨j.property (by simp), hj⟩
  · rintro ⟨hx,hy⟩
    exact ⟨⟨i,by simpa using hx⟩,hy,rfl⟩

/-- Intersections of two link columns agree literally after the embedding
into the common parent occurrence type. -/
theorem literal_link_pair_trace (B : I → Finset V) (x : V)
    (y z : {y : V // y ∉ ({x} : Finset V)}) :
    ((pointSupport (Multicover.subsetLink B {x}) y) ∩
      (pointSupport (Multicover.subsetLink B {x}) z)).map (Function.Embedding.subtype _) =
      pointSupport B x ∩ pointSupport B y.val ∩ pointSupport B z.val := by
  rw [map_inter,literal_link_trace,literal_link_trace]
  ext i
  simp only [mem_inter]
  tauto

/-- Each of the three outside groups contributes the other actual points
choosing the same two-set trace. When every other point agrees exactly once,
the sum is precisely |X|−1; duplicate traces retain their point multiplicity. -/
theorem complementary_agreement_identity {X J : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq J]
    (trace : Fin 3 → X → Finset J) (w : X)
    (h : ∀ y, y ≠ w → (univ.filter fun d : Fin 3 => trace d y = trace d w).card = 1) :
    (∑ d : Fin 3, ((univ.filter fun y => trace d y = trace d w).card - 1)) =
      Fintype.card X - 1 := by
  let g (d : Fin 3) := (univ.filter fun y => trace d y = trace d w).card
  have hp (d : Fin 3) : 1 ≤ g d := card_pos.mpr ⟨w,by simp⟩
  have hs : (∑ d, g d) = ∑ y : X, (univ.filter fun d : Fin 3 => trace d y = trace d w).card := by
    simp only [g, card_eq_sum_ones, sum_filter]
    exact sum_comm
  have hw : (univ.filter fun d : Fin 3 => trace d w = trace d w).card = 3 := by simp
  rw [← sum_erase_add _ _ (mem_univ w), hw] at hs
  have hy : (∑ y ∈ (univ : Finset X).erase w,
      (univ.filter fun d : Fin 3 => trace d y = trace d w).card) = Fintype.card X - 1 := by
    rw [sum_const_nat (fun y hy => h y (mem_erase.mp hy).1)]
    simp
  rw [hy] at hs
  have ht : (∑ d, (g d - 1)) + 3 = ∑ d, g d := by
    have hh := sum_congr (s₁ := (univ : Finset (Fin 3))) rfl
      (fun d _ => Nat.sub_add_cancel (hp d))
    simpa [sum_add_distrib] using hh
  change (∑ d, (g d - 1)) = _
  omega

#guard_standard_axioms literal_link_trace literal_link_pair_trace complementary_agreement_identity

end CoveringDesigns.C19_9_3
