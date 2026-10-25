import CoveringDesigns.Multicover.Schoenheim
import CoveringDesigns.LabelledCliques.Extensions
import CoveringDesigns.Foundations.StandardAxioms

/-! Local floors and minimum counts for actual indexed nineteen-point covers.
No link classification, geometry or distinctness assumption is imported. -/
namespace CoveringDesigns.C19_9_3
open Finset
universe u v
variable {V : Type u} {I : Type v} [Fintype V] [DecidableEq V] [Fintype I]

theorem pair_floor {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) {T : Finset V} (hT : T.card = 2) :
    3 ≤ indexedSubsetDegree B T := by
  apply Multicover.multiplicity_ge_of_coverLower hv h (by decide)
    (b := 3) (i := 2) _ hT
  exact Multicover.schoenheim_coverLower (by decide : 1 ≤ 7) (by decide : 7 ≤ 17)

theorem degree_floor {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x : V) : 7 ≤ indexedDegree B x := by
  rw [← Multicover.subsetDegree_singleton]
  apply Multicover.multiplicity_ge_of_coverLower hv h (by decide)
    (b := 7) (i := 1) _ (card_singleton x)
  exact Multicover.schoenheim_coverLower (by decide : 2 ≤ 8) (by decide : 8 ≤ 18)

def minimumPoints (B : I → Finset V) : Finset V := univ.filter fun x => indexedDegree B x = 7

@[simp] theorem mem_minimumPoints (B : I → Finset V) (x : V) :
    x ∈ minimumPoints B ↔ indexedDegree B x = 7 := by simp [minimumPoints]

theorem minimum_count_bound {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) :
    152 ≤ 9 * Fintype.card I + (minimumPoints B).card := by
  have hp (x : V) : 8 ≤ indexedDegree B x + if indexedDegree B x = 7 then 1 else 0 := by
    have := degree_floor hv h x
    split_ifs <;> omega
  have hs := sum_le_sum (s := (univ : Finset V)) (fun x _ => hp x)
  have hm : (∑ x : V, if indexedDegree B x = 7 then 1 else 0) = (minimumPoints B).card := by
    simp only [minimumPoints, card_eq_sum_ones, sum_filter]
  simpa only [sum_add_distrib, Multicover.degree_sum_of_uniform h.1, hm,
    sum_const, card_univ, Nat.nsmul_eq_mul, hv] using hs

theorem eight_minimum_points {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16) :
    8 ≤ (minimumPoints B).card := by
  have := minimum_count_bound hv h
  omega

/-- Exact degree excess, with nonnegative natural differences justified by
the derived degree floor. -/
theorem degree_excess {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) :
    (∑ x, (indexedDegree B x - 7)) + 133 = 9 * Fintype.card I := by
  have he (x : V) : indexedDegree B x - 7 + 7 = indexedDegree B x :=
    Nat.sub_add_cancel (degree_floor hv h x)
  have := sum_congr (s₁ := (univ : Finset V)) rfl (fun x _ => he x)
  simpa [sum_add_distrib, hv, Multicover.degree_sum_of_uniform h.1] using this

/-- Local extension count on the actual occurrence set. -/
theorem pair_sum {B : I → Finset V} (h : Multicover.Uniform B 9) (x : V) :
    ∑ y ∈ univ.erase x, indexedSubsetDegree B {x,y} = 8 * indexedDegree B x := by
  have hh := LabelledCliques.extension_sum h ({x} : Finset V)
  rw [LabelledCliques.sum_extensions] at hh
  simp only [card_singleton, sdiff_singleton_eq_erase,
    Multicover.subsetDegree_singleton] at hh
  convert hh using 1
  apply sum_congr rfl
  intro y _
  rw [pair_comm]

#guard_standard_axioms pair_floor degree_floor minimum_count_bound
  eight_minimum_points degree_excess pair_sum

end CoveringDesigns.C19_9_3
