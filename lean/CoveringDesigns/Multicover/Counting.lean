import CoveringDesigns.Multicover.Links
import CoveringDesigns.Schoenheim.LowerBound

/-! Incidence counting and the point-link lift for indexed occurrences. -/

namespace CoveringDesigns.Multicover

open Finset
universe u v
variable {α : Type u} {ι : Type v} [Fintype α] [DecidableEq α] [Fintype ι]

theorem degree_sum (B : ι → Finset α) :
    (∑ p, indexedDegree B p) = ∑ i, (B i).card := by
  simp only [indexedDegree, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp

theorem degree_sum_of_uniform {B : ι → Finset α} {k : ℕ} (h : Uniform B k) :
    (∑ p, indexedDegree B p) = k * Fintype.card ι := by
  rw [degree_sum]
  rw [sum_const_nat (fun i _ => h i), card_univ, Nat.mul_comm]

theorem subsetDegree_sum_of_uniform {B : ι → Finset α} {k : ℕ}
    (h : Uniform B k) (r : ℕ) :
    (∑ X ∈ (univ : Finset α).powersetCard r, indexedSubsetDegree B X) =
      k.choose r * Fintype.card ι := by
  rw [indexedSubsetDegree_sum]
  rw [sum_const_nat (fun i _ => congrArg (fun n => n.choose r) (h i)),
    card_univ, Nat.mul_comm]

/-- A counting implication only: no coverage or nonempty-type assumption. -/
theorem bound_of_links {B : ι → Finset α} {k m : ℕ}
    (hk : 0 < k) (hu : Uniform B k)
    (hl : ∀ p : α, m ≤ Fintype.card {i // ({p} : Finset α) ⊆ B i}) :
    Schoenheim.ceilDiv (Fintype.card α * m) k ≤ Fintype.card ι := by
  apply (Schoenheim.ceilDiv_le_iff hk).2
  have hd (p : α) : m ≤ indexedDegree B p := by
    simpa only [subsetLink_card, subsetDegree_singleton] using hl p
  have hs := sum_le_sum (s := (univ : Finset α)) (fun p _ => hd p)
  simpa only [sum_const, card_univ, Nat.nsmul_eq_mul, degree_sum_of_uniform hu] using hs

theorem lift_lower_bound {B : ι → Finset α} {v k t lam m : ℕ}
    (hn : Fintype.card α = v+1) (h : IsCover B (k+1) (t+1) lam)
    (hl : CoverLower.{u,v} v k t lam m) :
    Schoenheim.ceilDiv ((v+1)*m) (k+1) ≤ Fintype.card ι := by
  rw [← hn]
  apply bound_of_links (Nat.succ_pos k) h.1
  intro p
  apply hl (D := subsetLink B {p})
  · rw [subset_complement_card, card_singleton, hn, Nat.add_sub_cancel]
  · simpa using subsetLink_isCover h {p} (by simp)

end CoveringDesigns.Multicover
