import CoveringDesigns.ExactDesign.Basic
import CoveringDesigns.Multicover.Schoenheim
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-! Exact residual counts and integrality, by counting incidences in links. -/
namespace CoveringDesigns.ExactDesign
open Finset
universe u w
variable {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι]

theorem IsDesign.total_count {B : ι → Finset α} {k t lam : ℕ}
    (h : IsDesign B k t lam) :
    k.choose t*Fintype.card ι=lam*(Fintype.card α).choose t := by
  rw [← Multicover.subsetDegree_sum_of_uniform h.1]
  rw [sum_const_nat (fun X hx => h.2 X (mem_powersetCard.mp hx).2), card_powersetCard,
    card_univ, Nat.mul_comm]

/-- Double count a containing occurrence and a t-subset through X inside it. -/
theorem IsDesign.residual_count {B : ι → Finset α} {k t lam i : ℕ}
    (h : IsDesign B k t lam) (hi : i ≤ t) {X : Finset α} (hx : X.card=i) :
    (k-i).choose (t-i)*indexedSubsetDegree B X =
      lam*(Fintype.card α-i).choose (t-i) := by
  have he := (h.subsetLink X (by omega)).total_count
  simpa only [Multicover.subsetLink_card, Multicover.subset_complement_card, hx] using he

theorem residual_denominator_pos {k t i : ℕ} (ht : t ≤ k) (hi : i ≤ t) :
    0 < (k-i).choose (t-i) := Nat.choose_pos (by omega)

/-- A numerical definition; its exactness and integrality are proved from a design. -/
def residual (lam v k t i : ℕ) : ℕ := lam*(v-i).choose (t-i)/(k-i).choose (t-i)

@[simp] theorem residual_top (lam v k t : ℕ) : residual lam v k t t=lam := by
  simp [residual]

theorem IsDesign.multiplicity_eq {B : ι → Finset α} {v k t lam i : ℕ}
    (h : IsDesign B k t lam) (hn : Fintype.card α=v) (ht : t ≤ k)
    (hi : i ≤ t) {X : Finset α} (hx : X.card=i) :
    indexedSubsetDegree B X=residual lam v k t i := by
  have he := h.residual_count hi hx
  rw [hn] at he
  unfold residual
  rw [← he, Nat.mul_div_right _ (residual_denominator_pos ht hi)]

theorem IsDesign.residual_mul {B : ι → Finset α} {v k t lam i : ℕ}
    (h : IsDesign B k t lam) (hn : Fintype.card α=v) (ht : t ≤ k) (hk : k ≤ v)
    (hi : i ≤ t) :
    (k-i).choose (t-i)*residual lam v k t i=lam*(v-i).choose (t-i) := by
  obtain ⟨X, _, hx⟩ := exists_subset_card_eq (s := (univ : Finset α))
    (show i ≤ (univ : Finset α).card by simpa [hn] using hi.trans (ht.trans hk))
  have he := h.residual_count hi hx
  simpa only [hn, h.multiplicity_eq hn ht hi hx] using he

/-- Every lower strength is itself an exact design with the derived multiplicity. -/
theorem IsDesign.lower_strength {B : ι → Finset α} {v k t lam i : ℕ}
    (h : IsDesign B k t lam) (hn : Fintype.card α=v) (ht : t ≤ k) (hi : i ≤ t) :
    IsDesign B k i (residual lam v k t i) :=
  ⟨h.1, fun X hx => h.multiplicity_eq hn ht hi hx⟩

theorem IsDesign.residual_divisibility {B : ι → Finset α} {v k t lam i : ℕ}
    (h : IsDesign B k t lam) (hn : Fintype.card α=v) (ht : t ≤ k) (hk : k ≤ v)
    (hi : i ≤ t) : (k-i).choose (t-i) ∣ lam*(v-i).choose (t-i) :=
  ⟨residual lam v k t i, (h.residual_mul hn ht hk hi).symm⟩

theorem IsDesign.residual_pos {B : ι → Finset α} {v k t lam i : ℕ}
    (h : IsDesign B k t lam) (hn : Fintype.card α=v) (ht : t ≤ k) (hk : k ≤ v)
    (hl : 0 < lam) (hi : i ≤ t) : 0 < residual lam v k t i := by
  have he := h.residual_mul hn ht hk hi
  have hp := Nat.mul_pos hl (Nat.choose_pos (show t-i ≤ v-i by omega))
  rw [← he] at hp
  by_contra hn
  rw [Nat.eq_zero_of_not_pos hn, Nat.mul_zero] at hp
  exact Nat.lt_irrefl 0 hp

/-- The common denominator used in the alternating-transform calculation. -/
theorem IsDesign.residual_common {B : ι → Finset α} {v k t lam i : ℕ}
    (h : IsDesign B k t lam) (hn : Fintype.card α=v) (ht : t ≤ k) (hk : k ≤ v)
    (hi : i ≤ t) :
    (v-t).choose (k-t)*residual lam v k t i=lam*(v-i).choose (k-i) := by
  have he := h.residual_mul hn ht hk hi
  have hc := Nat.choose_mul (n := v-i) (k := k-i) (s := t-i) (by omega)
  have hv : v-i-(t-i)=v-t := by omega
  have hk' : k-i-(t-i)=k-t := by omega
  rw [hv, hk'] at hc
  apply Nat.eq_of_mul_eq_mul_left (residual_denominator_pos ht hi)
  calc
    _ = (v-t).choose (k-t)*((k-i).choose (t-i)*residual lam v k t i) := by ring
    _ = (v-t).choose (k-t)*(lam*(v-i).choose (t-i)) := by rw [he]
    _ = lam*((v-i).choose (t-i)*(v-t).choose (k-t)) := by ring
    _ = lam*((v-i).choose (k-i)*(k-i).choose (t-i)) := by rw [hc]
    _ = _ := by ring

theorem common_denominator_pos {v k t : ℕ} (ht : t ≤ k) (hk : k ≤ v) :
    0 < (v-t).choose (k-t) := Nat.choose_pos (by omega)

theorem IsDesign.residual_recurrence {B : ι → Finset α} {v k t lam i : ℕ}
    (h : IsDesign B k t lam) (hn : Fintype.card α=v) (ht : t ≤ k) (hk : k ≤ v)
    (hi : i < t) :
    (v-i)*residual lam v k t (i+1)=(k-i)*residual lam v k t i := by
  have h₀ := h.residual_common hn ht hk hi.le
  have h₁ := h.residual_common hn ht hk (show i+1 ≤ t by omega)
  have hc := Nat.add_one_mul_choose_eq (v-(i+1)) (k-(i+1))
  rw [show v-(i+1)+1=v-i by omega, show k-(i+1)+1=k-i by omega] at hc
  apply Nat.eq_of_mul_eq_mul_left (common_denominator_pos ht hk)
  calc
    _ = (v-i)*((v-t).choose (k-t)*residual lam v k t (i+1)) := by ring
    _ = (v-i)*(lam*(v-(i+1)).choose (k-(i+1))) := by rw [h₁]
    _ = lam*((v-i)*(v-(i+1)).choose (k-(i+1))) := by ring
    _ = lam*((v-i).choose (k-i)*(k-i)) := by rw [hc]
    _ = (k-i)*(lam*(v-i).choose (k-i)) := by ring
    _ = (k-i)*((v-t).choose (k-t)*residual lam v k t i) := by rw [h₀]
    _ = _ := by ring

theorem IsDesign.subset_total {B : ι → Finset α} {v k t lam i : ℕ}
    (h : IsDesign B k t lam) (hn : Fintype.card α=v) (ht : t ≤ k) (hi : i ≤ t) :
    v.choose i*residual lam v k t i=k.choose i*Fintype.card ι := by
  rw [← Multicover.subsetDegree_sum_of_uniform h.1]
  rw [sum_const_nat (fun X hx => h.multiplicity_eq hn ht hi (mem_powersetCard.mp hx).2),
    card_powersetCard, card_univ, hn]

theorem IsDesign.occurrences_eq {B : ι → Finset α} {v k t lam : ℕ}
    (h : IsDesign B k t lam) (hn : Fintype.card α=v) (ht : t ≤ k) :
    Fintype.card ι=residual lam v k t 0 := by
  simpa using h.multiplicity_eq hn ht (Nat.zero_le t) (X := ∅) rfl

/-- The existing ceiling at an exactly divisible numerator. -/
theorem ceilDiv_mul (k b : ℕ) (hk : 0 < k) : Schoenheim.ceilDiv (k*b) k=b := by
  apply Nat.le_antisymm ((Schoenheim.ceilDiv_le_iff hk).mpr le_rfl)
  exact Nat.le_of_mul_le_mul_left ((Schoenheim.ceilDiv_le_iff hk).mp le_rfl) hk

/-- Exact design integrality makes every residual Schönheim ceiling exact. -/
theorem IsDesign.residual_eq_bound {B : ι → Finset α} {v k t lam i : ℕ}
    (h : IsDesign B k t lam) (hn : Fintype.card α=v) (ht : t ≤ k) (hk : k ≤ v)
    (hi : i ≤ t) : residual lam v k t i=Multicover.bound lam (v-i) (k-i) (t-i) := by
  have main : ∀ r i, i+r=t → residual lam v k t i=Multicover.bound lam (v-i) (k-i) r := by
    intro r
    induction r with
    | zero =>
      intro i he
      have he' : i=t := by omega
      subst i
      simp
    | succ r ih =>
      intro i he
      have hit : i<t := by omega
      have he' := ih (i+1) (by omega)
      rw [Multicover.bound_succ, show v-i-1=v-(i+1) by omega,
        show k-i-1=k-(i+1) by omega, ← he', h.residual_recurrence hn ht hk hit,
        ceilDiv_mul _ _ (by omega)]
  exact main (t-i) i (by omega)

theorem IsDesign.residual_coverLower {B : ι → Finset α} {v k t lam i : ℕ}
    (h : IsDesign B k t lam) (hn : Fintype.card α=v) (ht : t ≤ k) (hk : k ≤ v)
    (hi : i ≤ t) :
    Multicover.CoverLower.{u,w} (v-i) (k-i) (t-i) lam (residual lam v k t i) := by
  rw [h.residual_eq_bound hn ht hk hi]
  exact Multicover.schoenheim_coverLower (by omega) (by omega)

end CoveringDesigns.ExactDesign
