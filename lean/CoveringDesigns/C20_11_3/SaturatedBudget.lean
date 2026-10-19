import CoveringDesigns.Foundations.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
Finite counting for the saturated-pair obstruction. The maps below have
actual members of the two supplied block families as their coordinates.
Their geometric construction and injectivity are established separately.
-/

namespace CoveringDesigns.C20_11_3

open Finset

variable {β γ : Type*} [DecidableEq β]

/-- Every nonsaturated cross-pair contributes at least three incidences. -/
theorem multiplicity_floor_count (T : Finset γ) (μ : γ → ℕ)
    (hμ : ∀ t ∈ T, 2 ≤ μ t) :
    3 * T.card ≤ (∑ t ∈ T, μ t) + (T.filter (μ · = 2)).card := by
  have hpoint (t : γ) (ht : t ∈ T) :
      3 ≤ μ t + if μ t = 2 then 1 else 0 := by
    have := hμ t ht
    split_ifs <;> omega
  have hs := sum_le_sum (s := T) hpoint
  have hf : (∑ t ∈ T, if μ t = 2 then 1 else 0) =
      (T.filter (μ · = 2)).card := by
    simp only [card_eq_sum_ones, sum_filter]
  simpa [sum_add_distrib, hf, mul_comm] using hs

/-- An injection into ordered actual block pairs gives the first budget. -/
theorem assignment_card_le {P Q : Finset β} {T : Finset γ} (f : γ → β × β)
    (htarget : ∀ t ∈ T, (f t).1 ∈ P ∧ (f t).2 ∈ Q)
    (hinj : Set.InjOn f T) : T.card ≤ P.card * Q.card := by
  have h := card_le_card_of_injOn (s := T) (t := P ×ˢ Q) f
    (fun t ht => mem_product.mpr (htarget t ht))
    hinj
  simpa using h

/-- Sum the endpoint and nonendpoint block capacities. -/
theorem capacity_bound (P Q N : Finset β) (w : β → ℕ)
    (hP : ∀ A ∈ P, w A ≤ 25) (hQ : ∀ D ∈ Q, w D ≤ 25)
    (hN : ∀ D ∈ N, w D ≤ 30) :
    (∑ A ∈ P, w A) + (∑ D ∈ Q, w D) + (∑ D ∈ N, w D) ≤
      25 * (P.card + Q.card) + 30 * N.card := by
  have hPs := sum_le_sum (s := P) hP
  have hQs := sum_le_sum (s := Q) hQ
  have hNs := sum_le_sum (s := N) hN
  simp only [sum_const, Nat.nsmul_eq_mul] at hPs hQs hNs
  omega

/-- A forced trace product at most nine loses sixteen from one Q-capacity. -/
theorem capacity_bound_loss16 (P Q N : Finset β) (w : β → ℕ)
    (hP : ∀ A ∈ P, w A ≤ 25) (hQ : ∀ D ∈ Q, w D ≤ 25)
    (hN : ∀ D ∈ N, w D ≤ 30)
    (hloss : ∃ D ∈ Q, w D ≤ 9) :
    (∑ A ∈ P, w A) + (∑ D ∈ Q, w D) + (∑ D ∈ N, w D) + 16 ≤
      25 * (P.card + Q.card) + 30 * N.card := by
  obtain ⟨D, hD, hwD⟩ := hloss
  have hpoint (A : β) (hA : A ∈ Q) :
      w A + (if A = D then 16 else 0) ≤ 25 := by
    split_ifs with he
    · subst A
      omega
    · have := hQ A hA
      omega
  have hQs := sum_le_sum (s := Q) hpoint
  have hPs := sum_le_sum (s := P) hP
  have hNs := sum_le_sum (s := N) hN
  simp [sum_add_distrib, hD] at hQs
  simp only [sum_const, Nat.nsmul_eq_mul] at hPs hNs
  omega

/-- The ordinary capacity count gives the saturated cross-pair lower bound. -/
theorem cross_count_lower {n m S s : ℕ} (hparts : m + n = 5)
    (hcapacity : S ≤ 25 * (n + 4) + 30 * m) (hfloor : 243 ≤ S + s) :
    5 * n - 7 ≤ s := by
  omega

/-- The sixteen-unit loss is incompatible even with the first assignment bound. -/
theorem no_second_partner_arithmetic {n m S s : ℕ} (hparts : m + n = 5)
    (hcapacity : S + 16 ≤ 25 * (n + 4) + 30 * m)
    (hfloor : 243 ≤ S + s) (hassignment : s ≤ 4 * n) : False := by
  omega

/-- In one row, partners of intersection size two number at most two. -/
theorem row_partner_bound {Q R : Finset β} (I : β → ℕ)
    (hQ : Q.card = 4) (hRQ : R ⊆ Q)
    (hrow : 20 ≤ ∑ D ∈ Q, I D)
    (hsmall : ∀ D ∈ R, I D = 2) (hcap : ∀ D ∈ Q, I D ≤ 10) :
    R.card ≤ 2 := by
  have hpoint (D : β) (hD : D ∈ Q) :
      I D + (if D ∈ R then 8 else 0) ≤ 10 := by
    split_ifs with hDR
    · rw [hsmall D hDR]
    · have := hcap D hD
      omega
  have hs := sum_le_sum (s := Q) hpoint
  have hf : Q.filter (· ∈ R) = R := by
    ext D
    simp only [mem_filter]
    exact ⟨And.right, fun h => ⟨hRQ h, h⟩⟩
  have hsum : (∑ D ∈ Q, if D ∈ R then 8 else 0) = 8 * R.card := by
    rw [← sum_filter, hf]
    simp [mul_comm]
  rw [sum_add_distrib, hsum] at hs
  simp only [sum_const, Nat.nsmul_eq_mul, hQ] at hs
  omega

/-- The same four Q-blocks restrict every P-row of the injective assignment. -/
theorem assignment_card_le_twice {P Q : Finset β} {T : Finset γ}
    (f : γ → β × β) (I : β → β → ℕ)
    (hQ : Q.card = 4)
    (htarget : ∀ t ∈ T, (f t).1 ∈ P ∧ (f t).2 ∈ Q)
    (hinj : Set.InjOn f T)
    (hrow : ∀ A ∈ P, 20 ≤ ∑ D ∈ Q, I A D)
    (hsmall : ∀ t ∈ T, I (f t).1 (f t).2 = 2)
    (hcap : ∀ A ∈ P, ∀ D ∈ Q, I A D ≤ 10) :
    T.card ≤ 2 * P.card := by
  have hfiber (A : β) (hA : A ∈ P) :
      (T.filter (fun t => (f t).1 = A)).card ≤ 2 := by
    let F := T.filter (fun t => (f t).1 = A)
    let R := F.image (fun t => (f t).2)
    have hR : R ⊆ Q := by
      intro D hD
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hD
      exact (htarget t (mem_filter.mp ht).1).2
    have hsmallR : ∀ D ∈ R, I A D = 2 := by
      intro D hD
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hD
      have htA := (mem_filter.mp ht).2
      rw [← htA]
      exact hsmall t (mem_filter.mp ht).1
    have hbound : R.card ≤ 2 := row_partner_bound (I A) hQ hR
      (hrow A hA) hsmallR (hcap A hA)
    have hsecond : Set.InjOn (fun t => (f t).2) F := by
      intro t ht u hu he
      apply hinj (mem_filter.mp ht).1 (mem_filter.mp hu).1
      apply Prod.ext
      · exact (mem_filter.mp ht).2.trans (mem_filter.mp hu).2.symm
      · exact he
    have hcard : R.card = F.card := card_image_of_injOn hsecond
    rw [hcard] at hbound
    exact hbound
  have hmaps : Set.MapsTo (fun t => (f t).1) T P :=
    fun t ht => (htarget t ht).1
  rw [card_eq_sum_card_fiberwise hmaps]
  calc
    ∑ A ∈ P, (T.filter (fun t => (f t).1 = A)).card ≤ ∑ _A ∈ P, 2 :=
      sum_le_sum hfiber
    _ = 2 * P.card := by simp [mul_comm]

/-- The final shared-block bound excludes both endpoint degree cases. -/
theorem final_partner_contradiction {n s : ℕ} (hn : n = 4 ∨ n = 5)
    (hlower : 5 * n - 7 ≤ s) (hupper : s ≤ 2 * n) : False := by
  omega

end CoveringDesigns.C20_11_3
