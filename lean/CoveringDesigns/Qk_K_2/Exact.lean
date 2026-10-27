import CoveringDesigns.Qk_K_2.Bounds
import CoveringDesigns.Qk_K_2.Construction

namespace CoveringDesigns.Qk_K_2
open PairDivisibility PairEquality
universe u

private theorem assemble {α : Type*} [Fintype α] {k n : ℕ}
    (hu : ∃ C : Family α, IsCover C k 2 ∧ C.card ≤ n)
    (hl : ∀ C : Family α, IsCover C k 2 → n ≤ C.card) :
    (∃ C : Family α, IsCover C k 2 ∧ C.card = n) ∧
      (∀ C : Family α, IsCover C k 2 → n ≤ C.card) := by
  obtain ⟨C,hC,hb⟩ := hu
  exact ⟨⟨C,hC,Nat.le_antisymm hb (hl C hC)⟩,hl⟩

/-- Divisible affine family, with exact ordinary attainment on any point type. -/
theorem affine_exact {α : Type*} [Fintype α] {q k : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hk : q ≤ k)
    (hd : q ∣ k) (hv : Fintype.card α = q*k) :
    (∃ C : Family α, IsCover C k 2 ∧ C.card = q*(q+1)) ∧
      (∀ C : Family α, IsCover C k 2 → q*(q+1) ≤ C.card) := by
  classical
  apply assemble
  · obtain ⟨m,rfl⟩ := hd
    have hm : 0 < m := by nlinarith
    obtain ⟨C,hC,hb⟩ := AffineConstructions.lemma8 (q := q) (m := m) (t := 2)
      hq hm (by decide) hv (by simp; nlinarith) (by simp [pow_two]; nlinarith)
    refine ⟨C,by simpa [Nat.mul_comm] using hC,?_⟩
    have he : AffineConstructions.blockBound q 2 = q*(q+1) := by
      rw [AffineConstructions.blockBound,AffineConstructions.quotient_eq_sum hq]
      simp [Finset.sum_range_succ,Nat.add_comm]
    exact he ▸ hb
  · intro C hC
    simpa using incidence_floor hq4 hk hv ((Multicover.ofFamily_isCover_one C k 2).mpr hC)

/-- Exact throughout the open-left weighted interval; no twisted-plane premise. -/
theorem weighted_open_exact {α : Type*} [Fintype α] {q u r v : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hr : 1 ≤ r) (hrq : r < q) (hru : r ≤ u)
    (hv : Fintype.card α = v) (hlo : q*(q*u+r) < v) (hhi : v ≤ q*(q*u+r)+r) :
    (∃ C : Family α, IsCover C (q*u+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*u+r) 2 → q*q+q+1 ≤ C.card) := by
  apply assemble (weighted_interval hq (by omega) hr hru hv hlo.le hhi)
  intro C hC
  have h := open_floor hq4 (show q ≤ q*u+r by nlinarith) (by omega) hC
  simpa only [Nat.mul_add,Nat.mul_one] using h

private theorem weighted_not_dvd {q u r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ¬ q ∣ q*u+r := by
  intro h
  have hd : q ∣ r := (Nat.dvd_add_iff_right (dvd_mul_right q u)).mpr h
  exact Nat.not_dvd_of_pos_of_lt (by omega) hrq hd

/-- Endpoint exactness by the existing general divisibility obstruction. -/
theorem weighted_endpoint_divisibility {α : Type*} [Fintype α] {q u r : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hr : 1 ≤ r) (hrq : r < q) (hru : r ≤ u)
    (hv : Fintype.card α = q*(q*u+r)) (hnd : ¬ (q+1) ∣ q*u+r) :
    (∃ C : Family α, IsCover C (q*u+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*u+r) 2 → q*q+q+1 ≤ C.card) := by
  apply assemble (weighted_interval hq (by omega) hr hru hv (by omega) (by omega))
  intro C hC
  have h := family_improved_floor hq4 (show q ≤ q*u+r by nlinarith) hv hC
    (weighted_not_dvd hr hrq) hnd
  simpa only [Nat.mul_add,Nat.mul_one] using h

/-- Endpoint exactness when a proved twisted-plane exclusion is available. -/
theorem weighted_endpoint_exclusion {α : Type u} [Fintype α] {q a r : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hr : 1 ≤ r) (hrq : r < q) (hra : r ≤ a)
    (hv : Fintype.card α = q*(q*a+r))
    (hn : ∀ {I : Type u} [Fintype I] [DecidableEq I] {H : Finset (Finset I)},
      IsTwistedPlane q H → False) :
    (∃ C : Family α, IsCover C (q*a+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*a+r) 2 → q*q+q+1 ≤ C.card) := by
  classical
  apply assemble (weighted_interval hq (by omega) hr hra hv (by omega) (by omega))
  intro C hC
  have h := indexed_exclusion hq4 (show q ≤ q*a+r by nlinarith) hv
    ((Multicover.ofFamily_isCover_one C (q*a+r) 2).mpr hC)
    (weighted_not_dvd hr hrq) (fun T => hn T)
  simpa only [Nat.mul_add,Nat.mul_one,Fintype.card_coe] using h

end CoveringDesigns.Qk_K_2
