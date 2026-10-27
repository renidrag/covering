import CoveringDesigns.Qk_K_2.Exact

/-! Full weighted intervals, including r≥q, and separately qualified endpoints. -/
namespace CoveringDesigns.PairConsequences
open Schoenheim PairEquality PairDivisibility
universe u

private theorem four_prime_power : IsPrimePow 4 := by
  exact (isPrimePow_nat_iff 4).mpr ⟨2,2,by decide,by decide,by decide⟩

/-- The elementary count needs only q≥2, independent of the equality geometry. -/
theorem indexed_pair_incidence {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 2 ≤ q) (hk : q ≤ k)
    (hv : q*k ≤ Fintype.card X) (hB : Multicover.IsCover B k 2 1) :
    Fintype.card X*(q+1) ≤ k*Fintype.card I := by
  have hk0 : 0 < k := by omega
  have hk1 : 0 < k-1 := by omega
  have hkx : k ≤ Fintype.card X := by nlinarith
  have hl := Multicover.lower_bound (by omega : 2 ≤ k) hkx hB
  simp only [Multicover.bound_succ,Multicover.bound_zero,Nat.mul_one] at hl
  have hd : q+1 ≤ ceilDiv (Fintype.card X-1) (k-1) := by
    by_contra hn
    have hh := (ceilDiv_le_iff hk1).mp (show ceilDiv (Fintype.card X-1) (k-1) ≤ q by omega)
    have hsub : k-1+1 = k := by omega
    have hx : Fintype.card X-1+1 = Fintype.card X := by omega
    nlinarith
  exact (Nat.mul_le_mul_left _ hd).trans ((ceilDiv_le_iff hk0).mp hl)

theorem indexed_pair_floor {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 2 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hB : Multicover.IsCover B k 2 1) :
    q*(q+1) ≤ Fintype.card I := by
  have h := indexed_pair_incidence hq hk hv.ge hB
  rw [hv] at h
  nlinarith

theorem indexed_open_floor {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 2 ≤ q) (hk : q ≤ k)
    (hv : q*k < Fintype.card X) (hB : Multicover.IsCover B k 2 1) :
    q*(q+1)+1 ≤ Fintype.card I := by
  have h := indexed_pair_incidence hq hk hv.le hB
  have hs := Nat.mul_lt_mul_of_pos_right hv (show 0 < q+1 by omega)
  nlinarith

theorem weighted_open_exact {α : Type*} [Fintype α] {q a r v : ℕ}
    (hq : IsPrimePow q) (hq2 : 2 ≤ q) (hr : 1 ≤ r) (hra : r ≤ a)
    (hv : Fintype.card α = v) (hlo : q*(q*a+r) < v) (hhi : v ≤ q*(q*a+r)+r) :
    (∃ C : Family α, IsCover C (q*a+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*a+r) 2 → q*q+q+1 ≤ C.card) := by
  classical
  have hl (C : Family α) (hC : IsCover C (q*a+r) 2) : q*q+q+1 ≤ C.card := by
    have h := indexed_open_floor hq2 (show q ≤ q*a+r by nlinarith)
      (by omega : q*(q*a+r) < Fintype.card α)
      ((Multicover.ofFamily_isCover_one C (q*a+r) 2).mpr hC)
    simpa [Nat.mul_add] using h
  obtain ⟨C,hC,hb⟩ := Qk_K_2.weighted_interval hq hq2 hr hra hv hlo.le hhi
  exact ⟨⟨C,hC,Nat.le_antisymm hb (hl C hC)⟩,hl⟩

theorem affine_exact {α : Type*} [Fintype α] {q k : ℕ}
    (hq : IsPrimePow q) (hq2 : 2 ≤ q) (hk : q ≤ k)
    (hd : q ∣ k) (hv : Fintype.card α = q*k) :
    (∃ C : Family α, IsCover C k 2 ∧ C.card = q*(q+1)) ∧
      (∀ C : Family α, IsCover C k 2 → q*(q+1) ≤ C.card) := by
  classical
  have hl (C : Family α) (hC : IsCover C k 2) : q*(q+1) ≤ C.card := by
    simpa using indexed_pair_floor hq2 hk hv ((Multicover.ofFamily_isCover_one C k 2).mpr hC)
  obtain ⟨m,rfl⟩ := hd
  have hm : 0 < m := by nlinarith
  obtain ⟨C,hC,hb⟩ := AffineConstructions.lemma8 (q := q) (m := m) (t := 2)
    hq hm (by decide) hv (by simp; nlinarith) (by simp [pow_two]; nlinarith)
  have he : AffineConstructions.blockBound q 2 = q*(q+1) := by
    rw [AffineConstructions.blockBound,AffineConstructions.quotient_eq_sum hq]
    simp [Finset.sum_range_succ,Nat.add_comm]
  have hc : IsCover C (q*m) 2 := by simpa [Nat.mul_comm] using hC
  exact ⟨⟨C,hc,Nat.le_antisymm (he ▸ hb) (hl C hc)⟩,hl⟩

theorem weighted_endpoint_divisibility {α : Type*} [Fintype α] {q a r : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hr : 1 ≤ r) (hra : r ≤ a)
    (hv : Fintype.card α = q*(q*a+r))
    (hnd : ¬ q ∣ q*a+r) (hnd' : ¬ (q+1) ∣ q*a+r) :
    (∃ C : Family α, IsCover C (q*a+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*a+r) 2 → q*q+q+1 ≤ C.card) := by
  have hl (C : Family α) (hC : IsCover C (q*a+r) 2) : q*q+q+1 ≤ C.card := by
    simpa [Nat.mul_add] using family_improved_floor hq4 (by nlinarith) hv hC hnd hnd'
  obtain ⟨C,hC,hb⟩ := Qk_K_2.weighted_interval hq (by omega) hr hra hv (by omega) (by omega)
  exact ⟨⟨C,hC,Nat.le_antisymm hb (hl C hC)⟩,hl⟩

theorem weighted_endpoint_exclusion {α : Type u} [Fintype α] {q a r : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hr : 1 ≤ r) (hra : r ≤ a)
    (hv : Fintype.card α = q*(q*a+r)) (hnd : ¬ q ∣ q*a+r)
    (hn : ∀ {I : Type u} [Fintype I] [DecidableEq I] {H : Finset (Finset I)},
      IsTwistedPlane q H → False) :
    (∃ C : Family α, IsCover C (q*a+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*a+r) 2 → q*q+q+1 ≤ C.card) := by
  classical
  have hl (C : Family α) (hC : IsCover C (q*a+r) 2) : q*q+q+1 ≤ C.card := by
    simpa [Nat.mul_add] using Qk_K_2.indexed_exclusion hq4 (by nlinarith) hv
      ((Multicover.ofFamily_isCover_one C (q*a+r) 2).mpr hC) hnd (fun T => hn T)
  obtain ⟨C,hC,hb⟩ := Qk_K_2.weighted_interval hq (by omega) hr hra hv (by omega) (by omega)
  exact ⟨⟨C,hC,Nat.le_antisymm hb (hl C hC)⟩,hl⟩

theorem exact_twenty_interval {α : Type*} [Fintype α] (hlo : 81 ≤ Fintype.card α)
    (hhi : Fintype.card α ≤ 84) :
    (∃ C : Family α, IsCover C 20 2 ∧ C.card = 21) ∧
      (∀ C : Family α, IsCover C 20 2 → 21 ≤ C.card) := by
  exact weighted_open_exact (q := 4) (a := 4) (r := 4)
    four_prime_power (by decide) (by decide) (by decide) rfl (by omega) hhi

theorem exact_twenty_four_interval {α : Type*} [Fintype α] (hlo : 97 ≤ Fintype.card α)
    (hhi : Fintype.card α ≤ 99) :
    (∃ C : Family α, IsCover C 24 2 ∧ C.card = 21) ∧
      (∀ C : Family α, IsCover C 24 2 → 21 ≤ C.card) := by
  exact weighted_open_exact (q := 4) (a := 5) (r := 4)
    four_prime_power (by decide) (by decide) (by decide) rfl (by omega) (by omega)

end CoveringDesigns.PairConsequences
