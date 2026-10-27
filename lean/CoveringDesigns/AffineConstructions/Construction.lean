import CoveringDesigns.AffineConstructions.Geometry
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.IsPrimePow

/-! Horsley–Singh Lemma 8 for every prime power, including nonprime powers. -/

namespace CoveringDesigns.AffineConstructions

/-- Number of affine hyperplane indices in positive dimension. -/
def blockBound (q t : ℕ) : ℕ := q * ((q^t-1)/(q-1))

theorem denominator_pos {q : ℕ} (hq : IsPrimePow q) : 0 < q-1 := by
  have := hq.two_le
  omega

theorem quotient_exact (q t : ℕ) : ((q^t-1)/(q-1))*(q-1) = q^t-1 :=
  Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one q t)

theorem quotient_eq_sum {q : ℕ} (hq : IsPrimePow q) (t : ℕ) :
    (q^t-1)/(q-1) = ∑ i ∈ Finset.range t, q^i :=
  (Nat.geomSum_eq hq.two_le t).symm

theorem strength_le_block_size {q m t : ℕ} (hq : IsPrimePow q)
    (hm : 0 < m) (ht : 0 < t) : t ≤ m*q^(t-1) := by
  have hp : t-1 < q^(t-1) := Nat.lt_pow_self hq.one_lt
  have hm' : 1*q^(t-1) ≤ m*q^(t-1) := Nat.mul_le_mul_right _ hm
  omega

theorem block_size_le_points {q m t : ℕ} (hq : IsPrimePow q) :
    m*q^(t-1) ≤ m*q^t :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq.pos (Nat.sub_le t 1))

/-- Mathlib supplies a field of each prime-power cardinality. -/
theorem exists_field {q : ℕ} (hq : IsPrimePow q) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = q := by
  obtain ⟨p, r, hp, hr, hpr⟩ := (isPrimePow_nat_iff q).mp hq
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype (GaloisField p r) := Fintype.ofFinite _
  refine ⟨GaloisField p r, inferInstance, inferInstance, ?_⟩
  rw [← Nat.card_eq_fintype_card, GaloisField.card p r hr.ne', hpr]

/-- Lemma 8 on the standard point type, assembled from its three constructions. -/
theorem lemma8_fin {q m t v : ℕ} (hq : IsPrimePow q) (_hm : 0 < m) (ht : 0 < t)
    (hkv : m*q^(t-1) ≤ v) (hv : v ≤ m*q^t) :
    ∃ C : Family (Fin v), IsCover C (m*q^(t-1)) t ∧ C.card ≤ blockBound q t := by
  obtain ⟨F, hF, hfin, hcard⟩ := exists_field hq
  let : Field F := hF
  let : Fintype F := hfin
  obtain ⟨C, hC, hn⟩ := affine_cover F ht
  obtain ⟨D, hD, hDn⟩ := blow_up (M := Fin m) hC (by
    rw [affine_points_card, hcard]
    exact (Nat.lt_pow_self hq.one_lt).le)
  have hD' : IsCover D (m*q^(t-1)) t := by simpa [hcard, Nat.mul_comm] using hD
  obtain ⟨E, hE, hEn⟩ := reduce_points (β := Fin v) hD'
    (by simpa [affine_points_card, hcard, Nat.mul_comm] using hv)
    (by simpa using hkv)
  exact ⟨E, hE, hEn.trans (hDn.trans (by simpa [blockBound, hcard] using hn))⟩

/-- Horsley–Singh Lemma 8: an ordinary covering on every finite point type
in the valid interval, with no field or construction assumed by the caller. -/
theorem lemma8 {α : Type*} [Fintype α] {q m t v : ℕ}
    (hq : IsPrimePow q) (hm : 0 < m) (ht : 0 < t) (hn : Fintype.card α = v)
    (hkv : m*q^(t-1) ≤ v) (hv : v ≤ m*q^t) :
    ∃ C : Family α, IsCover C (m*q^(t-1)) t ∧ C.card ≤ blockBound q t := by
  exact exists_cover_of_card_eq (by simpa using hn.symm) (lemma8_fin hq hm ht hkv hv)

end CoveringDesigns.AffineConstructions
