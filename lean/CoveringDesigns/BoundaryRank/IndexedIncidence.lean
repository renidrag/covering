import CoveringDesigns.AffineCapacity.Basic
import CoveringDesigns.BoundaryRank.CloneCapacity
import CoveringDesigns.BoundaryRank.Completion

/-!
# Actual indexed incidence at a boundary

All matrices and deficits are derived from actual blocks. Equal blocks
at different indices remain separate columns. Natural excesses are cast
only after establishing the relevant floors.
-/
namespace CoveringDesigns.BoundaryIncidence
open Finset Matrix AffineCapacity BoundaryRank

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]

def lowPoints (B : ι → Finset α) (r : ℕ) : Finset α :=
  univ.filter fun x => indexedDegree B x = r

abbrev Low (B : ι → Finset α) (r : ℕ) := ↥(lowPoints B r)

def highPoints (B : ι → Finset α) (r : ℕ) : Finset α :=
  univ \ lowPoints B r

def excess (B : ι → Finset α) (lam : ℕ) (x y : α) : ℕ :=
  if x = y then 0 else indexedSubsetDegree B {x, y} - lam

def deficit (B : ι → Finset α) (r lam : ℕ) (x : Low B r) : ℕ :=
  ∑ y ∈ highPoints B r, excess B lam x.val y

def positiveCount (B : ι → Finset α) (r lam : ℕ) : ℕ :=
  (univ.filter fun x : Low B r => 0 < deficit B r lam x).card

def eta (B : ι → Finset α) (r : ℕ) : ℕ :=
  ∑ y ∈ highPoints B r, (indexedDegree B y - (r+1))

def regularPoints (B : ι → Finset α) (r lam : ℕ) : Finset α :=
  (highPoints B r).filter fun y => indexedDegree B y = r+1 ∧
    ∀ x : Low B r, indexedSubsetDegree B {x.val, y} = lam

def incidence (B : ι → Finset α) (r : ℕ) : Matrix (Low B r) ι ℝ :=
  fun x => row B x.val

def excessMatrix (B : ι → Finset α) (r lam : ℕ) : Matrix (Low B r) (Low B r) ℝ :=
  fun x y => (excess B lam x.val y.val : ℝ)

@[simp] theorem low_degree (B : ι → Finset α) (r : ℕ) (x : Low B r) :
    indexedDegree B x.val = r := (mem_filter.mp x.property).2

theorem high_degree (B : ι → Finset α) (r : ℕ)
    (hdeg : ∀ x, r ≤ indexedDegree B x) {y : α} (hy : y ∈ highPoints B r) :
    r+1 ≤ indexedDegree B y := by
  have hn : indexedDegree B y ≠ r := by simpa [highPoints, lowPoints] using hy
  have := hdeg y
  omega

theorem low_ne_high (B : ι → Finset α) (r : ℕ) (x : Low B r)
    {y : α} (hy : y ∈ highPoints B r) : x.val ≠ y := by
  intro he
  exact (mem_sdiff.mp hy).2 (he ▸ x.property)

@[simp] theorem pair_self (B : ι → Finset α) (x : α) :
    indexedSubsetDegree B {x, x} = indexedDegree B x := by
  simp [indexedSubsetDegree, indexedDegree]

@[simp] theorem singleton_degree (B : ι → Finset α) (x : α) :
    indexedSubsetDegree B {x} = indexedDegree B x := by
  simp [indexedSubsetDegree, indexedDegree]

theorem pair_comm (B : ι → Finset α) (x y : α) :
    indexedSubsetDegree B {x, y} = indexedSubsetDegree B {y, x} := by
  rw [Finset.pair_comm x y]

theorem row_binary (B : ι → Finset α) (x : α) (i : ι) :
    row B x i = 0 ∨ row B x i = 1 := by
  by_cases hx : x ∈ B i <;> simp [AffineCapacity.row, hx]

theorem row_sum (B : ι → Finset α) (x : α) :
    (∑ i, row B x i) = (indexedDegree B x : ℝ) := by
  simp only [AffineCapacity.row, indexedDegree, card_eq_sum_ones, sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem row_dot (B : ι → Finset α) (x y : α) :
    (∑ i, row B x i * row B y i) = (indexedSubsetDegree B {x, y} : ℝ) := by
  simp only [AffineCapacity.row, indexedSubsetDegree, card_eq_sum_ones, sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    insert_subset_iff, singleton_subset_iff]
  apply sum_congr rfl
  intro i _
  by_cases hx : x ∈ B i <;> by_cases hy : y ∈ B i <;> simp [hx, hy]

theorem degree_sum (B : ι → Finset α) {k : ℕ}
    (hsize : ∀ i, (B i).card = k) :
    (∑ x, indexedDegree B x) = k * Fintype.card ι := by
  classical
  simp only [indexedDegree, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp [hsize, Nat.mul_comm]

theorem excess_cast (B : ι → Finset α) (lam : ℕ)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x, y}) (x y : α) :
    (excess B lam x y : ℝ) = (indexedSubsetDegree B {x,y} : ℝ) - lam -
      (if x = y then (indexedDegree B x : ℝ) - lam else 0) := by
  by_cases he : x = y
  · subst y
    simp [excess]
  · simp [excess, he, Nat.cast_sub (hpair x y he)]

theorem total_excess (B : ι → Finset α) {k r lam : ℕ}
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y})
    (hboundary : (r : ℝ) * (k-1) - lam * (Fintype.card α - 1) = r-lam)
    (x : Low B r) :
    (∑ y, (excess B lam x.val y : ℝ)) = (r : ℝ)-lam := by
  have hs : (∑ y, (indexedSubsetDegree B {x.val,y} : ℝ)) = (k : ℝ)*r := by
    exact_mod_cast (indexed_pair_sum_of_uniform B hsize x.val).trans
      (congrArg (k * ·) (low_degree B r x))
  simp_rw [excess_cast B lam hpair]
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    sum_ite_eq, mem_univ, ite_true, low_degree]
  rw [hs]
  nlinarith [hboundary]

/-- The exact boundary deficit identity, derived from block sizes and
pair floors, rather than assumed for a supplied matrix. -/
theorem balance (B : ι → Finset α) {k r lam : ℕ}
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y})
    (hboundary : (r : ℝ) * (k-1) - lam * (Fintype.card α - 1) = r-lam)
    (x : Low B r) :
    (∑ y, excessMatrix B r lam x y) + (deficit B r lam x : ℝ) = r-lam := by
  rw [deficit, Nat.cast_sum]
  simp only [highPoints, sum_sdiff_eq_sub (subset_univ _), excessMatrix]
  rw [sum_coe_sort (lowPoints B r) (fun y => (excess B lam x.val y : ℝ))]
  rw [total_excess B hsize hpair hboundary x]
  ring

theorem gram (B : ι → Finset α) {r lam : ℕ}
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y}) :
    incidence B r * (incidence B r).transpose =
      Matrix.diagonal (fun _ => (r : ℝ)-lam) + excessMatrix B r lam +
        Matrix.of (fun _ _ => (lam : ℝ)) := by
  classical
  ext x y
  change (∑ i, row B x.val i * row B y.val i) = _
  rw [row_dot]
  by_cases hxy : x = y
  · subst y
    simp [excessMatrix, excess, low_degree]
  · have hv : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
    simp [Matrix.diagonal_apply, hxy, excessMatrix, excess, hv,
      Nat.cast_sub (hpair x.val y.val hv)]

/-- Actual rank, centering and positive-deficit budget at the boundary. -/
theorem completion (B : ι → Finset α) {k r lam : ℕ}
    (hb : 0 < Fintype.card ι) (hlr : lam < r)
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y})
    (hboundary : (r : ℝ) * (k-1) - lam * (Fintype.card α - 1) = r-lam)
    (hcenter : (r : ℝ)^2 ≤ (Fintype.card ι : ℝ) * lam) :
    (centered (incidence B r) r).rank = (incidence B r).rank ∧
      centered (incidence B r) r *ᵥ (fun _ => (1 : ℝ)) = 0 ∧
      1 ≤ Fintype.card ι - (incidence B r).rank ∧
      (lowPoints B r).card + positiveCount B r lam ≤ 2 * (incidence B r).rank := by
  classical
  have hc := centered_completion (incidence B r) r ((r : ℝ)-lam) lam
    (excessMatrix B r lam) (fun x => (deficit B r lam x : ℝ))
    (sub_pos.mpr (by exact_mod_cast hlr)) (by positivity) hb
    (by intro x y; simp [excessMatrix, excess, eq_comm, pair_comm B])
    (by intro x y; exact Nat.cast_nonneg _) (by intro x; simp [excessMatrix, excess])
    (by intro x; exact Nat.cast_nonneg _)
    (balance B hsize hpair hboundary)
    (by intro x; exact (row_sum B x.val).trans (by rw [low_degree]))
    (gram B hpair) hcenter
  simpa only [Fintype.card_coe, Nat.cast_pos, positiveCount] using hc

/-- All incidence excesses are explicitly retained in the degree count. -/
theorem degree_balance (B : ι → Finset α) {k r : ℕ}
    (hsize : ∀ i, (B i).card = k) (hdeg : ∀ x, r ≤ indexedDegree B x) :
    k * Fintype.card ι + (lowPoints B r).card =
      (r+1) * Fintype.card α + eta B r := by
  classical
  have hp (y : α) : indexedDegree B y + (if y ∈ lowPoints B r then 1 else 0) =
      r+1 + (if y ∈ highPoints B r then indexedDegree B y - (r+1) else 0) := by
    by_cases hy : y ∈ lowPoints B r
    · have hd := (mem_filter.mp hy).2
      simp [highPoints, hy, hd]
    · have hh : y ∈ highPoints B r := by simp [highPoints, hy]
      have hd := high_degree B r hdeg hh
      simp only [if_neg hy, if_pos hh]
      omega
  have hs := sum_congr rfl (fun y (_ : y ∈ (univ : Finset α)) => hp y)
  simpa [sum_add_distrib, degree_sum B hsize, ← sum_filter, eta, Nat.mul_comm] using hs

theorem regular_degree (B : ι → Finset α) (r lam : ℕ)
    {y : α} (hy : y ∈ regularPoints B r lam) : indexedDegree B y = r+1 :=
  (mem_filter.mp hy).2.1

theorem regular_image (B : ι → Finset α) (r lam : ℕ)
    {y : α} (hy : y ∈ regularPoints B r lam) :
    incidence B r *ᵥ row B y = fun _ => (lam : ℝ) := by
  ext x
  change (∑ i, row B x.val i * row B y i) = _
  rw [row_dot, (mem_filter.mp hy).2.2 x]

theorem regular_centered_image (B : ι → Finset α) (r lam : ℕ)
    {y : α} (hy : y ∈ regularPoints B r lam) :
    centered (incidence B r) r *ᵥ row B y =
      fun _ => (lam : ℝ) - (r / (Fintype.card ι : ℝ)) * (r+1) := by
  rw [centered, Matrix.sub_mulVec, regular_image B r lam hy]
  funext x
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [← mul_sum, row_sum, regular_degree B r lam hy]
  simp

end CoveringDesigns.BoundaryIncidence
