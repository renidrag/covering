import CoveringDesigns.BoundaryRank.CloneCapacity
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Sum clone capacity over actual support fibres, retaining every point.
The additive natural-number interface precedes signed rearrangement. -/
namespace CoveringDesigns.SupportCapacity
open Finset BoundaryRank

variable {α ι β : Type*} [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq β]

/-- Aggregate over a support map. It may identify different actual points;
its fibres need only imply identical indexed memberships. -/
theorem aggregate (B : ι → Finset α) (F : Finset α) (f : α → β)
    {k h lam : ℕ} (hsize : ∀ i, (B i).card = k)
    (hdegree : ∀ x ∈ F, indexedDegree B x = h)
    (hf : ∀ x ∈ F, ∀ y ∈ F, f x = f y → ∀ i, x ∈ B i ↔ y ∈ B i)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x, y}) :
    lam * Fintype.card α * (F.image f).card + h * F.card ≤
      h * k * (F.image f).card + lam * F.card := by
  classical
  have hc (s : β) (hs : s ∈ F.image f) :
      lam * Fintype.card α + h * (F.filter fun x => f x = s).card ≤
        h * k + lam * (F.filter fun x => f x = s).card := by
    apply indexed_clone_capacity B _
      hsize (by
        obtain ⟨x, hx, he⟩ := mem_image.mp hs
        exact ⟨x, mem_filter.mpr ⟨hx, he⟩⟩)
    · intro x hx
      exact hdegree x (mem_filter.mp hx).1
    · intro x hx y hy
      exact hf x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
        ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
    · exact hpair
  have hs := sum_le_sum hc
  have hpartition := card_eq_sum_card_image f F
  simpa only [sum_add_distrib, ← mul_sum, ← hpartition,
    sum_const, Nat.nsmul_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hs

/-- Signed capacity. The numerator is a real difference, never truncated
natural subtraction; the empty support image is included. -/
theorem signed_aggregate (B : ι → Finset α) (F : Finset α) (f : α → β)
    {k h lam : ℕ} (hsize : ∀ i, (B i).card = k)
    (hdegree : ∀ x ∈ F, indexedDegree B x = h)
    (hf : ∀ x ∈ F, ∀ y ∈ F, f x = f y → ∀ i, x ∈ B i ↔ y ∈ B i)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x, y}) :
    ((h : ℝ) - lam) * F.card ≤
      (F.image f).card * ((h : ℝ) * k - lam * Fintype.card α) := by
  have hc := aggregate B F f hsize hdegree hf hpair
  have hcR : (lam : ℝ) * Fintype.card α * (F.image f).card + h * F.card ≤
      h * k * (F.image f).card + lam * F.card := by exact_mod_cast hc
  nlinarith

/-- Substitution of a support-count bound explicitly requires a
nonnegative signed numerator. No positivity of `h-lam` is needed here. -/
theorem of_support_bound (B : ι → Finset α) (F : Finset α) (f : α → β)
    {k h lam M : ℕ} (hsize : ∀ i, (B i).card = k)
    (hdegree : ∀ x ∈ F, indexedDegree B x = h)
    (hf : ∀ x ∈ F, ∀ y ∈ F, f x = f y → ∀ i, x ∈ B i ↔ y ∈ B i)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x, y})
    (hs : (F.image f).card ≤ M)
    (hA : 0 ≤ (h : ℝ) * k - lam * Fintype.card α) :
    ((h : ℝ) - lam) * F.card ≤
      M * ((h : ℝ) * k - lam * Fintype.card α) := by
  exact (signed_aggregate B F f hsize hdegree hf hpair).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hA)

/-- A nonempty class and positive degree-minus-floor force a positive
numerator. This prevents a sign-invalid support-count substitution. -/
theorem numerator_pos (B : ι → Finset α) (F : Finset α)
    {k h lam : ℕ} (hsize : ∀ i, (B i).card = k) (hF : F.Nonempty)
    (hdegree : ∀ x ∈ F, indexedDegree B x = h)
    (hclone : ∀ x ∈ F, ∀ y ∈ F, ∀ i, x ∈ B i ↔ y ∈ B i)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x, y})
    (hlh : lam < h) :
    (h : ℝ) - lam ≤ (h : ℝ) * k - lam * Fintype.card α := by
  have hc := indexed_clone_capacity B F hsize hF hdegree hclone hpair
  have hcR : (lam : ℝ) * Fintype.card α + h * F.card ≤
      h * k + lam * F.card := by exact_mod_cast hc
  have hg : (1 : ℝ) ≤ F.card := by exact_mod_cast card_pos.mpr hF
  have hq : (lam : ℝ) < h := by exact_mod_cast hlh
  nlinarith

/-- Division is justified only after proving `h > lam`. -/
theorem card_le_div_of_support_bound (B : ι → Finset α) (F : Finset α) (f : α → β)
    {k h lam M : ℕ} (hsize : ∀ i, (B i).card = k)
    (hdegree : ∀ x ∈ F, indexedDegree B x = h)
    (hf : ∀ x ∈ F, ∀ y ∈ F, f x = f y → ∀ i, x ∈ B i ↔ y ∈ B i)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x, y})
    (hs : (F.image f).card ≤ M) (hlh : lam < h)
    (hA : 0 ≤ (h : ℝ) * k - lam * Fintype.card α) :
    (F.card : ℝ) ≤ M * ((h : ℝ) * k - lam * Fintype.card α) / ((h : ℝ) - lam) := by
  apply (le_div_iff₀ (sub_pos.mpr (by exact_mod_cast hlh) :
    (0 : ℝ) < (h : ℝ) - lam)).mpr
  simpa [mul_comm] using of_support_bound B F f hsize hdegree hf hpair hs hA

end CoveringDesigns.SupportCapacity
