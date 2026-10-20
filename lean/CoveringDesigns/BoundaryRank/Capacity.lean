import CoveringDesigns.BoundaryRank.IndexedCounting
import CoveringDesigns.BoundaryRank.SupportDimension
import CoveringDesigns.BoundaryRank.SupportCapacity

/-!
# From actual boundary incidence to two capacity obstructions

The final contracts take block sizes, actual point/pair floors and the
boundary/centering scalar identities. Rank, regular-point counts and
support dimensions are conclusions. No component classification is used.
-/
namespace CoveringDesigns.BoundaryIncidence
open Finset Matrix BoundaryRank AffineCapacity
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]

theorem row_membership_eq (B : ι → Finset α) {x y : α}
    (he : row B x = row B y) (i : ι) : x ∈ B i ↔ y ∈ B i := by
  rw [← row_eq_one_iff, ← row_eq_one_iff, congrFun he i]

/-- The number of distinct actual regular supports, for arbitrary corank. -/
theorem supports_le (B : ι → Finset α) {k r lam : ℕ}
    (hb : 0 < Fintype.card ι) (hlr : lam < r)
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y})
    (hboundary : (r : ℝ) * (k-1) - lam * (Fintype.card α - 1) = r-lam)
    (hcenter : (r : ℝ)^2 ≤ (Fintype.card ι : ℝ) * lam) :
    ((regularPoints B r lam).image (row B)).card ≤
      2 ^ (Fintype.card ι - (incidence B r).rank - 1) := by
  classical
  obtain ⟨hr, hz, _, _⟩ := completion B hb hlr hsize hpair hboundary hcenter
  have hs := SupportDimension.binary_support_card_le (centered (incidence B r) r) hb hz
    (regularPoints B r lam) (row B) (fun x _ i => row_binary B x i)
    (fun _ => (lam : ℝ) - (r / (Fintype.card ι : ℝ)) * (r+1)) (r+1)
    (fun x hx => regular_centered_image B r lam hx)
    (by intro x hx; rw [row_sum, regular_degree B r lam hx]; simp)
  rwa [hr] at hs

/-- Affine dimension of actual regular supports. -/
theorem dimension_le (B : ι → Finset α) {k r lam : ℕ}
    (hb : 0 < Fintype.card ι) (hlr : lam < r)
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y})
    (hboundary : (r : ℝ) * (k-1) - lam * (Fintype.card α - 1) = r-lam)
    (hcenter : (r : ℝ)^2 ≤ (Fintype.card ι : ℝ) * lam) :
    dimension (row B '' (regularPoints B r lam : Set α)) ≤
      Fintype.card ι - (incidence B r).rank - 1 := by
  obtain ⟨hr, hz, _, _⟩ := completion B hb hlr hsize hpair hboundary hcenter
  have hd := SupportDimension.family_dimension_le (centered (incidence B r) r) hb hz
    (regularPoints B r lam) (row B)
    (fun _ => (lam : ℝ) - (r / (Fintype.card ι : ℝ)) * (r+1)) (r+1)
    (fun x hx => regular_centered_image B r lam hx)
    (by intro x hx; rw [row_sum, regular_degree B r lam hx]; simp)
  rwa [hr] at hd

/-- Clone capacity combined with the distinct-support bound.
The signed numerator's sign is an explicit premise in this intermediate
interface; `clone_obstruction` derives it from a positive lower count. -/
theorem clone_bound (B : ι → Finset α) {k r lam : ℕ}
    (hb : 0 < Fintype.card ι) (hlr : lam < r)
    (hsize : ∀ i, (B i).card = k)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y})
    (hboundary : (r : ℝ) * (k-1) - lam * (Fintype.card α - 1) = r-lam)
    (hcenter : (r : ℝ)^2 ≤ (Fintype.card ι : ℝ) * lam)
    (hA : 0 ≤ ((r : ℝ)+1)*k - lam*Fintype.card α) :
    ((r : ℝ)+1-lam) * (regularPoints B r lam).card ≤
      (2 : ℝ)^(Fintype.card ι - (incidence B r).rank - 1) *
        (((r : ℝ)+1)*k - lam*Fintype.card α) := by
  classical
  have hc := SupportCapacity.of_support_bound B (regularPoints B r lam) (row B) hsize
    (fun x hx => regular_degree B r lam hx)
    (fun _ _ _ _ he => row_membership_eq B he) hpair
    (supports_le B hb hlr hsize hpair hboundary hcenter)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hA)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using hc

/-- The full clone obstruction for actual boundary incidence. A positive
lower count forces a nonempty fibre and hence a positive numerator. -/
theorem clone_obstruction (B : ι → Finset α) {k r lam : ℕ}
    (hb : 0 < Fintype.card ι) (hlr : lam < r)
    (hsize : ∀ i, (B i).card = k) (hdeg : ∀ x, r ≤ indexedDegree B x)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y})
    (hboundary : (r : ℝ) * (k-1) - lam * (Fintype.card α - 1) = r-lam)
    (hcenter : (r : ℝ)^2 ≤ (Fintype.card ι : ℝ) * lam)
    (hQ : 0 < lowerCount (Fintype.card α) (Fintype.card ι) k r lam
      (eta B r) (Fintype.card ι - (incidence B r).rank)) :
    ((r : ℝ)+1-lam) ≤ ((r : ℝ)+1)*k - lam*Fintype.card α ∧
    ((r : ℝ)+1-lam) *
      lowerCount (Fintype.card α) (Fintype.card ι) k r lam
        (eta B r) (Fintype.card ι - (incidence B r).rank) ≤
      (2 : ℝ)^(Fintype.card ι - (incidence B r).rank - 1) *
        (((r : ℝ)+1)*k - lam*Fintype.card α) := by
  classical
  have hl := lowerCount_le B hb hlr hsize hdeg hpair hboundary hcenter
  have hn : (regularPoints B r lam).Nonempty := by
    apply card_pos.mp
    have hp : (0 : ℝ) < (regularPoints B r lam).card := lt_of_lt_of_le hQ hl
    exact_mod_cast hp
  obtain ⟨x, hx⟩ := hn
  have hnum := SupportCapacity.numerator_pos B {x} hsize (singleton_nonempty x)
    (by intro y hy; simpa only [mem_singleton.mp hy] using regular_degree B r lam hx)
    (by
      intro y hy z hz
      have hy' := mem_singleton.mp hy
      have hz' := mem_singleton.mp hz
      subst y
      subst z
      exact fun _ => Iff.rfl)
    hpair (show lam < r+1 by omega)
  have hnumR : ((r : ℝ)+1-lam) ≤ ((r : ℝ)+1)*k - lam*Fintype.card α := by
    simpa only [Nat.cast_add, Nat.cast_one] using hnum
  have hq : 0 ≤ (r : ℝ)+1-lam := by
    have : (lam : ℝ) < r := by exact_mod_cast hlr
    linarith
  refine ⟨hnumR, ?_⟩
  exact (mul_le_mul_of_nonneg_left hl hq).trans
    (clone_bound B hb hlr hsize hpair hboundary hcenter (hq.trans hnumR))

/-- The other capacity mechanism: actual covering strength forces a common
block. This final Q bound derives its own rank and selection estimates. -/
theorem covering_obstruction (B : ι → Finset α) {k r lam t : ℕ}
    (hb : 0 < Fintype.card ι) (hlr : lam < r)
    (hsize : ∀ i, (B i).card = k) (hdeg : ∀ x, r ≤ indexedDegree B x)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x,y})
    (hboundary : (r : ℝ) * (k-1) - lam * (Fintype.card α - 1) = r-lam)
    (hcenter : (r : ℝ)^2 ≤ (Fintype.card ι : ℝ) * lam)
    (ht : 1 ≤ t) (htv : t ≤ Fintype.card α)
    (hcover : ∀ U : Finset α, U.card = t → ∃ i, U ⊆ B i)
    (hu : Fintype.card ι - (incidence B r).rank ≤ t) :
    lowerCount (Fintype.card α) (Fintype.card ι) k r lam
      (eta B r) (Fintype.card ι - (incidence B r).rank) ≤ k := by
  have hl := lowerCount_le B hb hlr hsize hdeg hpair hboundary hcenter
  have hd := dimension_le B hb hlr hsize hpair hboundary hcenter
  have hp := (completion B hb hlr hsize hpair hboundary hcenter).2.2.1
  have hc := card_le_of_dimension_lt B (regularPoints B r lam) ht htv hcover
    (fun i => (hsize i).le) (by omega)
  exact hl.trans (by exact_mod_cast hc)

end CoveringDesigns.BoundaryIncidence
