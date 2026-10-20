import CoveringDesigns.Foundations.Intersecting

/-!
# Capacity of points with a common actual block support

In a uniform indexed incidence system, a class of degree-`h` points with
identical occurrence supports consumes `h` incidences per class member.
Every point outside the class requires at least `lam` incidences with a
representative. Counting in its incident blocks gives the division-free
capacity bound. Equal blocks at distinct indices remain distinct occurrences.
Formalisation: Rob Gardiner with AI assistance.
-/

namespace CoveringDesigns.BoundaryRank

open Finset

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]

/-- Count all companions of a point, including the point itself, in a
uniform indexed incidence system. -/
theorem indexed_pair_sum_of_uniform (B : ι → Finset α) {k : ℕ}
    (hsize : ∀ i, (B i).card = k) (x : α) :
    (∑ y, indexedSubsetDegree B {x, y}) = k * indexedDegree B x := by
  classical
  simp only [indexedSubsetDegree, indexedDegree, card_eq_sum_ones, sum_filter,
    insert_subset_iff, singleton_subset_iff]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro i _
  by_cases hx : x ∈ B i
  · simp [hx, hsize i]
  · simp [hx]

/-- Capacity of one actual support class. Only pair multiplicities from
the representative to points outside the class are needed. The additive
form avoids truncated natural subtraction and includes degree zero. -/
theorem indexed_clone_capacity_at (B : ι → Finset α) (F : Finset α)
    {k h lam : ℕ} (hsize : ∀ i, (B i).card = k) (x : α)
    (hdegree : indexedDegree B x = h)
    (hclone : ∀ y ∈ F, ∀ i, x ∈ B i ↔ y ∈ B i)
    (hpair : ∀ y, y ∉ F → lam ≤ indexedSubsetDegree B {x, y}) :
    lam * Fintype.card α + h * F.card ≤ h * k + lam * F.card := by
  classical
  have hinside (y : α) (hy : y ∈ F) : indexedSubsetDegree B {x, y} = h := by
    rw [← hdegree]
    unfold indexedSubsetDegree indexedDegree
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, insert_subset_iff,
      singleton_subset_iff]
    exact ⟨fun hi => hi.1, fun hi => ⟨hi, (hclone y hy i).mp hi⟩⟩
  have hpoint (y : α) :
      lam + (if y ∈ F then h else 0) ≤
        indexedSubsetDegree B {x, y} + if y ∈ F then lam else 0 := by
    by_cases hy : y ∈ F
    · simp [hy, hinside y hy, Nat.add_comm]
    · simpa [hy] using hpair y hy
  have hsum := sum_le_sum (s := (univ : Finset α)) (fun y _ => hpoint y)
  have hcount (n : ℕ) : (∑ y : α, if y ∈ F then n else 0) = F.card * n := by
    simp
  simpa only [sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul,
    hcount, indexed_pair_sum_of_uniform B hsize x, hdegree,
    Nat.mul_comm] using hsum

/-- A nonempty class of points with identical occurrence supports obeys
the clone capacity bound in every uniform indexed pair multicover. -/
theorem indexed_clone_capacity (B : ι → Finset α) (F : Finset α)
    {k h lam : ℕ} (hsize : ∀ i, (B i).card = k) (hF : F.Nonempty)
    (hdegree : ∀ x ∈ F, indexedDegree B x = h)
    (hclone : ∀ x ∈ F, ∀ y ∈ F, ∀ i, x ∈ B i ↔ y ∈ B i)
    (hpair : ∀ x y, x ≠ y → lam ≤ indexedSubsetDegree B {x, y}) :
    lam * Fintype.card α + h * F.card ≤ h * k + lam * F.card := by
  obtain ⟨x, hx⟩ := hF
  apply indexed_clone_capacity_at B F hsize x (hdegree x hx) (hclone x hx)
  intro y hy
  exact hpair x y (fun hxy => hy (hxy ▸ hx))

/-- In a threefold pair cover of 32 points by 17-subsets, any
degree-seven actual support class has at most five points. -/
theorem indexed_clone_card_le_five (B : ι → Finset α) (F : Finset α)
    (hv : Fintype.card α = 32) (hsize : ∀ i, (B i).card = 17)
    (hdegree : ∀ x ∈ F, indexedDegree B x = 7)
    (hclone : ∀ x ∈ F, ∀ y ∈ F, ∀ i, x ∈ B i ↔ y ∈ B i)
    (hpair : ∀ x y, x ≠ y → 3 ≤ indexedSubsetDegree B {x, y}) :
    F.card ≤ 5 := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  have hcap := indexed_clone_capacity B F hsize hF hdegree hclone hpair
  rw [hv] at hcap
  omega

/-- In a threefold pair cover of 68 points by 35-subsets, any
degree-seven actual support class has at most ten points. -/
theorem indexed_clone_card_le_ten (B : ι → Finset α) (F : Finset α)
    (hv : Fintype.card α = 68) (hsize : ∀ i, (B i).card = 35)
    (hdegree : ∀ x ∈ F, indexedDegree B x = 7)
    (hclone : ∀ x ∈ F, ∀ y ∈ F, ∀ i, x ∈ B i ↔ y ∈ B i)
    (hpair : ∀ x y, x ≠ y → 3 ≤ indexedSubsetDegree B {x, y}) :
    F.card ≤ 10 := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  have hcap := indexed_clone_capacity B F hsize hF hdegree hclone hpair
  rw [hv] at hcap
  omega

omit [Fintype α] in
private theorem indexedDegree_family (C : Family α) (x : α) :
    indexedDegree (fun B : C => B.val) x = degree C x := by
  classical
  simp only [indexedDegree, degree, star, card_eq_sum_ones, sum_filter]
  exact sum_coe_sort C (fun B => if x ∈ B then (1 : ℕ) else 0)

omit [Fintype α] in
private theorem indexedSubsetDegree_family_pair (C : Family α) (x y : α) :
    indexedSubsetDegree (fun B : C => B.val) {x, y} = degree (star C x) y := by
  classical
  simp only [indexedSubsetDegree, degree, star, card_eq_sum_ones, sum_filter,
    insert_subset_iff, singleton_subset_iff]
  rw [sum_coe_sort C (fun B => if x ∈ B ∧ y ∈ B then (1 : ℕ) else 0)]
  apply sum_congr rfl
  intro B _
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [hx, hy]

/-- Ordinary-family version of the indexed clone capacity bound. -/
theorem family_clone_capacity (C : Family α) (F : Finset α)
    {k h lam : ℕ} (hsize : Uniform C k) (hF : F.Nonempty)
    (hdegree : ∀ x ∈ F, degree C x = h)
    (hclone : ∀ x ∈ F, ∀ y ∈ F, ∀ B ∈ C, x ∈ B ↔ y ∈ B)
    (hpair : ∀ x y, x ≠ y → lam ≤ degree (star C x) y) :
    lam * Fintype.card α + h * F.card ≤ h * k + lam * F.card := by
  apply indexed_clone_capacity (fun B : C => B.val) F
    (fun B => hsize B.val B.property) hF
  · intro x hx
    simpa only [indexedDegree_family] using hdegree x hx
  · intro x hx y hy B
    exact hclone x hx y hy B.val B.property
  · intro x y hxy
    simpa only [indexedSubsetDegree_family_pair] using hpair x y hxy

/-- Every degree-seven support class in an ordinary threefold pair cover
of 32 points by 17-subsets contains at most five points. -/
theorem clone_card_le_five (C : Family α) (F : Finset α)
    (hv : Fintype.card α = 32) (hsize : Uniform C 17)
    (hdegree : ∀ x ∈ F, degree C x = 7)
    (hclone : ∀ x ∈ F, ∀ y ∈ F, ∀ B ∈ C, x ∈ B ↔ y ∈ B)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    F.card ≤ 5 := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  have hcap := family_clone_capacity C F hsize hF hdegree hclone hpair
  rw [hv] at hcap
  omega

/-- Every degree-seven support class in an ordinary threefold pair cover
of 68 points by 35-subsets contains at most ten points. -/
theorem clone_card_le_ten (C : Family α) (F : Finset α)
    (hv : Fintype.card α = 68) (hsize : Uniform C 35)
    (hdegree : ∀ x ∈ F, degree C x = 7)
    (hclone : ∀ x ∈ F, ∀ y ∈ F, ∀ B ∈ C, x ∈ B ↔ y ∈ B)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y) :
    F.card ≤ 10 := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  have hcap := family_clone_capacity C F hsize hF hdegree hclone hpair
  rw [hv] at hcap
  omega

/-- A uniform fibre bound converts a bound on distinct support patterns
into a bound on point occurrences. Empty point sets are included. -/
theorem card_le_mul_image_card {β γ : Type*} [DecidableEq γ]
    (F : Finset β) (f : β → γ) {g : ℕ}
    (hfibre : ∀ s ∈ F.image f, (F.filter fun x => f x = s).card ≤ g) :
    F.card ≤ g * (F.image f).card := by
  classical
  rw [card_eq_sum_card_image f F]
  calc
    _ ≤ ∑ _ ∈ F.image f, g := sum_le_sum hfibre
    _ = _ := by simp [Nat.mul_comm]

end CoveringDesigns.BoundaryRank
