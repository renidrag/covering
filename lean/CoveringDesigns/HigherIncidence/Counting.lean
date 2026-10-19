import CoveringDesigns.HigherIncidence.Binomial
import CoveringDesigns.HigherIncidence.Subsets

/-! Exact general excess accounting for Horsley–Singh Lemma 3(b). -/
namespace CoveringDesigns.HigherIncidence
open Finset HorsleySingh
variable {α : Type*} [DecidableEq α]

def defect (v k s : ℕ) (b : ℕ → ℕ) : ℤ :=
  (b s : ℤ)*((k.choose s : ℤ)-1) -
    ∑ i ∈ range s, (s.choose i : ℤ)*(v-s).choose (s-i)*b (2*s-i)

def excess (C : Family α) (b : ℕ → ℕ) (X Y : Finset α) : ℤ :=
  if X=Y then 0 else (multiplicity C (X ∪ Y) : ℤ)-b (X ∪ Y).card

theorem excess_comm (C : Family α) (b : ℕ → ℕ) (X Y : Finset α) :
    excess C b X Y = excess C b Y X := by simp only [excess, union_comm X Y, eq_comm]

theorem excess_nonneg {C : Family α} {b : ℕ → ℕ} {s : ℕ}
    (hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ multiplicity C Z)
    {X Y : Finset α} (hX : X.card=s) (hY : Y.card=s) : 0 ≤ excess C b X Y := by
  by_cases he : X=Y
  · simp [excess, he]
  · have hlo : s ≤ (X ∪ Y).card := by simpa [hX] using card_le_card (subset_union_left (s₁ := X) (s₂ := Y))
    have hhi : (X ∪ Y).card ≤ 2*s := by have := card_union_le X Y; omega
    have := hb (X ∪ Y) hlo hhi
    simp only [excess, ite_eq_right he]
    omega

/-- Summing an arbitrary function of union size over the off-diagonal rows. -/
theorem off_diagonal_baseline_sum [Fintype α] (b : ℕ → ℕ) {s : ℕ}
    {X : Finset α} (hX : X.card=s) :
    (∑ Y ∈ (subsets α s).erase X, (b (X ∪ Y).card : ℤ)) =
      ∑ i ∈ range s, (s.choose i : ℤ)*(Fintype.card α-s).choose (s-i)*b (2*s-i) := by
  have hm (Y : Finset α) (hy : Y ∈ (subsets α s).erase X) :
      (X ∩ Y).card ∈ range s := by
    obtain ⟨hne, hY⟩ := mem_erase.mp hy
    exact mem_range.mpr (intersection_lt_of_ne hX (mem_subsets.mp hY) hne.symm)
  rw [← sum_fiberwise_of_maps_to hm (fun Y => (b (X ∪ Y).card : ℤ))]
  apply sum_congr rfl
  intro i hi
  have hi' : i<s := mem_range.mp hi
  have hf : ((subsets α s).erase X).filter (fun Y => (X ∩ Y).card=i) =
      (subsets α s).filter (fun Y => (X ∩ Y).card=i) := by
    ext Y
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨_, hy⟩, h⟩; exact ⟨hy, h⟩
    · rintro ⟨hy, h⟩
      refine ⟨⟨?_, hy⟩, h⟩
      intro he
      subst Y
      simp [hX] at h
      omega
  rw [hf]
  have hv : (((subsets α s).filter (fun Y => (X ∩ Y).card=i)).card : ℤ) =
      (s.choose i : ℤ)*(Fintype.card α-s).choose (s-i) := by
    exact_mod_cast (by simpa [subsets, hX] using
      card_intersection_class (univ : Finset α) X s i (subset_univ _) hi'.le)
  calc
    _ = ∑ _Y ∈ (subsets α s).filter (fun Y => (X ∩ Y).card=i), (b (2*s-i) : ℤ) := by
      apply sum_congr rfl
      intro Y hY
      obtain ⟨hy, hI⟩ := mem_filter.mp hY
      rw [union_card hX (mem_subsets.mp hy), hI]
    _ = _ := by rw [sum_const, nsmul_eq_mul, hv]

/-- The exact signed excess row identity. Uniformity is its only family
hypothesis; coverage and lower bounds are not needed for this equality. -/
theorem excess_row_sum [Fintype α] {C : Family α} {k s : ℕ}
    (hu : Uniform C k) (b : ℕ → ℕ) {X : Finset α} (hX : X.card=s) :
    ∑ Y ∈ subsets α s, excess C b X Y =
      ((multiplicity C X : ℤ)-b s)*((k.choose s : ℤ)-1)+
        defect (Fintype.card α) k s b := by
  have hmem : X ∈ subsets α s := mem_subsets.mpr hX
  have hc : (∑ Y ∈ subsets α s, (multiplicity C (X ∪ Y) : ℤ)) =
      (k.choose s : ℤ)*multiplicity C X := by exact_mod_cast union_multiplicity_sum hu s X
  have hd : (∑ Y ∈ (subsets α s).erase X, (multiplicity C (X ∪ Y) : ℤ)) =
      (k.choose s : ℤ)*multiplicity C X-multiplicity C X := by
    have hh := sum_erase_add (s := subsets α s)
      (f := fun Y => (multiplicity C (X ∪ Y) : ℤ)) hmem
    rw [hc, union_self] at hh
    linarith
  have he : (∑ Y ∈ subsets α s, excess C b X Y) =
      (∑ Y ∈ (subsets α s).erase X, (multiplicity C (X ∪ Y) : ℤ)) -
      (∑ Y ∈ (subsets α s).erase X, (b (X ∪ Y).card : ℤ)) := by
    rw [← sum_erase_add (s := subsets α s) (f := excess C b X) hmem]
    simp only [excess, ite_true, add_zero, ← sum_sub_distrib]
    apply sum_congr rfl
    intro Y hY
    rw [ite_eq_right (mem_erase.mp hY).1.symm]
  rw [he, hd, off_diagonal_baseline_sum b hX]
  unfold defect
  ring

end CoveringDesigns.HigherIncidence
