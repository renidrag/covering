import CoveringDesigns.HorsleySingh.Counting

/-! General intersection-class counting, by splitting a subset into its inside
and outside parts. No covering hypotheses are needed. -/
namespace CoveringDesigns.HigherIncidence
open Finset
variable {α : Type*} [DecidableEq α]

/-- Subsets of a fixed size meeting X in exactly i points. -/
theorem card_intersection_class (V X : Finset α) (r i : ℕ)
    (hXV : X ⊆ V) (hi : i ≤ r) :
    ((V.powersetCard r).filter (fun Y => (X ∩ Y).card=i)).card =
      X.card.choose i * (V.card-X.card).choose (r-i) := by
  rw [← card_sdiff_of_subset hXV, ← card_powersetCard, ← card_powersetCard,
    ← card_product]
  apply card_bij (fun Y _ => (X ∩ Y, Y \ X))
  · intro Y hY
    obtain ⟨hY, hI⟩ := mem_filter.mp hY
    obtain ⟨hYV, hYr⟩ := mem_powersetCard.mp hY
    apply mem_product.mpr
    constructor
    · exact mem_powersetCard.mpr ⟨inter_subset_left, hI⟩
    · apply mem_powersetCard.mpr
      constructor
      · intro x hx
        exact mem_sdiff.mpr ⟨hYV (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
      · simp only [card_sdiff, inter_comm Y X, hYr, hI]
  · intro Y hY Z hZ he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    dsimp at h₁ h₂
    ext x
    by_cases hx : x ∈ X
    · have := congrArg (fun T => x ∈ T) h₁
      simpa [hx] using this
    · have := congrArg (fun T => x ∈ T) h₂
      simpa [hx] using this
  · intro AB hAB
    obtain ⟨hA, hB⟩ := mem_product.mp hAB
    obtain ⟨hAX, hAi⟩ := mem_powersetCard.mp hA
    obtain ⟨hBV, hBi⟩ := mem_powersetCard.mp hB
    have hd : Disjoint AB.1 AB.2 := by
      apply disjoint_left.mpr
      intro x hx hy
      exact (mem_sdiff.mp (hBV hy)).2 (hAX hx)
    have hI : X ∩ (AB.1 ∪ AB.2) = AB.1 := by
      ext x
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hx, ha | hb⟩
        · exact ha
        · exact False.elim ((mem_sdiff.mp (hBV hb)).2 hx)
      · intro ha
        exact ⟨hAX ha, Or.inl ha⟩
    have hD : (AB.1 ∪ AB.2) \ X = AB.2 := by
      ext x
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨ha | hb, hx⟩
        · exact False.elim (hx (hAX ha))
        · exact hb
      · intro hb
        exact ⟨Or.inr hb, (mem_sdiff.mp (hBV hb)).2⟩
    refine ⟨AB.1 ∪ AB.2, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact union_subset (hAX.trans hXV) (hBV.trans sdiff_subset)
    · rw [card_union_of_disjoint hd, hAi, hBi]
      omega
    · rw [hI, hAi]
    · exact Prod.ext hI hD

/-- Intersection size determines union size for two equally sized subsets. -/
theorem union_card {X Y : Finset α} {s : ℕ} (hX : X.card=s) (hY : Y.card=s) :
    (X ∪ Y).card = 2*s-(X ∩ Y).card := by
  have := card_union_add_card_inter X Y
  omega

theorem intersection_lt_of_ne {X Y : Finset α} {s : ℕ}
    (hX : X.card=s) (hY : Y.card=s) (hne : X ≠ Y) : (X ∩ Y).card < s := by
  have hi := card_le_card (inter_subset_left (s₁ := X) (s₂ := Y))
  by_contra hn
  have he : X ∩ Y = X := eq_of_subset_of_card_le inter_subset_left (by omega)
  have hsub : X ⊆ Y := by rw [← he]; exact inter_subset_right
  exact hne (eq_of_subset_of_card_le hsub (by omega))

/-- Ambient s-subsets, also for s=0 and for an empty point type. -/
def subsets (α : Type*) [Fintype α] (s : ℕ) : Finset (Finset α) :=
  univ.powersetCard s

omit [DecidableEq α] in
@[simp] theorem mem_subsets [Fintype α] {X : Finset α} {s : ℕ} :
    X ∈ subsets α s ↔ X.card=s := mem_powersetCard_univ

omit [DecidableEq α] in
@[simp] theorem card_subsets [Fintype α] (s : ℕ) :
    (subsets α s).card = (Fintype.card α).choose s := by simp [subsets]

theorem multiplicity_sum [Fintype α] {C : Family α} {k : ℕ}
    (hu : Uniform C k) (s : ℕ) :
    ∑ X ∈ subsets α s, HorsleySingh.multiplicity C X = k.choose s*C.card := by
  rw [subsets, HorsleySingh.multiplicity_sum,
    sum_const_nat (fun B hB => congrArg (fun n => n.choose s) (hu B hB))]
  exact Nat.mul_comm _ _

theorem union_multiplicity_sum [Fintype α] {C : Family α} {k : ℕ}
    (hu : Uniform C k) (s : ℕ) (X : Finset α) :
    ∑ Y ∈ subsets α s, HorsleySingh.multiplicity C (X ∪ Y) =
      k.choose s*HorsleySingh.multiplicity C X := by
  have he (Y : Finset α) : HorsleySingh.multiplicity C (X ∪ Y) =
      HorsleySingh.multiplicity (C.filter (X ⊆ ·)) Y := by
    unfold HorsleySingh.multiplicity
    congr 1
    ext B
    simp [union_subset_iff, and_assoc]
  simp_rw [he]
  exact multiplicity_sum (fun B hB => hu B (mem_filter.mp hB).1) s

end CoveringDesigns.HigherIncidence
