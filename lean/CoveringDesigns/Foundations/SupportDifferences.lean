import CoveringDesigns.Foundations.SupportObstruction

/-! Finite support differences and agreement, on arbitrary actual indices. -/
namespace CoveringDesigns.SupportObstruction
open Finset
variable {ι : Type*} [DecidableEq ι]

/-- Equal supports of size n+1 meeting in n indices differ in one index each. -/
theorem single_differences (H G : Finset ι) (n : ℕ)
    (hH : H.card = n+1) (hG : G.card = n+1) (hHG : (H ∩ G).card = n) :
    ∃ a b, a ≠ b ∧ H \ G = {a} ∧ G \ H = {b} ∧
      a ∈ H ∧ a ∉ G ∧ b ∈ G ∧ b ∉ H ∧ (H ∩ {a,b}).card = 1 := by
  have h1 : (H \ G).card = 1 := by
    have hh := card_sdiff_add_card_inter H G
    omega
  have h2 : (G \ H).card = 1 := by
    have hh := card_sdiff_add_card_inter G H
    rw [inter_comm G H] at hh
    omega
  obtain ⟨a,ha⟩ := card_eq_one.mp h1
  obtain ⟨b,hb⟩ := card_eq_one.mp h2
  have ha' : a ∈ H ∧ a ∉ G := mem_sdiff.mp (ha.symm ▸ mem_singleton_self a)
  have hb' : b ∈ G ∧ b ∉ H := mem_sdiff.mp (hb.symm ▸ mem_singleton_self b)
  have hab : a ≠ b := by intro h; subst b; exact ha'.2 hb'.1
  refine ⟨a,b,hab,ha,hb,ha'.1,ha'.2,hb'.1,hb'.2,?_⟩
  have hi : H ∩ {a,b} = {a} := by ext i; simp; aesop
  rw [hi,card_singleton]

/-- Agreement at the two exceptional indices gives equal intersection counts.
The common support can be arbitrary. -/
theorem intersections_eq_of_agree (H G S : Finset ι) {a b : ι}
    (ha : H \ G = {a}) (hb : G \ H = {b}) (hab : a ∈ S ↔ b ∈ S) :
    (S ∩ H).card = (S ∩ G).card := by
  have h1 := card_sdiff_add_card_inter (S ∩ H) G
  have h2 := card_sdiff_add_card_inter (S ∩ G) H
  have he1 : (S ∩ H) \ G = S ∩ {a} := by
    rw [← ha]
    ext i
    simp only [mem_sdiff,mem_inter]
    tauto
  have he2 : (S ∩ G) \ H = S ∩ {b} := by
    rw [← hb]
    ext i
    simp only [mem_sdiff,mem_inter]
    tauto
  have he3 : (S ∩ H) ∩ G = (S ∩ G) ∩ H := by
    ext i
    simp only [mem_inter]
    tauto
  have he4 : (S ∩ {a}).card = (S ∩ {b}).card := by
    by_cases haS : a ∈ S
    · simp [haS,hab.mp haS]
    · have hbS : b ∉ S := fun h => haS (hab.mpr h)
      simp [haS,hbS]
  rw [he1,he3] at h1
  rw [he2] at h2
  omega

/-- Natural-subtraction version of the obstruction, with containment ensuring
the subtraction is exact. The main identity remains subtraction-free. -/
theorem empty_of_subtraction_bound (I A H S T : Finset ι)
    (hH : H ⊆ I) (hunion : S ∪ T = I \ A)
    (hbound : (H ∩ S).card + (H ∩ T).card ≤ H.card - (H ∩ A).card) :
    (H ∩ S) ∩ T = ∅ := by
  apply empty_of_intersection_bound I A H S T hH hunion
  have hh := card_le_card (inter_subset_left (s₁ := H) (s₂ := A))
  omega

end CoveringDesigns.SupportObstruction
