import CoveringDesigns.TruncatedPlaneLoads.Supports

/-! The four-base lemma depends only on a partition, not on plane geometry. -/

namespace CoveringDesigns.TruncatedPlaneLoads
open Finset
variable {V G I : Type*} [DecidableEq G] [Fintype I]

/-- Intersecting full-group-plus-one supports using at least four bases
share a coordinate. The stronger conclusion specifies every extra outside
that coordinate's group. No injectivity of the indexing is needed. -/
theorem common_coordinate (g : V → G) (b : I → G) (a : I → V)
    (outside : ∀ u, g (a u) ≠ b u)
    (meet : ∀ u v, b u ≠ b v → g (a u) = b v ∨ g (a v) = b u ∨ a u = a v)
    (many : 4 ≤ (univ.image b).card) :
    ∃ c : V, ∀ u, b u = g c ∨ a u = c := by
  classical
  have duplicate : ∃ u v, b u ≠ b v ∧ a u = a v := by
    by_contra hn
    push_neg at hn
    have orient (u v : I) (h : b u ≠ b v) : g (a u) = b v ∨ g (a v) = b u := by
      rcases meet u v h with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exact False.elim (hn u v h h')
    obtain ⟨i, hi, j, hj, k, hk, l, hl, hij, hik, hil, hjk, hjl, hkl⟩ :=
      three_lt_card.mp (by omega : 3 < (univ.image b).card)
    obtain ⟨u, _, rfl⟩ := mem_image.mp hi
    obtain ⟨v, _, rfl⟩ := mem_image.mp hj
    obtain ⟨w, _, rfl⟩ := mem_image.mp hk
    obtain ⟨z, _, rfl⟩ := mem_image.mp hl
    have uv := orient u v hij
    have uw := orient u w hik
    have uz := orient u z hil
    have vw := orient v w hjk
    have vz := orient v z hjl
    have wz := orient w z hkl
    rcases uv with uv | uv <;> rcases uw with uw | uw <;>
      rcases uz with uz | uz <;> rcases vw with vw | vw <;>
      rcases vz with vz | vz <;> rcases wz with wz | wz <;> simp_all
  obtain ⟨u, v, huv, huv'⟩ := duplicate
  have hnot : ¬ univ.image b ⊆ {b u, b v, g (a u)} := by
    intro h
    have hle' : (univ.image b).card ≤ 3 := (card_le_card h).trans card_le_three
    omega
  obtain ⟨j, hj, hjnot⟩ := not_subset.mp hnot
  obtain ⟨w, _, rfl⟩ := mem_image.mp hj
  simp only [mem_insert, mem_singleton, not_or] at hjnot
  have hu : g (a u) ≠ b u := outside u
  have hv : g (a u) ≠ b v := by simpa [huv'] using outside v
  have hw : a w = a u := by
    have hwu := meet w u hjnot.1
    have hwv := meet w v hjnot.2.1
    rw [← huv'] at hwv
    rcases hwu with h | h | h
    · rcases hwv with h' | h' | h'
      · exact False.elim (huv (h.symm.trans h'))
      · exact False.elim (hjnot.2.2 h'.symm)
      · exact h'
    · exact False.elim (hjnot.2.2 h.symm)
    · exact h
  have force (r s z : I) (hrs : b r ≠ b s)
      (hr : a r = a u) (hs : a s = a u)
      (hz : b z ≠ g (a u)) (hzr : b z ≠ b r) (hzs : b z ≠ b s) :
      a z = a u := by
    have hzr' := meet z r hzr
    have hzs' := meet z s hzs
    rw [hr] at hzr'
    rw [hs] at hzs'
    rcases hzr' with h | h | h
    · rcases hzs' with h' | h' | h'
      · exact False.elim (hrs (h.symm.trans h'))
      · exact False.elim (hz h'.symm)
      · exact h'
    · exact False.elim (hz h.symm)
    · exact h
  refine ⟨a u, fun z => ?_⟩
  by_cases hz : b z = g (a u)
  · exact Or.inl hz
  apply Or.inr
  by_cases hzu : b z = b u
  · exact force v w z (Ne.symm hjnot.2.1) huv'.symm hw hz
      (by simpa [hzu] using huv) (by simpa [hzu] using Ne.symm hjnot.1)
  by_cases hzv : b z = b v
  · exact force u w z (Ne.symm hjnot.1) rfl hw hz hzu
      (by simpa [hzv] using Ne.symm hjnot.2.1)
  exact force u v z huv rfl huv'.symm hz hzu hzv

end CoveringDesigns.TruncatedPlaneLoads
