import CoveringDesigns.C12_6_3.Structural.Reduction

/-! Abstract intersection geometry used by the structural C(13,7,4) proof. -/

namespace CoveringDesigns.C13Structural

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Deleting a point is injective on blocks known to contain it. -/
theorem subtype_ne_inj {p : α} {A B : Finset α} (hpA : p ∈ A) (hpB : p ∈ B) :
    A.subtype (· ≠ p) = B.subtype (· ≠ p) ↔ A = B := by
  constructor
  · intro h
    simpa only [GPPTStructural.liftBlock_subtype p hpA,
      GPPTStructural.liftBlock_subtype p hpB] using
      congrArg (GPPTStructural.liftBlock p) h
  · rintro rfl
    rfl

/-- Deleting a common point lowers the intersection size by one. -/
theorem subtype_ne_inter_card {p : α} {A B : Finset α}
    (hpA : p ∈ A) (hpB : p ∈ B) :
    (A.subtype (· ≠ p) ∩ B.subtype (· ≠ p)).card = (A ∩ B).card - 1 := by
  have he : A.subtype (· ≠ p) ∩ B.subtype (· ≠ p) = (A ∩ B).subtype (· ≠ p) := by
    ext x
    simp
  rw [he, card_subtype, filter_ne', card_erase_of_mem (mem_inter.mpr ⟨hpA, hpB⟩)]

/-- The twelve full rows and three completed rows of an ordinary GPPT link. -/
structure OrdinaryGeometry (C : Family α) where
  core : Family α
  completed : Family α
  union_eq : C = core ∪ completed
  disjoint : Disjoint core completed
  completed_card : completed.card = 3
  core_card : core.card = 12
  core_degree : ∀ p, degree core p = 6
  core_inter : ∀ A ∈ core, ∀ B ∈ core, A ≠ B → (A ∩ B).card ≤ 3
  block_inter : ∀ A ∈ C, ∀ B ∈ C, A ≠ B → (A ∩ B).card ≤ 4

/-- The distinguished pair and intersection geometry of the exceptional link. -/
structure ExceptionalGeometry (C : Family α) where
  high : Finset α
  high_card : high.card = 2
  degree_high : ∀ p ∈ high, degree C p = 10
  degree_low : ∀ p ∉ high, degree C p = 7
  high_columns : ∀ A ∈ C, ∀ p ∈ high, p ∈ A → high ⊆ A
  high_low : ∀ p ∈ high, ∀ q ∉ high, degree (star C p) q = 4
  block_inter : ∀ A ∈ C, ∀ B ∈ C, A ≠ B → (A ∩ B).card ≤ 4
  inter_four : ∀ A ∈ C, ∀ B ∈ C, A ≠ B → (A ∩ B).card = 4 → high ⊆ A ∩ B

/-- A matching refers to distinct block endpoints, not disjoint point sets. -/
structure IntersectionFourMatching (C : Family α) (n : ℕ) where
  block : Fin n × Bool → Finset α
  injective : Function.Injective block
  mem : ∀ j, block j ∈ C
  inter : ∀ i, (block (i, false) ∩ block (i, true)).card = 4

namespace IntersectionFourMatching

variable {C : Family α} {n : ℕ}

theorem ne (M : IntersectionFourMatching C n) (i : Fin n) :
    M.block (i, false) ≠ M.block (i, true) := by
  intro h
  have := congrArg Prod.snd (M.injective h)
  simp at this

/-- An endpoint hitting set must have at least as many rows as the matching. -/
theorem card_le (M : IntersectionFourMatching C n) (E : Family α)
    (hE : ∀ i, M.block (i, false) ∈ E ∨ M.block (i, true) ∈ E) : n ≤ E.card := by
  let side (i : Fin n) : Bool := if M.block (i, false) ∈ E then false else true
  let f (i : Fin n) : Finset α := M.block (i, side i)
  have hf (i : Fin n) : f i ∈ E := by
    dsimp [f, side]
    split_ifs with h
    · exact h
    · exact (hE i).resolve_left h
  have hi : Function.Injective f := by
    intro i j h
    exact congrArg Prod.fst (M.injective h)
  have hh := card_le_card_of_injOn f
    (show Set.MapsTo f (univ : Finset (Fin n)) E from fun i _ => hf i)
    (show Set.InjOn f (univ : Finset (Fin n)) from hi.injOn)
  simpa only [card_univ, Fintype.card_fin] using hh

end IntersectionFourMatching

namespace OrdinaryGeometry

variable {C : Family α}

theorem completed_degree (G : OrdinaryGeometry C) (p : α) :
    6 + degree G.completed p = degree C p := by
  conv_rhs => rw [G.union_eq]
  unfold degree star
  rw [filter_union, card_union_of_disjoint (G.disjoint.mono
    (filter_subset _ _) (filter_subset _ _))]
  change 6 + degree G.completed p = degree G.core p + degree G.completed p
  rw [G.core_degree]

theorem degree_le_nine (G : OrdinaryGeometry C) (p : α) : degree C p ≤ 9 := by
  have he : degree G.completed p ≤ 3 := by
    calc
      degree G.completed p ≤ G.completed.card := card_le_card (filter_subset _ _)
      _ = 3 := G.completed_card
  have hd := G.completed_degree p
  omega

theorem completed_degree_one (G : OrdinaryGeometry C) {p : α}
    (hp : degree C p = 7) : degree G.completed p = 1 := by
  have := G.completed_degree p
  omega

theorem inter_four_endpoint (G : OrdinaryGeometry C)
    {A B : Finset α} (hA : A ∈ C) (hB : B ∈ C)
    (hne : A ≠ B) (hi : (A ∩ B).card = 4) : A ∈ G.completed ∨ B ∈ G.completed := by
  rw [G.union_eq] at hA hB
  rcases mem_union.mp hA with hA | hA
  · rcases mem_union.mp hB with hB | hB
    · have := G.core_inter A hA B hB hne
      omega
    · exact Or.inr hB
  · exact Or.inl hA

theorem matching_le_three (G : OrdinaryGeometry C) {n : ℕ}
    (M : IntersectionFourMatching C n) : n ≤ 3 := by
  rw [← G.completed_card]
  exact M.card_le _ (fun i => G.inter_four_endpoint
    (M.mem _) (M.mem _) (M.ne i) (M.inter i))

/-- If all matching endpoints meet a set of points, each selected completed
endpoint lies in the union of those points' completed-row stars. -/
theorem matching_le_completed_union (G : OrdinaryGeometry C) {n : ℕ}
    (M : IntersectionFourMatching C n) (Z : Finset α)
    (hZ : ∀ j, ∃ p ∈ Z, p ∈ M.block j) :
    n ≤ (Z.biUnion (star G.completed)).card := by
  apply M.card_le
  intro i
  have lift (j : Fin n × Bool) (hj : M.block j ∈ G.completed) :
      M.block j ∈ Z.biUnion (star G.completed) := by
    obtain ⟨p, hp, hpm⟩ := hZ j
    exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hj, hpm⟩⟩
  exact (G.inter_four_endpoint (M.mem _) (M.mem _) (M.ne i) (M.inter i)).imp
    (lift _) (lift _)

theorem matching_le_sum_completed_degree (G : OrdinaryGeometry C) {n : ℕ}
    (M : IntersectionFourMatching C n) (Z : Finset α)
    (hZ : ∀ j, ∃ p ∈ Z, p ∈ M.block j) :
    n ≤ ∑ p ∈ Z, (degree C p - 6) := by
  calc
    n ≤ (Z.biUnion (star G.completed)).card := G.matching_le_completed_union M Z hZ
    _ ≤ ∑ p ∈ Z, (star G.completed p).card := card_biUnion_le
    _ = ∑ p ∈ Z, (degree C p - 6) := by
      apply sum_congr rfl
      intro p _
      have hd := G.completed_degree p
      change degree G.completed p = degree C p - 6
      omega

theorem matching_le_two_of_degree_seven (G : OrdinaryGeometry C) {n : ℕ}
    (M : IntersectionFourMatching C n) (p q : α)
    (hp : degree C p = 7) (hq : degree C q = 7)
    (hZ : ∀ j, p ∈ M.block j ∨ q ∈ M.block j) : n ≤ 2 := by
  have h := G.matching_le_sum_completed_degree M {p, q} (fun j => by
    rcases hZ j with hj | hj
    · exact ⟨p, by simp, hj⟩
    · exact ⟨q, by simp, hj⟩)
  have hbound : ∑ x ∈ ({p, q} : Finset α), (degree C x - 6) ≤ 2 := by
    by_cases hpq : p = q <;> simp [hpq, hp, hq]
  exact h.trans hbound

end OrdinaryGeometry

namespace ExceptionalGeometry

variable {C : Family α}

theorem degree_eq_ten_iff (G : ExceptionalGeometry C) (p : α) :
    degree C p = 10 ↔ p ∈ G.high := by
  constructor
  · intro hp
    by_contra hn
    have := G.degree_low p hn
    omega
  · exact G.degree_high p

theorem degree_eq_seven_iff (G : ExceptionalGeometry C) (p : α) :
    degree C p = 7 ↔ p ∉ G.high := by
  constructor
  · intro hp hin
    have := G.degree_high p hin
    omega
  · exact G.degree_low p

theorem degree_le_ten (G : ExceptionalGeometry C) (p : α) : degree C p ≤ 10 := by
  by_cases hp : p ∈ G.high
  · rw [G.degree_high p hp]
  · rw [G.degree_low p hp]
    decide

theorem matching_subset (G : ExceptionalGeometry C) {n : ℕ}
    (M : IntersectionFourMatching C n) (j : Fin n × Bool) : G.high ⊆ M.block j := by
  have h := G.inter_four (M.block (j.1, false)) (M.mem _)
    (M.block (j.1, true)) (M.mem _) (M.ne j.1) (M.inter j.1)
  cases j with
  | mk i b => cases b
              · exact h.trans inter_subset_left
              · exact h.trans inter_subset_right

end ExceptionalGeometry

#guard_standard_axioms subtype_ne_inj subtype_ne_inter_card
  IntersectionFourMatching.card_le
  OrdinaryGeometry.completed_degree OrdinaryGeometry.degree_le_nine
  OrdinaryGeometry.matching_le_three OrdinaryGeometry.matching_le_sum_completed_degree
  OrdinaryGeometry.matching_le_two_of_degree_seven ExceptionalGeometry.matching_subset
  ExceptionalGeometry.degree_eq_ten_iff ExceptionalGeometry.degree_eq_seven_iff

end CoveringDesigns.C13Structural
