import CoveringDesigns.Schoenheim

/-! Contracts and axioms for the standalone λ = 1 lower-bound component. -/

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.Schoenheim.ceilDiv
#print CoveringDesigns.Schoenheim.bound

universe u

open CoveringDesigns CoveringDesigns.Schoenheim

#check (ceilDiv_le_iff : ∀ {a b c : ℕ}, 0 < b → (ceilDiv a b ≤ c ↔ a ≤ b * c))
#check (bound_zero : ∀ v k, bound v k 0 = 1)
#check (bound_succ_div : ∀ v k t,
  bound v k (t + 1) = (v * bound (v - 1) (k - 1) t + k - 1) / k)
#check (bound_one : ∀ v k, bound v k 1 = ceilDiv v k)

#check (bound_of_links :
  ∀ {α : Type u} [Fintype α] [DecidableEq α] {C : Family α} {k m : ℕ},
    0 < k → Uniform C k → (∀ p, m ≤ (link C p).card) →
    ceilDiv (Fintype.card α * m) k ≤ C.card)

#check (lift_lower_bound :
  ∀ {α : Type u} [Fintype α] [DecidableEq α] {C : Family α} {v k t m : ℕ},
    Fintype.card α = v + 1 → IsCover C (k + 1) (t + 1) →
    (∀ {β : Type u} [Fintype β] [DecidableEq β] {D : Family β},
      Fintype.card β = v → IsCover D k t → m ≤ D.card) →
    ceilDiv ((v + 1) * m) (k + 1) ≤ C.card)

#check (lower_bound :
  ∀ {α : Type u} [Fintype α] [DecidableEq α] {C : Family α} {k t : ℕ},
    1 ≤ t → t ≤ k → k ≤ Fintype.card α → IsCover C k t →
    bound (Fintype.card α) k t ≤ C.card)

#check (Schoenheim.lower_bound_11_5_2 :
  ∀ {α : Type u} [Fintype α] [DecidableEq α] {C : Family α},
    Fintype.card α = 11 → IsCover C 5 2 → 7 ≤ C.card)
#check (Schoenheim.lower_bound_12_6_3 :
  ∀ {α : Type u} [Fintype α] [DecidableEq α] {C : Family α},
    Fintype.card α = 12 → IsCover C 6 3 → 14 ≤ C.card)
#check (Schoenheim.lower_bound_13_7_4 :
  ∀ {α : Type u} [Fintype α] [DecidableEq α] {C : Family α},
    Fintype.card α = 13 → IsCover C 7 4 → 26 ≤ C.card)

namespace CoveringDesigns.AuditSchoenheim

/-- The general bound, with the covering conditions written out explicitly. -/
theorem lower_bound_explicit {α : Type u} [Fintype α] [DecidableEq α]
    {v k t : ℕ} {C : Finset (Finset α)} (hn : Fintype.card α = v)
    (ht : 1 ≤ t) (htk : t ≤ k) (hkv : k ≤ v)
    (hu : ∀ B ∈ C, B.card = k)
    (hc : ∀ T : Finset α, T.card = t → ∃ B ∈ C, T ⊆ B) :
    Schoenheim.bound v k t ≤ C.card := by
  subst v
  exact Schoenheim.lower_bound ht htk hkv ⟨hu, hc⟩

-- Kernel reduction also checks the boundary arithmetic and the three examples.
example : Schoenheim.ceilDiv 0 5 = 0 := rfl
example : Schoenheim.bound 1 1 1 = 1 := rfl
example : Schoenheim.bound 5 5 5 = 1 := rfl
example : Schoenheim.bound 11 5 2 = 7 := rfl
example : Schoenheim.bound 12 6 3 = 14 := rfl
example : Schoenheim.bound 13 7 4 = 26 := rfl

end CoveringDesigns.AuditSchoenheim

#guard_standard_axioms CoveringDesigns.Schoenheim.ceilDiv_le_iff
  CoveringDesigns.Schoenheim.bound_zero CoveringDesigns.Schoenheim.bound_succ
  CoveringDesigns.Schoenheim.bound_succ_div CoveringDesigns.Schoenheim.bound_one
  CoveringDesigns.Schoenheim.bound_of_links CoveringDesigns.Schoenheim.lift_lower_bound
  CoveringDesigns.Schoenheim.lower_bound
  CoveringDesigns.Schoenheim.bound_11_5_2 CoveringDesigns.Schoenheim.bound_12_6_3
  CoveringDesigns.Schoenheim.bound_13_7_4
  CoveringDesigns.Schoenheim.lower_bound_11_5_2
  CoveringDesigns.Schoenheim.lower_bound_12_6_3
  CoveringDesigns.Schoenheim.lower_bound_13_7_4
  CoveringDesigns.AuditSchoenheim.lower_bound_explicit

#print axioms CoveringDesigns.Schoenheim.ceilDiv_le_iff
#print axioms CoveringDesigns.Schoenheim.bound_zero
#print axioms CoveringDesigns.Schoenheim.bound_succ
#print axioms CoveringDesigns.Schoenheim.bound_succ_div
#print axioms CoveringDesigns.Schoenheim.bound_one
#print axioms CoveringDesigns.Schoenheim.bound_of_links
#print axioms CoveringDesigns.Schoenheim.lift_lower_bound
#print axioms CoveringDesigns.Schoenheim.lower_bound
#print axioms CoveringDesigns.Schoenheim.bound_11_5_2
#print axioms CoveringDesigns.Schoenheim.bound_12_6_3
#print axioms CoveringDesigns.Schoenheim.bound_13_7_4
#print axioms CoveringDesigns.Schoenheim.lower_bound_11_5_2
#print axioms CoveringDesigns.Schoenheim.lower_bound_12_6_3
#print axioms CoveringDesigns.Schoenheim.lower_bound_13_7_4
#print axioms CoveringDesigns.AuditSchoenheim.lower_bound_explicit
