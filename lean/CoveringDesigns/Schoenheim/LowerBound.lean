import CoveringDesigns.Foundations.Bounds

/-!
The ordinary covering (λ = 1) case of Schönheim's Theorem I, “On coverings”
(1964), p. 1407. The argument uses point links, incidence counting and
induction on the covering strength. No result-specific component is imported.
-/

namespace CoveringDesigns.Schoenheim

universe u

/-- Exact ceiling division on natural numbers, with value zero at divisor zero. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- For a positive divisor, ceiling division is the least integer upper quotient. -/
theorem ceilDiv_le_iff {a b c : ℕ} (hb : 0 < b) :
    ceilDiv a b ≤ c ↔ a ≤ b * c := by
  unfold ceilDiv
  rw [Nat.div_le_iff_le_mul_add_pred hb]
  omega

/-- The iterated Schönheim bound. Strength zero is the recursion seed.
For valid positive-strength parameters all divisors in the recursion are positive. -/
def bound (v k : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => ceilDiv (v * bound (v - 1) (k - 1) t) k

@[simp] theorem bound_zero (v k : ℕ) : bound v k 0 = 1 := rfl

theorem bound_succ (v k t : ℕ) :
    bound v k (t + 1) = ceilDiv (v * bound (v - 1) (k - 1) t) k := rfl

/-- The recurrence uses exact natural-number ceiling arithmetic. -/
theorem bound_succ_div (v k t : ℕ) :
    bound v k (t + 1) = (v * bound (v - 1) (k - 1) t + k - 1) / k := rfl

@[simp] theorem bound_one (v k : ℕ) : bound v k 1 = ceilDiv v k := by
  simp [bound]

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Any common lower bound on point-link sizes lifts by double counting.
Uniformity and a positive block size suffice; coverage is not required. -/
theorem bound_of_links {C : Family α} {k m : ℕ}
    (hk : 0 < k) (hu : Uniform C k) (hl : ∀ p, m ≤ (link C p).card) :
    ceilDiv (Fintype.card α * m) k ≤ C.card := by
  apply (ceilDiv_le_iff hk).2
  have hd (p : α) : m ≤ degree C p := by simpa only [link_card] using hl p
  simpa only [Nat.mul_comm m] using incidence_lower_bound hu hd

/-- Apply any proved lower bound for smaller coverings to all point links. -/
theorem lift_lower_bound {C : Family α} {v k t m : ℕ}
    (hn : Fintype.card α = v + 1) (h : IsCover C (k + 1) (t + 1))
    (hl : ∀ {β : Type u} [Fintype β] [DecidableEq β] {D : Family β},
      Fintype.card β = v → IsCover D k t → m ≤ D.card) :
    ceilDiv ((v + 1) * m) (k + 1) ≤ C.card := by
  rw [← hn]
  apply bound_of_links (Nat.succ_pos k) h.1
  intro p
  exact hl (by rw [complement_point_card, hn, Nat.add_sub_cancel]) (link_isCover h p)

/-- Schönheim's lower-bound theorem for ordinary coverings (λ = 1),
for every `1 ≤ t ≤ k ≤ v`, with `v` the cardinality of the ambient type. -/
theorem lower_bound {C : Family α} {k t : ℕ}
    (ht : 1 ≤ t) (htk : t ≤ k) (hkv : k ≤ Fintype.card α)
    (h : IsCover C k t) : bound (Fintype.card α) k t ≤ C.card := by
  induction t generalizing α k with
  | zero => omega
  | succ t ih =>
    cases t with
    | zero =>
      rw [bound_one]
      exact (ceilDiv_le_iff (by omega : 0 < k)).2 (one_cover_bound h)
    | succ t =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [bound_succ]
      apply bound_of_links (Nat.succ_pos j) h.1
      intro p
      have hn := complement_point_card p
      have hi := ih (α := {q : α // q ≠ p}) (k := j)
        (by omega) (by omega) (by omega) (link_isCover h p)
      simpa only [hn, Nat.succ_sub_one] using hi

end CoveringDesigns.Schoenheim
