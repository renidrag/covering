import CoveringDesigns.Multicover.Counting

/-! The multiplicity version of the iterated Schönheim bound, including strength zero. -/

namespace CoveringDesigns.Multicover

universe u v

/-- Exact nested ceilings. Strength zero counts the required occurrences. -/
def bound (lam v k : ℕ) : ℕ → ℕ
  | 0 => lam
  | t+1 => Schoenheim.ceilDiv (v * bound lam (v-1) (k-1) t) k

@[simp] theorem bound_zero (lam v k : ℕ) : bound lam v k 0 = lam := rfl

theorem bound_succ (lam v k t : ℕ) :
    bound lam v k (t+1) = Schoenheim.ceilDiv (v * bound lam (v-1) (k-1) t) k := rfl

theorem bound_one_eq (v k t : ℕ) : bound 1 v k t = Schoenheim.bound v k t := by
  induction t generalizing v k with
  | zero => rfl
  | succ t ih => simp only [bound_succ, Schoenheim.bound_succ, ih]

@[simp] theorem bound_multiplicity_zero (v k t : ℕ) : bound 0 v k t = 0 := by
  induction t generalizing v k with
  | zero => rfl
  | succ t ih =>
    rw [bound_succ, ih, Nat.mul_zero]
    cases k with
    | zero => rfl
    | succ k => simp [Schoenheim.ceilDiv, Nat.div_eq_of_lt (Nat.lt_succ_self k)]

/-- General multiplicity Schönheim: arbitrary finite point and occurrence types. -/
theorem lower_bound {α : Type u} {ι : Type v}
    [Fintype α] [DecidableEq α] [Fintype ι]
    {B : ι → Finset α} {k t lam : ℕ}
    (htk : t ≤ k) (hkv : k ≤ Fintype.card α) (h : IsCover B k t lam) :
    bound lam (Fintype.card α) k t ≤ Fintype.card ι := by
  induction t generalizing α ι k with
  | zero => exact (covers_zero_iff B lam).mp h.2
  | succ t ih =>
    rw [bound_succ]
    apply bound_of_links (by omega) h.1
    intro p
    have hn := subset_complement_card ({p} : Finset α)
    have hi := ih (by omega : t ≤ k-1) (by simpa using Nat.sub_le_sub_right hkv 1)
      (subsetLink_isCover h {p} (by simp))
    simpa only [hn, Finset.card_singleton] using hi

theorem schoenheim_coverLower {lam v k t : ℕ} (htk : t ≤ k) (hkv : k ≤ v) :
    CoverLower.{u,v} v k t lam (bound lam v k t) := by
  intro α ι _ _ _ B hn h
  simpa only [hn] using lower_bound htk (by omega) h

end CoveringDesigns.Multicover
