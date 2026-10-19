import CoveringDesigns.HorsleySingh.Counting

/-! Exact specialisation of the numerical hypotheses of Lemma 3. -/

namespace CoveringDesigns.HorsleySingh

/-- Lemma 3's numerical hypotheses for λ = 1 and s = 2.
The smaller-cover lower bounds are supplied separately as `CoverLower`.
The coefficient `b₃-b₄` and the defect are proved nonnegative below. -/
structure Parameters (v k t b₂ b₃ b₄ : ℕ) : Prop where
  strength : 4 ≤ t
  strength_lt : t < k
  block_lt : k < v
  pos₂ : 0 < b₂
  pos₃ : 0 < b₃
  pos₄ : 0 < b₄
  seed : Schoenheim.bound (v-4) (k-4) (t-4) ≤ b₄
  step₃ : Schoenheim.ceilDiv ((v-3)*b₄) (k-3) ≤ b₃
  step₂ : Schoenheim.ceilDiv ((v-2)*b₃) (k-2) ≤ b₂
  diagonal_nonneg : 0 ≤ diagonal b₂ b₃ b₄

theorem Parameters.denominators_pos {v k t b₂ b₃ b₄ : ℕ}
    (h : Parameters v k t b₂ b₃ b₄) :
    0 < k-4 ∧ 0 < k-3 ∧ 0 < k-2 ∧ 0 < k.choose 2 + 1 := by
  have := h.strength
  have := h.strength_lt
  omega

theorem Parameters.recurrences {v k t b₂ b₃ b₄ : ℕ}
    (h : Parameters v k t b₂ b₃ b₄) :
    (v-3)*b₄ ≤ (k-3)*b₃ ∧ (v-2)*b₃ ≤ (k-2)*b₂ := by
  have := h.strength
  have := h.strength_lt
  exact ⟨(Schoenheim.ceilDiv_le_iff (by omega)).mp h.step₃,
    (Schoenheim.ceilDiv_le_iff (by omega)).mp h.step₂⟩

/-- The `a₁` coefficient is nonnegative, as follows from the ceiling recurrence. -/
theorem Parameters.coefficient_nonneg {v k t b₂ b₃ b₄ : ℕ}
    (h : Parameters v k t b₂ b₃ b₄) : b₄ ≤ b₃ := by
  have hr := h.recurrences.1
  have ht := h.strength
  have htk := h.strength_lt
  have hkv := h.block_lt
  by_contra hh
  have hk : 0 < k-3 := by omega
  have hvk : k-3 ≤ v-3 := by omega
  have hmul := Nat.mul_le_mul_right b₄ hvk
  have hstrict := Nat.mul_lt_mul_of_pos_left (show b₃ < b₄ by omega) hk
  omega

/-- A division-free identity for pair counts. -/
theorem two_mul_choose (n : ℕ) :
    2*(n.choose 2 : ℤ) = (n : ℤ)*(n-1 : ℕ) := by
  cases n with
  | zero => simp
  | succ n =>
    have he : (n+1)*n = (n+1).choose 2 * 2 := by
      simpa using Nat.add_one_mul_choose_eq n 1
    have hz : ((n+1).choose 2 : ℤ)*2 = (n+1 : ℕ)* (n : ℤ) := by
      exact_mod_cast he.symm
    simpa [mul_comm] using hz

/-- The nonnegativity assertion in Lemma 3(b), derived from both ceiling
recurrences, without assuming a pair of minimum multiplicity exists. -/
theorem Parameters.defect_nonneg {v k t b₂ b₃ b₄ : ℕ}
    (h : Parameters v k t b₂ b₃ b₄) : 0 ≤ defect v k b₂ b₃ b₄ := by
  have hr := h.recurrences
  have h₃ : (v-3 : ℕ)*(b₄ : ℤ) ≤ (k-3 : ℕ)*(b₃ : ℤ) := by exact_mod_cast hr.1
  have h₂ : (v-2 : ℕ)*(b₃ : ℤ) ≤ (k-2 : ℕ)*(b₂ : ℤ) := by exact_mod_cast hr.2
  have hc₃ := mul_le_mul_of_nonneg_left h₃ (Int.natCast_nonneg (v-2))
  have hc₂ := mul_le_mul_of_nonneg_left h₂ (Int.natCast_nonneg (k-3))
  have hc : (v-2 : ℕ)*(v-3 : ℕ)*(b₄ : ℤ) ≤
      (k-2 : ℕ)*(k-3 : ℕ)*(b₂ : ℤ) := by nlinarith only [hc₃, hc₂]
  have hv := two_mul_choose (v-2)
  have hk := two_mul_choose (k-2)
  simp only [Nat.sub_sub] at hv hk
  have hchoose : ((v-2).choose 2 : ℤ)*b₄ ≤ ((k-2).choose 2 : ℤ)*b₂ := by
    nlinarith only [hc, congrArg (fun z : ℤ => z * b₄) hv,
      congrArg (fun z : ℤ => z * b₂) hk]
  have ht := h.strength
  have htk := h.strength_lt
  have hstep := choose_two_step (n := k) (by omega)
  unfold defect
  rw [hstep]
  nlinarith only [hchoose, h₂]

theorem Parameters.diagonal_lt {v k t b₂ b₃ b₄ : ℕ}
    (h : Parameters v k t b₂ b₃ b₄) : diagonal b₂ b₃ b₄ < b₂ := by
  have hc := h.coefficient_nonneg
  have hp := h.pos₄
  unfold diagonal
  omega

theorem Parameters.diagonal_pos {v k t b₂ b₃ b₄ : ℕ}
    (h : Parameters v k t b₂ b₃ b₄)
    (hd : defect v k b₂ b₃ b₄ < diagonal b₂ b₃ b₄) : 0 < diagonal b₂ b₃ b₄ :=
  lt_of_le_of_lt h.defect_nonneg hd

end CoveringDesigns.HorsleySingh
