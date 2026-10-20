import CoveringDesigns.TwoKMinusTwo.Capacity
import Mathlib.Tactic.Linarith

/-! Exact cross-loss accounting and refined per-block assignment capacity.
All sums retain occurrence identities. Formalisation: Rob Gardiner with AI assistance. -/

namespace CoveringDesigns.SaturatedMatching
open Finset
variable {α β γ : Type*} [DecidableEq β]

/-- Exact multiplicity count, retaining positive nonsaturated excess.
Natural subtraction is used only after the pair floor is supplied. -/
theorem cross_excess_identity (T : Finset γ) (μ : γ → ℕ)
    (hμ : ∀ z ∈ T, 2 ≤ μ z) :
    (∑ z ∈ T, μ z) + (T.filter (fun z => μ z = 2)).card =
      3*T.card + ∑ z ∈ T, (μ z - 3) := by
  classical
  have hp (z : γ) (hz : z ∈ T) :
      μ z + (if μ z = 2 then 1 else 0) = 3 + (μ z - 3) := by
    have hh := hμ z hz
    split_ifs <;> omega
  have hs := sum_congr rfl hp
  simpa [sum_add_distrib, ← card_filter, Nat.mul_comm] using hs

/-- Exact total capacity loss, including all individual block losses. -/
theorem loss_identity (A : Finset β) (w cap : β → ℕ)
    (hw : ∀ i ∈ A, w i ≤ cap i) :
    (∑ i ∈ A, (cap i - w i)) + (∑ i ∈ A, w i) = ∑ i ∈ A, cap i := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  exact Nat.sub_add_cancel (hw i hi)

/-- Division-free exact identity, with both capacity losses and positive
multiplicity excess. No loss term is discarded. -/
theorem cross_loss_identity (T : Finset γ) (A : Finset β)
    (μ : γ → ℕ) (w cap : β → ℕ)
    (hμ : ∀ z ∈ T, 2 ≤ μ z) (hw : ∀ i ∈ A, w i ≤ cap i)
    (hcount : ∑ z ∈ T, μ z = ∑ i ∈ A, w i) :
    (∑ i ∈ A, (cap i - w i)) + (∑ z ∈ T, (μ z - 3)) + 3*T.card =
      (∑ i ∈ A, cap i) + (T.filter (fun z => μ z = 2)).card := by
  have hm := cross_excess_identity T μ hμ
  have hl := loss_identity A w cap hw
  rw [hcount] at hm
  omega

/-- Vanishing total loss forces every individual capacity equality. -/
theorem balanced_of_loss_zero (A : Finset β) (w cap : β → ℕ)
    (hw : ∀ i ∈ A, w i ≤ cap i)
    (hz : ∑ i ∈ A, (cap i - w i) = 0) :
    ∀ i ∈ A, w i = cap i := by
  intro i hi
  have hh := (sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le (cap j - w j))).mp hz i hi
  have hc := hw i hi
  omega

/-- A single deficient occurrence loses its full deficit in the total. -/
theorem capacity_loss_at (A : Finset β) (w cap : β → ℕ)
    (hw : ∀ i ∈ A, w i ≤ cap i) {i : β} (hi : i ∈ A) :
    (∑ j ∈ A, w j) + (cap i - w i) ≤ ∑ j ∈ A, cap j := by
  have he := loss_identity A w cap hw
  have hl := single_le_sum (f := fun j => cap j - w j)
    (fun j _ => Nat.zero_le _) hi
  omega

/-- Refined shared-block bound. The lower incidence sum counts every point
at least twice; j actual intersections have size two. -/
theorem shared_block_bound {Q R : Finset β} (I : β → ℕ) {k : ℕ}
    (hk : 3 ≤ k) (hQ : 2 ≤ Q.card) (hRQ : R ⊆ Q)
    (hrow : 2*(k-1) ≤ ∑ D ∈ Q, I D)
    (hsmall : ∀ D ∈ R, I D = 2)
    (hcap : ∀ D ∈ Q, I D ≤ k-1) :
    (k-3)*R.card ≤ (Q.card-2)*(k-1) := by
  classical
  have hpoint (D : β) (hD : D ∈ Q) :
      I D + (if D ∈ R then k-3 else 0) ≤ k-1 := by
    split_ifs with hr
    · rw [hsmall D hr]; omega
    · have hh := hcap D hD; omega
  have hs := sum_le_sum hpoint
  have hf : Q.filter (· ∈ R) = R := filter_mem_eq_inter.trans (inter_eq_right.mpr hRQ)
  have he : (∑ D ∈ Q, if D ∈ R then k-3 else 0) = R.card*(k-3) := by
    rw [← sum_filter, hf]; simp
  rw [sum_add_distrib, he] at hs
  simp only [sum_const, Nat.nsmul_eq_mul] at hs
  have hq : Q.card-2+2=Q.card := by omega
  nlinarith

/-- Restrict an injection into block pairs to one first coordinate.
Only on this fibre is the second coordinate injective. -/
theorem assignment_fibre_bound {P Q : Finset β} {T : Finset γ}
    (f : γ → β × β) (I : β → β → ℕ) {k : ℕ}
    (hk : 3 ≤ k) (hQ : 2 ≤ Q.card)
    (htarget : ∀ z ∈ T, (f z).1 ∈ P ∧ (f z).2 ∈ Q)
    (hinj : Set.InjOn f T)
    (hrow : ∀ A ∈ P, 2*(k-1) ≤ ∑ E ∈ Q, I A E)
    (hsmall : ∀ z ∈ T, I (f z).1 (f z).2 = 2)
    (hcap : ∀ A ∈ P, ∀ E ∈ Q, I A E ≤ k-1) :
    ∀ A ∈ P, (k-3)*(T.filter (fun z => (f z).1 = A)).card ≤
      (Q.card-2)*(k-1) := by
  classical
  intro A hA
  let F := T.filter (fun z => (f z).1 = A)
  let R := F.image (fun z => (f z).2)
  have hR : R ⊆ Q := by
    intro E hE
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hE
    exact (htarget z (mem_filter.mp hz).1).2
  have hs : ∀ E ∈ R, I A E = 2 := by
    intro E hE
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hE
    rw [← (mem_filter.mp hz).2]
    exact hsmall z (mem_filter.mp hz).1
  have hi : Set.InjOn (fun z => (f z).2) F := by
    intro z hz w hw he
    apply hinj (mem_filter.mp hz).1 (mem_filter.mp hw).1
    exact Prod.ext ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm) he
  have hh := shared_block_bound (I A) hk hQ hR (hrow A hA) hs (hcap A hA)
  rwa [show R.card = F.card from card_image_of_injOn hi] at hh

/-- Sum the refined per-block estimate without division. -/
theorem assignment_total_bound {P Q : Finset β} {T : Finset γ}
    (f : γ → β × β) (I : β → β → ℕ) {k : ℕ}
    (hk : 3 ≤ k) (hQ : 2 ≤ Q.card)
    (htarget : ∀ z ∈ T, (f z).1 ∈ P ∧ (f z).2 ∈ Q)
    (hinj : Set.InjOn f T)
    (hrow : ∀ A ∈ P, 2*(k-1) ≤ ∑ E ∈ Q, I A E)
    (hsmall : ∀ z ∈ T, I (f z).1 (f z).2 = 2)
    (hcap : ∀ A ∈ P, ∀ E ∈ Q, I A E ≤ k-1) :
    (k-3)*T.card ≤ P.card*((Q.card-2)*(k-1)) := by
  have hh := sum_le_sum (assignment_fibre_bound f I hk hQ htarget hinj hrow hsmall hcap)
  have hp := card_eq_sum_card_fiberwise (f := fun z => (f z).1)
    (s := T) (t := P) (fun z hz => (htarget z hz).1)
  simpa only [← mul_sum, ← hp, sum_const, Nat.nsmul_eq_mul,
    Nat.mul_left_comm] using hh

end CoveringDesigns.SaturatedMatching
