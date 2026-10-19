import CoveringDesigns.Foundations.Links
import Mathlib.Tactic.Linarith

/-! Actual endpoint classes and finite trace counts for the saturated-pair argument. -/
namespace CoveringDesigns.C20_11_3
open Finset
variable {α : Type*} [DecidableEq α]

def onlyBlocks (C : Family α) (p q : α) : Family α :=
  C.filter (fun B => p ∈ B ∧ q ∉ B)

def neitherBlocks (C : Family α) (p q : α) : Family α :=
  C.filter (fun B => p ∉ B ∧ q ∉ B)

@[simp] theorem mem_onlyBlocks {C : Family α} {p q : α} {B : Finset α} :
    B ∈ onlyBlocks C p q ↔ B ∈ C ∧ p ∈ B ∧ q ∉ B := by
  simp [onlyBlocks]

@[simp] theorem mem_neitherBlocks {C : Family α} {p q : α} {B : Finset α} :
    B ∈ neitherBlocks C p q ↔ B ∈ C ∧ p ∉ B ∧ q ∉ B := by
  simp [neitherBlocks]

theorem onlyBlocks_card_add_pair (C : Family α) (p q : α) :
    (onlyBlocks C p q).card + degree (star C p) q = degree C p := by
  have h := card_filter_add_card_filter_not (s := star C p) (fun B => q ∈ B)
  simpa [degree, star, onlyBlocks, filter_filter, and_left_comm, Nat.add_comm] using h

theorem endpoint_sum_partition (C : Family α) (p q : α) (w : Finset α → ℕ) :
    (∑ B ∈ C, w B) =
      (∑ B ∈ onlyBlocks C p q, w B) +
      (∑ B ∈ onlyBlocks C q p, w B) +
      (∑ B ∈ neitherBlocks C p q, w B) +
      (∑ B ∈ star (star C p) q, w B) := by
  simp only [onlyBlocks, neitherBlocks, star, sum_filter, filter_filter]
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro B _
  by_cases hp : p ∈ B <;> by_cases hq : q ∈ B <;> simp [hp, hq]

theorem endpoint_card_partition (C : Family α) (p q : α) :
    C.card = (onlyBlocks C p q).card + (onlyBlocks C q p).card +
      (neitherBlocks C p q).card + degree (star C p) q := by
  simpa [degree] using endpoint_sum_partition C p q (fun _ => 1)

/-- Traces on complementary residual sets account for every nonendpoint. -/
theorem trace_sum [Fintype α] {p q : α} {X Y : Finset α}
    (hdis : Disjoint X Y) (hpart : X ∪ Y = univ \ {p,q}) (B : Finset α) :
    (X ∩ B).card + (Y ∩ B).card + (B ∩ {p,q}).card = B.card := by
  have he : (X ∩ B) ∪ (Y ∩ B) = B \ {p,q} := by
    rw [← union_inter_distrib_right, hpart]
    ext x
    simp [and_comm]
  rw [← card_union_of_disjoint (hdis.mono inter_subset_left inter_subset_left), he]
  exact card_sdiff_add_card_inter B {p,q}

theorem trace_sum_only [Fintype α] {p q : α} {X Y B : Finset α}
    (hdis : Disjoint X Y) (hpart : X ∪ Y = univ \ {p,q})
    (hB : B.card = 11) (hp : p ∈ B) (hq : q ∉ B) :
    (X ∩ B).card + (Y ∩ B).card = 10 := by
  have hi : B ∩ {p,q} = {p} := by ext x; simp; aesop
  have h := trace_sum hdis hpart B
  rw [hi, card_singleton, hB] at h
  omega

theorem trace_sum_neither [Fintype α] {p q : α} {X Y B : Finset α}
    (hdis : Disjoint X Y) (hpart : X ∪ Y = univ \ {p,q})
    (hB : B.card = 11) (hp : p ∉ B) (hq : q ∉ B) :
    (X ∩ B).card + (Y ∩ B).card = 11 := by
  have hi : B ∩ {p,q} = ∅ := by ext x; simp; aesop
  have h := trace_sum hdis hpart B
  rw [hi, card_empty, hB, Nat.add_zero] at h
  exact h

/-- Integer AM–GM at the size-ten and size-eleven trace boundaries. -/
theorem trace_product_le {a b : ℕ} :
    (a+b = 10 → a*b ≤ 25) ∧ (a+b = 11 → a*b ≤ 30) := by
  have hs := sq_nonneg ((a : ℤ) - (b : ℤ))
  constructor
  · intro h
    have hh : (a : ℤ)+(b : ℤ)=10 := by exact_mod_cast h
    have hab : (a : ℤ)*(b : ℤ) ≤ 25 := by nlinarith
    exact_mod_cast hab
  · intro h
    have hh : (a : ℤ)+(b : ℤ)=11 := by exact_mod_cast h
    have hab : (a : ℤ)*(b : ℤ) ≤ 30 := by nlinarith
    exact_mod_cast hab

/-- A block omitting an endpoint meets an endpoint block in at most ten points. -/
theorem intersection_le_ten {A D : Finset α} {p : α}
    (hA : A.card = 11) (hp : p ∈ A) (hpD : p ∉ D) :
    (A ∩ D).card ≤ 10 := by
  have hsub : A ∩ D ⊆ A.erase p := by
    intro z hz
    obtain ⟨hzA,hzD⟩ := mem_inter.mp hz
    exact mem_erase.mpr ⟨by intro he; subst z; exact hpD hzD, hzA⟩
  have h := card_le_card hsub
  rw [card_erase_of_mem hp, hA] at h
  exact h

/-- Summing the point degrees in one actual block exchanges the two incidences. -/
theorem intersection_sum (A : Finset α) (Q : Family α) :
    (∑ D ∈ Q, (A ∩ D).card) = ∑ z ∈ A, degree Q z := by
  simp only [← filter_mem_eq_inter, card_eq_sum_ones, degree, star, sum_filter]
  rw [sum_comm]

theorem endpoint_degree_partition (C : Family α) (p q z : α) :
    degree (star C q) z = degree (onlyBlocks C q p) z +
      degree (star (star C p) q) z := by
  have h := card_filter_add_card_filter_not (s := star (star C q) z) (fun B => p ∈ B)
  simpa [degree, star, onlyBlocks, filter_filter, and_assoc, and_left_comm,
    and_comm, Nat.add_comm] using h.symm

theorem residual_pair_eq [Fintype α] {p q z : α} {C : Family α} {B D : Finset α}
    (hstar : star (star C p) q = {B,D}) (hzB : z ∈ B) (hzD : z ∉ D) :
    degree (star C q) z = degree (onlyBlocks C q p) z + 1 := by
  rw [endpoint_degree_partition C p q z, hstar]
  simp [degree, star, filter_insert, filter_singleton, hzB, hzD]

/-- Equal unordered pairs have equal ordered representatives across disjoint sides. -/
theorem cross_pair_eq_of_pair_eq {X Y : Finset α} (hdis : Disjoint X Y)
    {a b : α × α} (ha : a ∈ X ×ˢ Y) (hb : b ∈ X ×ˢ Y)
    (he : ({a.1,a.2} : Finset α) = {b.1,b.2}) : a = b := by
  obtain ⟨haX,haY⟩ := mem_product.mp ha
  obtain ⟨hbX,hbY⟩ := mem_product.mp hb
  have hfst : a.1 = b.1 := by
    have hm : a.1 ∈ ({b.1,b.2} : Finset α) := by rw [← he]; simp
    rcases mem_insert.mp hm with hh | hh
    · exact hh
    · have hh' := mem_singleton.mp hh
      exact (disjoint_left.mp hdis haX (hh' ▸ hbY)).elim
  have hsnd : a.2 = b.2 := by
    have hm : a.2 ∈ ({b.1,b.2} : Finset α) := by rw [← he]; simp
    rcases mem_insert.mp hm with hh | hh
    · exact (disjoint_left.mp hdis (hh ▸ hbX) haY).elim
    · exact mem_singleton.mp hh
  exact Prod.ext hfst hsnd

/-- The same actual four blocks must meet the ten residual points twice each. -/
theorem shared_intersection_sum {C : Family α} {p q : α} {A : Finset α}
    (hA : A.card = 11) (hpA : p ∈ A) (hqA : q ∉ A)
    (hpoint : ∀ z, z ≠ p → z ≠ q → 2 ≤ degree (onlyBlocks C q p) z) :
    20 ≤ ∑ D ∈ onlyBlocks C q p, (A ∩ D).card := by
  rw [intersection_sum]
  have hc : (A.erase p).card = 10 := by rw [card_erase_of_mem hpA,hA]
  calc
    20 = ∑ z ∈ A.erase p, 2 := by simp [hc]
    _ ≤ ∑ z ∈ A.erase p, degree (onlyBlocks C q p) z := by
      apply sum_le_sum
      intro z hz
      obtain ⟨hzp,hzA⟩ := mem_erase.mp hz
      exact hpoint z hzp (by intro h; subst z; exact hqA hzA)
    _ ≤ ∑ z ∈ A, degree (onlyBlocks C q p) z := by
      exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (by intros; exact Nat.zero_le _)

end CoveringDesigns.C20_11_3
