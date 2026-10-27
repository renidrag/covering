import CoveringDesigns.TruncatedPlaneLoads.CommonCoordinate

/-! The two weighted incidence identities used in the load classification. -/

namespace CoveringDesigns.TruncatedPlaneLoads
open Finset
variable {V G I : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable {q : ℕ} (P : Plane q V G)

namespace Plane

theorem extra_group_card {i j : G} {a : V} (ha : P.group a ≠ i) :
    ((P.extra i a).filter (P.group · = j)).card =
      (if i = j then q else 0) + (if P.group a = j then 1 else 0) := by
  have he : ((P.groupSet i).filter (P.group · = j)) =
      if i = j then P.groupSet i else ∅ := by
    split_ifs with h
    · subst j
      ext x
      simp
    · ext x
      simp only [mem_filter, mem_groupSet, notMem_empty, iff_false]
      rintro ⟨hx, hj⟩
      exact h (hx.symm.trans hj)
  rw [extra, filter_insert]
  by_cases h : P.group a = j
  · simp only [if_pos h]
    rw [card_insert_of_notMem (by simp [ha]), he]
    split_ifs <;> simp
  · simp only [if_neg h, he]
    split_ifs <;> simp

theorem extra_edge_card {i : G} {a : V} (ha : P.group a ≠ i)
    {E : Finset V} (hE : E ∈ P.core) :
    (E ∩ P.extra i a).card = 1 + if a ∈ E then 1 else 0 := by
  have hg : E ∩ P.groupSet i = E.filter (P.group · = i) := by ext x; simp
  by_cases h : a ∈ E
  · have he : E ∩ P.extra i a = insert a (E ∩ P.groupSet i) := by
      ext x; simp [extra, h]
    rw [he, card_insert_of_notMem (by simp [ha]), hg, P.transversal E hE i]
    simp [h]
  · have he : E ∩ P.extra i a = E ∩ P.groupSet i := by
      ext x
      simp only [mem_inter, mem_extra, mem_groupSet]
      constructor
      · rintro ⟨hx, rfl | hx'⟩
        · exact (h hx).elim
        · exact ⟨hx, hx'⟩
      · exact fun hx => ⟨hx.1, Or.inr hx.2⟩
    rw [he, hg, P.transversal E hE i]
    simp [h]

end Plane

namespace Internal

/-- Intermediate data obtained by the proved support classification. It is
not the finite-plane contract or a hypothesis of the final family theorem. -/
structure Loads [Fintype I] (P : Plane q V G) (K : ℝ) where
  coreWeight : Finset V → ℝ
  base : I → G
  tip : I → V
  weight : I → ℝ
  outside : ∀ j, P.group (tip j) ≠ base j
  injective : Function.Injective (fun j => (base j, tip j))
  core_pos : ∀ E ∈ P.core, 0 < coreWeight E
  extra_pos : ∀ j, 0 < weight j
  meet : ∀ j k, base j ≠ base k →
    P.group (tip j) = base k ∨ P.group (tip k) = base j ∨ tip j = tip k
  load : ∀ x,
    (∑ E ∈ P.core, if x ∈ E then coreWeight E else 0) +
      (∑ j, if x ∈ P.extra (base j) (tip j) then weight j else 0) = K

variable {P} [Fintype I] {K : ℝ} (D : Loads (I := I) P K)

namespace Loads

def coreMass : ℝ := ∑ E ∈ P.core, D.coreWeight E
def extraMass : ℝ := ∑ j, D.weight j
def baseMass (i : G) : ℝ := ∑ j, if D.base j = i then D.weight j else 0
def tipMass (i : G) : ℝ := ∑ j, if P.group (D.tip j) = i then D.weight j else 0
def edgeMass (E : Finset V) : ℝ := ∑ j, if D.tip j ∈ E then D.weight j else 0

private theorem weighted_intersection {J : Type*} (F : Finset J)
    (B : J → Finset V) (w : J → ℝ) (S : Finset V) :
    (∑ x ∈ S, ∑ j ∈ F, if x ∈ B j then w j else 0) =
      ∑ j ∈ F, ((S ∩ B j).card : ℝ) * w j := by
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [← sum_filter]
  have h : S.filter (· ∈ B j) = S ∩ B j := by ext x; simp
  simp [h]

theorem sum_load (S : Finset V) :
    (S.card : ℝ) * K =
      (∑ E ∈ P.core, ((S ∩ E).card : ℝ) * D.coreWeight E) +
        ∑ j, ((S ∩ P.extra (D.base j) (D.tip j)).card : ℝ) * D.weight j := by
  calc
    _ = ∑ x ∈ S, K := by simp
    _ = ∑ x ∈ S, ((∑ E ∈ P.core, if x ∈ E then D.coreWeight E else 0) +
        ∑ j, if x ∈ P.extra (D.base j) (D.tip j) then D.weight j else 0) := by
      apply sum_congr rfl
      intro x hx
      exact (D.load x).symm
    _ = _ := by rw [sum_add_distrib, weighted_intersection, weighted_intersection]

theorem total_mass : D.coreMass + D.extraMass = q*K := by
  have h := D.sum_load univ
  simp only [card_univ, univ_inter, P.coordinates_card, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one] at h
  have he : (∑ E ∈ P.core, ((E.card : ℕ) : ℝ) * D.coreWeight E) =
      (q+1 : ℝ) * D.coreMass := by
    unfold coreMass
    rw [mul_sum]
    apply sum_congr rfl
    intro E hE
    rw [P.core_size hE, Nat.cast_add, Nat.cast_one]
  have hx : (∑ j : I, (((P.extra (D.base j) (D.tip j)).card : ℕ) : ℝ) * D.weight j) =
      (q+1 : ℝ) * D.extraMass := by
    simp [P.extra_size (D.outside _), extraMass, mul_sum]
  rw [he, hx] at h
  have hq : (0 : ℝ) < q+1 := by positivity
  nlinarith

theorem group_equation (i : G) : q * D.baseMass i + D.tipMass i = D.extraMass := by
  have h := D.sum_load (P.groupSet i)
  rw [P.groupSet_card] at h
  have he : (∑ E ∈ P.core, (((P.groupSet i ∩ E).card : ℕ) : ℝ) * D.coreWeight E) =
      D.coreMass := by
    apply sum_congr rfl
    intro E hE
    have hh : P.groupSet i ∩ E = E.filter (P.group · = i) := by ext x; simp [and_comm]
    rw [hh, P.transversal E hE i]
    simp
  have hx : (∑ j : I, (((P.groupSet i ∩ P.extra (D.base j) (D.tip j)).card : ℕ) : ℝ) * D.weight j) =
      q * D.baseMass i + D.tipMass i := by
    unfold baseMass tipMass
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    have hh : P.groupSet i ∩ P.extra (D.base j) (D.tip j) =
        (P.extra (D.base j) (D.tip j)).filter (P.group · = i) := by ext x; simp [and_comm]
    rw [hh, P.extra_group_card (D.outside j)]
    split_ifs <;> simp_all <;> ring
  rw [he, hx] at h
  have ht := D.total_mass
  linarith

theorem core_equation {E : Finset V} (hE : E ∈ P.core) :
    q * D.coreWeight E + D.edgeMass E = K := by
  have h := D.sum_load E
  rw [P.core_size hE, Nat.cast_add, Nat.cast_one] at h
  have he : (∑ F ∈ P.core, (((E ∩ F).card : ℕ) : ℝ) * D.coreWeight F) =
      D.coreMass + q * D.coreWeight E := by
    have hf (F : Finset V) (hF : F ∈ P.core) :
        (((E ∩ F).card : ℕ) : ℝ) * D.coreWeight F =
          D.coreWeight F + if F = E then q * D.coreWeight E else 0 := by
      by_cases hFE : F = E
      · subst F
        simp [P.core_size hE]
        ring
      · rw [P.intersection E hE F hF (Ne.symm hFE)]
        simp [hFE]
    rw [sum_congr rfl hf, sum_add_distrib]
    simp [coreMass, hE]
  have hx : (∑ j : I, (((E ∩ P.extra (D.base j) (D.tip j)).card : ℕ) : ℝ) * D.weight j) =
      D.extraMass + D.edgeMass E := by
    unfold extraMass edgeMass
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rw [P.extra_edge_card (D.outside j) hE]
    split_ifs <;> simp <;> ring
  rw [he, hx] at h
  have ht := D.total_mass
  linarith

end Loads
end Internal
end CoveringDesigns.TruncatedPlaneLoads
