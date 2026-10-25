import CoveringDesigns.C19_9_3.AffineModel

/-! The three column forms, deduced by integral character orthogonality.
The hypotheses name the local Fano structure that an actual recognition
theorem must supply; this is not itself the parent exclusion. -/
namespace CoveringDesigns.C19_9_3
open Finset

def completeDirections (D : Finset (Fin 7)) : Finset PlanePosition := D ×ˢ univ

private def bothDirections (U : Finset PlanePosition) : Finset (Fin 7) :=
  univ.filter fun n => (n,false) ∈ U ∧ (n,true) ∈ U

private theorem coefficient_zero_iff (U : Finset PlanePosition) (n : Fin 7) :
    columnCoefficient U n = 0 ↔ ((n,false) ∈ U ↔ (n,true) ∈ U) := by
  by_cases h0 : (n,false) ∈ U <;> by_cases h1 : (n,true) ∈ U <;>
    simp [columnCoefficient,h0,h1]

private theorem complete_of_zero (U : Finset PlanePosition)
    (h : ∀ n, columnCoefficient U n = 0) : U = completeDirections (bothDirections U) := by
  ext p
  rcases p with ⟨n,b⟩
  have hn := (coefficient_zero_iff U n).mp (h n)
  cases b <;> simp [completeDirections,bothDirections,hn]

private theorem directions_complete (D : Finset (Fin 7)) (x : Fin 8) :
    columnDirections (completeDirections D) x = D := by
  ext n
  simp [columnDirections,completeDirections]

private theorem card_complete (D : Finset (Fin 7)) : (completeDirections D).card = 2 * D.card := by
  simp [completeDirections,Nat.mul_comm]

private theorem single_of_coefficients (U : Finset PlanePosition) (n : Fin 7)
    (hn : columnCoefficient U n = 1 ∨ columnCoefficient U n = -1)
    (hr : ∀ m, m ≠ n → columnCoefficient U m = 0) :
    ∃ b : Bool, n ∉ bothDirections U ∧ U = insert (n,b) (completeDirections (bothDirections U)) := by
  have hex : ∃ b : Bool, (n,b) ∈ U ∧ (n,!b) ∉ U := by
    by_cases h0 : (n,false) ∈ U <;> by_cases h1 : (n,true) ∈ U <;>
      simp [columnCoefficient,h0,h1] at hn
    · exact ⟨false,h0,h1⟩
    · exact ⟨true,h1,h0⟩
  obtain ⟨b,hb,hnB⟩ := hex
  have hnb : n ∉ bothDirections U := by
    cases b <;> simp_all [bothDirections]
  refine ⟨b,hnb,?_⟩
  ext p
  rcases p with ⟨m,c⟩
  by_cases hmn : m = n
  · subst m
    cases b <;> cases c <;> simp_all [completeDirections]
  · have he := (coefficient_zero_iff U m).mp (hr m hmn)
    cases c <;> simp [completeDirections,bothDirections,hmn,he]

private theorem insert_directions (D : Finset (Fin 7)) (n : Fin 7) (b : Bool) (x : Fin 8)
    (hx : orientation n x ≠ b) :
    columnDirections (insert (n,b) (completeDirections D)) x = D := by
  ext m
  simp only [columnDirections,mem_filter,mem_univ,true_and,mem_insert,
    Prod.mk.injEq,completeDirections,mem_product,and_true]
  constructor
  · rintro (⟨rfl,he⟩ | hm)
    · exact False.elim (hx he)
    · exact hm
  · exact Or.inr

private theorem exists_other_side (n : Fin 7) (b : Bool) :
    ∃ x : Fin 8, orientation n x ≠ b := by
  have hc := affine_plane_card (n,b)
  by_contra hn
  push Not at hn
  have he : affinePlane (n,b) = univ := by ext x; simp [affinePlane,hn]
  rw [he] at hc
  norm_num at hc

private theorem four_set_contains_line : ∀ D ∈ (univ : Finset (Fin 7)).powersetCard 4,
    (∀ l, (D ∩ SevenBlock.line l).Nonempty) → ∃ l, SevenBlock.line l ⊆ D := by
  decide +kernel

/-- A column has one of the three reviewed forms. The proof is universal in
the selected plane set: constant character sums give complete directions;
unit square gives precisely one single direction. -/
theorem column_forms (U : Finset PlanePosition) (j : ℕ)
    (hj : j ≤ 2) (hsize : U.card + j = 8)
    (hvalue : ∀ x : Fin 8, 3 ≤ columnValue U x ∧ columnValue U x ≤ 4)
    (hlow : ∀ x, columnValue U x = 3 → ∃ l, columnDirections U x = SevenBlock.line l)
    (hhigh : ∀ x, columnValue U x = 4 → ∀ l, (columnDirections U x ∩ SevenBlock.line l).Nonempty) :
    (j = 2 ∧ ∃ l, U = completeDirections (SevenBlock.line l)) ∨
    (j = 1 ∧ ∃ l n b, n ∉ SevenBlock.line l ∧
      U = insert (n,b) (completeDirections (SevenBlock.line l))) ∨
    (j = 0 ∧ ∃ D, D.card = 4 ∧ (∃ l, SevenBlock.line l ⊆ D) ∧ U = completeDirections D) := by
  have hsum := column_incidence_sum U
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · have hconst (x : Fin 8) : columnValue U x = 4 := by
      have hs : (∑ x : Fin 8, columnValue U x) = ∑ _ : Fin 8, (4 : ℕ) := by simp; omega
      exact (sum_eq_sum_iff_of_le (fun x _ => (hvalue x).2)).mp hs x (mem_univ _)
    have hcoef : ∀ n, columnCoefficient U n = 0 := by
      apply coefficients_zero
      intro x
      have he := column_character_identity U x
      rw [hconst] at he
      omega
    have he := complete_of_zero U hcoef
    have hd : (bothDirections U).card = 4 := by
      have := congrArg card he
      rw [card_complete] at this
      omega
    have hm (l : Fin 7) : (bothDirections U ∩ SevenBlock.line l).Nonempty := by
      have hh := hhigh 0 (hconst 0) l
      rw [he,directions_complete] at hh
      exact hh
    exact Or.inr (Or.inr ⟨rfl,bothDirections U,hd,
      four_set_contains_line _ (mem_powersetCard_univ.mpr hd) hm,he⟩)
  · have hsq (x : Fin 8) : (∑ n : Fin 7, columnCoefficient U n * character n x)^2 = 1 := by
      rw [← column_character_identity]
      have hv := hvalue x
      have he : columnValue U x = 3 ∨ columnValue U x = 4 := by omega
      rcases he with he | he <;> rw [he] <;> norm_num <;> have hc : U.card = 7 := by omega
      all_goals rw [hc]; norm_num
    obtain ⟨n,hn,hr⟩ := character_unit_square (columnCoefficient U) hsq
    obtain ⟨b,hnb,he⟩ := single_of_coefficients U n hn hr
    have hd : (bothDirections U).card = 3 := by
      have hnot : (n,b) ∉ completeDirections (bothDirections U) := by
        simpa only [completeDirections,mem_product,mem_univ,and_true] using hnb
      have hc := congrArg card he
      rw [card_insert_of_notMem hnot,card_complete] at hc
      omega
    obtain ⟨x,hx⟩ := exists_other_side n b
    have hdir : columnDirections U x = bothDirections U := by
      calc
        columnDirections U x = columnDirections (insert (n,b) (completeDirections (bothDirections U))) x :=
          congrArg (fun S => columnDirections S x) he
        _ = bothDirections U := insert_directions _ n b x hx
    have hv : columnValue U x = 3 := by rw [columnValue,hdir,hd]
    obtain ⟨l,hl⟩ := hlow x hv
    rw [hdir] at hl
    exact Or.inr (Or.inl ⟨rfl,l,n,b,hl ▸ hnb,by rw [← hl]; exact he⟩)
  · have hconst (x : Fin 8) : columnValue U x = 3 := by
      have hs : (∑ _ : Fin 8, (3 : ℕ)) = ∑ x : Fin 8, columnValue U x := by simp; omega
      exact ((sum_eq_sum_iff_of_le (fun x _ => (hvalue x).1)).mp hs x (mem_univ _)).symm
    have hcoef : ∀ n, columnCoefficient U n = 0 := by
      apply coefficients_zero
      intro x
      have he := column_character_identity U x
      rw [hconst] at he
      omega
    have he := complete_of_zero U hcoef
    obtain ⟨l,hl⟩ := hlow 0 (hconst 0)
    rw [he,directions_complete] at hl
    exact Or.inl ⟨rfl,l,by rw [← hl]; exact he⟩

#guard_standard_axioms column_forms

end CoveringDesigns.C19_9_3
