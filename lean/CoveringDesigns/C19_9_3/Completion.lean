import CoveringDesigns.C19_9_3.ActualColumns
import CoveringDesigns.C19_9_3.Fifteen

/-! Internal finite budgets on the eleven actual nonminimum columns.
This bookkeeping is not a separate supported classification interface. -/
namespace CoveringDesigns.C19_9_3.Internal
open Finset SevenBlock

def ColumnForm (U : Finset PlanePosition) (E : Finset Bool) : Prop :=
  (E.card = 2 ∧ ∃ l, U = completeDirections (line l)) ∨
  (E.card = 1 ∧ ∃ l n b, n ∉ line l ∧ U = insert (n,b) (completeDirections (line l))) ∨
  (E.card = 0 ∧ ∃ D, D.card = 4 ∧ (∃ l, line l ⊆ D) ∧ U = completeDirections D)

structure Completion (X : Type*) [Fintype X] [DecidableEq X] where
  plane : X → Finset PlanePosition
  avoid : X → Finset Bool
  form : ∀ x, ColumnForm (plane x) (avoid x)
  plane_row : ∀ p, (univ.filter fun x => p ∈ plane x).card = 5
  avoid_row : ∀ b, (univ.filter fun x => b ∈ avoid x).card = 9
  avoid_distinct : (univ.filter fun x => false ∈ avoid x) ≠ (univ.filter fun x => true ∈ avoid x)
  triples : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
    (plane x ∩ plane y ∩ plane z).Nonempty ∨ (avoid x ∩ avoid y ∩ avoid z).Nonempty

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem nonminimum_card {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16) :
    Fintype.card {x : V // x ∉ minimumPoints B} = 11 := by
  rw [Fintype.card_subtype_compl,Fintype.card_coe,hv,minimum_points_card hv h hi]

theorem actual_completion {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16) :
    Nonempty (Completion {x : V // x ∉ minimumPoints B}) := by
  classical
  obtain ⟨F⟩ := actual_affine_configuration hv h hi
  let X := {x : V // x ∉ minimumPoints B}
  let U (x : X) := F.planeColumn x.val
  let E (x : X) := F.emptyColumn x.val
  have row (i : I) : (univ.filter fun x : X => x.val ∈ B i).card =
      (B i \ minimumPoints B).card := by
    have he : (univ.filter fun x : X => x.val ∈ B i) = (B i).subtype (· ∉ minimumPoints B) := by
      ext x
      simp only [mem_filter,mem_univ,true_and]
      constructor
      · exact fun hx => mem_subtype.mpr hx
      · exact fun hx => mem_subtype.mp hx
    rw [he,card_subtype]
    congr 1
    ext x
    simp
  refine ⟨⟨U,E,?_,?_,?_,?_,?_⟩⟩
  · intro x
    exact actual_column_forms hv h hi F x.val x.property
  · intro p
    have he : (univ.filter fun x : X => p ∈ U x) = univ.filter fun x : X => x.val ∈ B (F.planes p) := by
      ext x
      simp [U,AffineConfiguration.planeColumn]
    rw [he,row,affine_nonminimum_row hv h hi F p]
  · intro b
    have he : (univ.filter fun x : X => b ∈ E x) = univ.filter fun x : X => x.val ∈ B (F.empty b) := by
      ext x
      simp [E,AffineConfiguration.emptyColumn]
    rw [he,row,empty_nonminimum_row h.1 F b]
  · intro he
    have hB : B (F.empty false) = B (F.empty true) := by
      ext x
      by_cases hx : x ∈ minimumPoints B
      · exact iff_of_false (F.avoidance false ⟨x,hx⟩) (F.avoidance true ⟨x,hx⟩)
      · have hh := Finset.ext_iff.mp he (⟨x,hx⟩ : X)
        simpa only [E,AffineConfiguration.emptyColumn,mem_filter,mem_univ,true_and] using hh
    have hh := F.empty.injective (sixteen_blocks_injective hv h hi hB)
    contradiction
  · intro x y z hxy hxz hyz
    have hxy' : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
    have hxz' : x.val ≠ z.val := fun he => hxz (Subtype.ext he)
    have hyz' : y.val ≠ z.val := fun he => hyz (Subtype.ext he)
    obtain ⟨i,hT⟩ := (Multicover.covers_one_iff B 3).mp h.2 {x.val,y.val,z.val}
      (by simp [hxy',hxz',hyz'])
    have hx : x.val ∈ B i := hT (by simp)
    have hy : y.val ∈ B i := hT (by simp)
    have hz : z.val ∈ B i := hT (by simp)
    rcases F.partition i with ⟨p,rfl⟩ | ⟨b,rfl⟩
    · left
      exact ⟨p,by simp [U,AffineConfiguration.planeColumn,hx,hy,hz]⟩
    · right
      exact ⟨b,by simp [E,AffineConfiguration.emptyColumn,hx,hy,hz]⟩

variable {X : Type*} [Fintype X] [DecidableEq X]

def Completion.class (C : Completion X) (j : ℕ) := univ.filter fun x => (C.avoid x).card = j

theorem Completion.budgets (C : Completion X) (hc : Fintype.card X = 11) :
    ((C.class 2).card = 9 ∧ (C.class 1).card = 0 ∧ (C.class 0).card = 2) ∨
    ((C.class 2).card = 8 ∧ (C.class 1).card = 2 ∧ (C.class 0).card = 1) ∨
    ((C.class 2).card = 7 ∧ (C.class 1).card = 4 ∧ (C.class 0).card = 0) := by
  have hsum : (∑ x : X, (C.avoid x).card) = 18 := by
    have hh := Multicover.degree_sum C.avoid
    have hr (b : Bool) : indexedDegree C.avoid b = 9 := C.avoid_row b
    simp only [hr,sum_const,card_univ,Fintype.card_bool,Nat.nsmul_eq_mul] at hh
    omega
  have hcases (x : X) : (C.avoid x).card = 0 ∨ (C.avoid x).card = 1 ∨ (C.avoid x).card = 2 := by
    have hle : (C.avoid x).card ≤ 2 := (card_le_univ _).trans_eq (by simp)
    omega
  have hterm (x : X) : (C.avoid x).card =
      2*(if (C.avoid x).card = 2 then 1 else 0) + (if (C.avoid x).card = 1 then 1 else 0) := by
    rcases hcases x with hh | hh | hh <;> simp [hh]
  have hone (x : X) : (if (C.avoid x).card = 2 then 1 else 0) +
      (if (C.avoid x).card = 1 then 1 else 0) + (if (C.avoid x).card = 0 then 1 else 0) = 1 := by
    rcases hcases x with hh | hh | hh <;> simp [hh]
  have hcard (j : ℕ) : (∑ x : X, if (C.avoid x).card = j then 1 else 0) = (C.class j).card := by
    rw [← sum_filter,sum_const,Nat.nsmul_eq_mul,mul_one]
    rfl
  have htotsum := sum_congr (s₁ := (univ : Finset X)) rfl (fun x _ => hterm x)
  rw [sum_add_distrib,← mul_sum,hcard,hcard,hsum] at htotsum
  have hh := sum_congr (s₁ := (univ : Finset X)) rfl (fun x _ => hone x)
  simp only [sum_add_distrib,hcard,sum_const,card_univ,hc,Nat.nsmul_eq_mul,mul_one] at hh
  omega

private theorem avoiding_agreement : ∀ E : Finset Bool, E.card ≠ 1 → (false ∈ E ↔ true ∈ E) := by
  decide +kernel

theorem Completion.exclude_no_single (C : Completion X) (h0 : (C.class 1).card = 0) : False := by
  apply C.avoid_distinct
  ext x
  simp only [mem_filter,mem_univ,true_and]
  apply avoiding_agreement
  intro hx
  have hm : x ∈ C.class 1 := mem_filter.mpr ⟨mem_univ _,hx⟩
  rw [card_eq_zero.mp h0] at hm
  exact notMem_empty _ hm

end CoveringDesigns.C19_9_3.Internal
