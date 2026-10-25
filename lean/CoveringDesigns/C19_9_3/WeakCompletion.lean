import CoveringDesigns.C19_9_3.ActualColumns

/-! The completion interface needed by the shorter obstruction. Occurrence
images may repeat; a four-direction column need not contain a Fano line. -/
namespace CoveringDesigns.C19_9_3
open Finset SevenBlock

def WeakColumnForm (U : Finset PlanePosition) (E : Finset Bool) : Prop :=
  (E.card = 2 ∧ ∃ l, U = completeDirections (line l)) ∨
  (E.card = 1 ∧ ∃ l n b, n ∉ line l ∧ U = insert (n,b) (completeDirections (line l))) ∨
  (E.card = 0 ∧ ∃ D, D.card = 4 ∧ U = completeDirections D)

structure WeakCompletion (X : Type*) [Fintype X] [DecidableEq X] where
  plane : X → Finset PlanePosition
  avoid : X → Finset Bool
  form : ∀ x, WeakColumnForm (plane x) (avoid x)
  plane_row : ∀ p, (univ.filter fun x => p ∈ plane x).card = 5
  avoid_row : ∀ b, (univ.filter fun x => b ∈ avoid x).card = 9
  triples : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
    (plane x ∩ plane y ∩ plane z).Nonempty ∨ (avoid x ∩ avoid y ∩ avoid z).Nonempty


variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- Direct transfer of the actual indexed covering to the weaker completion.
No fifteen-occurrence exclusion or exceptional-image distinctness is used. -/
theorem actual_weak_completion {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16) :
    Nonempty (WeakCompletion {x : V // x ∉ minimumPoints B}) := by
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
  refine ⟨⟨U,E,?_,?_,?_,?_⟩⟩
  · intro x
    rcases actual_column_forms hv h hi F x.val x.property with ha | hb | ⟨he,D,hD,_,hU⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr ⟨he,D,hD,hU⟩)
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

#guard_standard_axioms actual_weak_completion

namespace Internal.Short
open Finset SevenBlock

variable {X : Type*} [Fintype X] [DecidableEq X]

def pointClass (C : WeakCompletion X) (j : ℕ) := univ.filter fun x => (C.avoid x).card = j

theorem budgets (C : WeakCompletion X) (hc : Fintype.card X = 11) :
    (pointClass C 2).card + (pointClass C 1).card + (pointClass C 0).card = 11 ∧
    2*(pointClass C 2).card + (pointClass C 1).card = 18 ∧
    (pointClass C 1).card + 2*(pointClass C 0).card = 4 := by
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
  have hcard (j : ℕ) : (∑ x : X, if (C.avoid x).card = j then 1 else 0) = (pointClass C j).card := by
    rw [← sum_filter,sum_const,Nat.nsmul_eq_mul,mul_one]
    rfl
  have htotsum := sum_congr (s₁ := (univ : Finset X)) rfl (fun x _ => hterm x)
  rw [sum_add_distrib,← mul_sum,hcard,hcard,hsum] at htotsum
  have hh := sum_congr (s₁ := (univ : Finset X)) rfl (fun x _ => hone x)
  simp only [sum_add_distrib,hcard,sum_const,card_univ,hc,Nat.nsmul_eq_mul,mul_one] at hh
  omega

inductive Column where
  | a (l : Fin 7)
  | b (l n : Fin 7) (side avoiding : Bool)
  | c (directions : Finset (Fin 7))
deriving DecidableEq

def Column.plane : Column → Finset PlanePosition
  | .a l => completeDirections (line l)
  | .b l n side _ => insert (n,side) (completeDirections (line l))
  | .c D => completeDirections D

def Column.avoid : Column → Finset Bool
  | .a _ => univ
  | .b _ _ _ e => {e}
  | .c _ => ∅

def Column.Valid : Column → Prop
  | .a _ => True
  | .b l n _ _ => n ∉ line l
  | .c D => D.card = 4

def Column.base : Column → Option (Fin 7)
  | .a l | .b l _ _ _ => some l
  | .c _ => none

def Column.extra : Column → Option PlanePosition
  | .b _ n side _ => some (n,side)
  | _ => none

def Column.wide : Column → Finset (Fin 7)
  | .c D => D
  | _ => ∅

private theorem column_normal_form (U : Finset PlanePosition) (E : Finset Bool)
    (h : WeakColumnForm U E) : ∃ c : Column, c.Valid ∧ U = c.plane ∧ E = c.avoid := by
  rcases h with ⟨he,l,hl⟩ | ⟨he,l,n,b,hn,hl⟩ | ⟨he,D,hD,hU⟩
  · refine ⟨.a l,True.intro,hl,?_⟩
    exact eq_univ_of_card E (by simpa using he)
  · obtain ⟨e,heE⟩ := card_eq_one.mp he
    exact ⟨.b l n b e,hn,hl,heE⟩
  · exact ⟨.c D,hD,hU,card_eq_zero.mp he⟩

variable {X : Type*} [Fintype X] [DecidableEq X]

structure Normalized (C : WeakCompletion X) where
  col : X → Column
  valid : ∀ x, (col x).Valid
  plane : ∀ x, C.plane x = (col x).plane
  avoid : ∀ x, C.avoid x = (col x).avoid

theorem normalize (C : WeakCompletion X) : Nonempty (Normalized C) := by
  choose col hv hp he using fun x => column_normal_form (C.plane x) (C.avoid x) (C.form x)
  exact ⟨⟨col,hv,hp,he⟩⟩

def Normalized.weight {C : WeakCompletion X} (N : Normalized C) (l : Fin 7) :=
  (univ.filter fun x => (N.col x).base = some l).card

def Normalized.single {C : WeakCompletion X} (N : Normalized C) (n : Fin 7) (b : Bool) :=
  (univ.filter fun x => (N.col x).extra = some (n,b)).card

def Normalized.wideCount {C : WeakCompletion X} (N : Normalized C) (n : Fin 7) :=
  (univ.filter fun x => n ∈ (N.col x).wide).card

private theorem base_row (c : Column) (n : Fin 7) :
    (∑ l : Fin 7, if n ∈ line l ∧ c.base = some l then 1 else 0) =
      match c.base with | none => 0 | some l => if n ∈ line l then 1 else 0 := by
  cases c with
  | a l => simp [Column.base,and_comm,ite_and]
  | b l m b e => simp [Column.base,and_comm,ite_and]
  | c D => simp [Column.base]

private theorem column_row (c : Column) (hc : c.Valid) (n : Fin 7) (b : Bool) :
    (if (n,b) ∈ c.plane then 1 else 0) =
      (match c.base with | none => 0 | some l => if n ∈ line l then 1 else 0) +
      (if c.extra = some (n,b) then 1 else 0) + (if n ∈ c.wide then 1 else 0) := by
  cases c with
  | a l => simp [Column.plane,Column.base,Column.extra,Column.wide,completeDirections]
  | c D => by_cases hn : n ∈ D <;> simp [Column.plane,Column.base,Column.extra,Column.wide,completeDirections,hn]
  | b l m s e =>
    change m ∉ line l at hc
    by_cases hnm : n = m
    · subst n
      simp [Column.plane,Column.base,Column.extra,Column.wide,completeDirections,hc,eq_comm]
    · simp [Column.plane,Column.base,Column.extra,Column.wide,completeDirections,hnm,Ne.symm hnm]

theorem Normalized.row {C : WeakCompletion X} (N : Normalized C) (n : Fin 7) (b : Bool) :
    (∑ l ∈ univ.filter (fun l => n ∈ line l), N.weight l) + N.single n b + N.wideCount n = 5 := by
  have hb : (∑ l ∈ univ.filter (fun l => n ∈ line l), N.weight l) =
      ∑ x : X, (match (N.col x).base with | none => 0 | some l => if n ∈ line l then 1 else 0) := by
    simp only [Normalized.weight,card_eq_sum_ones,sum_filter]
    have hp (l : Fin 7) : (if n ∈ line l then ∑ x : X, if (N.col x).base = some l then 1 else 0 else 0) =
        ∑ x : X, if n ∈ line l ∧ (N.col x).base = some l then 1 else 0 := by
      by_cases hn : n ∈ line l <;> simp [hn]
    simp_rw [hp]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    exact base_row (N.col x) n
  have hr := C.plane_row (n,b)
  have ht := sum_congr (s₁ := (univ : Finset X)) rfl (fun x _ => column_row (N.col x) (N.valid x) n b)
  simp_rw [← N.plane] at ht
  simp only [sum_add_distrib] at ht
  rw [← hb] at ht
  have hs : (∑ x : X, if (N.col x).extra = some (n,b) then 1 else 0) = N.single n b := by
    simp only [Normalized.single,card_eq_sum_ones,sum_filter]
  have hw : (∑ x : X, if n ∈ (N.col x).wide then 1 else 0) = N.wideCount n := by
    simp only [Normalized.wideCount,card_eq_sum_ones,sum_filter]
  have hleft : (∑ x : X, if (n,b) ∈ C.plane x then 1 else 0) = 5 := by
    simpa only [card_eq_sum_ones,sum_filter] using hr
  rw [hs,hw,hleft] at ht
  exact ht.symm

theorem Normalized.single_balanced {C : WeakCompletion X} (N : Normalized C) (n : Fin 7) :
    N.single n false = N.single n true := by
  have h0 := N.row n false
  have h1 := N.row n true
  omega

theorem Normalized.weight_total {C : WeakCompletion X} (N : Normalized C) :
    (∑ l : Fin 7, N.weight l) + (pointClass C 0).card = Fintype.card X := by
  have hterm (x : X) : (∑ l : Fin 7, if (N.col x).base = some l then 1 else 0) +
      (if (C.avoid x).card = 0 then 1 else 0) = 1 := by
    rw [N.avoid]
    cases N.col x <;> simp [Column.base,Column.avoid]
  have hh := sum_congr (s₁ := (univ : Finset X)) rfl (fun x _ => hterm x)
  rw [sum_add_distrib,sum_comm] at hh
  have hW (l : Fin 7) : (∑ x : X, if (N.col x).base = some l then 1 else 0) = N.weight l := by
    simp only [Normalized.weight,card_eq_sum_ones,sum_filter]
  have hC : (∑ x : X, if (C.avoid x).card = 0 then 1 else 0) = (pointClass C 0).card := by
    simp only [pointClass,card_eq_sum_ones,sum_filter]
  simpa only [hW,hC,sum_const,card_univ,Nat.nsmul_eq_mul,mul_one] using hh

theorem Normalized.single_total {C : WeakCompletion X} (N : Normalized C) :
    2 * (∑ n : Fin 7, N.single n false) = (pointClass C 1).card := by
  have hterm (x : X) : (∑ n : Fin 7, ((if (N.col x).extra = some (n,false) then 1 else 0) +
      (if (N.col x).extra = some (n,true) then 1 else 0))) =
      if (C.avoid x).card = 1 then 1 else 0 := by
    rw [N.avoid]
    cases N.col x with
    | a l => simp [Column.extra,Column.avoid]
    | c D => simp [Column.extra,Column.avoid]
    | b l n b e => cases b <;> simp [Column.extra,Column.avoid]
  have hh := sum_congr (s₁ := (univ : Finset X)) rfl (fun x _ => hterm x)
  rw [sum_comm] at hh
  simp only [sum_add_distrib] at hh
  have hs (n : Fin 7) (b : Bool) : (∑ x : X, if (N.col x).extra = some (n,b) then 1 else 0) = N.single n b := by
    simp only [Normalized.single,card_eq_sum_ones,sum_filter]
  have hB : (∑ x : X, if (C.avoid x).card = 1 then 1 else 0) = (pointClass C 1).card := by
    simp only [pointClass,card_eq_sum_ones,sum_filter]
  simp only [hs,hB,← N.single_balanced] at hh
  omega

end Internal.Short
end CoveringDesigns.C19_9_3
