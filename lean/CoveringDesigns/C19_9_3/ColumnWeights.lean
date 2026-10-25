import CoveringDesigns.C19_9_3.Completion

/-! Internal exact Fano incidence weights for the two remaining budgets. -/
namespace CoveringDesigns.C19_9_3.Internal
open Finset SevenBlock

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
  | .c D => D.card = 4 ∧ ∃ l, line l ⊆ D

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
    (h : ColumnForm U E) : ∃ c : Column, c.Valid ∧ U = c.plane ∧ E = c.avoid := by
  rcases h with ⟨he,l,hl⟩ | ⟨he,l,n,b,hn,hl⟩ | ⟨he,D,hD,hL,hU⟩
  · refine ⟨.a l,True.intro,hl,?_⟩
    exact eq_univ_of_card E (by simpa using he)
  · obtain ⟨e,heE⟩ := card_eq_one.mp he
    exact ⟨.b l n b e,hn,hl,heE⟩
  · exact ⟨.c D,⟨hD,hL⟩,hU,card_eq_zero.mp he⟩

variable {X : Type*} [Fintype X] [DecidableEq X]

structure Normalized (C : Completion X) where
  col : X → Column
  valid : ∀ x, (col x).Valid
  plane : ∀ x, C.plane x = (col x).plane
  avoid : ∀ x, C.avoid x = (col x).avoid

theorem normalize (C : Completion X) : Nonempty (Normalized C) := by
  choose col hv hp he using fun x => column_normal_form (C.plane x) (C.avoid x) (C.form x)
  exact ⟨⟨col,hv,hp,he⟩⟩

def Normalized.weight {C : Completion X} (N : Normalized C) (l : Fin 7) :=
  (univ.filter fun x => (N.col x).base = some l).card

def Normalized.single {C : Completion X} (N : Normalized C) (n : Fin 7) (b : Bool) :=
  (univ.filter fun x => (N.col x).extra = some (n,b)).card

def Normalized.wideCount {C : Completion X} (N : Normalized C) (n : Fin 7) :=
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

theorem Normalized.row {C : Completion X} (N : Normalized C) (n : Fin 7) (b : Bool) :
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

theorem Normalized.single_balanced {C : Completion X} (N : Normalized C) (n : Fin 7) :
    N.single n false = N.single n true := by
  have h0 := N.row n false
  have h1 := N.row n true
  omega

theorem Normalized.weight_total {C : Completion X} (N : Normalized C) :
    (∑ l : Fin 7, N.weight l) + (C.class 0).card = Fintype.card X := by
  have hterm (x : X) : (∑ l : Fin 7, if (N.col x).base = some l then 1 else 0) +
      (if (C.avoid x).card = 0 then 1 else 0) = 1 := by
    rw [N.avoid]
    cases N.col x <;> simp [Column.base,Column.avoid]
  have hh := sum_congr (s₁ := (univ : Finset X)) rfl (fun x _ => hterm x)
  rw [sum_add_distrib,sum_comm] at hh
  have hW (l : Fin 7) : (∑ x : X, if (N.col x).base = some l then 1 else 0) = N.weight l := by
    simp only [Normalized.weight,card_eq_sum_ones,sum_filter]
  have hC : (∑ x : X, if (C.avoid x).card = 0 then 1 else 0) = (C.class 0).card := by
    simp only [Completion.class,card_eq_sum_ones,sum_filter]
  simpa only [hW,hC,sum_const,card_univ,Nat.nsmul_eq_mul,mul_one] using hh

theorem Normalized.single_total {C : Completion X} (N : Normalized C) :
    2 * (∑ n : Fin 7, N.single n false) = (C.class 1).card := by
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
  have hB : (∑ x : X, if (C.avoid x).card = 1 then 1 else 0) = (C.class 1).card := by
    simp only [Completion.class,card_eq_sum_ones,sum_filter]
  simp only [hs,hB,← N.single_balanced] at hh
  omega

end CoveringDesigns.C19_9_3.Internal
