import CoveringDesigns.QuadrupleAssembly.FiniteChecks
import Mathlib.Data.Finset.Sort

/-! Kernel-checked incidence selectors for small retained bases.
The supplied index table is only a hint: coverage and its inverse are checked
for every required subset. No trust in the table-producing program is assumed. -/
namespace CoveringDesigns.QuadrupleAssembly
open Finset
attribute [local instance 2000] Finset.decidableDforallFinset

/-- Boolean fold on a multiset, avoiding proof-producing universal deciders. -/
def allMultiset {α : Type*} (s : Multiset α) (p : α → Bool) : Bool :=
  Quotient.liftOn s (fun l => l.all p) (by
    intro a b h
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    exact ⟨fun ha x hx => ha x (h.mem_iff.mpr hx),
      fun hb x hx => hb x (h.mem_iff.mp hx)⟩)

theorem allMultiset_eq_true {α : Type*} (s : Multiset α) (p : α → Bool) :
    allMultiset s p = true ↔ ∀ x ∈ s, p x = true := by
  induction s using Quotient.inductionOn with
  | h l => simp [allMultiset,List.all_eq_true]

def allFinset {α : Type*} (s : Finset α) (p : α → Bool) : Bool := allMultiset s.val p

theorem allFinset_eq_true {α : Type*} (s : Finset α) (p : α → Bool) :
    allFinset s p = true ↔ ∀ x ∈ s, p x = true := allMultiset_eq_true s.val p

/-- Compact immutable lookup tree. Branching on low bits avoids linear list
or array reconstruction during kernel reduction of the small seed checks. -/
inductive IndexTree where
  | leaf : ℕ → IndexTree
  | fork : IndexTree → IndexTree → IndexTree

def IndexTree.get : IndexTree → ℕ → ℕ
  | .leaf x, _ => x
  | .fork a b, k => if k % 2 = 0 then a.get (k/2) else b.get (k/2)

/-- Colexicographic key on the sorted two or three labels. Its formula need
not be trusted: the selector checks below verify the actual selected blocks. -/
def subsetCode {n : ℕ} (t : ℕ) (T : Finset (Fin n)) : ℕ :=
  T.sum (fun x =>
    let r := (T.filter (fun y => y ≤ x)).card
    if r = 1 then x.val else if r = 2 then x.val*(x.val-1)/2
    else if t = 3 then x.val*(x.val-1)*(x.val-2)/6 else 0)

def selected {α : Type*} (rows : List (Finset α))
    (index : Finset α → Fin rows.length) (T : Finset α) : Finset α := rows.get (index T)

def selectorCoverCheck {α γ : Type*} [Fintype α] [DecidableEq α] [DecidableEq γ]
    (g : α → γ) (t : ℕ) (rows : List (Finset α)) (index : Finset α → Fin rows.length) : Bool :=
  allFinset ((univ : Finset α).powersetCard t) (fun T =>
    if (T.image g).card = T.card then decide (T ⊆ selected rows index T) else true)

def selectorMasterCheck {α γ : Type*} [Fintype α] [DecidableEq α] [DecidableEq γ]
    (g : α → γ) (t : ℕ) (rows : List (Finset α)) (index : Finset α → Fin rows.length) : Bool :=
  rows.all (fun B => decide ((B.image g).card = B.card)) &&
    selectorCoverCheck g t rows index &&
    rows.all (fun B => allFinset (B.powersetCard t) (fun T => decide (selected rows index T = B)))

theorem selectorMasterCheck_sound {α γ : Type*} [Fintype α] [DecidableEq α] [DecidableEq γ]
    (g : α → γ) (t : ℕ) (rows : List (Finset α)) (index : Finset α → Fin rows.length)
    (h : selectorMasterCheck g t rows index = true) : Master g t rows.toFinset := by
  simp only [selectorMasterCheck, selectorCoverCheck, Bool.and_eq_true,
    List.all_eq_true, allFinset_eq_true, Bool.ite_eq_true_distrib, decide_eq_true_eq] at h
  refine ⟨?_,?_⟩
  · intro B hB
    exact card_image_iff.mp (h.1.1 B (List.mem_toFinset.mp hB))
  · intro T hT ht
    have hs := h.1.2 T (mem_powersetCard_univ.mpr hT)
    rw [if_pos (card_image_iff.mpr ht)] at hs
    have hm : selected rows index T ∈ rows.toFinset := by
      exact List.mem_toFinset.mpr (List.get_mem ..)
    refine ⟨selected rows index T,⟨hm,hs⟩,?_⟩
    intro D hD
    exact (h.2 D (List.mem_toFinset.mp hD.1) T (mem_powersetCard.mpr ⟨hD.2,hT⟩)).symm

def selectorDesignCheck {α γ : Type*} [Fintype α] [DecidableEq α] [DecidableEq γ]
    (g : α → γ) (k t : ℕ) (rows : List (Finset α)) (index : Finset α → Fin rows.length) : Bool :=
  rows.all (fun B => decide (B.card = k)) && selectorMasterCheck g t rows index

theorem selectorDesignCheck_sound {α γ : Type*} [Fintype α] [DecidableEq α] [DecidableEq γ]
    (g : α → γ) (k t : ℕ) (rows : List (Finset α)) (index : Finset α → Fin rows.length)
    (h : selectorDesignCheck g k t rows index = true) : GroupDesign g k t rows.toFinset := by
  simp only [selectorDesignCheck, Bool.and_eq_true, List.all_eq_true, allFinset_eq_true, Bool.ite_eq_true_distrib, decide_eq_true_eq] at h
  have hm := selectorMasterCheck_sound g t rows index h.2
  exact ⟨fun B hB => h.1 B (List.mem_toFinset.mp hB),hm.transverse,hm.exact⟩

theorem selectorCoverCheck_sound {α : Type*} [Fintype α] [DecidableEq α]
    (k t : ℕ) (rows : List (Finset α)) (index : Finset α → Fin rows.length)
    (hu : rows.all (fun B => decide (B.card = k)) = true)
    (h : selectorCoverCheck id t rows index = true) : IsCover rows.toFinset k t := by
  simp only [List.all_eq_true, allFinset_eq_true, Bool.ite_eq_true_distrib, decide_eq_true_eq] at hu
  simp only [selectorCoverCheck, allFinset_eq_true, Bool.ite_eq_true_distrib, decide_eq_true_eq] at h
  refine ⟨fun B hB => hu B (List.mem_toFinset.mp hB),?_⟩
  intro T ht
  exact ⟨selected rows index T,List.mem_toFinset.mpr (List.get_mem ..),
    by simpa using h T (mem_powersetCard_univ.mpr ht)⟩

def selectorCoverAt {α γ : Type*} [Fintype α] [LinearOrder α] [DecidableEq γ]
    (g : α → γ) (t : ℕ) (rows : List (Finset α)) (index : Finset α → Fin rows.length)
    (a : α) : Bool :=
  allFinset ((univ : Finset α).powersetCard t) (fun T =>
    if a ∈ T ∧ (∀ x ∈ T, a ≤ x) then
      if (T.image g).card = T.card then decide (T ⊆ selected rows index T) else true
    else true)

theorem selectorCoverCheck_of_slices {α γ : Type*} [Fintype α] [LinearOrder α] [DecidableEq γ]
    (g : α → γ) (t : ℕ) (rows : List (Finset α)) (index : Finset α → Fin rows.length)
    (ht : 0 < t) (h : ∀ a, selectorCoverAt g t rows index a = true) :
    selectorCoverCheck g t rows index = true := by
  simp only [selectorCoverCheck,allFinset_eq_true]
  intro T hT
  have hc := mem_powersetCard_univ.mp hT
  have hn : T.Nonempty := card_pos.mp (hc ▸ ht)
  have hs := h (T.min' hn)
  simp only [selectorCoverAt,allFinset_eq_true] at hs
  have hs' := hs T hT
  rw [if_pos ⟨min'_mem T hn,fun x hx => min'_le T x hx⟩] at hs'
  exact hs'

def selectorInverseCheck {α : Type*} [DecidableEq α] (t : ℕ)
    (rows : List (Finset α)) (index : Finset α → Fin rows.length)
    (part : List (Finset α)) : Bool :=
  part.all (fun B => allFinset (B.powersetCard t) (fun T => decide (selected rows index T = B)))

theorem selectorMasterCheck_of_parts {α γ : Type*} [Fintype α] [DecidableEq α] [DecidableEq γ]
    (g : α → γ) (t : ℕ) (rows : List (Finset α)) (index : Finset α → Fin rows.length)
    (htr : rows.all (fun B => decide ((B.image g).card = B.card)) = true)
    (hc : selectorCoverCheck g t rows index = true)
    (hr : selectorInverseCheck t rows index rows = true) :
    selectorMasterCheck g t rows index = true := by
  simp only [selectorMasterCheck,htr,hc,Bool.true_and]
  exact hr

end CoveringDesigns.QuadrupleAssembly
