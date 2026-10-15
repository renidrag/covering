import CoveringDesigns.C13_7_4.Structural.RootedCore
import CoveringDesigns.Foundations.Links
import CoveringDesigns.C13_7_4.Structural.GPPTGeometryHelpers
import Mathlib.Logic.Equiv.Fin.Basic

/-! The row geometry forced by a single spouse swap. These lemmas concern
one fixed configuration. There is no search over coverings or completions. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace CoveringDesigns.C13Structural

open Finset

/-- The two roots, their three companions, and four spouse pairs. -/
abbrev SwapPoint := Bool ⊕ TracePoint

def swapRoot (b : Bool) : SwapPoint := Sum.inl b

def swapCompanion (m : Fin 3) : SwapPoint := Sum.inr (Sum.inl m)

def swapSpouse (v : Fin 4) (b : Bool) : SwapPoint := Sum.inr (Sum.inr (v, b))

/-- The private blocks when both roots have the same full core. -/
def identicalPrivateBlock (i : Fin 3 × Bool) (root : Bool) : Finset SwapPoint :=
  insert (swapRoot root) ((privateTrace i.1 i.2).image Sum.inr)

theorem privateTrace_covers_points : ∀ z : TracePoint,
    ∃ i : Fin 3 × Bool, z ∈ privateTrace i.1 i.2 := by decide +kernel

theorem identicalPrivateBlock_ne : ∀ i,
    identicalPrivateBlock i false ≠ identicalPrivateBlock i true := by decide +kernel

theorem identicalPrivateBlock_inter : ∀ i,
    (identicalPrivateBlock i false ∩ identicalPrivateBlock i true).card = 6 := by
  decide +kernel

theorem identicalPrivateBlock_through : ∀ i z,
    z ∈ privateTrace i.1 i.2 → ∀ b, Sum.inr z ∈ identicalPrivateBlock i b := by
  decide +kernel

/-- Swap the two members of the spouse pair indexed by zero. -/
def swapTrace : TracePoint → TracePoint
  | Sum.inl m => Sum.inl m
  | Sum.inr (v, b) => Sum.inr (v, if v = 0 then !b else b)

theorem swapTrace_involutive : Function.Involutive swapTrace := by
  change ∀ z, swapTrace (swapTrace z) = z
  decide +kernel

def swappedPrivateBlock (i : Fin 3 × Bool) (root : Bool) : Finset SwapPoint :=
  insert (swapRoot root)
    ((privateTrace i.1 i.2).image
      (fun z => Sum.inr (if root then swapTrace z else z)))

def swappedCommonBlock (i : Fin 3 × Bool) : Finset SwapPoint :=
  insert (swapRoot false) (insert (swapRoot true)
    ((commonTrace i.1 i.2).image Sum.inr))

def swappedOwnBlock (R : Finset TracePoint) : Finset SwapPoint :=
  insert (swapRoot false) (insert (swapRoot true)
    ((companions ∪ R).image Sum.inr))

def swappedForeignBlock : Finset SwapPoint :=
  insert (swapRoot false) (insert (swapRoot true)
    (insert (swapSpouse 0 true) ((transverse false).image Sum.inr)))

theorem swappedPrivateBlock_card :
    ∀ i root, (swappedPrivateBlock i root).card = 7 := by decide +kernel

theorem swappedPrivateBlock_injective :
    Function.Injective (fun j : (Fin 3 × Bool) × Bool =>
      swappedPrivateBlock j.1 j.2) := by decide +kernel

theorem swappedPrivateBlock_inter : ∀ i,
    (swappedPrivateBlock i false ∩ swappedPrivateBlock i true).card = 5 := by
  decide +kernel

theorem swappedPrivateBlock_root : ∀ i b,
    swapRoot b ∈ swappedPrivateBlock i b := by decide +kernel

theorem swappedPrivateBlock_other_root : ∀ i b,
    swapRoot (!b) ∉ swappedPrivateBlock i b := by decide +kernel

theorem swappedCommonBlock_roots : ∀ i b,
    swapRoot b ∈ swappedCommonBlock i := by decide +kernel

/-- At a spouse point, select the one private pair from each matching
whose endpoints contain that point. -/
def spouseOrientation (m : Fin 3) (v : Fin 4) (b : Bool) : Bool :=
  if v ∈ half m false then b else !b

def spouseMatchingBlock (v : Fin 4) (b : Bool) (j : Fin 3 × Bool) : Finset SwapPoint :=
  swappedPrivateBlock (j.1, spouseOrientation j.1 v b) j.2

theorem spouseMatchingBlock_injective : ∀ v b,
    Function.Injective (spouseMatchingBlock v b) := by decide +kernel

theorem spouseMatchingBlock_through : ∀ v b, v ≠ 0 → ∀ j,
    swapSpouse v b ∈ spouseMatchingBlock v b j := by decide +kernel

theorem spouseMatchingBlock_inter : ∀ v b i,
    (spouseMatchingBlock v b (i, false) ∩
      spouseMatchingBlock v b (i, true)).card = 5 := by decide +kernel

theorem spouseMatchingBlock_common : ∀ v b, v ≠ 0 → ∀ z,
    (∀ j, z ∈ spouseMatchingBlock v b j) → z = swapSpouse v b := by decide +kernel

theorem spouseMatchingBlock_roots : ∀ v b j,
    swapRoot false ∈ spouseMatchingBlock v b j ∨
      swapRoot true ∈ spouseMatchingBlock v b j := by decide +kernel

/-- Four private pairs through a companion, two from either other matching. -/
def companionMatchingIndex (k : Fin 3) (i : Fin 4) : Fin 3 × Bool :=
  (⟨(k.val + if i.val < 2 then 1 else 2) % 3, Nat.mod_lt _ (by decide)⟩,
    decide (i.val % 2 = 1))

def companionMatchingBlock (k : Fin 3) (j : Fin 4 × Bool) : Finset SwapPoint :=
  swappedPrivateBlock (companionMatchingIndex k j.1) j.2

theorem companionMatchingBlock_injective : ∀ k,
    Function.Injective (companionMatchingBlock k) := by decide +kernel

theorem companionMatchingBlock_through : ∀ k j,
    swapCompanion k ∈ companionMatchingBlock k j := by decide +kernel

theorem companionMatchingBlock_inter : ∀ k i,
    (companionMatchingBlock k (i, false) ∩
      companionMatchingBlock k (i, true)).card = 5 := by decide +kernel

theorem companionMatchingBlock_common : ∀ k z,
    (∀ j, z ∈ companionMatchingBlock k j) → z = swapCompanion k := by decide +kernel

/-- Any two spouse indices lie together in some edge of K₄. -/
theorem two_vertices_in_half : ∀ v w : Fin 4,
    ∃ i : Fin 3 × Bool, v ∈ half i.1 i.2 ∧ w ∈ half i.1 i.2 := by decide +kernel

/-- The two additions fit into the spouse part of a common full row. -/
theorem additions_in_common (R : Finset (Fin 4 × Bool)) (hR : R.card = 2) :
    ∃ i : Fin 3 × Bool, ∀ z ∈ R, z.1 ∈ half i.1 i.2 := by
  obtain ⟨a, b, _, rfl⟩ := card_eq_two.mp hR
  obtain ⟨i, ha, hb⟩ := two_vertices_in_half a.1 b.1
  refine ⟨i, ?_⟩
  intro z hz
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact ha
  · exact hb

theorem swappedOwnBlock_roots : ∀ (R : Finset TracePoint) b,
    swapRoot b ∈ swappedOwnBlock R := by
  intro R b
  cases b <;> simp [swappedOwnBlock]

theorem swappedOwnBlock_companions (R : Finset TracePoint) (k : Fin 3) :
    swapCompanion k ∈ swappedOwnBlock R := by
  simp [swapCompanion, swappedOwnBlock, companions]

theorem swappedOwnBlock_addition (R : Finset (Fin 4 × Bool))
    {z : Fin 4 × Bool} (hz : z ∈ R) :
    swapSpouse z.1 z.2 ∈ swappedOwnBlock (R.image Sum.inr) := by
  rcases z with ⟨v, b⟩
  cases b <;> simpa [swapSpouse, swappedOwnBlock, swapRoot, companions] using hz

theorem swappedOwnBlock_common_inter (R : Finset (Fin 4 × Bool))
    (i : Fin 3 × Bool) (hfit : ∀ z ∈ R, z.1 ∈ half i.1 i.2) :
    swappedOwnBlock (R.image Sum.inr) ∩ swappedCommonBlock i =
      insert (swapRoot false) (insert (swapRoot true)
        (insert (swapCompanion i.1) (R.image (fun z => swapSpouse z.1 z.2)))) := by
  ext z
  rcases z with b | (k | ⟨v, b⟩)
  · cases b <;> simp [swappedOwnBlock, swappedCommonBlock, swapRoot, swapCompanion,
      swapSpouse]
  · simp [swappedOwnBlock, swappedCommonBlock, swapRoot, swapCompanion, swapSpouse,
      companions, commonTrace]
  · have hh : ((v, b) ∈ R ∧ v ∈ half i.1 i.2) ↔ (v, b) ∈ R :=
      ⟨And.left, fun h => ⟨h, hfit (v, b) h⟩⟩
    cases b <;> simpa [swappedOwnBlock, swappedCommonBlock, swapRoot, swapCompanion,
      swapSpouse, commonTrace, companions] using hh

theorem swappedOwnBlock_common_inter_card (R : Finset (Fin 4 × Bool))
    (hR : R.card = 2) (i : Fin 3 × Bool)
    (hfit : ∀ z ∈ R, z.1 ∈ half i.1 i.2) :
    (swappedOwnBlock (R.image Sum.inr) ∩ swappedCommonBlock i).card = 5 := by
  rw [swappedOwnBlock_common_inter R i hfit]
  have hi : Function.Injective (fun z : Fin 4 × Bool => swapSpouse z.1 z.2) := by
    intro a b h
    exact Sum.inr.inj (Sum.inr.inj h)
  simp [swapRoot, swapCompanion, swapSpouse]
  simpa [swapSpouse] using (card_image_of_injective R hi).trans hR

theorem swappedOwnBlock_ne_common (R : Finset TracePoint) (i : Fin 3 × Bool) :
    swappedOwnBlock R ≠ swappedCommonBlock i := by
  have hx : ∀ i : Fin 3 × Bool, ∃ k : Fin 3,
      swapCompanion k ∉ swappedCommonBlock i := by decide +kernel
  obtain ⟨k, hk⟩ := hx i
  intro he
  exact hk (he ▸ swappedOwnBlock_companions R k)

theorem ne_swappedPrivateBlock_of_roots (B : Finset SwapPoint)
    (hB : ∀ b, swapRoot b ∈ B) (i : Fin 3 × Bool) (b : Bool) :
    B ≠ swappedPrivateBlock i b := by
  intro he
  exact swappedPrivateBlock_other_root i b (he ▸ hB (!b))

theorem swappedForeignBlock_roots : ∀ b, swapRoot b ∈ swappedForeignBlock := by
  decide +kernel

theorem foreign_common_extra_pair : ∀ v : Fin 4, v ≠ 0 →
    ∃ i : Fin 3 × Bool,
      (swappedForeignBlock ∩ swappedCommonBlock i).card = 5 ∧
      swapSpouse v false ∈ swappedForeignBlock ∩ swappedCommonBlock i ∧
      swappedForeignBlock ≠ swappedCommonBlock i := by decide +kernel

section Generic
variable {α : Type*} [DecidableEq α]

/-- A matching of global row pairs with five-point intersections through r.
Deleting r will turn it into an intersection-four matching in its link. -/
structure FiveIntersectionMatching (C : Family α) (r : α) (n : ℕ) where
  block : Fin n × Bool → Finset α
  injective : Function.Injective block
  mem : ∀ j, block j ∈ C
  through : ∀ j, r ∈ block j
  inter : ∀ i, (block (i, false) ∩ block (i, true)).card = 5

namespace FiveIntersectionMatching

variable {C : Family α} {r : α} {n : ℕ}

def deletedBlock (M : FiveIntersectionMatching C r n) (j : Fin n × Bool) :
    Finset {x : α // x ≠ r} := (M.block j).subtype (· ≠ r)

theorem deleted_injective (M : FiveIntersectionMatching C r n) :
    Function.Injective M.deletedBlock := by
  intro i j hij
  exact M.injective ((subtype_ne_inj (M.through i) (M.through j)).mp hij)

theorem deleted_mem (M : FiveIntersectionMatching C r n) (j : Fin n × Bool) :
    M.deletedBlock j ∈ link C r := by
  exact mem_image.mpr ⟨M.block j, mem_filter.mpr ⟨M.mem j, M.through j⟩, rfl⟩

theorem deleted_inter (M : FiveIntersectionMatching C r n) (i : Fin n) :
    (M.deletedBlock (i, false) ∩ M.deletedBlock (i, true)).card = 4 := by
  rw [deletedBlock, deletedBlock, subtype_ne_inter_card (M.through _) (M.through _), M.inter]

theorem deleted_common_empty (M : FiveIntersectionMatching C r n)
    (hcommon : ∀ x, (∀ j, x ∈ M.block j) → x = r)
    (x : {x : α // x ≠ r}) : ¬ ∀ j, x ∈ M.deletedBlock j := by
  intro hx
  exact x.property (hcommon x.val (fun j => by simpa [deletedBlock] using hx j))

/-- Deleting the common point gives the matching seen by its link. -/
def toLink (M : FiveIntersectionMatching C r n) :
    IntersectionFourMatching (link C r) n where
  block := M.deletedBlock
  injective := M.deleted_injective
  mem := M.deleted_mem
  inter := M.deleted_inter

theorem not_exceptional (M : FiveIntersectionMatching C r n)
    (hcommon : ∀ x, (∀ j, x ∈ M.block j) → x = r)
    (G : ExceptionalGeometry (link C r)) : False := by
  have hp : 0 < G.high.card := by rw [G.high_card]; omega
  obtain ⟨x, hx⟩ := card_pos.mp hp
  exact M.deleted_common_empty hcommon x (fun j => G.matching_subset M.toLink j hx)

/-- Add one pair whose endpoints are distinct from the old matching. -/
def extend (M : FiveIntersectionMatching C r n) (A B : Finset α)
    (hA : A ∈ C) (hB : B ∈ C) (hrA : r ∈ A) (hrB : r ∈ B)
    (hAB : A ≠ B) (hAM : ∀ j, A ≠ M.block j) (hBM : ∀ j, B ≠ M.block j)
    (hinter : (A ∩ B).card = 5) : FiveIntersectionMatching C r (n + 1) := by
  let f (j : Fin (n + 1) × Bool) : Finset α :=
    Fin.cases (if j.2 then B else A) (fun i => M.block (i, j.2)) j.1
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro ⟨i, b⟩ ⟨j, c⟩ h
    cases i using Fin.cases <;> cases j using Fin.cases
    · cases b <;> cases c <;> simp_all [f]
    · cases b
      · exact False.elim (hAM _ h)
      · exact False.elim (hBM _ h)
    · cases c
      · exact False.elim (hAM _ h.symm)
      · exact False.elim (hBM _ h.symm)
    · exact congrArg (fun j : Fin n × Bool => (j.1.succ, j.2)) (M.injective h)
  · intro ⟨i, b⟩
    cases i using Fin.cases
    · cases b <;> assumption
    · exact M.mem _
  · intro ⟨i, b⟩
    cases i using Fin.cases
    · cases b <;> assumption
    · exact M.through _
  · intro i
    cases i using Fin.cases
    · exact hinter
    · exact M.inter _

theorem extend_common (M : FiveIntersectionMatching C r n)
    (hcommon : ∀ x, (∀ j, x ∈ M.block j) → x = r)
    (A B : Finset α)
    (hA : A ∈ C) (hB : B ∈ C) (hrA : r ∈ A) (hrB : r ∈ B)
    (hAB : A ≠ B) (hAM : ∀ j, A ≠ M.block j) (hBM : ∀ j, B ≠ M.block j)
    (hinter : (A ∩ B).card = 5) :
    ∀ x, (∀ j, x ∈ (M.extend A B hA hB hrA hrB hAB hAM hBM hinter).block j) →
      x = r := by
  intro x hx
  apply hcommon x
  intro j
  simpa [extend] using hx (j.1.succ, j.2)

end FiveIntersectionMatching

variable {β : Type*} [DecidableEq β]

/-- Put a displayed finite row matching into an arbitrary point labelling. -/
def embeddedFiveMatching {C : Family α} {n : ℕ} (e : β ↪ α) (r : β)
    (B : Fin n × Bool → Finset β)
    (hi : Function.Injective B) (hmem : ∀ j, (B j).map e ∈ C)
    (hr : ∀ j, r ∈ B j) (hc : ∀ i, (B (i, false) ∩ B (i, true)).card = 5) :
    FiveIntersectionMatching C (e r) n where
  block j := (B j).map e
  injective := (Finset.map_injective e).comp hi
  mem := hmem
  through j := mem_map.mpr ⟨r, hr j, rfl⟩
  inter i := by rw [← map_inter, card_map, hc]

omit [DecidableEq α] [DecidableEq β] in
theorem embedded_common {n : ℕ} (hn : 0 < n) (e : β ↪ α)
    (r : β) (B : Fin n × Bool → Finset β)
    (hc : ∀ z, (∀ j, z ∈ B j) → z = r) :
    ∀ z, (∀ j, z ∈ (B j).map e) → z = e r := by
  intro z hz
  obtain ⟨x, _, rfl⟩ := mem_map.mp (hz (⟨0, hn⟩, false))
  apply congrArg e
  apply hc x
  intro j
  simpa using hz j

end Generic

#guard_standard_axioms swappedPrivateBlock_injective swappedPrivateBlock_inter
  spouseMatchingBlock_injective spouseMatchingBlock_common
  companionMatchingBlock_injective companionMatchingBlock_common
  additions_in_common swappedOwnBlock_common_inter_card
  FiveIntersectionMatching.deleted_injective FiveIntersectionMatching.toLink
  FiveIntersectionMatching.not_exceptional FiveIntersectionMatching.extend
  embeddedFiveMatching embedded_common identicalPrivateBlock_inter

end CoveringDesigns.C13Structural
