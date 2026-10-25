import CoveringDesigns.Multicover.Family
import CoveringDesigns.Foundations.Relabelling
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Tactic.Linarith

/-! Actual point and occurrence equivalences, and the universal lower seven.
No classification or assumption of distinct block images occurs here. -/
namespace CoveringDesigns.SevenBlock
open Finset
universe u v w z

/-- Equivalence of indexed coverings retains every point and occurrence. -/
def IndexedIsomorphic {V : Type u} {I : Type v} {W : Type w} {J : Type z}
    (B : I → Finset V) (C : J → Finset W) : Prop :=
  ∃ e : V ≃ W, ∃ f : I ≃ J, ∀ x i, x ∈ B i ↔ e x ∈ C (f i)

theorem IndexedIsomorphic.refl {V I : Type*} (B : I → Finset V) :
    IndexedIsomorphic B B := ⟨Equiv.refl _, Equiv.refl _, fun _ _ => Iff.rfl⟩

theorem IndexedIsomorphic.symm {V I W J : Type*}
    {B : I → Finset V} {C : J → Finset W} (h : IndexedIsomorphic B C) :
    IndexedIsomorphic C B := by
  obtain ⟨e, f, h⟩ := h
  exact ⟨e.symm, f.symm, fun x i => by simpa using (h (e.symm x) (f.symm i)).symm⟩

theorem IndexedIsomorphic.trans {V I W J U K : Type*}
    {B : I → Finset V} {C : J → Finset W} {D : K → Finset U}
    (h : IndexedIsomorphic B C) (g : IndexedIsomorphic C D) : IndexedIsomorphic B D := by
  obtain ⟨e, f, h⟩ := h
  obtain ⟨e', f', g⟩ := g
  exact ⟨e.trans e', f.trans f', fun x i => (h x i).trans (g (e x) (f i))⟩

theorem incidence_degree_eq {V I W J : Type*}
    [DecidableEq V] [DecidableEq W] [Fintype I] [Fintype J]
    {B : I → Finset V} {C : J → Finset W} (e : V ≃ W) (f : I ≃ J)
    (h : ∀ x i, x ∈ B i ↔ e x ∈ C (f i)) (x : V) :
    indexedDegree B x = indexedDegree C (e x) := by
  rw [← Multicover.subsetDegree_singleton, ← Multicover.subsetDegree_singleton,
    Multicover.subsetDegree_eq_card, Multicover.subsetDegree_eq_card]
  exact Fintype.card_congr (f.subtypeEquiv (fun i => by simpa using h x i))

theorem incidence_codegree_eq {V I W J : Type*}
    [DecidableEq V] [DecidableEq W] [Fintype I] [Fintype J]
    {B : I → Finset V} {C : J → Finset W} (e : V ≃ W) (f : I ≃ J)
    (h : ∀ x i, x ∈ B i ↔ e x ∈ C (f i)) (x y : V) :
    indexedSubsetDegree B {x,y} = indexedSubsetDegree C {e x,e y} := by
  rw [Multicover.subsetDegree_eq_card, Multicover.subsetDegree_eq_card]
  exact Fintype.card_congr (f.subtypeEquiv (fun i => by
    simpa only [insert_subset_iff, singleton_subset_iff] using and_congr (h x i) (h y i)))

variable {V : Type u} {I : Type v} [Fintype V] [DecidableEq V] [Fintype I]

theorem degree_floor {a : ℕ} (ha : 1 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1) (x : V) :
    3 ≤ indexedDegree B x := by
  have hl := Multicover.subsetLink_isCover h ({x} : Finset V) (by simp)
  have hn : Fintype.card {y : V // y ∉ ({x} : Finset V)} = 7*a+3 := by
    rw [Multicover.subset_complement_card, card_singleton, hv]
    omega
  have hk : 3*a+2-1 = 3*a+1 := by omega
  have hb := Multicover.lower_bound (by omega : 1 ≤ 3*a+1)
    (by omega : 3*a+1 ≤ Fintype.card {y : V // y ∉ ({x} : Finset V)})
    (by simpa only [card_singleton, hk] using hl)
  rw [hn, Multicover.bound_one_eq, Schoenheim.bound_one,
    Multicover.subsetLink_card, Multicover.subsetDegree_singleton] at hb
  have hc := (Schoenheim.ceilDiv_le_iff (by omega : 0 < 3*a+1)).mp hb
  by_contra hd
  have hm := Nat.mul_le_mul_left (3*a+1) (show indexedDegree B x ≤ 2 by omega)
  omega

/-- Universal numerical lower bound, with arbitrary occurrence count and
possible repeated images. This does not depend on classification. -/
theorem seven_le_card {a : ℕ} (ha : 1 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1) :
    7 ≤ Fintype.card I := by
  have hs := sum_le_sum (s := (univ : Finset V)) (fun x _ => degree_floor ha hv h x)
  rw [Multicover.degree_sum_of_uniform h.1] at hs
  simp only [sum_const, card_univ, Nat.nsmul_eq_mul, hv] at hs
  by_contra hn
  have hm := Nat.mul_le_mul_left (3*a+2) (show Fintype.card I ≤ 6 by omega)
  omega

theorem ordinary_seven_le_card {a : ℕ} (ha : 1 ≤ a) {C : Family V}
    (hv : Fintype.card V = 7*a+4) (h : IsCover C (3*a+2) 2) : 7 ≤ C.card := by
  simpa only [Multicover.ofFamily_card] using
    seven_le_card ha hv ((Multicover.ofFamily_isCover_one C (3*a+2) 2).mpr h)

/-- Simplicity is derived, never a premise of a seven-occurrence covering. -/
theorem blocks_injective {a : ℕ} (ha : 1 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1)
    (hi : Fintype.card I = 7) : Function.Injective B := by
  have hl := ordinary_seven_le_card ha hv
    ((Multicover.deduplicate_isCover_one B (3*a+2) 2).mpr h)
  have hu := Multicover.deduplicate_card_le B
  have he : (univ.image B).card = (univ : Finset I).card := by
    change (Multicover.deduplicate B).card = _
    rw [card_univ]
    omega
  exact fun x y hxy => (card_image_iff.mp he) (mem_univ x) (mem_univ y) hxy

/-- The proved ordinary/indexed adapter retains a bijection with actual
block images. It is used only after distinctness has been derived. -/
noncomputable def occurrenceEquiv {B : I → Finset V} (hinj : Function.Injective B) :
    I ≃ ↥(Multicover.deduplicate B) :=
  Equiv.ofBijective (fun i => ⟨B i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), by
      intro D
      obtain ⟨i, _, hi⟩ := mem_image.mp D.property
      exact ⟨i, Subtype.ext hi⟩⟩

theorem indexed_ordinary_equivalence {B : I → Finset V} (hinj : Function.Injective B) :
    IndexedIsomorphic B (Multicover.ofFamily (Multicover.deduplicate B)) :=
  ⟨Equiv.refl _, occurrenceEquiv hinj, fun _ _ => Iff.rfl⟩

/-- Lift an ordinary point relabelling to an indexed equivalence once both
occurrence maps have been proved injective. -/
theorem ordinary_isomorphism_to_indexed {W : Type*} {J : Type*}
    [DecidableEq W] [Fintype J] {B : I → Finset V} {C : J → Finset W}
    (hB : Function.Injective B) (hC : Function.Injective C)
    (h : Isomorphic (Multicover.deduplicate B) (Multicover.deduplicate C)) :
    IndexedIsomorphic B C := by
  classical
  obtain ⟨e,he⟩ := h
  let r : ↥(Multicover.deduplicate B) ≃ ↥(Multicover.deduplicate C) :=
    Equiv.subtypeEquiv (Equiv.finsetCongr e) (fun D => by
      change D ∈ Multicover.deduplicate B ↔ D.map e.toEmbedding ∈ Multicover.deduplicate C
      rw [← he]
      exact (mem_relabel e _ D).symm)
  let f := (occurrenceEquiv hB).trans (r.trans (occurrenceEquiv hC).symm)
  refine ⟨e,f,?_⟩
  intro x i
  have hh : occurrenceEquiv hC (f i) = r (occurrenceEquiv hB i) := by simp [f]
  have hvv := congrArg Subtype.val hh
  change C (f i) = (B i).map e.toEmbedding at hvv
  rw [hvv]
  simp

#guard_standard_axioms IndexedIsomorphic.refl IndexedIsomorphic.symm
  IndexedIsomorphic.trans incidence_degree_eq incidence_codegree_eq
  degree_floor seven_le_card ordinary_seven_le_card
  blocks_injective indexed_ordinary_equivalence ordinary_isomorphism_to_indexed

end CoveringDesigns.SevenBlock
