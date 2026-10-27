import CoveringDesigns.TruncatedPlaneLoads.Integer
import CoveringDesigns.Multicover.Basic
import CoveringDesigns.Foundations.Relabelling
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators

/-! Actual points, block occurrences, ordinary families and relabelling. -/

namespace CoveringDesigns.TruncatedPlaneLoads
open Finset
variable {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable {q : ℕ} {P : Plane q V G}

/-- The second coordinate retains the identity of every point with a repeated support. -/
abbrev Point (H : Finset (Finset V)) (m : Finset V → ℕ) := Σ S : H, Fin (m S.val)

def block (H : Finset (Finset V)) (m : Finset V → ℕ) (x : V) : Finset (Point H m) :=
  univ.filter (fun p => x ∈ p.1.val)

@[simp] theorem mem_block (H : Finset (Finset V)) (m : Finset V → ℕ)
    (x : V) (p : Point H m) : p ∈ block H m x ↔ x ∈ p.1.val := by simp [block]

theorem point_card {H : Finset (Finset V)} {m : Finset V → ℕ} {K : ℕ}
    (h : NatAdmissible P H m K) : Fintype.card (Point H m) = q*K := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, sum_coe_sort]
  exact h.mass

theorem block_card {H : Finset (Finset V)} {m : Finset V → ℕ} {K : ℕ}
    (h : NatAdmissible P H m K) (x : V) : (block H m x).card = K := by
  calc
    _ = ∑ S : H, if x ∈ S.val then m S.val else 0 := by
      simp only [block, card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
      apply sum_congr rfl
      intro S hS
      by_cases hx : x ∈ S.val <;> simp [hx]
    _ = ∑ S ∈ H, if x ∈ S then m S else 0 := sum_coe_sort H (fun S => if x ∈ S then m S else 0)
    _ = K := h.load x

theorem expanded_cover {H : Finset (Finset V)} {m : Finset V → ℕ} {K : ℕ}
    (h : NatAdmissible P H m K) : Multicover.IsCover (block H m) K 2 1 := by
  refine ⟨block_card h, (Multicover.covers_one_iff _ _).mpr ?_⟩
  intro T hT
  obtain ⟨p,r,hpr,rfl⟩ := card_eq_two.mp hT
  obtain ⟨x,hx⟩ := h.intersect p.1.val p.1.property r.1.val r.1.property
  exact ⟨x, by simpa only [insert_subset_iff, singleton_subset_iff, mem_block, mem_inter] using hx⟩

/-- A positive core separates coordinates, so these indexed blocks really
have distinct images. This precedes the ordinary-family cardinality claim. -/
theorem blocks_injective (hq : 2 ≤ q) {H : Finset (Finset V)}
    {m : Finset V → ℕ} {K : ℕ} (h : NatAdmissible P H m K) :
    Function.Injective (block H m) := by
  intro x y he
  by_contra hxy
  obtain ⟨E,hE,hx,hy⟩ := P.distinguish hq hxy
  let p : Point H m := ⟨⟨E,h.core_subset hE⟩,⟨0,h.positive E (h.core_subset hE)⟩⟩
  have hp : p ∈ block H m x := by simpa [p] using hx
  rw [he] at hp
  exact hy (by simpa [p] using hp)

def expandedFamily (H : Finset (Finset V)) (m : Finset V → ℕ) : Family (Point H m) :=
  univ.image (block H m)

theorem expanded_family_card (hq : 2 ≤ q) {H : Finset (Finset V)}
    {m : Finset V → ℕ} {K : ℕ} (h : NatAdmissible P H m K) :
    (expandedFamily H m).card = q*(q+1) := by
  rw [expandedFamily, card_image_of_injective _ (blocks_injective hq h), card_univ,
    P.coordinates_card]

theorem expanded_family_cover {H : Finset (Finset V)} {m : Finset V → ℕ} {K : ℕ}
    (h : NatAdmissible P H m K) : IsCover (expandedFamily H m) K 2 := by
  refine ⟨?_,?_⟩
  · intro B hB
    obtain ⟨x,_,rfl⟩ := mem_image.mp hB
    exact block_card h x
  · intro T hT
    obtain ⟨x,hx⟩ := (Multicover.covers_one_iff _ _).mp (expanded_cover h).2 T hT
    exact ⟨block H m x, mem_image.mpr ⟨x,mem_univ _,rfl⟩, hx⟩

theorem expanded_on (hq : 2 ≤ q) {H : Finset (Finset V)}
    {m : Finset V → ℕ} {K : ℕ} (h : NatAdmissible P H m K)
    {X : Type*} [Fintype X] [DecidableEq X] (hv : Fintype.card X = q*K) :
    ∃ C : Family X, C.card = q*(q+1) ∧ IsCover C K 2 := by
  let e : Point H m ≃ X := Fintype.equivOfCardEq ((point_card h).trans hv.symm)
  exact ⟨relabel e (expandedFamily H m),
    (relabel_card e _).trans (expanded_family_card hq h),
    relabel_isCover e (expanded_family_cover h)⟩

/-- Reindexing is a bijection of occurrences, so no occurrence is discarded. -/
theorem expanded_reindex {H : Finset (Finset V)} {m : Finset V → ℕ} {K : ℕ}
    (h : NatAdmissible P H m K) {J : Type*} [Fintype J] (e : J ≃ V) :
    Fintype.card J = q*(q+1) ∧ Multicover.IsCover (block H m ∘ e) K 2 1 :=
  ⟨(Fintype.card_congr e).trans P.coordinates_card,
    (Multicover.isCover_reindex e _ _ _ _).mpr (expanded_cover h)⟩

end CoveringDesigns.TruncatedPlaneLoads
