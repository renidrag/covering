import CoveringDesigns.AffineCapacity.Basic
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Tactic.Linarith

/-!
# The first affine boundary for actual binary incidence

Omitted-basis coordinates force every binary row in the affine span to be
a basis row. This is a structural affine argument; point fibres and block
occurrences are never identified. Formalisation: Rob Gardiner with AI assistance.
-/

namespace CoveringDesigns.AffineCapacity
open Finset Module

variable {α ι κ : Type*} [Fintype ι]

/-- Finite affine-span membership supplies coefficients summing to one.
The coefficients are real and are not assumed nonnegative. -/
theorem affine_coefficients [Fintype κ] (p : κ → ι → ℝ) {z : ι → ℝ}
    (hz : z ∈ affineSpan ℝ (Set.range p)) :
    ∃ w : κ → ℝ, (∑ j, w j) = 1 ∧ z = ∑ j, w j • p j := by
  classical
  obtain ⟨s, w, hw, he⟩ := (mem_affineSpan_iff_eq_affineCombination ℝ (ι → ℝ)).mp hz
  refine ⟨fun j => if j ∈ s then w j else 0, ?_, ?_⟩
  · simpa using hw
  · rw [he, Finset.affineCombination_eq_linear_combination _ _ _ hw]
    simp

/-- An omitted coordinate reads one minus its coefficient. -/
theorem omitted_coordinate [Fintype κ] [DecidableEq κ]
    (p : κ → ι → ℝ) (a : κ → ι) (w : κ → ℝ)
    (hp : ∀ i j, p j (a i) = if i = j then 0 else 1)
    (hw : ∑ j, w j = 1) (i : κ) :
    (∑ j, w j • p j) (a i) = 1 - w i := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hp]
  have he : ∀ j, w j * (if i = j then (0 : ℝ) else 1) =
      w j - if i = j then w i else 0 := by
    intro j
    by_cases h : i = j
    · subst j; simp
    · simp [h]
  simp_rw [he]
  simp [sum_sub_distrib, hw]

/-- Binary rigidity from actual omitted-basis coordinates. No covering,
uniformity, affine independence, or nonnegative coefficient premise. -/
theorem omitted_coordinates_rigidity [Fintype κ] [DecidableEq κ]
    (p : κ → ι → ℝ) (a : κ → ι)
    (hp : ∀ i j, p j (a i) = if i = j then 0 else 1)
    {z : ι → ℝ} (hz : z ∈ affineSpan ℝ (Set.range p))
    (hbinary : ∀ i, z i = 0 ∨ z i = 1) :
    ∃ j, z = p j := by
  classical
  obtain ⟨w, hw, he⟩ := affine_coefficients p hz
  have hc (i : κ) : w i = 0 ∨ w i = 1 := by
    have hh := omitted_coordinate p a w hp hw i
    rw [← he] at hh
    rcases hbinary (a i) with hb | hb
    · right; linarith
    · left; linarith
  have hn (i : κ) : 0 ≤ w i := by rcases hc i with h | h <;> simp [h]
  have hex : ∃ i, w i = 1 := by
    by_contra h
    push Not at h
    have hz' (i : κ) : w i = 0 := (hc i).resolve_right (h i)
    simp [hz'] at hw
  obtain ⟨i, hi⟩ := hex
  have hzero (j : κ) (hji : j ≠ i) : w j = 0 := by
    have hs : w i + w j ≤ ∑ l, w l := by
      have hh := sum_le_sum_of_subset_of_nonneg
        (s := ({i,j} : Finset κ)) (t := univ) (subset_univ _)
        (fun l _ _ => hn l)
      simpa [hji, hji.symm] using hh
    have hh := hn j
    rw [hw, hi] at hs
    linarith
  refine ⟨i, he.trans ?_⟩
  rw [sum_eq_single i]
  · simp [hi]
  · intro j _ hji; simp [hzero j hji]
  · simp

/-- The omitted-coordinate pattern itself certifies affine independence. -/
theorem omitted_coordinates_independent [Fintype κ] [DecidableEq κ]
    (p : κ → ι → ℝ) (a : κ → ι)
    (hp : ∀ i j, p j (a i) = if i = j then 0 else 1) :
    AffineIndependent ℝ p := by
  classical
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv he
  rw [affineCombination_eq_linear_combination _ _ _ hu,
    affineCombination_eq_linear_combination _ _ _ hv] at he
  funext i
  have hh := congrFun he (a i)
  rw [omitted_coordinate p a u hp hu, omitted_coordinate p a v hp hv] at hh
  linarith

/-- Actual coverage at the affine boundary: either a common block, or
exactly a simplex of actual support rows, with blocks omitting each fibre.
The second alternative retains nonexistence of a common block. -/
theorem boundary_dichotomy [Fintype α] [DecidableEq α]
    (B : ι → Finset α) (F : Finset α) {t : ℕ}
    (hF : F.Nonempty) (ht : 1 ≤ t) (htv : t ≤ Fintype.card α)
    (hcover : ∀ U : Finset α, U.card = t → ∃ i, U ⊆ B i)
    (hd : dimension (row B '' (F : Set α)) ≤ t) :
    (∃ i, F ⊆ B i) ∨
      (¬ ∃ i, F ⊆ B i) ∧ dimension (row B '' (F : Set α)) = t ∧
      ∃ S : Finset α, S ⊆ F ∧ S.card = t+1 ∧
        AffineIndependent ℝ (fun x : S => row B x.val) ∧
        row B '' (F : Set α) = row B '' (S : Set α) ∧
        ∀ x ∈ S, ∃ i, B i ∩ F = F.filter (fun y => row B y ≠ row B x) := by
  classical
  by_cases hcommon : ∃ i, F ⊆ B i
  · exact Or.inl hcommon
  right
  have hdim : dimension (row B '' (F : Set α)) = t := by
    by_contra hn
    exact hcommon (exists_block_of_dimension_lt B F hF ht htv hcover (by omega))
  obtain ⟨S, hS, hcard, hspan⟩ := exists_spanning_points F hF (row B)
  rw [hdim] at hcard
  have homit (x : S) : ∃ i, ∀ y : S, (y.val ∈ B i ↔ y ≠ x) := by
    obtain ⟨i, hi⟩ := hcover (S.erase x.val) (by
      rw [card_erase_of_mem x.property, hcard]; omega)
    have hxnot : x.val ∉ B i := by
      intro hx
      apply hcommon
      refine ⟨i, ?_⟩
      have hss : ∀ y ∈ S, y ∈ B i := by
        intro y hy
        by_cases he : y = x.val
        · simpa [he] using hx
        · exact hi (mem_erase.mpr ⟨he, hy⟩)
      have hh := common_support_eq B F S hS hspan
      exact (Set.ext_iff.mp hh i).mpr hss
    refine ⟨i, fun y => ⟨?_, ?_⟩⟩
    · intro hy he; subst y; exact hxnot hy
    · intro hy
      exact hi (mem_erase.mpr ⟨fun he => hy (Subtype.ext he), y.property⟩)
  choose a ha using homit
  have hpat (x y : S) :
      row B y.val (a x) = if x = y then 0 else 1 := by
    by_cases he : x = y
    · subst y; simp [row, ha]
    · have hne : y ≠ x := Ne.symm he
      simp [row, (ha x y).mpr hne, he]
  have hind := omitted_coordinates_independent (fun x : S => row B x.val) a hpat
  have hrange : Set.range (fun x : S => row B x.val) = row B '' (S : Set α) := by
    ext z
    simp
  have hrows (y : α) (hy : y ∈ F) : ∃ x : S, row B y = row B x.val := by
    apply omitted_coordinates_rigidity (fun x : S => row B x.val) a hpat
    · rw [hrange, hspan]
      exact mem_affineSpan ℝ (Set.mem_image_of_mem _ hy)
    · intro i
      by_cases hi : y ∈ B i <;> simp [row, hi]
  refine ⟨hcommon, hdim, S, hS, hcard, hind, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro z ⟨y, hy, rfl⟩
      obtain ⟨x, hx⟩ := hrows y hy
      exact ⟨x.val, x.property, hx.symm⟩
    · exact Set.image_mono hS
  · intro x hx
    refine ⟨a ⟨x,hx⟩, ?_⟩
    ext y
    simp only [mem_inter, mem_filter]
    constructor
    · rintro ⟨hy, hyF⟩
      refine ⟨hyF, ?_⟩
      intro he
      have hh := congrFun he (a ⟨x,hx⟩)
      have hxx := (ha ⟨x,hx⟩ ⟨x,hx⟩).not.mpr (by simp)
      simp [row, hy, hxx] at hh
    · rintro ⟨hyF, hne⟩
      obtain ⟨z, hz⟩ := hrows y hyF
      have hzx : z ≠ ⟨x,hx⟩ := by intro he; subst z; exact hne hz
      have hh := congrFun hz (a ⟨x,hx⟩)
      have hzmem := (ha ⟨x,hx⟩ z).mpr hzx
      have hyy : row B y (a ⟨x,hx⟩) = 1 := by
        rw [hh]; exact (row_eq_one_iff _ _ _).mpr hzmem
      exact ⟨(row_eq_one_iff _ _ _).mp hyy, hyF⟩

/-- Exact support-class count and omitted fibres, in a form convenient for
capacity estimates. Every class is an actual nonempty point fibre. -/
theorem boundary_supports [Fintype α] [DecidableEq α]
    (B : ι → Finset α) (F : Finset α) {t : ℕ}
    (hF : F.Nonempty) (ht : 1 ≤ t) (htv : t ≤ Fintype.card α)
    (hcover : ∀ U : Finset α, U.card = t → ∃ i, U ⊆ B i)
    (hd : dimension (row B '' (F : Set α)) ≤ t)
    (hn : ¬ ∃ i, F ⊆ B i) :
    (F.image (row B)).card = t+1 ∧
    ∀ r ∈ F.image (row B),
      (F.filter (fun x => row B x = r)).Nonempty ∧
      ∃ i, B i ∩ F = F.filter (fun x => row B x ≠ r) := by
  classical
  obtain hc | ⟨_, _, S, hS, hcard, hind, himage, homit⟩ :=
    boundary_dichotomy B F hF ht htv hcover hd
  · exact (hn hc).elim
  have himage' : F.image (row B) = S.image (row B) := by
    apply Finset.coe_injective
    simpa only [coe_image] using himage
  constructor
  · rw [himage', card_image_of_injOn, hcard]
    intro x hx y hy he
    exact congrArg Subtype.val (hind.injective (show
      (fun z : S => row B z.val) ⟨x,hx⟩ =
        (fun z : S => row B z.val) ⟨y,hy⟩ from he))
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hr
    refine ⟨⟨x, mem_filter.mpr ⟨hx,rfl⟩⟩, ?_⟩
    have hs : row B x ∈ S.image (row B) := by rw [← himage']; exact mem_image_of_mem _ hx
    obtain ⟨y, hy, he⟩ := mem_image.mp hs
    simpa only [he] using homit y hy

/-- Boundary capacity for nonuniform blocks of size at most k, including
the empty selection. All points in duplicate-support fibres are counted. -/
theorem card_mul_le_of_dimension_le [Fintype α] [DecidableEq α]
    (B : ι → Finset α) (F : Finset α) {t k : ℕ}
    (ht : 1 ≤ t) (htv : t ≤ Fintype.card α)
    (hcover : ∀ U : Finset α, U.card = t → ∃ i, U ⊆ B i)
    (hsize : ∀ i, (B i).card ≤ k)
    (hd : dimension (row B '' (F : Set α)) ≤ t) :
    t * F.card ≤ (t+1)*k := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  by_cases hn : ∃ i, F ⊆ B i
  · obtain ⟨i, hi⟩ := hn
    have hh := (card_le_card hi).trans (hsize i)
    nlinarith
  obtain ⟨hs, hf⟩ := boundary_supports B F hF ht htv hcover hd hn
  have hb (r : ι → ℝ) (hr : r ∈ F.image (row B)) :
      F.card ≤ k + (F.filter (fun x => row B x = r)).card := by
    obtain ⟨_, i, hi⟩ := hf r hr
    have hc := (card_le_card (inter_subset_left (s₁ := B i) (s₂ := F))).trans (hsize i)
    rw [hi] at hc
    have he := card_filter_add_card_filter_not (s := F) (p := fun x => row B x = r)
    change (F.filter (fun x => row B x = r)).card +
      (F.filter (fun x => row B x ≠ r)).card = F.card at he
    omega
  have hh := sum_le_sum hb
  have hp := card_eq_sum_card_image (row B) F
  simp only [sum_const, Nat.nsmul_eq_mul, sum_add_distrib, ← hp, hs] at hh
  nlinarith

/-- Combine the boundary theorem with a bound on every nonempty actual
support fibre. Empty selections do not require choosing a representative. -/
theorem card_le_max_of_fibres [Fintype α] [DecidableEq α]
    (B : ι → Finset α) (F : Finset α) {t k M : ℕ}
    (ht : 1 ≤ t) (htv : t ≤ Fintype.card α)
    (hcover : ∀ U : Finset α, U.card = t → ∃ i, U ⊆ B i)
    (hsize : ∀ i, (B i).card ≤ k)
    (hd : dimension (row B '' (F : Set α)) ≤ t)
    (hfibre : ∀ r ∈ F.image (row B), (F.filter (fun x => row B x = r)).card ≤ M) :
    F.card ≤ max k ((t+1)*M) := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  by_cases hn : ∃ i, F ⊆ B i
  · obtain ⟨i, hi⟩ := hn
    exact ((card_le_card hi).trans (hsize i)).trans (le_max_left _ _)
  have hs := (boundary_supports B F hF ht htv hcover hd hn).1
  have hh := sum_le_sum hfibre
  have hp := card_eq_sum_card_image (row B) F
  simp only [← hp, sum_const, Nat.nsmul_eq_mul, hs] at hh
  exact hh.trans (le_max_right _ _)

end CoveringDesigns.AffineCapacity
