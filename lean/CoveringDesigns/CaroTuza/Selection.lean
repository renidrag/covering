import CoveringDesigns.CaroTuza.Graph

/-! Caro–Tuza selection for finite multigraphs and Horsley's weighted extension.
The proof deletes a maximum-degree vertex and inducts on the finite vertex set.
Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.CaroTuza
open Finset
variable {α : Type*}

/-- A deletion used by the induction strictly reduces the number of vertices. -/
theorem erase_card_lt [DecidableEq α] {V : Finset α} {z : α} (hz : z ∈ V) :
    (V.erase z).card < V.card := card_erase_lt_of_mem hz

/-- Real-valued selection estimate, before rounding to an integer. -/
theorem exists_selection_real {m : ℕ} (hm : 0 < m) (w : α → α → ℝ)
    (V : Finset α) (h : GraphOn w V) (hu : UnitEdges m w V) :
    ∃ S ⊆ V, (∀ x ∈ S, degree w S x < m) ∧ potential m w V ≤ S.card := by
  classical
  induction V using Finset.strongInductionOn with
  | _ V ih =>
    by_cases hlow : ∀ x ∈ V, degree w V x < m
    · exact ⟨V, Subset.rfl, hlow, potential_le_card hm h⟩
    · obtain ⟨x, hx, hxlarge⟩ : ∃ x ∈ V, (m : ℝ) ≤ degree w V x := by
        simpa only [not_forall, not_lt, exists_prop] using hlow
      obtain ⟨z, hz, hmax⟩ := V.exists_max_image (degree w V) ⟨x, hx⟩
      have hlarge := hxlarge.trans (hmax x hx)
      obtain ⟨S, hS, hdeg, hsize⟩ := ih (V.erase z) (erase_ssubset hz)
        (h.mono (erase_subset z V)) (hu.mono h (erase_subset z V))
      exact ⟨S, hS.trans (erase_subset z V), hdeg,
        (potential_erase_le hm h hu hz hmax hlarge).trans hsize⟩

/-- Horsley's weighted extension of Caro–Tuza, with exact natural ceiling.
The graph has a finite vertex set in an arbitrary ambient type. -/
theorem exists_selection {m : ℕ} (hm : 0 < m) (w : α → α → ℝ)
    (V : Finset α) (h : GraphOn w V) (hu : UnitEdges m w V) :
    ∃ S ⊆ V, (∀ x ∈ S, degree w S x < m) ∧
      ⌈potential m w V⌉₊ ≤ S.card := by
  obtain ⟨S, hS, hdeg, hsize⟩ := exists_selection_real hm w V h hu
  exact ⟨S, hS, hdeg, Nat.ceil_le.mpr hsize⟩

/-- Degree upper bounds give a possibly weaker, still justified selection
estimate. The degrees being bounded are those induced by V. -/
theorem exists_selection_of_degree_le {m : ℕ} (hm : 0 < m)
    (w : α → α → ℝ) (V : Finset α) (h : GraphOn w V) (hu : UnitEdges m w V)
    (D : α → ℝ) (hD : ∀ x ∈ V, degree w V x ≤ D x) :
    ∃ S ⊆ V, (∀ x ∈ S, degree w S x < m) ∧
      ⌈∑ x ∈ V, f m (D x)⌉₊ ≤ S.card := by
  obtain ⟨S, hS, hdeg, hsize⟩ := exists_selection_real hm w V h hu
  refine ⟨S, hS, hdeg, Nat.ceil_le.mpr (le_trans ?_ hsize)⟩
  exact sum_le_sum (fun x hx => f_antitone hm (degree_nonneg h hx) (hD x hx))

/-- Select inside a specified induced subgraph. The high-high condition is
inherited from V; D bounds degrees in T, not degrees in V. -/
theorem exists_selection_in {m : ℕ} (hm : 0 < m)
    (w : α → α → ℝ) (V : Finset α) (h : GraphOn w V) (hu : UnitEdges m w V)
    (T : Finset α) (hTV : T ⊆ V) (D : α → ℝ)
    (hD : ∀ x ∈ T, degree w T x ≤ D x) :
    ∃ S ⊆ T, (∀ x ∈ S, degree w S x < m) ∧
      ⌈∑ x ∈ T, f m (D x)⌉₊ ≤ S.card :=
  exists_selection_of_degree_le hm w T (h.mono hTV) (hu.mono h hTV) D hD

/-- Natural edge weights satisfy the weighted integrality substitute. -/
theorem nat_unitEdges (m : ℕ) (w : α → α → ℕ) (V : Finset α) :
    UnitEdges m (fun x y => (w x y : ℝ)) V := by
  intro x _ y _ _ _ hpos
  change (0 : ℝ) < w x y at hpos
  change (1 : ℝ) ≤ w x y
  have hp : 0 < w x y := by exact_mod_cast hpos
  exact_mod_cast (show 1 ≤ w x y from hp)

/-- The Caro–Tuza multigraph statement used in Horsley–Singh Theorem 12.
Parallel edges count with their natural multiplicity; no extra hypothesis on
degrees or positive edges is required. -/
theorem exists_nat_selection {m : ℕ} (hm : 0 < m) (w : α → α → ℕ)
    (V : Finset α) (hsym : ∀ x ∈ V, ∀ y ∈ V, w x y = w y x)
    (hdiag : ∀ x ∈ V, w x x = 0) :
    ∃ S ⊆ V, (∀ x ∈ S, ∑ y ∈ S, w x y < m) ∧
      ⌈∑ x ∈ V, f m ((∑ y ∈ V, w x y : ℕ) : ℝ)⌉₊ ≤ S.card := by
  have hg : GraphOn (fun x y => (w x y : ℝ)) V :=
    ⟨fun x hx y hy => by rw [hsym x hx y hy],
      fun _ _ _ _ => Nat.cast_nonneg _, fun x hx => by simp [hdiag x hx]⟩
  obtain ⟨S, hS, hdeg, hsize⟩ := exists_selection hm _ V hg (nat_unitEdges m w V)
  refine ⟨S, hS, ?_, ?_⟩
  · intro x hx
    have hd := hdeg x hx
    change (∑ y ∈ S, (w x y : ℝ)) < m at hd
    exact_mod_cast hd
  · simpa only [potential, degree, Nat.cast_sum] using hsize

end CoveringDesigns.CaroTuza
