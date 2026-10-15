import CoveringDesigns.C13_7_4.Structural.FourPoint

/-! Edge colourings obtained from the six intrinsic Stanton selections. -/

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural StantonGeometry

variable {α : Type*} [Fintype α] [DecidableEq α]

set_option maxHeartbeats 1000000

namespace FourPointSystem

variable {C : Family α} {K : Finset α} (F : FourPointSystem C K)

theorem marked_mem (p : α) (hp : p ∈ K) (q : α) (hq : q ∈ K)
    (hqp : q ≠ p) (j : Fin 3) :
    {p, q} ∪ markedRow F.common.triad (F.selected p hp q hq hqp) j ∈ C := by
  have he := (F.vertex p hp).marked_mem (F.neighborIndex p hp q hq hqp) j
  simpa only [F.neighborIndex_spec, F.aligned, selected,
    insert_union, singleton_union] using he

/-- Three edges at a root are monochromatic or rainbow in each triad. -/
theorem local_allowed (p : α) (hp : p ∈ K)
    (q : α) (hq : q ∈ K) (hqp : q ≠ p)
    (r : α) (hr : r ∈ K) (hrp : r ≠ p)
    (s : α) (hs : s ∈ K) (hsp : s ≠ p)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (j : Fin 3) :
    K4.Allowed (F.selected p hp q hq hqp j)
      (F.selected p hp r hr hrp j) (F.selected p hp s hs hsp j) := by
  have hiqr : F.neighborIndex p hp q hq hqp ≠ F.neighborIndex p hp r hr hrp := by
    intro he
    exact hqr ((F.neighborIndex_spec p hp q hq hqp).symm.trans
      ((congrArg (F.vertex p hp).neighbor he).trans (F.neighborIndex_spec p hp r hr hrp)))
  have hiqs : F.neighborIndex p hp q hq hqp ≠ F.neighborIndex p hp s hs hsp := by
    intro he
    exact hqs ((F.neighborIndex_spec p hp q hq hqp).symm.trans
      ((congrArg (F.vertex p hp).neighbor he).trans (F.neighborIndex_spec p hp s hs hsp)))
  have hirs : F.neighborIndex p hp r hr hrp ≠ F.neighborIndex p hp s hs hsp := by
    intro he
    exact hrs ((F.neighborIndex_spec p hp r hr hrp).symm.trans
      ((congrArg (F.vertex p hp).neighbor he).trans (F.neighborIndex_spec p hp s hs hsp)))
  rcases (F.vertex p hp).column_pattern j with hi | ⟨x, hx⟩
  · exact Or.inr ⟨fun h => hiqr (hi h), fun h => hiqs (hi h), fun h => hirs (hi h)⟩
  · exact Or.inl ⟨(hx _).trans (hx _).symm, (hx _).trans (hx _).symm⟩

/-- Labels only name the four root points; they impose no symmetry condition. -/
noncomputable def indexedSelected (v : Fin 4 → α) (hv : Function.Injective v)
    (hmem : ∀ i, v i ∈ K) (i k : Fin 4) : Fin 3 → α :=
  if hik : i = k then fun _ => v i
  else F.selected (v i) (hmem i) (v k) (hmem k) (fun he => hik (hv he.symm))

theorem indexedSelected_symm (hK : K.card = 4) (v : Fin 4 → α)
    (hv : Function.Injective v) (hmem : ∀ i, v i ∈ K) (i k : Fin 4) :
    F.indexedSelected v hv hmem i k = F.indexedSelected v hv hmem k i := by
  by_cases hik : i = k
  · subst k
    rfl
  · simp only [indexedSelected, dite_eq_right hik, dite_eq_right (Ne.symm hik)]
    exact F.selected_symm hK _ _ _ _ _

theorem indexedSelected_mem (v : Fin 4 → α)
    (hv : Function.Injective v) (hmem : ∀ i, v i ∈ K) {i k : Fin 4}
    (hik : i ≠ k) (j : Fin 3) :
    F.indexedSelected v hv hmem i k j ∈ F.common.triad j := by
  simp only [indexedSelected, dite_eq_right hik]
  exact F.selected_mem _ _ _ _ _ _

theorem indexedSelected_allowed (v : Fin 4 → α)
    (hv : Function.Injective v) (hmem : ∀ i, v i ∈ K) {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (j : Fin 3) :
    K4.Allowed (F.indexedSelected v hv hmem a b j)
      (F.indexedSelected v hv hmem a c j) (F.indexedSelected v hv hmem a d j) := by
  simp only [indexedSelected, dite_eq_right hab, dite_eq_right hac, dite_eq_right had]
  apply F.local_allowed
  · exact fun h => hbc (hv h)
  · exact fun h => hbd (hv h)
  · exact fun h => hcd (hv h)

/-- GPPT's four local constraints give the tetrahedral coloring dichotomy. -/
theorem indexed_column_dichotomy (hK : K.card = 4) (v : Fin 4 → α)
    (hv : Function.Injective v) (hmem : ∀ i, v i ∈ K) (j : Fin 3) :
    K4.Constant
      (F.indexedSelected v hv hmem 0 1 j) (F.indexedSelected v hv hmem 0 2 j)
      (F.indexedSelected v hv hmem 0 3 j) (F.indexedSelected v hv hmem 1 2 j)
      (F.indexedSelected v hv hmem 1 3 j) (F.indexedSelected v hv hmem 2 3 j) ∨
    K4.Proper
      (F.indexedSelected v hv hmem 0 1 j) (F.indexedSelected v hv hmem 0 2 j)
      (F.indexedSelected v hv hmem 0 3 j) (F.indexedSelected v hv hmem 1 2 j)
      (F.indexedSelected v hv hmem 1 3 j) (F.indexedSelected v hv hmem 2 3 j) := by
  apply K4.local_pattern_dichotomy_of_mem (F.common.triad j)
    (le_of_eq (F.common.triad_card j))
    (F.indexedSelected_mem v hv hmem (by decide : (0 : Fin 4) ≠ 1) j)
    (F.indexedSelected_mem v hv hmem (by decide : (0 : Fin 4) ≠ 2) j)
    (F.indexedSelected_mem v hv hmem (by decide : (0 : Fin 4) ≠ 3) j)
    (F.indexedSelected_mem v hv hmem (by decide : (1 : Fin 4) ≠ 2) j)
    (F.indexedSelected_mem v hv hmem (by decide : (1 : Fin 4) ≠ 3) j)
    (F.indexedSelected_mem v hv hmem (by decide : (2 : Fin 4) ≠ 3) j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact F.indexedSelected_allowed v hv hmem (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) j
  · have hh := F.indexedSelected_allowed v hv hmem
      (a := 1) (b := 0) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j
    rw [F.indexedSelected_symm hK v hv hmem 1 0] at hh
    exact hh
  · have hh := F.indexedSelected_allowed v hv hmem
      (a := 2) (b := 0) (c := 1) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j
    rw [F.indexedSelected_symm hK v hv hmem 2 0,
      F.indexedSelected_symm hK v hv hmem 2 1] at hh
    exact hh
  · have hh := F.indexedSelected_allowed v hv hmem
      (a := 3) (b := 0) (c := 1) (d := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j
    rw [F.indexedSelected_symm hK v hv hmem 3 0,
      F.indexedSelected_symm hK v hv hmem 3 1,
      F.indexedSelected_symm hK v hv hmem 3 2] at hh
    exact hh

/-- A constant coordinate in the six named edges is constant in every
incident row, regardless of the choices of names or row orders. -/
theorem constant_column_global (hK : K.card = 4) (v : Fin 4 → α)
    (hv : Function.Injective v) (hmem : ∀ i, v i ∈ K)
    (himage : univ.image v = K) (j : Fin 3)
    (hc : K4.Constant
      (F.indexedSelected v hv hmem 0 1 j) (F.indexedSelected v hv hmem 0 2 j)
      (F.indexedSelected v hv hmem 0 3 j) (F.indexedSelected v hv hmem 1 2 j)
      (F.indexedSelected v hv hmem 1 3 j) (F.indexedSelected v hv hmem 2 3 j)) :
    ∀ p hp q hq hqp, F.selected p hp q hq hqp j = F.indexedSelected v hv hmem 0 1 j := by
  have hall (a b : Fin 4) (hab : a ≠ b) :
      F.indexedSelected v hv hmem a b j = F.indexedSelected v hv hmem 0 1 j := by
    have h10 := congrFun (F.indexedSelected_symm hK v hv hmem 1 0) j
    have h20 := congrFun (F.indexedSelected_symm hK v hv hmem 2 0) j
    have h30 := congrFun (F.indexedSelected_symm hK v hv hmem 3 0) j
    have h21 := congrFun (F.indexedSelected_symm hK v hv hmem 2 1) j
    have h31 := congrFun (F.indexedSelected_symm hK v hv hmem 3 1) j
    have h32 := congrFun (F.indexedSelected_symm hK v hv hmem 3 2) j
    rcases hc with ⟨h02, h03, h12, h13, h23⟩
    fin_cases a <;> fin_cases b <;> simp_all
  intro p hp q hq hqp
  have hp' : p ∈ univ.image v := himage ▸ hp
  have hq' : q ∈ univ.image v := himage ▸ hq
  obtain ⟨a, _, rfl⟩ := mem_image.mp hp'
  obtain ⟨b, _, rfl⟩ := mem_image.mp hq'
  have hab : a ≠ b := fun he => hqp (congrArg v he.symm)
  simpa only [indexedSelected, dite_eq_right hab] using hall a b hab

end FourPointSystem

#guard_standard_axioms FourPointSystem.local_allowed FourPointSystem.indexed_column_dichotomy
  FourPointSystem.constant_column_global

end CoveringDesigns.C13Structural
