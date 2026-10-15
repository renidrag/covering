import CoveringDesigns.C13_7_4.Structural.FourPointConstant
import CoveringDesigns.C13_7_4.Structural.FourPointProper

/-!
A triplicate quadruple of minimum points with degree-seven pairs is
impossible.  The four GPPT vertex frames give six compatible Stanton edge
frames. A constant triad coordinate violates the two-block residual budget;
three proper coordinates violate both possible GPPT link geometries at a
fifth minimum point.
-/

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The incidence budget supplies a minimum point outside any four roots. -/
theorem fifth_minimum_outside {C : Family α} {K : Finset α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) (hb : C.card ≤ 29)
    (hK : K.card = 4) : ∃ p, p ∉ K ∧ degree C p = 15 := by
  have hm := five_minimum_points hn hC hb
  have hnot : ¬ minimumPoints C 15 ⊆ K := by
    intro hs
    have hc := card_le_card hs
    omega
  obtain ⟨p, hp, hpn⟩ := not_subset.mp hnot
  exact ⟨p, hpn, (mem_filter.mp hp).2⟩

/-- Structural exclusion of a triplicate four-set of minimum points. The
hypothesis concerns only its six internal pair multiplicities. -/
theorem bad_quadruple_excluded {C : Family α} {K : Finset α}
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4) (hb : C.card ≤ 29)
    (hK : K.card = 4) (hmin : ∀ p ∈ K, degree C p = 15)
    (hpair : ∀ p ∈ K, ∀ q ∈ K, p ≠ q → degree (star C p) q = 7) :
    containmentCount C K ≠ 3 := by
  classical
  intro hthree
  obtain ⟨F⟩ := exists_fourPointSystem hn hC hK hthree hmin hpair
  let e : Fin 4 ≃ K :=
    (Fintype.equivFinOfCardEq (by simpa using hK : Fintype.card K = 4)).symm
  let v : Fin 4 → α := fun i => (e i).val
  have hv : Function.Injective v := Subtype.val_injective.comp e.injective
  have hmem (i : Fin 4) : v i ∈ K := (e i).property
  have himage : univ.image v = K := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact hmem i
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact mem_image.mpr ⟨i, mem_univ _, congrArg Subtype.val hi⟩
  have hproper (j : Fin 3) : K4.Proper
      (F.indexedSelected v hv hmem 0 1 j) (F.indexedSelected v hv hmem 0 2 j)
      (F.indexedSelected v hv hmem 0 3 j) (F.indexedSelected v hv hmem 1 2 j)
      (F.indexedSelected v hv hmem 1 3 j) (F.indexedSelected v hv hmem 2 3 j) := by
    rcases F.indexed_column_dichotomy hK v hv hmem j with hc | hc
    · exact False.elim (constant_column_impossible F hn hC hb hK j _
        (F.constant_column_global hK v hv hmem himage j hc))
    · exact hc
  obtain ⟨p, hpK, hp⟩ := fifth_minimum_outside hn hC hb hK
  exact F.proper_columns_impossible hn hC hK v hv hmem himage hproper hp hpK

#guard_standard_axioms fifth_minimum_outside bad_quadruple_excluded

end CoveringDesigns.C13Structural
