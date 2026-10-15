import CoveringDesigns.C11_5_2.Stanton

/-! The two elementary Stanton consequences used by the structural GPPT proof. -/

namespace CoveringDesigns

open Finset

theorem stanton_representative_degree_bound (tag : Bool) :
    ∀ q : Fin 11, degree (stantonRepresentative tag) q ≤ 4 := by
  cases tag <;> decide +kernel

-- Keep bounded block quantification from enumerating the powerset repeatedly.
section
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem stanton_representative_intersection_bound (tag : Bool) :
    ∀ B ∈ stantonRepresentative tag, ∀ D ∈ stantonRepresentative tag,
      B ≠ D → (B ∩ D).card ≤ 3 := by
  cases tag <;> decide +kernel

end

/-- The degree bound follows before the template classification is needed. -/
theorem stanton_degree_bound_on {α : Type*} [Fintype α] [DecidableEq α]
    (hn : Fintype.card α = 11) {C : Family α}
    (hC : IsCover C 5 2) (hb : C.card = 7) (q : α) : degree C q ≤ 4 :=
  structural_degree_bound hn hC hb q

theorem stanton_degree_bound {C : Family (Fin 11)}
    (hC : IsCover C 5 2) (hb : C.card = 7) (q : Fin 11) : degree C q ≤ 4 :=
  stanton_degree_bound_on (by simp) hC hb q

/-- Likewise, the intersection bound has a direct structural proof. -/
theorem stanton_intersection_bound_on {α : Type*} [Fintype α] [DecidableEq α]
    (hn : Fintype.card α = 11) {C : Family α}
    (hC : IsCover C 5 2) (hb : C.card = 7)
    {B D : Finset α} (hB : B ∈ C) (hD : D ∈ C) (hBD : B ≠ D) :
    (B ∩ D).card ≤ 3 :=
  structural_intersection_le_three hn hC hb hB hD hBD

theorem stanton_intersection_bound {C : Family (Fin 11)}
    (hC : IsCover C 5 2) (hb : C.card = 7)
    {B D : Finset (Fin 11)} (hB : B ∈ C) (hD : D ∈ C) (hBD : B ≠ D) :
    (B ∩ D).card ≤ 3 :=
  stanton_intersection_bound_on (by simp) hC hb hB hD hBD

end CoveringDesigns
