import CoveringDesigns.CaroTuza
import CoveringDesigns.Foundations.StandardAxioms

/-! Full contracts and transitive foundational-axiom audit for standalone
Caro–Tuza selection and Horsley's weighted extension. -/
open Finset CoveringDesigns CoveringDesigns.CaroTuza
universe u

#print CaroTuza.f
#print CaroTuza.degree
#print CaroTuza.GraphOn
#print CaroTuza.UnitEdges
#print CaroTuza.potential
#print CaroTuza.Examples.parallel
#print CaroTuza.Examples.fractional
#print CaroTuza.Examples.twoEdges

#check (CaroTuza.f_low : ∀ {m : ℕ} {x : ℝ}, x ≤ m → f m x=1-x/(2*m))
#check (CaroTuza.f_high : ∀ {m : ℕ}, 0 < m → ∀ {x : ℝ}, (m : ℝ) ≤ x →
  f m x=(m+1)/(2*(x+1)))
#check (CaroTuza.f_zero : ∀ m : ℕ, f m 0=1)
#check (CaroTuza.f_join : ∀ {m : ℕ}, 0 < m → f m m=1/2)
#check (CaroTuza.f_nonneg : ∀ {m : ℕ}, 0 < m → ∀ {x : ℝ}, 0 ≤ x → 0 ≤ f m x)
#check (CaroTuza.f_le_one : ∀ {m : ℕ}, 0 < m → ∀ {x : ℝ}, 0 ≤ x → f m x ≤ 1)
#check (CaroTuza.f_antitone : ∀ {m : ℕ}, 0 < m → ∀ {x y : ℝ},
  0 ≤ x → x ≤ y → f m y ≤ f m x)
#check (CaroTuza.decrement : ∀ {m : ℕ}, 0 < m → ∀ {x y : ℝ},
  (m : ℝ) ≤ x → 1 ≤ y → y ≤ x →
  y*((m : ℝ)+1)/(2*x*(x+1)) ≤ f m (x-y)-f m x)
#check (CaroTuza.decrement_of_le_max : ∀ {m : ℕ}, 0 < m → ∀ {D X y : ℝ},
  (m : ℝ) ≤ D → 0 ≤ X → X ≤ D → 0 ≤ y → y ≤ X →
  ((m : ℝ) ≤ X → 0 < y → 1 ≤ y) →
  y*(((m : ℝ)+1)/(2*D*(D+1))) ≤ f m (X-y)-f m X)

#check (CaroTuza.GraphOn.mono : ∀ {α : Type u} {w : α → α → ℝ} {V T : Finset α},
  GraphOn w V → T ⊆ V → GraphOn w T)
#check (CaroTuza.degree_nonneg : ∀ {α : Type u} {w : α → α → ℝ} {V : Finset α},
  GraphOn w V → ∀ {x : α}, x ∈ V → 0 ≤ degree w V x)
#check (CaroTuza.degree_mono : ∀ {α : Type u} {w : α → α → ℝ} {V T : Finset α},
  GraphOn w V → T ⊆ V → ∀ {x : α}, x ∈ V → degree w T x ≤ degree w V x)
#check (CaroTuza.weight_le_degree : ∀ {α : Type u} {w : α → α → ℝ} {V : Finset α},
  GraphOn w V → ∀ {x y : α}, x ∈ V → y ∈ V → w x y ≤ degree w V x)
#check (CaroTuza.UnitEdges.mono : ∀ {α : Type u} {m : ℕ}
  {w : α → α → ℝ} {V T : Finset α},
  UnitEdges m w V → GraphOn w V → T ⊆ V → UnitEdges m w T)
#check (CaroTuza.degree_erase : ∀ {α : Type u} [DecidableEq α] (w : α → α → ℝ)
  {V : Finset α} {z : α}, z ∈ V → ∀ x : α,
  degree w (V.erase z) x=degree w V x-w x z)
#check (CaroTuza.potential_nonneg : ∀ {α : Type u} {m : ℕ}, 0 < m →
  ∀ {w : α → α → ℝ} {V : Finset α}, GraphOn w V → 0 ≤ potential m w V)
#check (CaroTuza.potential_le_card : ∀ {α : Type u} {m : ℕ}, 0 < m →
  ∀ {w : α → α → ℝ} {V : Finset α}, GraphOn w V → potential m w V ≤ V.card)
#check (CaroTuza.potential_erase_le : ∀ {α : Type u} [DecidableEq α] {m : ℕ}, 0 < m →
  ∀ {w : α → α → ℝ} {V : Finset α}, GraphOn w V → UnitEdges m w V →
  ∀ {z : α}, z ∈ V → (∀ x ∈ V, degree w V x ≤ degree w V z) →
  (m : ℝ) ≤ degree w V z → potential m w V ≤ potential m w (V.erase z))

#check (CaroTuza.erase_card_lt : ∀ {α : Type u} [DecidableEq α]
  {V : Finset α} {z : α}, z ∈ V → (V.erase z).card < V.card)
#check (CaroTuza.exists_selection_real : ∀ {α : Type u} {m : ℕ}, 0 < m →
  ∀ (w : α → α → ℝ) (V : Finset α), GraphOn w V → UnitEdges m w V →
  ∃ S ⊆ V, (∀ x ∈ S, degree w S x < m) ∧ potential m w V ≤ S.card)
#check (CaroTuza.exists_selection : ∀ {α : Type u} {m : ℕ}, 0 < m →
  ∀ (w : α → α → ℝ) (V : Finset α), GraphOn w V → UnitEdges m w V →
  ∃ S ⊆ V, (∀ x ∈ S, degree w S x < m) ∧ ⌈potential m w V⌉₊ ≤ S.card)
#check (CaroTuza.exists_selection_of_degree_le : ∀ {α : Type u} {m : ℕ}, 0 < m →
  ∀ (w : α → α → ℝ) (V : Finset α), GraphOn w V → UnitEdges m w V →
  ∀ D : α → ℝ, (∀ x ∈ V, degree w V x ≤ D x) →
  ∃ S ⊆ V, (∀ x ∈ S, degree w S x < m) ∧ ⌈∑ x ∈ V, f m (D x)⌉₊ ≤ S.card)
#check (CaroTuza.exists_selection_in : ∀ {α : Type u} {m : ℕ}, 0 < m →
  ∀ (w : α → α → ℝ) (V : Finset α), GraphOn w V → UnitEdges m w V →
  ∀ T : Finset α, T ⊆ V → ∀ D : α → ℝ, (∀ x ∈ T, degree w T x ≤ D x) →
  ∃ S ⊆ T, (∀ x ∈ S, degree w S x < m) ∧ ⌈∑ x ∈ T, f m (D x)⌉₊ ≤ S.card)
#check (CaroTuza.nat_unitEdges : ∀ {α : Type u} (m : ℕ) (w : α → α → ℕ) (V : Finset α),
  UnitEdges m (fun x y => (w x y : ℝ)) V)
#check (CaroTuza.exists_nat_selection : ∀ {α : Type u} {m : ℕ}, 0 < m →
  ∀ (w : α → α → ℕ) (V : Finset α),
  (∀ x ∈ V, ∀ y ∈ V, w x y=w y x) → (∀ x ∈ V, w x x=0) →
  ∃ S ⊆ V, (∀ x ∈ S, ∑ y ∈ S, w x y < m) ∧
  ⌈∑ x ∈ V, f m ((∑ y ∈ V, w x y : ℕ) : ℝ)⌉₊ ≤ S.card)

namespace CoveringDesigns.AuditCaroTuza

/-- Fully expanded weighted contract: nonedges are allowed between high-degree
vertices, and both the internal-degree and rounded size claims are explicit. -/
theorem weighted_selection_explicit {α : Type u} {m : ℕ} (hm : 0 < m)
    (w : α → α → ℝ) (V : Finset α)
    (hsym : ∀ x ∈ V, ∀ y ∈ V, w x y=w y x)
    (hnonneg : ∀ x ∈ V, ∀ y ∈ V, 0 ≤ w x y)
    (hdiag : ∀ x ∈ V, w x x=0)
    (hunit : ∀ x ∈ V, ∀ y ∈ V, (m : ℝ) ≤ ∑ z ∈ V, w x z →
      (m : ℝ) ≤ ∑ z ∈ V, w y z → 0 < w x y → 1 ≤ w x y) :
    ∃ S ⊆ V, (∀ x ∈ S, ∑ y ∈ S, w x y < (m : ℝ)) ∧
      ⌈∑ x ∈ V, if (∑ y ∈ V, w x y) ≤ (m : ℝ)
        then 1-(∑ y ∈ V, w x y)/(2*m)
        else ((m : ℝ)+1)/(2*((∑ y ∈ V, w x y)+1))⌉₊ ≤ S.card := by
  exact CaroTuza.exists_selection hm w V ⟨hsym, hnonneg, hdiag⟩ hunit

end CoveringDesigns.AuditCaroTuza

#check (CaroTuza.Examples.empty_selection : ∀ {α : Type u} {m : ℕ}, 0 < m →
  ∀ w : α → α → ℝ, ∃ S ⊆ (∅ : Finset α),
  (∀ x ∈ S, degree w S x < m) ∧ ⌈potential m w ∅⌉₊ ≤ S.card)
#check (CaroTuza.Examples.edgeless : ∀ {α : Type u} {m : ℕ}, 0 < m →
  ∀ V : Finset α, (∀ x ∈ V, degree (fun _ _ : α => (0 : ℝ)) V x < m) ∧
  ⌈potential m (fun _ _ : α => (0 : ℝ)) V⌉₊=V.card)
#check (CaroTuza.Examples.singleton : ∀ {α : Type u} [DecidableEq α] {m : ℕ}, 0 < m →
  ∀ (w : α → α → ℝ) (x : α), w x x=0 →
  degree w {x} x < m ∧ ⌈potential m w {x}⌉₊=1)
#check (CaroTuza.Examples.threshold_one : ∀ {α : Type u} (w : α → α → ℕ) (V : Finset α),
  (∀ x ∈ V, ∀ y ∈ V, w x y=w y x) → (∀ x ∈ V, w x x=0) →
  ∃ S ⊆ V, (∀ x ∈ S, ∑ y ∈ S, w x y=0) ∧
  ⌈∑ x ∈ V, f 1 ((∑ y ∈ V, w x y : ℕ) : ℝ)⌉₊ ≤ S.card)
#check (CaroTuza.Examples.join_one : f 1 1=1/2 ∧ (1+1 : ℝ)/(2*(1+1))=1/2)
#check (CaroTuza.Examples.parallel_edges : ∃ S ⊆ (univ : Finset (Fin 2)),
  (∀ x ∈ S, ∑ y ∈ S, CaroTuza.Examples.parallel x y < 2) ∧ 1 ≤ S.card)
#check (CaroTuza.Examples.fractional_hypotheses :
  GraphOn CaroTuza.Examples.fractional univ ∧ UnitEdges 1 CaroTuza.Examples.fractional univ ∧
  (∀ x, degree CaroTuza.Examples.fractional univ x=1/2) ∧ CaroTuza.Examples.fractional 0 1=1/2)
#check (CaroTuza.Examples.fractional_selection : ∃ S ⊆ (univ : Finset (Fin 2)),
  (∀ x ∈ S, degree CaroTuza.Examples.fractional S x < 1) ∧ 2 ≤ S.card)
#check (CaroTuza.Examples.zero_high_pairs :
  GraphOn CaroTuza.Examples.twoEdges univ ∧ UnitEdges 1 CaroTuza.Examples.twoEdges univ ∧
  (∀ x, degree CaroTuza.Examples.twoEdges univ x=2) ∧ CaroTuza.Examples.twoEdges 0 2=0)
#check (CaroTuza.Examples.zero_high_selection : ∃ S ⊆ (univ : Finset (Fin 4)),
  (∀ x ∈ S, degree CaroTuza.Examples.twoEdges S x < 1) ∧ 2 ≤ S.card)
#check (CaroTuza.Examples.restriction_hypotheses : ∀ {α : Type u} {m : ℕ}
  {w : α → α → ℝ} {V T : Finset α}, GraphOn w V → UnitEdges m w V → T ⊆ V →
  GraphOn w T ∧ UnitEdges m w T ∧ (∀ x ∈ T, degree w T x ≤ degree w V x))
#check (CaroTuza.Examples.calibration_84 : ⌈(84 : ℝ)*f 5 35⌉₊=7 ∧ ¬8 ≤ ⌈(84 : ℝ)*f 5 35⌉₊)
#check (CaroTuza.Examples.selection_84_degree35 : ∀ {α : Type u}
  (w : α → α → ℕ) (V : Finset α),
  (∀ x ∈ V, ∀ y ∈ V, w x y=w y x) → (∀ x ∈ V, w x x=0) →
  V.card=84 → (∀ x ∈ V, ∑ y ∈ V, w x y=35) →
  ∃ S ⊆ V, (∀ x ∈ S, ∑ y ∈ S, w x y < 5) ∧ 7 ≤ S.card)

#guard_standard_axioms CaroTuza.f_low CaroTuza.f_high CaroTuza.f_zero CaroTuza.f_join
  CaroTuza.f_nonneg CaroTuza.f_le_one CaroTuza.f_antitone CaroTuza.decrement
  CaroTuza.decrement_of_le_max CaroTuza.GraphOn.mono CaroTuza.degree_nonneg
  CaroTuza.degree_mono CaroTuza.weight_le_degree CaroTuza.UnitEdges.mono
  CaroTuza.degree_erase CaroTuza.potential_nonneg CaroTuza.potential_le_card
  CaroTuza.potential_erase_le CaroTuza.erase_card_lt CaroTuza.exists_selection_real
  CaroTuza.exists_selection CaroTuza.exists_selection_of_degree_le CaroTuza.exists_selection_in
  CaroTuza.nat_unitEdges CaroTuza.exists_nat_selection AuditCaroTuza.weighted_selection_explicit
  CaroTuza.Examples.empty_selection CaroTuza.Examples.edgeless CaroTuza.Examples.singleton
  CaroTuza.Examples.threshold_one CaroTuza.Examples.join_one CaroTuza.Examples.parallel_edges
  CaroTuza.Examples.fractional_hypotheses CaroTuza.Examples.fractional_selection
  CaroTuza.Examples.zero_high_pairs CaroTuza.Examples.zero_high_selection
  CaroTuza.Examples.restriction_hypotheses CaroTuza.Examples.calibration_84
  CaroTuza.Examples.selection_84_degree35
#print axioms CoveringDesigns.CaroTuza.exists_selection
#print axioms CoveringDesigns.CaroTuza.exists_nat_selection
#print axioms CoveringDesigns.CaroTuza.exists_selection_real
#print axioms CoveringDesigns.CaroTuza.potential_erase_le
#print axioms CoveringDesigns.CaroTuza.exists_selection_of_degree_le
#print axioms CoveringDesigns.CaroTuza.exists_selection_in
#print axioms CoveringDesigns.CaroTuza.f_low
#print axioms CoveringDesigns.CaroTuza.f_high
#print axioms CoveringDesigns.CaroTuza.f_zero
#print axioms CoveringDesigns.CaroTuza.f_join
#print axioms CoveringDesigns.CaroTuza.f_nonneg
#print axioms CoveringDesigns.CaroTuza.f_le_one
#print axioms CoveringDesigns.CaroTuza.f_antitone
#print axioms CoveringDesigns.CaroTuza.decrement
#print axioms CoveringDesigns.CaroTuza.decrement_of_le_max
#print axioms CoveringDesigns.CaroTuza.GraphOn.mono
#print axioms CoveringDesigns.CaroTuza.degree_nonneg
#print axioms CoveringDesigns.CaroTuza.degree_mono
#print axioms CoveringDesigns.CaroTuza.weight_le_degree
#print axioms CoveringDesigns.CaroTuza.UnitEdges.mono
#print axioms CoveringDesigns.CaroTuza.degree_erase
#print axioms CoveringDesigns.CaroTuza.potential_nonneg
#print axioms CoveringDesigns.CaroTuza.potential_le_card
#print axioms CoveringDesigns.CaroTuza.erase_card_lt
#print axioms CoveringDesigns.CaroTuza.nat_unitEdges
#print axioms CoveringDesigns.CaroTuza.Examples.empty_selection
#print axioms CoveringDesigns.CaroTuza.Examples.edgeless
#print axioms CoveringDesigns.CaroTuza.Examples.singleton
#print axioms CoveringDesigns.CaroTuza.Examples.threshold_one
#print axioms CoveringDesigns.CaroTuza.Examples.join_one
#print axioms CoveringDesigns.CaroTuza.Examples.parallel_edges
#print axioms CoveringDesigns.CaroTuza.Examples.fractional_hypotheses
#print axioms CoveringDesigns.CaroTuza.Examples.fractional_selection
#print axioms CoveringDesigns.CaroTuza.Examples.zero_high_pairs
#print axioms CoveringDesigns.CaroTuza.Examples.zero_high_selection
#print axioms CoveringDesigns.CaroTuza.Examples.restriction_hypotheses
#print axioms CoveringDesigns.CaroTuza.Examples.calibration_84
#print axioms CoveringDesigns.CaroTuza.Examples.selection_84_degree35
#print axioms CoveringDesigns.AuditCaroTuza.weighted_selection_explicit
