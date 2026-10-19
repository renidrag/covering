import CoveringDesigns.CaroTuza.Function
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Finite symmetric weights, restriction, and the potential inequality for
deleting any maximum-degree vertex. No graph or covering enumeration is used.
The argument follows Horsley's Lemma 7. Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.CaroTuza
open Finset
variable {α : Type*}

/-- Degree induced by V, including zero entries (nonedges). -/
noncomputable def degree (w : α → α → ℝ) (V : Finset α) (x : α) : ℝ :=
  ∑ y ∈ V, w x y

/-- Local hypotheses for a finite loopless weighted graph. -/
structure GraphOn (w : α → α → ℝ) (V : Finset α) : Prop where
  symm : ∀ x ∈ V, ∀ y ∈ V, w x y = w y x
  nonneg : ∀ x ∈ V, ∀ y ∈ V, 0 ≤ w x y
  loopless : ∀ x ∈ V, w x x = 0

/-- Horsley's integrality substitute: only positive high-high weights are
required to be at least one. Zero weights remain allowed. -/
def UnitEdges (m : ℕ) (w : α → α → ℝ) (V : Finset α) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, (m : ℝ) ≤ degree w V x →
    (m : ℝ) ≤ degree w V y → 0 < w x y → 1 ≤ w x y

/-- Caro–Tuza potential of an induced weighted graph. -/
noncomputable def potential (m : ℕ) (w : α → α → ℝ) (V : Finset α) : ℝ :=
  ∑ x ∈ V, f m (degree w V x)

theorem GraphOn.mono {w : α → α → ℝ} {V T : Finset α}
    (h : GraphOn w V) (hTV : T ⊆ V) : GraphOn w T :=
  ⟨fun x hx y hy => h.symm x (hTV hx) y (hTV hy),
   fun x hx y hy => h.nonneg x (hTV hx) y (hTV hy),
   fun x hx => h.loopless x (hTV hx)⟩

theorem degree_nonneg {w : α → α → ℝ} {V : Finset α}
    (h : GraphOn w V) {x : α} (hx : x ∈ V) : 0 ≤ degree w V x :=
  sum_nonneg (fun y hy => h.nonneg x hx y hy)

theorem degree_mono {w : α → α → ℝ} {V T : Finset α}
    (h : GraphOn w V) (hTV : T ⊆ V) {x : α} (hx : x ∈ V) :
    degree w T x ≤ degree w V x := by
  exact sum_le_sum_of_subset_of_nonneg hTV (fun y hy _ => h.nonneg x hx y hy)

theorem weight_le_degree {w : α → α → ℝ} {V : Finset α}
    (h : GraphOn w V) {x y : α} (hx : x ∈ V) (hy : y ∈ V) :
    w x y ≤ degree w V x :=
  single_le_sum (fun z hz => h.nonneg x hx z hz) hy

theorem UnitEdges.mono {m : ℕ} {w : α → α → ℝ} {V T : Finset α}
    (hu : UnitEdges m w V) (h : GraphOn w V) (hTV : T ⊆ V) :
    UnitEdges m w T := by
  intro x hx y hy hdx hdy hpos
  exact hu x (hTV hx) y (hTV hy)
    (hdx.trans (degree_mono h hTV (hTV hx)))
    (hdy.trans (degree_mono h hTV (hTV hy))) hpos

theorem degree_erase [DecidableEq α] (w : α → α → ℝ) {V : Finset α}
    {z : α} (hz : z ∈ V) (x : α) :
    degree w (V.erase z) x = degree w V x-w x z := by
  have := sum_erase_add V (fun y => w x y) hz
  unfold degree
  linarith

theorem potential_nonneg {m : ℕ} (hm : 0 < m) {w : α → α → ℝ}
    {V : Finset α} (h : GraphOn w V) : 0 ≤ potential m w V :=
  sum_nonneg (fun x hx => f_nonneg hm (degree_nonneg h hx))

theorem potential_le_card {m : ℕ} (hm : 0 < m) {w : α → α → ℝ}
    {V : Finset α} (h : GraphOn w V) : potential m w V ≤ V.card := by
  calc
    potential m w V ≤ ∑ _x ∈ V, (1 : ℝ) :=
      sum_le_sum (fun x hx => f_le_one hm (degree_nonneg h hx))
    _ = V.card := by simp

/-- Main deletion milestone: deleting any maximum-degree vertex whose degree
is at least m does not decrease the potential. Zero-weight pairs are covered
by the scalar lemma before its positive-edge case invokes UnitEdges. -/
theorem potential_erase_le [DecidableEq α] {m : ℕ} (hm : 0 < m)
    {w : α → α → ℝ} {V : Finset α} (h : GraphOn w V)
    (hu : UnitEdges m w V) {z : α} (hz : z ∈ V)
    (hzmax : ∀ x ∈ V, degree w V x ≤ degree w V z)
    (hzlarge : (m : ℝ) ≤ degree w V z) :
    potential m w V ≤ potential m w (V.erase z) := by
  let D := degree w V z
  let c := ((m : ℝ)+1)/(2*D*(D+1))
  have hD : 0 < D := lt_of_lt_of_le (by exact_mod_cast hm) hzlarge
  have hs : ∑ x ∈ V.erase z, w x z*c ≤
      ∑ x ∈ V.erase z, (f m (degree w (V.erase z) x)-f m (degree w V x)) := by
    apply sum_le_sum
    intro x hx
    have hxV := mem_of_mem_erase hx
    rw [degree_erase w hz x]
    exact decrement_of_le_max hm hzlarge (degree_nonneg h hxV) (hzmax x hxV)
      (h.nonneg x hxV z hz) (weight_le_degree h hxV hz)
      (fun hxlarge hpos => hu x hxV z hz hxlarge hzlarge hpos)
  have hw : ∑ x ∈ V.erase z, w x z = D := by
    calc
      _ = ∑ x ∈ V.erase z, w z x :=
        sum_congr rfl (fun x hx => h.symm x (mem_of_mem_erase hx) z hz)
      _ = D := by
        have he := sum_erase_add V (fun x => w z x) hz
        simpa only [h.loopless z hz, add_zero, D, degree] using he
  have hc : D*c = f m D := by
    rw [f_high hm hzlarge]
    change D*c = ((m : ℝ)+1)/(2*(D+1))
    dsimp [c]
    field_simp
  rw [← sum_mul, hw, hc, sum_sub_distrib] at hs
  have he := sum_erase_add V (fun x => f m (degree w V x)) hz
  unfold potential
  dsimp [D] at hs
  linarith

end CoveringDesigns.CaroTuza
