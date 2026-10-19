import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! A self-contained finite-potential proof for integer-weighted partitions.
This standard graph argument is associated with Lovász's decomposition
principle; it is not a literal translation of an unobtained original paper.
Formalisation: Rob Gardiner. No covering theorem is imported. -/

namespace CoveringDesigns.WeightedPartition
open Finset
variable {α : Type*} [Fintype α]

/-- Weight from `x` into the labelled part `i`. -/
def classDegree {q : ℕ} (w : α → α → ℤ) (c : α → Fin q) (x : α) (i : Fin q) : ℤ :=
  ∑ y, if c y = i then w x y else 0

/-- Twice the unordered monochromatic edge potential when the diagonal is zero. -/
def potential {q : ℕ} (w : α → α → ℤ) (c : α → Fin q) : ℤ :=
  ∑ x, ∑ y, if c x = c y then w x y else 0

/-- Exact change of potential when a single vertex changes its label. -/
theorem potential_update [DecidableEq α] {q : ℕ} (w : α → α → ℤ)
    (hsym : ∀ x y, w x y = w y x) (hdiag : ∀ x, w x x = 0)
    (c : α → Fin q) (x : α) (i : Fin q) :
    potential w (Function.update c x i) = potential w c +
      2 * (classDegree w c x i - classDegree w c x (c x)) := by
  classical
  let g : α → ℤ := fun y =>
    (if c y = i then w x y else 0) - (if c y = c x then w x y else 0)
  have he (u v : α) :
      (if Function.update c x i u = Function.update c x i v then w u v else 0) =
      (if c u = c v then w u v else 0) +
        (if u = x then g v else 0) + (if v = x then g u else 0) := by
    by_cases hu : u = x <;> by_cases hv : v = x
    · subst u; subst v; simp [hdiag, g]
    · subst u
      simp [hv, g, eq_comm]
    · subst v
      simp [hu, g, hsym u x, eq_comm]
    · simp [hu, hv]
  have hz : (∑ u, ∑ v, if u = x then g v else 0) = ∑ v, g v := by
    rw [sum_comm]
    simp
  unfold potential
  simp_rw [he, sum_add_distrib]
  simp only [sum_ite_eq', mem_univ, ite_true]
  have hg : ∑ y, g y = classDegree w c x i - classDegree w c x (c x) := by
    simp [g, classDegree, sum_sub_distrib]
  rw [hz, hg]
  ring

/-- A minimum-potential partition satisfies the vertexwise balance inequality.
It even holds for signed weights. Nonnegativity is needed later for isolating
zero-sum rows, not for this finite minimisation. Empty types and parts are allowed. -/
theorem exists_balanced_partition {q : ℕ} (hq : 0 < q) (w : α → α → ℤ)
    (hsym : ∀ x y, w x y = w y x) (hdiag : ∀ x, w x x = 0) :
    ∃ c : α → Fin q, ∀ x,
      (q : ℤ) * classDegree w c x (c x) ≤ ∑ y, w x y := by
  classical
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨c, hc⟩ := Finite.exists_min (potential (α := α) w : (α → Fin q) → ℤ)
  refine ⟨c, fun x => ?_⟩
  have hmove (i : Fin q) : classDegree w c x (c x) ≤ classDegree w c x i := by
    have hm := hc (Function.update c x i)
    rw [potential_update w hsym hdiag] at hm
    omega
  have hs := sum_le_sum (s := (univ : Finset (Fin q))) (fun i _ => hmove i)
  have ht : ∑ i : Fin q, classDegree w c x i = ∑ y, w x y := by
    unfold classDegree
    rw [sum_comm]
    simp
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ht] using hs

/-- Pigeonhole for labelled parts, including the empty vertex set.
The second inequality is the exact natural ceiling, without a covering import. -/
theorem exists_large_part {q : ℕ} (hq : 0 < q) (c : α → Fin q) :
    ∃ i : Fin q, Fintype.card α ≤ q * (univ.filter (fun x => c x = i)).card ∧
      (Fintype.card α + q - 1) / q ≤ (univ.filter (fun x => c x = i)).card := by
  classical
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun i : Fin q => (univ.filter (fun x => c x = i)).card)
  have ht : ∑ i : Fin q, (univ.filter (fun x => c x = i)).card = Fintype.card α := by
    simp_rw [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    simp
  have hs := sum_le_sum (s := (univ : Finset (Fin q))) (fun j _ => hi j)
  have hb : Fintype.card α ≤ q * (univ.filter (fun x => c x = i)).card := by
    simpa only [ht, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id] using hs
  refine ⟨i, hb, ?_⟩
  rw [Nat.div_le_iff_le_mul_add_pred hq]
  omega

/-- A degree bound gives a partition with internal degrees at most its floor
quotient, and a part with at least the ceiling quotient of the vertex count. -/
theorem exists_bounded_partition {q : ℕ} (hq : 0 < q) (w : α → α → ℤ)
    (hsym : ∀ x y, w x y = w y x) (hdiag : ∀ x, w x x = 0)
    (D : ℤ) (hdegree : ∀ x, ∑ y, w x y ≤ D) :
    ∃ c : α → Fin q,
      (∀ x, classDegree w c x (c x) ≤ D / (q : ℤ)) ∧
      ∃ i : Fin q, Fintype.card α ≤ q * (univ.filter (fun x => c x = i)).card ∧
        (Fintype.card α + q - 1) / q ≤ (univ.filter (fun x => c x = i)).card := by
  classical
  obtain ⟨c, hc⟩ := exists_balanced_partition hq w hsym hdiag
  refine ⟨c, ?_, exists_large_part hq c⟩
  intro x
  apply (Int.le_ediv_iff_mul_le (by exact_mod_cast hq)).mpr
  simpa [mul_comm] using (hc x).trans (hdegree x)

/-- Finset interface for selecting a large part of an induced weighted graph.
The ambient type need not be finite. -/
theorem exists_large_subset {β : Type*} [DecidableEq β] (V : Finset β)
    {q : ℕ} (hq : 0 < q) (w : β → β → ℤ)
    (hsym : ∀ x ∈ V, ∀ y ∈ V, w x y = w y x)
    (hdiag : ∀ x ∈ V, w x x = 0)
    (D : ℤ) (hdegree : ∀ x ∈ V, ∑ y ∈ V, w x y ≤ D) :
    ∃ T ⊆ V, V.card ≤ q*T.card ∧
      (∀ x ∈ T, ∑ y ∈ T, w x y ≤ D / (q : ℤ)) := by
  classical
  let w' : V → V → ℤ := fun x y => w x.val y.val
  have hd (x : V) : ∑ y : V, w' x y ≤ D := by
    simpa only [w', sum_coe_sort] using hdegree x.val x.property
  obtain ⟨c, hc, i, hi, _⟩ := exists_bounded_partition hq w'
    (fun x y => hsym x.val x.property y.val y.property)
    (fun x => hdiag x.val x.property) D hd
  let U := (univ : Finset V).filter (fun x => c x = i)
  let T := U.image Subtype.val
  have hcard : T.card = U.card := card_image_of_injective _ Subtype.val_injective
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := mem_image.mp hx
    exact y.property
  · rw [hcard]
    simpa only [Fintype.card_coe] using hi
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    have he : c y = i := (mem_filter.mp hy).2
    have hs : ∑ z ∈ T, w y.val z = classDegree w' c y i := by
      rw [show T = U.image Subtype.val from rfl,
        sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
      simp only [U, sum_filter, classDegree, w']
    rw [hs, ← he]
    exact hc y

end CoveringDesigns.WeightedPartition
