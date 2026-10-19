import CoveringDesigns.CaroTuza.Selection
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.FinCases

/-! Boundary and hypothesis calibrations for the standalone selection theorem.
No covering-number application is asserted. Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.CaroTuza.Examples
open Finset
variable {α : Type*}

theorem empty_selection {m : ℕ} (hm : 0 < m) (w : α → α → ℝ) :
    ∃ S ⊆ (∅ : Finset α), (∀ x ∈ S, degree w S x < m) ∧
      ⌈potential m w ∅⌉₊ ≤ S.card := by
  apply exists_selection hm
  · exact ⟨by simp, by simp, by simp⟩
  · simp [UnitEdges]

theorem edgeless {m : ℕ} (hm : 0 < m) (V : Finset α) :
    (∀ x ∈ V, degree (fun _ _ : α => (0 : ℝ)) V x < m) ∧
      ⌈potential m (fun _ _ : α => (0 : ℝ)) V⌉₊ = V.card := by
  constructor
  · intro x _
    simpa [degree] using (show (0 : ℝ) < m by exact_mod_cast hm)
  · simp [potential, degree, f_zero]

theorem singleton [DecidableEq α] {m : ℕ} (hm : 0 < m)
    (w : α → α → ℝ) (x : α) (hx : w x x = 0) :
    degree w {x} x < m ∧ ⌈potential m w {x}⌉₊ = 1 := by
  constructor
  · simpa [degree, hx] using (show (0 : ℝ) < m by exact_mod_cast hm)
  · simp [potential, degree, hx, f_zero]

theorem threshold_one (w : α → α → ℕ) (V : Finset α)
    (hs : ∀ x ∈ V, ∀ y ∈ V, w x y=w y x) (hd : ∀ x ∈ V, w x x=0) :
    ∃ S ⊆ V, (∀ x ∈ S, ∑ y ∈ S, w x y=0) ∧
      ⌈∑ x ∈ V, f 1 ((∑ y ∈ V, w x y : ℕ) : ℝ)⌉₊ ≤ S.card := by
  obtain ⟨S, hS, hi, hn⟩ := exists_nat_selection (by decide : 0 < 1) w V hs hd
  exact ⟨S, hS, fun x hx => Nat.lt_one_iff.mp (hi x hx), hn⟩

theorem join_one : f 1 1 = 1/2 ∧ (1+1 : ℝ)/(2*(1+1)) = 1/2 := by
  norm_num [f]

def parallel (x y : Fin 2) : ℕ := if x=y then 0 else 3

theorem parallel_edges :
    ∃ S ⊆ (univ : Finset (Fin 2)),
      (∀ x ∈ S, ∑ y ∈ S, parallel x y < 2) ∧ 1 ≤ S.card := by
  have hs : ∀ x ∈ (univ : Finset (Fin 2)), ∀ y ∈ univ,
      parallel x y=parallel y x := by
    intros; simp [parallel, eq_comm]
  obtain ⟨S, hS, hi, hn⟩ := exists_nat_selection (by decide : 0 < 2) parallel univ hs
    (by intros; simp [parallel])
  refine ⟨S, hS, hi, ?_⟩
  norm_num [Fin.sum_univ_two, parallel, f] at hn
  have hp : (0 : ℝ) < S.card := by linarith
  exact_mod_cast hp

noncomputable def fractional (x y : Fin 2) : ℝ := if x=y then 0 else 1/2

/-- Small positive weights are allowed at low-degree endpoints. -/
theorem fractional_hypotheses : GraphOn fractional univ ∧ UnitEdges 1 fractional univ ∧
    (∀ x, degree fractional univ x=1/2) ∧ fractional 0 1=1/2 := by
  have hg : GraphOn fractional univ := by
    refine ⟨?_, ?_, ?_⟩
    · intros; simp [fractional, eq_comm]
    · intros; unfold fractional; split_ifs <;> norm_num
    · intros; simp [fractional]
  have hd (x : Fin 2) : degree fractional univ x=1/2 := by
    fin_cases x <;> norm_num [degree, Fin.sum_univ_two, fractional]
  refine ⟨hg, ?_, hd, by norm_num [fractional]⟩
  intro x _ y _ hx _ _
  rw [hd x] at hx
  norm_num at hx

theorem fractional_selection :
    ∃ S ⊆ (univ : Finset (Fin 2)), (∀ x ∈ S, degree fractional S x < 1) ∧
      2 ≤ S.card := by
  obtain ⟨S, hS, hi, hn⟩ := exists_selection (by decide : 0 < 1) fractional univ
    fractional_hypotheses.1 fractional_hypotheses.2.1
  refine ⟨S, hS, by simpa using hi, ?_⟩
  norm_num [potential, fractional_hypotheses.2.2.1, f, Fin.sum_univ_two] at hn
  have hp : (1 : ℝ) < S.card := by linarith
  exact_mod_cast hp

/-- Two disjoint edges of weight two. Cross-component nonedges have weight zero. -/
noncomputable def twoEdges (x y : Fin 4) : ℝ :=
  if x=y then 0 else if x.val/2=y.val/2 then 2 else 0

theorem zero_high_pairs : GraphOn twoEdges univ ∧ UnitEdges 1 twoEdges univ ∧
    (∀ x, degree twoEdges univ x=2) ∧ twoEdges 0 2=0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intros; simp [twoEdges, eq_comm]
    · intros; unfold twoEdges; split_ifs <;> norm_num
    · intros; simp [twoEdges]
  · intro x _ y _ _ _ hp
    unfold twoEdges at *
    split_ifs at * <;> norm_num at *
  · intro x
    fin_cases x <;> norm_num [degree, Fin.sum_univ_succ, twoEdges]
  · norm_num [twoEdges]

theorem zero_high_selection :
    ∃ S ⊆ (univ : Finset (Fin 4)), (∀ x ∈ S, degree twoEdges S x < 1) ∧
      2 ≤ S.card := by
  obtain ⟨S, hS, hi, hn⟩ := exists_selection (by decide : 0 < 1) twoEdges univ
    zero_high_pairs.1 zero_high_pairs.2.1
  refine ⟨S, hS, by simpa using hi, ?_⟩
  norm_num [potential, zero_high_pairs.2.2.1, f, Fin.sum_univ_succ] at hn
  have hp : (1 : ℝ) < S.card := by linarith
  exact_mod_cast hp

theorem restriction_hypotheses {m : ℕ} {w : α → α → ℝ} {V T : Finset α}
    (h : GraphOn w V) (hu : UnitEdges m w V) (hTV : T ⊆ V) :
    GraphOn w T ∧ UnitEdges m w T ∧
      (∀ x ∈ T, degree w T x ≤ degree w V x) :=
  ⟨h.mono hTV, hu.mono h hTV, fun _ hx => degree_mono h hTV (hTV hx)⟩

/-- Exact calibration: this selection estimate is seven, never eight. -/
theorem calibration_84 : ⌈(84 : ℝ)*f 5 35⌉₊ = 7 ∧
    ¬ 8 ≤ ⌈(84 : ℝ)*f 5 35⌉₊ := by norm_num [f]

theorem selection_84_degree35 (w : α → α → ℕ) (V : Finset α)
    (hs : ∀ x ∈ V, ∀ y ∈ V, w x y=w y x) (hd : ∀ x ∈ V, w x x=0)
    (hcard : V.card=84) (hdeg : ∀ x ∈ V, ∑ y ∈ V, w x y=35) :
    ∃ S ⊆ V, (∀ x ∈ S, ∑ y ∈ S, w x y < 5) ∧ 7 ≤ S.card := by
  obtain ⟨S, hS, hi, hn⟩ := exists_nat_selection (by decide : 0 < 5) w V hs hd
  have he : (∑ x ∈ V, f 5 ((∑ y ∈ V, w x y : ℕ) : ℝ)) = 84*f 5 35 := by
    calc
      _ = ∑ _x ∈ V, f 5 35 := sum_congr rfl (fun x hx => by rw [hdeg x hx]; norm_num)
      _ = _ := by simp [hcard]
  rw [he, calibration_84.1] at hn
  exact ⟨S, hS, hi, hn⟩

end CoveringDesigns.CaroTuza.Examples
