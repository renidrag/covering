import CoveringDesigns.TwoKMinusC.LargeDefect
import CoveringDesigns.TwoKMinusC.OffsetTwoArithmetic
import CoveringDesigns.TwoKMinusTwo.Bounds
import CoveringDesigns.TwoKMinusTwo.Construction

/-! New compositions with unchanged point/pair floors, saturation exclusions
and arbitrary-label affine attainment. Formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.TwoKMinusC.OffsetTwo
variable {α : Type*} [Fintype α] {k : ℕ}

theorem thirteen_le_card {C : Family α}
    (hv : Fintype.card α=2*k-2) (hk : 18≤k) (hC : IsCover C k 3) :
    13 ≤ C.card := by
  classical
  by_contra hn
  have hb : C.card≤12 := by omega
  have hp (p q : α) (hpq : p≠q) : 3≤degree (star C p) q := by
    have htwo := TwoKMinusTwo.pair_ge_two hv (by omega) hC hpq
    have hne := TwoKMinusTwo.no_saturation_twelve hv (by omega) hC hb hpq
    omega
  have hr := actual_floors_real (c := 2) (by omega : Fintype.card α+2=2*k)
    (by norm_num) (by omega) (by omega) hC.1
    (TwoKMinusTwo.degree_ge_six hv (by omega) hC) hp
  have hstrict := twelve_lt_Q_two hk
  have hbR : (C.card : ℝ)≤12 := by exact_mod_cast hb
  linarith

theorem fourteen_le_card {C : Family α}
    (hv : Fintype.card α=2*k-2) (hk : 36≤k) (hC : IsCover C k 3) :
    14 ≤ C.card := by
  classical
  by_contra hn
  have hb : C.card≤13 := by omega
  have hp (p q : α) (hpq : p≠q) : 3≤degree (star C p) q := by
    have htwo := TwoKMinusTwo.pair_ge_two hv (by omega) hC hpq
    have hne := TwoKMinusTwo.no_saturation_thirteen hv (by omega) hC hb hpq
    omega
  have hr := actual_floors_real (c := 2) (by omega : Fintype.card α+2=2*k)
    (by norm_num) (by omega) (by omega) hC.1
    (TwoKMinusTwo.degree_ge_six hv (by omega) hC) hp
  have hstrict := thirteen_lt_Q_two hk
  have hbR : (C.card : ℝ)≤13 := by exact_mod_cast hb
  linarith

theorem exactness (hv : Fintype.card α=2*k-2) (hk : 36≤k) :
    (∃ C : Family α, IsCover C k 3 ∧ C.card=14) ∧
    (∀ C : Family α, IsCover C k 3 → 14≤C.card) := by
  obtain ⟨C,hC,hcard⟩ := TwoKMinusTwo.upper_bound hv (by omega : 3≤k)
  exact ⟨⟨C,hC,Nat.le_antisymm hcard (fourteen_le_card hv hk hC)⟩,
    fun _ h => fourteen_le_card hv hk h⟩

theorem covering_number (hk : 36≤k) :
    (∃ C : Family (Fin (2*k-2)), IsCover C k 3 ∧ C.card=14) ∧
    (∀ C : Family (Fin (2*k-2)), IsCover C k 3 → 14≤C.card) :=
  exactness (by simp) hk

theorem interval_34_18_3_on (hv : Fintype.card α=34) :
    (∃ C : Family α, IsCover C 18 3 ∧ C.card≤14) ∧
    (∀ C : Family α, IsCover C 18 3 → 13≤C.card) :=
  ⟨TwoKMinusTwo.upper_bound (by omega : Fintype.card α=2*18-2) (by norm_num),
    fun _ h => thirteen_le_card (by omega) (by norm_num) h⟩

theorem exactness_70_36_3_on (hv : Fintype.card α=70) :
    (∃ C : Family α, IsCover C 36 3 ∧ C.card=14) ∧
    (∀ C : Family α, IsCover C 36 3 → 14≤C.card) :=
  exactness (by omega) (by norm_num)

end CoveringDesigns.TwoKMinusC.OffsetTwo
