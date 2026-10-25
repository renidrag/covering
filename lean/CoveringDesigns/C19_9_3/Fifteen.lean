import CoveringDesigns.C19_9_3.Incidence
import CoveringDesigns.MulticoverIncidence.LowerBound
import CoveringDesigns.Multicover.Family

/-! Independent lower sixteen. The existing selected-row Gram theorem has
diagonal coefficient four and excess row sum two in this application.
This module has no seven-block-classification dependency. -/
namespace CoveringDesigns.C19_9_3
open Finset
universe u v
variable {V : Type u} {I : Type v} [Fintype V] [DecidableEq V] [Fintype I]

private def floorSequence (i : ℕ) : ℕ := if i = 1 then 7 else 3

/-- The selected minimum incidence rows satisfy strict diagonal dominance:
defect two is less than the diagonal coefficient four. The reusable rank
theorem then gives 19·8≤10·|I|, hence at least sixteen occurrences. -/
theorem sixteen_le_card {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) : 16 ≤ Fintype.card I := by
  have hb (T : Finset V) (hl : 1 ≤ T.card) (hu : T.card ≤ 2*1) :
      floorSequence T.card ≤ indexedSubsetDegree B T := by
    have ht : T.card = 1 ∨ T.card = 2 := by omega
    rcases ht with ht | ht
    · obtain ⟨x, rfl⟩ := card_eq_one.mp ht
      simpa [floorSequence, Multicover.subsetDegree_singleton] using degree_floor hv h x
    · simpa [floorSequence, ht] using pair_floor hv h ht
  have ha : ∀ j < 1, 0 ≤ HigherIncidence.coefficient 1 floorSequence j := by
    intro j hj
    have : j = 0 := by omega
    subst j
    decide +kernel
  have hd : HigherIncidence.defect (Fintype.card V) 9 1 floorSequence <
      HigherIncidence.coefficient 1 floorSequence 1 := by
    rw [hv]
    decide +kernel
  have hh := MulticoverIncidence.lower_bound_inequality_of_multiplicities h.1 ha hb hd
  norm_num [hv, floorSequence] at hh
  omega

theorem ordinary_sixteen_le_card {C : Family V} (hv : Fintype.card V = 19)
    (h : IsCover C 9 3) : 16 ≤ C.card := by
  simpa only [Multicover.ofFamily_card] using
    sixteen_le_card hv ((Multicover.ofFamily_isCover_one C 9 3).mpr h)

theorem no_fifteen {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 15) : False := by
  have := sixteen_le_card hv h
  omega

/-- At sixteen occurrences, repeated block images would deduplicate to a
cover below the independent lower sixteen. No classification is used. -/
theorem sixteen_blocks_injective {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16) : Function.Injective B := by
  classical
  have hlo := ordinary_sixteen_le_card hv ((Multicover.deduplicate_isCover_one B 9 3).mpr h)
  have hhi := Multicover.deduplicate_card_le B
  have hc : (univ.image B).card = (univ : Finset I).card := by
    change (Multicover.deduplicate B).card = Fintype.card I
    omega
  have he := card_image_iff.mp hc
  exact fun i j hij => he (mem_univ i) (mem_univ j) hij

#guard_standard_axioms sixteen_le_card ordinary_sixteen_le_card no_fifteen sixteen_blocks_injective

end CoveringDesigns.C19_9_3
