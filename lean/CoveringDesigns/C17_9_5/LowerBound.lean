import CoveringDesigns.Applications.ZeroDefect
import CoveringDesigns.HorsleySingh.Examples

/-! A structural lower bound of sixty blocks. No construction, exact covering
number, novelty or current world-best status is asserted. The underlying
covering results are due to Schönheim, Horsley and Singh; the partition proof
is the standard finite-potential argument. Formalisation: Rob Gardiner. -/

namespace CoveringDesigns.C17_9_5
open Finset HorsleySingh Applications.ZeroDefect
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The division-free count underlying the lower bound; no prescribed block
count or unproved matrix property is assumed. -/
theorem counting_bound {C : Family α} (hn : Fintype.card α = 17)
    (h : IsCover C 9 5) : (15368 : ℤ) ≤ 260 * C.card := by
  have h₂ (X : Finset α) (hX : X.card = 2) : 15 ≤ multiplicity C X :=
    multiplicity_ge_of_coverLower hn h (by decide) smaller_15_7_3 hX
  have h₃ (X : Finset α) (hX : X.card = 3) : 7 ≤ multiplicity C X :=
    multiplicity_ge_of_coverLower hn h (by decide) smaller_14_6_2 hX
  have h₄ (X : Finset α) (hX : X.card = 4) : 3 ≤ multiplicity C X :=
    multiplicity_ge_of_coverLower hn h (by decide) smaller_13_5_1 hX
  have hr := zero_defect_rank_bound (b₂ := 15) (q := 8) h.1
    (by decide : 3 ≤ 7) h₃ h₄ (by rw [hn]; rfl)
    (by decide) (by decide) (by decide)
  have hc := two_level_count (pairs α) (multiplicity C) (by decide : 2 ≤ 8)
    (fun X hX => h₂ X (mem_pairs.mp hX)) (multiplicity_pair_sum h.1) hr
  norm_num [card_pairs, hn, Nat.choose] at hc
  exact hc

/-- Every ordinary (17,9,5) covering on any finite point type has at least
sixty blocks. -/
theorem lower_bound {C : Family α} (hn : Fintype.card α = 17)
    (h : IsCover C 9 5) : 60 ≤ C.card := by
  have := counting_bound hn h
  omega

end CoveringDesigns.C17_9_5
