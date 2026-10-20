import CoveringDesigns.SaturatedMatching.Pattern

/-! Five mutually separating saturated pairs force two distinct
cross-pairs of multiplicity four. No uniformity or point count is assumed.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset
variable {α ι M : Type*} [Fintype α] [Fintype ι] [Fintype M]
  [DecidableEq α] [DecidableEq ι] [DecidableEq M]
variable {B : ι → Finset α} (P : Pattern (M := M) B)

/-- For any two matching edges, the minority correlation among the other
three yields two complementary endpoint combinations of multiplicity four.
They are separated by the minority edge's actual supporting blocks. -/
theorem five_pair_excess (hM : Fintype.card M = 5)
    (hdeg : ∀ f b, indexedDegree B (P.point (f,b)) = 6)
    (hpair : ∀ f g, f ≠ g → ∀ b c,
      3 ≤ indexedSubsetDegree B {P.point (f,b),P.point (g,c)})
    (f g : M) (hfg : f ≠ g) :
    ∃ e, e ≠ f ∧ e ≠ g ∧ ∃ b c : Bool,
      indexedSubsetDegree B {P.point (f,b),P.point (g,c)} = 4 ∧
      indexedSubsetDegree B {P.point (f,!b),P.point (g,!c)} = 4 ∧
      (∀ a, (P.point (f,b) ∈ B (P.block (e,a)) ↔
        P.point (g,c) ∉ B (P.block (e,a)))) ∧
      (∀ a, (P.point (f,!b) ∈ B (P.block (e,a)) ↔
        P.point (g,!c) ∉ B (P.block (e,a)))) := by
  classical
  let T : Finset M := univ \ {f,g}
  let U := T.filter (fun e => P.sign e f = P.sign e g)
  let W := T.filter (fun e => P.sign e f ≠ P.sign e g)
  have hT : T.card = 3 := by
    dsimp only [T]
    rw [card_sdiff_of_subset (subset_univ _),card_univ,hM,card_pair hfg]
  have hUW : U.card+W.card=3 := by
    have hh := card_filter_add_card_filter_not (s := T) (p := fun e => P.sign e f = P.sign e g)
    change U.card+W.card=T.card at hh
    rwa [hT] at hh
  have hs (b : Bool) :
      indexedSubsetDegree B {P.point (f,b),P.point (g,b)} = 2+U.card := by
    rw [P.five_pair_multiplicity hM hdeg f g b b hfg]
    congr 1
    change (∑ e ∈ T, if (b == P.sign e f) = (b == P.sign e g) then 1 else 0) = U.card
    simp only [U,card_eq_sum_ones,sum_filter]
    apply sum_congr rfl
    intro e _
    cases hf : P.sign e f <;> cases hg : P.sign e g <;> cases b <;> simp [hf,hg]
  have hd (b : Bool) :
      indexedSubsetDegree B {P.point (f,b),P.point (g,!b)} = 2+W.card := by
    rw [P.five_pair_multiplicity hM hdeg f g b (!b) hfg]
    congr 1
    change (∑ e ∈ T, if (b == P.sign e f) = ((!b) == P.sign e g) then 1 else 0) = W.card
    simp only [W,card_eq_sum_ones,sum_filter]
    apply sum_congr rfl
    intro e _
    cases hf : P.sign e f <;> cases hg : P.sign e g <;> cases b <;> simp [hf,hg]
  have hU : 1 ≤ U.card := by
    have hh := hpair f g hfg false false
    rw [hs] at hh
    omega
  have hW : 1 ≤ W.card := by
    have hh := hpair f g hfg false true
    have he := hd false
    simp only [Bool.not_false] at he
    omega
  have hcases : (U.card=2 ∧ W.card=1) ∨ (U.card=1 ∧ W.card=2) := by omega
  rcases hcases with ⟨hU2,hW1⟩ | ⟨hU1,hW2⟩
  · obtain ⟨e,he⟩ := card_pos.mp (show 0 < W.card by omega)
    obtain ⟨heT,heW⟩ := mem_filter.mp he
    have hef : e ≠ f := by
      intro h; exact (mem_sdiff.mp heT).2 (by simp [h])
    have heg : e ≠ g := by
      intro h; exact (mem_sdiff.mp heT).2 (by simp [h])
    refine ⟨e,hef,heg,false,false,?_,?_,?_,?_⟩
    · rw [hs,hU2]
    · simpa only [Bool.not_false,hU2] using hs true
    · intro a
      simp only [P.matched,hef,heg,false_or]
      cases hf : P.sign e f <;> cases hg : P.sign e g <;>
        cases a <;> simp_all
    · intro a
      simp only [P.matched,hef,heg,false_or,Bool.not_false]
      cases hf : P.sign e f <;> cases hg : P.sign e g <;>
        cases a <;> simp_all
  · obtain ⟨e,he⟩ := card_pos.mp (show 0 < U.card by omega)
    obtain ⟨heT,heU⟩ := mem_filter.mp he
    have hef : e ≠ f := by
      intro h; exact (mem_sdiff.mp heT).2 (by simp [h])
    have heg : e ≠ g := by
      intro h; exact (mem_sdiff.mp heT).2 (by simp [h])
    refine ⟨e,hef,heg,false,true,?_,?_,?_,?_⟩
    · simpa only [Bool.not_false,hW2] using hd false
    · simpa only [Bool.not_false,Bool.not_true,hW2] using hd true
    · intro a
      simp only [P.matched,hef,heg,false_or]
      cases hf : P.sign e f <;> cases hg : P.sign e g <;>
        cases a <;> simp_all
    · intro a
      simp only [P.matched,hef,heg,false_or,Bool.not_false,Bool.not_true]
      cases hf : P.sign e f <;> cases hg : P.sign e g <;>
        cases a <;> simp_all

end CoveringDesigns.SaturatedMatching
