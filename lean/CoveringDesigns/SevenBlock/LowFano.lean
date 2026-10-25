import CoveringDesigns.SevenBlock.LowShadow
import CoveringDesigns.SevenBlock.ShadowGeometry

/-! Recovering the common Fano plane of the actual low-support fibres. -/
namespace CoveringDesigns.SevenBlock
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- Every low support, with its actual point multiplicity still available,
belongs to one common Fano plane; all seven lines occur. -/
theorem low_support_fano {a : ℕ} (ha : 2 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1)
    (hi : Fintype.card I = 7) (p q : V) (hpq : p ≠ q)
    (hp : indexedDegree B p = 4) (hq : indexedDegree B q = 4)
    (hr : ∀ x, x ≠ p → x ≠ q → indexedDegree B x = 3) :
    ∃ e : I ≃ Fin 7,
      relabel e (univ.image (remainingSupports B {p,q})) = univ.image line := by
  let S := remainingSupports B {p,q}
  have hs : ∀ x, (S x).card = 3 := by
    intro x
    exact hr x.val (fun he => x.property (by simp [he]))
      (fun he => x.property (by simp [he]))
  have hc : ∀ T ∈ univ.image S, T.card = 3 := by
    intro T hT
    obtain ⟨x,_,rfl⟩ := mem_image.mp hT
    exact hs x
  have hm : ∀ U ∈ univ.image S, ∀ W ∈ univ.image S, (U ∩ W).Nonempty := by
    intro U hU W hW
    obtain ⟨x,_,rfl⟩ := mem_image.mp hU
    obtain ⟨y,_,rfl⟩ := mem_image.mp hW
    by_cases hxy : x = y
    · subst y
      rw [inter_self]
      exact card_pos.mp (by rw [hs]; decide)
    · exact pointSupports_meet h x.val y.val (fun he => hxy (Subtype.ext he))
  have hshadow : ∀ i j : I, i ≠ j → ∃ T ∈ univ.image S, i ∈ T ∧ j ∈ T := by
    intro i j hij
    have hpos := low_support_shadow ha hv h hi p q hpq hp hq hr {i,j} (card_pair hij)
    obtain ⟨x,hx⟩ := card_pos.mp hpos
    refine ⟨S x,mem_image.mpr ⟨x,mem_univ _,rfl⟩,?_,?_⟩
    · exact (mem_filter.mp hx).2 (by simp)
    · exact (mem_filter.mp hx).2 (by simp)
  rcases complete_pair_shadow hi (univ.image S) hc hm hshadow with ⟨c,hstar⟩ | hfano
  · have hsub : univ \ ({p,q} : Finset V) ⊆ B c := by
      intro x hx
      let y : {x : V // x ∉ ({p,q} : Finset V)} := ⟨x,(mem_sdiff.mp hx).2⟩
      have hmS : S y ∈ univ.image S := mem_image.mpr ⟨y,mem_univ _,rfl⟩
      simpa only [S,remainingSupports,mem_pointSupport,y] using ((hstar (S y)).mp hmS).2
    have hcap := card_le_card hsub
    rw [card_sdiff_of_subset (subset_univ _),card_univ,card_pair hpq,hv,h.1 c] at hcap
    omega
  · exact hfano

/-- The low Fano supports have no partial two-position overlaps, even when
different actual points have the same support. -/
theorem fano_partial_overlap_zero {X : Type*} [Fintype X] [DecidableEq X]
    (S : X → Finset I) (e : I ≃ Fin 7)
    (he : relabel e (univ.image S) = univ.image line) : partialOverlap S 3 = 0 := by
  have hline (x : X) : ∃ l, (S x).map e.toEmbedding = line l := by
    have hx := (mem_relabel e (univ.image S) (S x)).mpr (mem_image.mpr ⟨x,mem_univ _,rfl⟩)
    rw [he] at hx
    obtain ⟨l,_,hl⟩ := mem_image.mp hx
    exact ⟨l,hl.symm⟩
  unfold partialOverlap
  apply sum_eq_zero
  intro P hP
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp (mem_powersetCard_univ.mp hP)
  rw [indexedCommon_pair]
  obtain ⟨l,hl⟩ := hline x
  obtain ⟨m,hm⟩ := hline y
  have heq : (S x ∩ S y).card = (line l ∩ line m).card := by
    rw [← hl,← hm,← map_inter,card_map]
  by_cases hne : l = m
  · simp [heq,hne,line_card]
  · simp [heq,line_inter_card l m hne]

/-- The exceptional pair has precisely one of the two advertised codegrees.
The parity exclusion uses the exact signed slack, not a rounded inequality. -/
theorem exceptional_codegree_dichotomy {a : ℕ} (ha : 2 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1)
    (hi : Fintype.card I = 7) (p q : V) (hpq : p ≠ q)
    (hp : indexedDegree B p = 4) (hq : indexedDegree B q = 4)
    (hr : ∀ x, x ≠ p → x ≠ q → indexedDegree B x = 3) :
    indexedSubsetDegree B {p,q} = 2 ∨ indexedSubsetDegree B {p,q} = 4 := by
  let S := remainingSupports B {p,q}
  obtain ⟨e,he⟩ := low_support_fano ha hv h hi p q hpq hp hq hr
  have hz := fano_partial_overlap_zero S e he
  have hs : ∀ x, (S x).card = 3 := by
    intro x
    exact hr x.val (fun he => x.property (by simp [he]))
      (fun he => x.property (by simp [he]))
  have hc : Fintype.card {x : V // x ∉ ({p,q} : Finset V)} = 7*a+2 := by
    rw [Multicover.subset_complement_card,card_pair hpq,hv]
    omega
  have hdiv : Fintype.card {x : V // x ∉ ({p,q} : Finset V)} * Nat.choose 3 2 =
      (Fintype.card I).choose 2 * a + 6 := by
    rw [hc,hi]
    norm_num [show Nat.choose 7 2 = 21 by decide,show Nat.choose 3 2 = 3 by decide]
    omega
  have hn := support_imbalance_nonneg S 3 a 6 hs hdiv
  have heq := covering_slack hv h.1 hi p q hpq hp hq
  change partialOverlap S 3 + 2 * supportImbalance S a 6 = _ at heq
  rw [hz] at heq
  have hu : indexedSubsetDegree B {p,q} ≤ 4 := by
    rw [← pointSupport_pair]
    exact (card_le_card inter_subset_left).trans_eq hp
  omega

#guard_standard_axioms low_support_fano fano_partial_overlap_zero exceptional_codegree_dichotomy

end CoveringDesigns.SevenBlock
