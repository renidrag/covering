import CoveringDesigns.SevenBlock.SupportSlack

/-! Complete-pair-shadow boundary arithmetic. The divisibility proof counts
disjoint pair shadows of distinct triples; actual point multiplicities are
retained in the moment identity before taking this image. -/
namespace CoveringDesigns.SevenBlock
open Finset
variable {X I : Type*} [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]

def pairShadow (S : X → Finset I) : Finset (Finset I) :=
  ((univ : Finset I).powersetCard 2).filter fun P => 0 < indexedSubsetDegree S P

private theorem shadow_eq (S : X → Finset I) :
    pairShadow S = (univ.image S).biUnion (fun L => L.powersetCard 2) := by
  ext P
  constructor
  · intro hP
    obtain ⟨hP,hpos⟩ := mem_filter.mp hP
    obtain ⟨x,hx⟩ := card_pos.mp hpos
    exact mem_biUnion.mpr ⟨S x, mem_image.mpr ⟨x,mem_univ _,rfl⟩,
      mem_powersetCard.mpr ⟨(mem_filter.mp hx).2, mem_powersetCard_univ.mp hP⟩⟩
  · intro hP
    obtain ⟨L,hL,hP⟩ := mem_biUnion.mp hP
    obtain ⟨x,_,rfl⟩ := mem_image.mp hL
    obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hP
    exact mem_filter.mpr ⟨mem_powersetCard_univ.mpr hcard,
      card_pos.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,hsub⟩⟩⟩

/-- Zero partial-overlap slack forces the pair shadow size to be divisible
by three. This is a universal finite-set proof, not a family enumeration. -/
theorem zero_partial_shadow_divisible (S : X → Finset I)
    (hs : ∀ x, (S x).card = 3)
    (hm : ∀ x y, x ≠ y → (S x ∩ S y).Nonempty)
    (hz : partialOverlap S 3 = 0) : 3 ∣ (pairShadow S).card := by
  have hn (x y : X) (hxy : x ≠ y) : (S x ∩ S y).card ≠ 2 := by
    intro hc
    have he := partial_overlap_three S hs hm
    rw [hz] at he
    have hzero : (((univ : Finset X).powersetCard 2).filter
      (fun P => (indexedCommon S P).card = 2)).card = 0 := by omega
    have hmem : {x,y} ∈ (((univ : Finset X).powersetCard 2).filter
      (fun P => (indexedCommon S P).card = 2)) :=
      mem_filter.mpr ⟨mem_powersetCard_univ.mpr (card_pair hxy), by
        simpa only [indexedCommon_pair] using hc⟩
    rw [card_eq_zero.mp hzero] at hmem
    exact notMem_empty _ hmem
  have hd : (↑(univ.image S) : Set (Finset I)).PairwiseDisjoint (fun L => L.powersetCard 2) := by
    intro L hL M hM hLM
    obtain ⟨x,_,rfl⟩ := mem_image.mp hL
    obtain ⟨y,_,rfl⟩ := mem_image.mp hM
    apply disjoint_left.mpr
    intro P hP hQ
    have hp := mem_powersetCard.mp hP
    have hq := mem_powersetCard.mp hQ
    have hl : 2 ≤ (S x ∩ S y).card := by
      rw [← hp.2]
      exact card_le_card (subset_inter hp.1 hq.1)
    have hu : (S x ∩ S y).card ≤ 3 := (card_le_card inter_subset_left).trans_eq (hs x)
    have h3 : (S x ∩ S y).card ≠ 3 := by
      intro he
      have hx := eq_of_subset_of_card_le (inter_subset_left (s₁ := S x) (s₂ := S y))
        (by rw [he,hs x])
      have hy := eq_of_subset_of_card_le (inter_subset_right (s₁ := S x) (s₂ := S y))
        (by rw [he,hs y])
      exact hLM (hx.symm.trans hy)
    exact hn x y (fun he => hLM (congrArg S he)) (by omega)
  rw [shadow_eq, card_biUnion hd]
  have he : (∑ L ∈ univ.image S, (L.powersetCard 2).card) = 3 * (univ.image S).card := by
    rw [sum_const_nat]
    · exact Nat.mul_comm _ _
    · intro L hL
      obtain ⟨x,_,rfl⟩ := mem_image.mp hL
      rw [card_powersetCard,hs]
      decide
  rw [he]
  exact dvd_mul_right _ _

/-- The slack-six bound forces full pair shadow when a≥2. At a=2 a missing
pair would leave exactly twenty shadow pairs, contradicting the preceding
divisibility theorem. The quotient identity is retained explicitly. -/
theorem shadow_positive (S : X → Finset I) {a : ℕ} (ha : 2 ≤ a)
    (hi : Fintype.card I = 7) (hs : ∀ x, (S x).card = 3)
    (hm : ∀ x y, x ≠ y → (S x ∩ S y).Nonempty)
    (hdiv : Fintype.card X * Nat.choose 3 2 = (Fintype.card I).choose 2 * a + 6)
    (hbudget : partialOverlap S 3 + 2 * supportImbalance S a 6 ≤ 6)
    (P : Finset I) (hP : P.card = 2) : 0 < indexedSubsetDegree S P := by
  let Q := (univ : Finset I).powersetCard 2
  let c (T : Finset I) : ℤ :=
    ((indexedSubsetDegree S T : ℤ)-a) * ((indexedSubsetDegree S T : ℤ)-a-1)
  have hnon (T : Finset I) : 0 ≤ c T := consecutive_nonneg _
  have heq : 2 * supportImbalance S a 6 = ∑ T ∈ Q, c T :=
    support_imbalance_identity S 3 a 6 hs hdiv
  have hpart := partial_overlap_nonneg S 3 hs hm
  have htotal : (∑ T ∈ Q, c T) ≤ 6 := by omega
  have hmem : P ∈ Q := mem_powersetCard_univ.mpr hP
  have hsingle : c P ≤ ∑ T ∈ Q, c T := single_le_sum (fun T _ => hnon T) hmem
  by_contra hn
  have hz : indexedSubsetDegree S P = 0 := by omega
  have hc : c P = (a : ℤ) * (a+1) := by simp [c,hz]; ring
  have ha2 : a = 2 := by
    have ha' : (2 : ℤ) ≤ a := by omega
    have ha₀ : (0 : ℤ) ≤ a := by omega
    nlinarith
  have hc6 : c P = 6 := by rw [hc,ha2]; norm_num
  have hsum6 : ∑ T ∈ Q, c T = 6 := by omega
  have hp0 : partialOverlap S 3 = 0 := by omega
  have herase : ∑ T ∈ Q.erase P, c T = 0 := by
    have hh := sum_erase_add Q c hmem
    omega
  have hrest (T : Finset I) (hT : T ∈ Q) (hTP : T ≠ P) :
      indexedSubsetDegree S T = 2 ∨ indexedSubsetDegree S T = 3 := by
    have hle := single_le_sum (s := Q.erase P) (f := c)
      (fun T _ => hnon T) (mem_erase.mpr ⟨hTP,hT⟩)
    have hzero : c T = 0 := by have := hnon T; omega
    change ((indexedSubsetDegree S T : ℤ)-a) * ((indexedSubsetDegree S T : ℤ)-a-1) = 0 at hzero
    rw [ha2] at hzero
    rcases mul_eq_zero.mp hzero with hzero | hzero <;> omega
  have hshadow : pairShadow S = Q.erase P := by
    ext T
    constructor
    · intro hT
      have ht := mem_filter.mp hT
      exact mem_erase.mpr ⟨by intro he; subst T; omega, ht.1⟩
    · intro hT
      have ht := mem_erase.mp hT
      have hr := hrest T ht.2 ht.1
      exact mem_filter.mpr ⟨ht.2,by omega⟩
  have hcard : (pairShadow S).card = 20 := by
    rw [hshadow,card_erase_of_mem hmem]
    simp only [Q,card_powersetCard,card_univ,hi]
    decide
  have hd := zero_partial_shadow_divisible S hs hm hp0
  rw [hcard] at hd
  norm_num at hd

#guard_standard_axioms zero_partial_shadow_divisible shadow_positive

end CoveringDesigns.SevenBlock
