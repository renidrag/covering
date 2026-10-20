import CoveringDesigns.SaturatedMatching.Endpoints

/-! Global matching and separation precede coordinate injectivity.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset C20_11_3 TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {C : Family α} {p q : α}

/-- Every saturated endpoint has only its own mate, globally. -/
theorem saturated_matching (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13)
    (hpq : p ≠ q) (hs : degree (star C p) q = 2) :
    ∀ z, z ≠ q → degree (star C q) z = 2 → z = p := by
  obtain ⟨s⟩ := Split.exists_of_saturated (k := 31) (by simpa using hv) (by omega) hC hpq hs
  intro z hz hsat
  by_contra hzp
  exact s.no_second_partner (by simpa using hv) (Or.inl rfl) hC hb z hzp hz hsat

namespace Split
variable (s : Split C p q 31)
include s

theorem loss_le_five (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) : s.loss ≤ 5 := by
  obtain ⟨_,hP,hQ,_,_,hc⟩ := s.surviving_counts (by simpa using hv) (Or.inl rfl) hC hb
  have he := s.exact_budget (by simpa using hv) (by omega) hC
  have hp := s.parts
  rw [hb,hP,hQ] at hp
  rw [hP,hQ] at he
  norm_num [capacity] at he
  omega

/-- A second saturated pair cannot be wholly in one residual side. -/
theorem no_internal_left (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) {x y : α}
    (hx : x ∈ s.X) (hy : y ∈ s.X) (hxy : x ≠ y) :
    degree (star C x) y ≠ 2 := by
  intro hsat
  obtain ⟨E,hEC,_,hu,hi⟩ := SaturatedMatching.saturated_partner_of_mem
    (k := 31) (by simpa using hv) (by omega) hC hxy hsat s.left_mem
    (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1
  have hE : E = s.Y ∪ {x,y} := by
    rw [other_block_eq_complement hu hi,
      saturated_residual_complement s.union_eq s.inter_eq]
    rfl
  have hxp : x ≠ p := by intro he; subst x; exact (mem_sdiff.mp hx).2 (by simp)
  have hxq : x ≠ q := by intro he; subst x; exact (mem_sdiff.mp hx).2 (by simp)
  have hyp : y ≠ p := by intro he; subst y; exact (mem_sdiff.mp hy).2 (by simp)
  have hyq : y ≠ q := by intro he; subst y; exact (mem_sdiff.mp hy).2 (by simp)
  have hEN : E ∈ s.N := by
    apply mem_neitherBlocks.mpr
    refine ⟨hEC,?_,?_⟩
    · rw [hE]; simp [Y,hxp.symm,hyp.symm]
    · rw [hE]; simp [Y,hxq.symm,hyq.symm]
  have hleft : s.X ∩ E = {x,y} := by
    rw [hE,inter_union_distrib_left,disjoint_iff_inter_eq_empty.mp s.geometry.1]
    simp only [empty_union]
    exact inter_eq_right.mpr (by simp [insert_subset_iff,hx,hy])
  have hright : s.Y ∩ E = s.Y := by
    rw [hE]
    exact inter_eq_left.mpr subset_union_left
  have hw : s.weight E = 58 := by
    rw [weight,hleft,hright,card_pair hxy,s.geometry.2.2.1]
  have hl := s.loss_at hC hEC
  rw [s.cap_N hEN,hw] at hl
  norm_num [capacity] at hl
  have hh := s.loss_le_five hv hC hb
  omega

/-- Exchange the two supporting occurrences without changing endpoints. -/
def reverse : Split C p q 31 where
  left := s.right
  right := s.left
  distinct := s.distinct.symm
  left_mem := s.right_mem
  right_mem := s.left_mem
  left_card := s.right_card
  right_card := s.left_card
  endpoints := s.endpoints
  star_eq := by simpa [pair_comm] using s.star_eq
  union_eq := by simpa [union_comm] using s.union_eq
  inter_eq := by simpa [inter_comm] using s.inter_eq

/-- Every other saturated pair crosses the actual residual partition. -/
theorem separates (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) {x y : α}
    (hx : x ≠ p ∧ x ≠ q) (hy : y ≠ p ∧ y ≠ q)
    (hxy : x ≠ y) (hsat : degree (star C x) y = 2) :
    (x ∈ s.X ∧ y ∈ s.Y) ∨ (x ∈ s.Y ∧ y ∈ s.X) := by
  have hxU : x ∈ s.X ∪ s.Y := by rw [s.geometry.2.2.2]; simp [hx]
  have hyU : y ∈ s.X ∪ s.Y := by rw [s.geometry.2.2.2]; simp [hy]
  rcases mem_union.mp hxU with hxX | hxY <;> rcases mem_union.mp hyU with hyX | hyY
  · exact (s.no_internal_left hv hC hb hxX hyX hxy hsat).elim
  · exact Or.inl ⟨hxX,hyY⟩
  · exact Or.inr ⟨hxY,hyX⟩
  · exact (s.reverse.no_internal_left hv hC hb hxY hyY hxy hsat).elim

/-- Two distinct saturated pairs cannot share any supporting block.
The hypotheses retain all four endpoint identities. -/
theorem no_shared_support (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) {x y : α}
    (hx : x ≠ p ∧ x ≠ q) (hy : y ≠ p ∧ y ≠ q)
    (hxy : x ≠ y) (hsat : degree (star C x) y = 2)
    {A : Finset α} (hA : A ∈ C) (hpA : p ∈ A) (hqA : q ∈ A) :
    ¬ (x ∈ A ∧ y ∈ A) := by
  have ha : A ∈ star (star C p) q := by simp [star,hA,hpA,hqA]
  rw [s.star_eq] at ha
  intro hboth
  rcases s.separates hv hC hb hx hy hxy hsat with ⟨hxX,hyY⟩ | ⟨hxY,hyX⟩
  · rcases mem_insert.mp ha with he | he
    · subst A
      exact residual_not_mem_other (B := s.right) (D := s.left)
        (by simpa [inter_comm] using s.inter_eq) hyY hboth.2
    · have he := mem_singleton.mp he
      subst A
      exact residual_not_mem_other s.inter_eq hxX hboth.1
  · rcases mem_insert.mp ha with he | he
    · subst A
      exact residual_not_mem_other (B := s.right) (D := s.left)
        (by simpa [inter_comm] using s.inter_eq) hxY hboth.1
    · have he := mem_singleton.mp he
      subst A
      exact residual_not_mem_other s.inter_eq hyX hboth.2

/-- Different saturated cross-pairs have four distinct endpoints.
This uses global matching, not injectivity of a block assignment. -/
theorem cross_disjoint (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) {z w : α × α}
    (hz : z ∈ s.crosses) (hw : w ∈ s.crosses) (hzw : z ≠ w) :
    (w.1 ≠ z.1 ∧ w.1 ≠ z.2) ∧ (w.2 ≠ z.1 ∧ w.2 ≠ z.2) := by
  obtain ⟨hzP,hzs⟩ := mem_filter.mp hz
  obtain ⟨hwP,hws⟩ := mem_filter.mp hw
  obtain ⟨hzX,hzY⟩ := mem_product.mp hzP
  obtain ⟨hwX,hwY⟩ := mem_product.mp hwP
  have hsep (x y : α) (hx : x ∈ s.X) (hy : y ∈ s.Y) : x ≠ y := by
    intro he; exact disjoint_left.mp s.geometry.1 hx (he.symm ▸ hy)
  have hzneq := hsep z.1 z.2 hzX hzY
  have hwneq := hsep w.1 w.2 hwX hwY
  refine ⟨⟨?_,hsep _ _ hwX hzY⟩,⟨(hsep _ _ hzX hwY).symm,?_⟩⟩
  · intro he
    have hzrev : degree (star C z.2) z.1 = 2 := by rwa [pair_degree_comm]
    have hwrev : degree (star C z.1) w.2 = 2 := by simpa only [he] using hws
    have hh := saturated_matching hv hC hb hzneq.symm hzrev w.2
      (by simpa only [he] using hwneq.symm) hwrev
    exact hzw (Prod.ext he.symm hh.symm)
  · intro he
    have hwrev : degree (star C z.2) w.1 = 2 := by
      rw [pair_degree_comm]
      simpa only [he] using hws
    have hh := saturated_matching hv hC hb hzneq hzs w.1
      (by simpa only [he] using hwneq) hwrev
    exact hzw (Prod.ext hh.symm he.symm)

/-- Only after global separation is established does the first coordinate
of the actual block assignment become injective. -/
theorem cross_card_le_four (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) : s.crosses.card ≤ 4 := by
  obtain ⟨_,hP,_,_,_,_⟩ := s.surviving_counts (by simpa using hv) (Or.inl rfl) hC hb
  obtain ⟨f,hf,hi⟩ := s.assignment (by simpa using hv) (by omega) hC
  have hinj : Set.InjOn (fun z => (f z).1) s.crosses := by
    intro z hz w hw he
    change (f z).1 = (f w).1 at he
    by_contra hzw
    obtain ⟨hx,hy⟩ := s.cross_disjoint hv hC hb hz hw hzw
    have hzP := mem_product.mp (mem_filter.mp hz).1
    have hwP := mem_product.mp (mem_filter.mp hw).1
    have hzneq : z.1 ≠ z.2 := by
      intro he
      exact disjoint_left.mp s.geometry.1 hzP.1 (he.symm ▸ hzP.2)
    have hwneq : w.1 ≠ w.2 := by
      intro he
      exact disjoint_left.mp s.geometry.1 hwP.1 (he.symm ▸ hwP.2)
    obtain ⟨sz⟩ := exists_of_saturated (k := 31) (by simpa using hv)
      (by omega) hC hzneq (mem_filter.mp hz).2
    have hzA : z.1 ∈ (f z).1 ∧ z.2 ∈ (f z).1 := by
      constructor <;> apply inter_subset_left <;> rw [(hf z hz).2.2] <;> simp
    have hwA : w.1 ∈ (f z).1 ∧ w.2 ∈ (f z).1 := by
      rw [he]
      constructor <;> apply inter_subset_left <;> rw [(hf w hw).2.2] <;> simp
    exact sz.no_shared_support hv hC hb hx hy hwneq (mem_filter.mp hw).2
      (mem_onlyBlocks.mp (hf z hz).1).1 hzA.1 hzA.2 hwA
  have hh := card_le_card_of_injOn (fun z => (f z).1)
    (fun z hz => (hf z hz).1) hinj
  rwa [hP] at hh

/-- There are three or four other saturated edges. The exact loss and
excess budget is zero or one, respectively. -/
theorem small_budget (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) :
    (s.crosses.card = 3 ∨ s.crosses.card = 4) ∧
      s.loss+s.excess+3=s.crosses.card := by
  obtain ⟨_,hP,hQ,_,_,_⟩ := s.surviving_counts (by simpa using hv) (Or.inl rfl) hC hb
  have he := s.exact_budget (by simpa using hv) (by omega) hC
  have hp := s.parts
  rw [hb,hP,hQ] at hp
  rw [hP,hQ] at he
  norm_num [capacity] at he
  have hc := s.cross_card_le_four hv hC hb
  omega

end Split
end CoveringDesigns.SaturatedMatching
