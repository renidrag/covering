import CoveringDesigns.C18_10_3.SaturatedLocal
import CoveringDesigns.Foundations.IncidencePacking

/-! Saturated edges form an eight-edge matching if any exists. Separation is
reapplied at every edge before packing sixteen occurrences into eleven indices. -/
namespace CoveringDesigns.C18_10_3
open Finset C20_11_3
variable {α : Type*} [Fintype α] [DecidableEq α]

def saturatedEdges (C : Family α) : Finset (Finset α) :=
  (univ.powersetCard 2).filter (fun e => (C.filter (fun B => e ⊆ B)).card = 2)

theorem pair_filter (C : Family α) (p q : α) :
    C.filter (fun B => ({p,q} : Finset α) ⊆ B) = star (star C p) q := by
  ext B
  simp [star, and_assoc, insert_subset_iff, singleton_subset_iff]

theorem mem_saturatedEdges_pair (C : Family α) {p q : α} (hpq : p ≠ q) :
    ({p,q} : Finset α) ∈ saturatedEdges C ↔ degree (star C p) q = 2 := by
  simp [saturatedEdges, pair_filter, degree, hpq]

theorem edge_cases {C : Family α} {e : Finset α} (he : e ∈ saturatedEdges C) :
    ∃ p q, p ≠ q ∧ e = {p,q} ∧ degree (star C p) q = 2 := by
  have hc : e.card = 2 := (mem_powersetCard.mp (mem_filter.mp he).1).2
  obtain ⟨p,q,hpq,rfl⟩ := card_eq_two.mp hc
  exact ⟨p,q,hpq,rfl,(mem_saturatedEdges_pair C hpq).mp he⟩

theorem edge_partner {C : Family α} {e : Finset α} (he : e ∈ saturatedEdges C)
    {p : α} (hp : p ∈ e) :
    ∃ q, p ≠ q ∧ e = {p,q} ∧ degree (star C p) q = 2 := by
  obtain ⟨a,b,hab,rfl,hs⟩ := edge_cases he
  rcases mem_insert.mp hp with rfl | hp
  · exact ⟨b,hab,rfl,hs⟩
  · have hp := mem_singleton.mp hp
    subst p
    exact ⟨a,hab.symm,pair_comm _ _,by simpa [pair_degree_comm] using hs⟩

theorem saturated_endpoints {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2) :
    degree C p = 6 ∧ degree C q = 6 := by
  rcases saturated_low_endpoint hv hC hb hpq hsat with hp | hq
  · exact ⟨hp,(saturated_local hv hC hb hpq.symm hp
      (by simpa [pair_degree_comm] using hsat)).1⟩
  · exact ⟨(saturated_local hv hC hb hpq hq hsat).1,hq⟩

theorem saturated_no_second {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2)
    (z : α) (hzp : z ≠ p) (hzq : z ≠ q) : degree (star C p) z ≠ 2 := by
  have hp := (saturated_endpoints hv hC hb hpq hsat).1
  exact (saturated_local hv hC hb hpq.symm hp
    (by simpa [pair_degree_comm] using hsat)).2.1 z hzq hzp

theorem edges_disjoint {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11) :
    (saturatedEdges C : Set (Finset α)).PairwiseDisjoint id := by
  intro e he f hf hef
  apply disjoint_left.mpr
  intro p hpE hpF
  obtain ⟨q,hpq,heq,hsq⟩ := edge_partner he hpE
  obtain ⟨r,hpr,her,hsr⟩ := edge_partner hf hpF
  by_cases hqr : q = r
  · exact hef (heq.trans (by simpa [hqr] using her.symm))
  · exact saturated_no_second hv hC hb hpq hsq r hpr.symm (Ne.symm hqr) hsr

theorem edges_card_le_eight {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11) :
    (saturatedEdges C).card ≤ 8 := by
  have hhigh : ∃ h, degree C h ≠ 6 := by
    rcases degree_profiles hv hC hb with ⟨h,hh,_⟩ | ⟨h,g,_,hh,_,_⟩ <;>
      exact ⟨h,by omega⟩
  obtain ⟨h,hh⟩ := hhigh
  have hsub : (saturatedEdges C).biUnion id ⊆ univ.erase h := by
    intro p hp
    obtain ⟨e,he,hpe⟩ := mem_biUnion.mp hp
    obtain ⟨q,hpq,_,hs⟩ := edge_partner he hpe
    have hp6 := (saturated_endpoints hv hC hb hpq hs).1
    exact mem_erase.mpr ⟨by intro hp; subst p; exact hh hp6,mem_univ _⟩
  have hc := card_le_card hsub
  rw [card_biUnion (edges_disjoint hv hC hb),card_erase_of_mem (mem_univ h),card_univ,hv] at hc
  have he : (∑ e ∈ saturatedEdges C, (id e).card) = 2 * (saturatedEdges C).card := by
    calc
      _ = ∑ _e ∈ saturatedEdges C, 2 := sum_congr rfl fun e he =>
        (mem_powersetCard.mp (mem_filter.mp he).1).2
      _ = _ := by simp [Nat.mul_comm]
  rw [he] at hc
  omega

/-- The seven local cross-edges exhaust every other edge. Thus this lemma
applies at each edge's own partition, not just a first chosen partition. -/
theorem all_other_edges_cross {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2)
    {B D : Finset α} (hBC : B ∈ C) (hDC : D ∈ C)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p,q})
    (hseven : 7 ≤ (((B \ {p,q}) ×ˢ (D \ {p,q})).filter
      (fun z => degree (star C z.1) z.2 = 2)).card) :
    (saturatedEdges C).card = 8 ∧
    ∀ e ∈ saturatedEdges C, e ≠ {p,q} →
      ∃ x ∈ B \ {p,q}, ∃ y ∈ D \ {p,q}, e = {x,y} := by
  let X := B \ {p,q}
  let Y := D \ {p,q}
  let T := (X ×ˢ Y).filter (fun z => degree (star C z.1) z.2 = 2)
  let M := saturatedEdges C
  have hdis := (TwoKMinusTwo.saturated_residual_geometry hpq
    (hC.1 B hBC) (hC.1 D hDC) hunion hinter).1
  have hinj : Set.InjOn (fun z : α × α => ({z.1,z.2} : Finset α)) T := by
    intro z hz w hw he
    exact cross_pair_eq_of_pair_eq hdis (mem_filter.mp hz).1 (mem_filter.mp hw).1 he
  let F := T.image (fun z => ({z.1,z.2} : Finset α))
  have hF : F.card = T.card := card_image_of_injOn hinj
  have hpqM : ({p,q} : Finset α) ∈ M := (mem_saturatedEdges_pair C hpq).mpr hsat
  have hsub : F ⊆ M.erase {p,q} := by
    intro e he
    obtain ⟨z,hz,rfl⟩ := mem_image.mp he
    obtain ⟨hzT,hs⟩ := mem_filter.mp hz
    obtain ⟨hzX,hzY⟩ := mem_product.mp hzT
    have hxy : z.1 ≠ z.2 := fun he => disjoint_left.mp hdis hzX (he.symm ▸ hzY)
    refine mem_erase.mpr ⟨?_,(mem_saturatedEdges_pair C hxy).mpr hs⟩
    intro he
    have hm : z.1 ∈ ({p,q} : Finset α) := by rw [← he]; simp
    exact (mem_sdiff.mp hzX).2 hm
  have hle := edges_card_le_eight hv hC hb
  have hfc := card_le_card hsub
  rw [card_erase_of_mem hpqM,hF] at hfc
  change 7 ≤ T.card at hseven
  change M.card ≤ 8 at hle
  have hM : M.card = 8 := by omega
  have heq : F = M.erase {p,q} := eq_of_subset_of_card_le hsub (by
    rw [card_erase_of_mem hpqM,hF]; omega)
  refine ⟨hM,?_⟩
  intro e he hne
  have hf : e ∈ F := heq.symm ▸ mem_erase.mpr ⟨hne,he⟩
  obtain ⟨z,hz,he⟩ := mem_image.mp hf
  obtain ⟨hzX,hzY⟩ := mem_product.mp (mem_filter.mp hz).1
  exact ⟨z.1,hzX,z.2,hzY,he.symm⟩

/-- An actual block index supports at most one edge, derived by reapplying
the local partition theorem to that edge. -/
theorem supporting_index_unique {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    (A : Finset α) (hAC : A ∈ C) (e : Finset α) (he : e ∈ saturatedEdges C)
    (f : Finset α) (hf : f ∈ saturatedEdges C) (heA : e ⊆ A) (hfA : f ⊆ A) : e = f := by
  by_contra hne
  obtain ⟨p,q,hpq,rfl,hs⟩ := edge_cases he
  have hq6 := (saturated_endpoints hv hC hb hpq hs).2
  obtain ⟨_,_,B,hBC,D,hDC,_,hstar,hunion,hinter,hseven⟩ := saturated_local hv hC hb hpq hq6 hs
  obtain ⟨x,hx,y,hy,hfxy⟩ := (all_other_edges_cross hv hC hb hpq hs hBC hDC
    hunion hinter hseven).2 f hf (Ne.symm hne)
  have hAs : A ∈ star (star C p) q := by
    simp only [star, mem_filter]
    exact ⟨⟨hAC,heA (by simp)⟩,heA (by simp)⟩
  rw [hstar] at hAs
  have hxA : x ∈ A := hfA (by rw [hfxy]; simp)
  have hyA : y ∈ A := hfA (by rw [hfxy]; simp)
  rcases mem_insert.mp hAs with hAB | hAD
  · exact residual_not_mem_other (B := D) (D := B)
      (by simpa [inter_comm] using hinter) hy (hAB ▸ hyA)
  · exact residual_not_mem_other hinter hx ((mem_singleton.mp hAD) ▸ hxA)

theorem no_saturated_pair {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    {p q : α} (hpq : p ≠ q) (hsat : degree (star C p) q = 2) : False := by
  obtain ⟨_,_,B,hBC,D,hDC,_,_,hunion,hinter,hseven⟩ := saturated_local hv hC hb hpq
    (saturated_endpoints hv hC hb hpq hsat).2 hsat
  have hM := (all_other_edges_cross hv hC hb hpq hsat hBC hDC hunion hinter hseven).1
  have hpack := IncidencePacking.packing (saturatedEdges C) C (fun e B => e ⊆ B) 2
    (fun e he => (mem_filter.mp he).2) (supporting_index_unique hv hC hb)
  rw [hM,hb] at hpack
  omega

theorem pair_ge_three {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    (p q : α) (hpq : p ≠ q) : 3 ≤ degree (star C p) q := by
  have hl := pair_ge_two hv hC hpq
  have hn : degree (star C p) q ≠ 2 := no_saturated_pair hv hC hb hpq
  omega

end CoveringDesigns.C18_10_3
