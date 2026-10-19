import CoveringDesigns.C20_11_3.SaturatedGeometry
import CoveringDesigns.C20_11_3.SaturatedPartition

/-! The injective assignment uses actual blocks, oriented by the original endpoints. -/
namespace CoveringDesigns.C20_11_3
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- A cross-point lies in only its own original endpoint block. -/
theorem residual_not_mem_other {p q x : α} {B D : Finset α}
    (hinter : B ∩ D = {p,q}) (hx : x ∈ B \ {p,q}) : x ∉ D := by
  intro hxD
  have hi : x ∈ B ∩ D := mem_inter.mpr ⟨(mem_sdiff.mp hx).1,hxD⟩
  rw [hinter] at hi
  exact (mem_sdiff.mp hx).2 hi

/-- Saturated cross-pairs have a unique orientation in the two endpoint classes.
Existence is enough here; their exact intersection proves injectivity below. -/
theorem cross_partner_exists {C : Family α} {p q x y : α} {B D : Finset α}
    (hv : Fintype.card α = 20) (hC : IsCover C 11 3)
    (hstar : star (star C p) q = {B,D}) (hinter : B ∩ D = {p,q})
    (hx : x ∈ B \ {p,q}) (hy : y ∈ D \ {p,q})
    (hsat : degree (star C x) y = 2) :
    ∃ A ∈ onlyBlocks C p q, ∃ E ∈ onlyBlocks C q p, A ∩ E = {x,y} := by
  have hxD := residual_not_mem_other hinter hx
  have hyB : y ∉ B := residual_not_mem_other (B := D) (D := B)
    (by simpa [inter_comm] using hinter) hy
  have hxy : x ≠ y := by intro h; subst y; exact hxD (mem_sdiff.mp hy).1
  obtain ⟨A,hAC,E,hEC,hAE,hAEStar,hunion,hAEinter⟩ :=
    saturated_pair_blocks hv hC hxy hsat
  have hxA : x ∈ A := inter_subset_left (by rw [hAEinter]; simp)
  have hyA : y ∈ A := inter_subset_left (by rw [hAEinter]; simp)
  have hxE : x ∈ E := inter_subset_right (by rw [hAEinter]; simp)
  have hyE : y ∈ E := inter_subset_right (by rw [hAEinter]; simp)
  have hnotboth (F : Finset α) (hFC : F ∈ C) (hxF : x ∈ F) (hyF : y ∈ F) :
      ¬ (p ∈ F ∧ q ∈ F) := by
    intro hh
    have hF : F ∈ star (star C p) q := by simp [star,hFC,hh.1,hh.2]
    rw [hstar] at hF
    rcases mem_insert.mp hF with hFB | hFD
    · subst F; exact hyB hyF
    · have hFD := mem_singleton.mp hFD
      subst F; exact hxD hxF
  have hpU : p ∈ A ∪ E := by rw [hunion]; simp
  have hqU : q ∈ A ∪ E := by rw [hunion]; simp
  by_cases hpA : p ∈ A
  · have hqA : q ∉ A := fun h => hnotboth A hAC hxA hyA ⟨hpA,h⟩
    have hqE := (mem_union.mp hqU).resolve_left hqA
    have hpE : p ∉ E := fun h => hnotboth E hEC hxE hyE ⟨h,hqE⟩
    exact ⟨A,mem_onlyBlocks.mpr ⟨hAC,hpA,hqA⟩,
      E,mem_onlyBlocks.mpr ⟨hEC,hqE,hpE⟩,hAEinter⟩
  · have hpE := (mem_union.mp hpU).resolve_left hpA
    have hqE : q ∉ E := fun h => hnotboth E hEC hxE hyE ⟨hpE,h⟩
    have hqA := (mem_union.mp hqU).resolve_right hqE
    exact ⟨E,mem_onlyBlocks.mpr ⟨hEC,hpE,hqE⟩,
      A,mem_onlyBlocks.mpr ⟨hAC,hqA,hpA⟩,by simpa [inter_comm] using hAEinter⟩

omit [Fintype α] in
/-- For a saturated pair, its actual endpoint-oriented partners are unique.
The reverse implication from an intersection of size two is not used. -/
theorem endpoint_partner_unique {C : Family α} {p q x y : α}
    {A E A' E' : Finset α} (hsat : degree (star C x) y = 2)
    (hA : A ∈ onlyBlocks C p q) (hE : E ∈ onlyBlocks C q p)
    (hi : A ∩ E = {x,y})
    (hA' : A' ∈ onlyBlocks C p q) (hE' : E' ∈ onlyBlocks C q p)
    (hi' : A' ∩ E' = {x,y}) : A = A' ∧ E = E' := by
  have hmem {F G : Finset α} (hFC : F ∈ C) (hiFG : F ∩ G = {x,y}) :
      F ∈ star (star C x) y := by
    have hx : x ∈ F := inter_subset_left (by rw [hiFG]; simp)
    have hy : y ∈ F := inter_subset_left (by rw [hiFG]; simp)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hFC,hx⟩,hy⟩
  have hAS := hmem (mem_onlyBlocks.mp hA).1 hi
  have hES := hmem (mem_onlyBlocks.mp hE).1
    (show E ∩ A = {x,y} by simpa [inter_comm] using hi)
  have hAE : A ≠ E := by
    intro he
    have hpE : p ∈ E := he ▸ (mem_onlyBlocks.mp hA).2.1
    exact (mem_onlyBlocks.mp hE).2.2 hpE
  have hstar := saturated_pair_star_eq hsat hAS hES hAE
  have hAS' := hmem (mem_onlyBlocks.mp hA').1 hi'
  have hES' := hmem (mem_onlyBlocks.mp hE').1
    (show E' ∩ A' = {x,y} by simpa [inter_comm] using hi')
  rw [hstar] at hAS' hES'
  have hAA : A' = A := by
    rcases mem_insert.mp hAS' with he | he
    · exact he
    · have he := mem_singleton.mp he
      exact ((mem_onlyBlocks.mp hE).2.2 (he ▸ (mem_onlyBlocks.mp hA').2.1)).elim
  have hEE : E' = E := by
    rcases mem_insert.mp hES' with he | he
    · exact ((mem_onlyBlocks.mp hA).2.2 (he ▸ (mem_onlyBlocks.mp hE').2.1)).elim
    · exact mem_singleton.mp he
  exact ⟨hAA.symm,hEE.symm⟩

/-- One simultaneous actual-block assignment, injective on all saturated cross-pairs. -/
theorem exists_cross_assignment {C : Family α} {p q : α} {B D : Finset α}
    (hv : Fintype.card α = 20) (hC : IsCover C 11 3)
    (hstar : star (star C p) q = {B,D}) (hinter : B ∩ D = {p,q})
    (hdis : Disjoint (B \ {p,q}) (D \ {p,q})) :
    let T := ((B \ {p,q}) ×ˢ (D \ {p,q})).filter
      (fun z => degree (star C z.1) z.2 = 2)
    ∃ f : α × α → Finset α × Finset α,
      (∀ z ∈ T, (f z).1 ∈ onlyBlocks C p q ∧
        (f z).2 ∈ onlyBlocks C q p ∧ (f z).1 ∩ (f z).2 = {z.1,z.2}) ∧
      Set.InjOn f (T : Set (α × α)) := by
  classical
  dsimp only
  let T := ((B \ {p,q}) ×ˢ (D \ {p,q})).filter
    (fun z => degree (star C z.1) z.2 = 2)
  have hex (z : α × α) : ∃ a : Finset α × Finset α,
      z ∈ T → a.1 ∈ onlyBlocks C p q ∧ a.2 ∈ onlyBlocks C q p ∧
        a.1 ∩ a.2 = {z.1,z.2} := by
    by_cases hz : z ∈ T
    · obtain ⟨hz',hs⟩ := mem_filter.mp hz
      obtain ⟨hx,hy⟩ := mem_product.mp hz'
      obtain ⟨A,hA,E,hE,hi⟩ := cross_partner_exists hv hC hstar hinter hx hy hs
      exact ⟨(A,E),fun _ => ⟨hA,hE,hi⟩⟩
    · exact ⟨(∅,∅),fun h => (hz h).elim⟩
  choose f hf using hex
  refine ⟨f,hf,?_⟩
  intro z hz w hw he
  apply cross_pair_eq_of_pair_eq hdis (mem_filter.mp hz).1 (mem_filter.mp hw).1
  exact (hf z hz).2.2.symm.trans ((congrArg (fun a => a.1 ∩ a.2) he).trans
    (hf w hw).2.2)

end CoveringDesigns.C20_11_3
