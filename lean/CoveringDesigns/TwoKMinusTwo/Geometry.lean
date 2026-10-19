import CoveringDesigns.C20_11_3.SaturatedAssignment

/-! General saturated geometry and an injection into pairs of actual blocks. -/
namespace CoveringDesigns.TwoKMinusTwo
open Finset C20_11_3
variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
variable {C : Family α} {p q : α} {B D : Finset α}

/-- On 2k-2 points, the two size-k blocks intersect exactly in the
pair. This is not a converse to saturation. -/
theorem saturated_pair_inter (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hpq : p ≠ q)
    (hstar : star (star C p) q = {B, D}) : B ∩ D = {p, q} := by
  have hB : B ∈ star (star C p) q := by rw [hstar]; simp
  have hD : D ∈ star (star C p) q := by rw [hstar]; simp
  have hBC : B ∈ C := (mem_filter.mp (mem_filter.mp hB).1).1
  have hDC : D ∈ C := (mem_filter.mp (mem_filter.mp hD).1).1
  have hpB : p ∈ B := (mem_filter.mp (mem_filter.mp hB).1).2
  have hpD : p ∈ D := (mem_filter.mp (mem_filter.mp hD).1).2
  have hqB : q ∈ B := (mem_filter.mp hB).2
  have hqD : q ∈ D := (mem_filter.mp hD).2
  have hsub : ({p, q} : Finset α) ⊆ B ∩ D := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_inter.mpr ⟨hpB, hpD⟩
    · have : x = q := mem_singleton.mp hx
      subst x
      exact mem_inter.mpr ⟨hqB, hqD⟩
  have hcount := card_union_add_card_inter B D
  rw [saturated_pair_union hC.2 hpq hstar, card_univ, hv,
    hC.1 B hBC, hC.1 D hDC] at hcount
  apply (eq_of_subset_of_card_le hsub _).symm
  rw [card_pair hpq]
  omega

/-- A saturated pair supplies two distinct actual covering blocks. -/
theorem saturated_pair_blocks (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2) :
    ∃ B ∈ C, ∃ D ∈ C, B ≠ D ∧ star (star C p) q = {B, D} ∧
      B ∪ D = univ ∧ B ∩ D = {p, q} := by
  obtain ⟨B, D, hBD, hstar⟩ := card_eq_two.mp hsat
  have hB : B ∈ star (star C p) q := by rw [hstar]; simp
  have hD : D ∈ star (star C p) q := by rw [hstar]; simp
  refine ⟨B, (mem_filter.mp (mem_filter.mp hB).1).1,
    D, (mem_filter.mp (mem_filter.mp hD).1).1, hBD, hstar,
    saturated_pair_union hC.2 hpq hstar, saturated_pair_inter hv hk hC hpq hstar⟩

/-- Geometry with two already named blocks, for later cross-pair counting. -/
theorem saturated_pair_geometry (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2)
    (hBC : B ∈ C) (hDC : D ∈ C) (hBD : B ≠ D)
    (hpB : p ∈ B) (hqB : q ∈ B) (hpD : p ∈ D) (hqD : q ∈ D) :
    B ∪ D = univ ∧ B ∩ D = {p, q} := by
  have hB : B ∈ star (star C p) q :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨hBC, hpB⟩, hqB⟩
  have hD : D ∈ star (star C p) q :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨hDC, hpD⟩, hqD⟩
  have hstar := saturated_pair_star_eq hsat hB hD hBD
  exact ⟨saturated_pair_union hC.2 hpq hstar,
    saturated_pair_inter hv hk hC hpq hstar⟩

/-- Removing the saturated pair leaves two complementary (k-2)-sets. -/
theorem saturated_residual_geometry (hpq : p ≠ q)
    (hBcard : B.card = k) (hDcard : D.card = k)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p, q}) :
    Disjoint (B \ {p, q}) (D \ {p, q}) ∧
      (B \ {p, q}).card = k-2 ∧ (D \ {p, q}).card = k-2 ∧
      (B \ {p, q}) ∪ (D \ {p, q}) = univ \ {p, q} := by
  have hpB : ({p, q} : Finset α) ⊆ B := by rw [← hinter]; exact inter_subset_left
  have hpD : ({p, q} : Finset α) ⊆ D := by rw [← hinter]; exact inter_subset_right
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro x hxB hxD
    have hx : x ∈ B ∩ D := mem_inter.mpr
      ⟨(mem_sdiff.mp hxB).1, (mem_sdiff.mp hxD).1⟩
    rw [hinter] at hx
    exact (mem_sdiff.mp hxB).2 hx
  · rw [card_sdiff_of_subset hpB, hBcard, card_pair hpq]
  · rw [card_sdiff_of_subset hpD, hDcard, card_pair hpq]
  · ext x
    have hxU : x ∈ B ∪ D := by rw [hunion]; simp
    simp only [mem_union, mem_sdiff, mem_univ, true_and]
    constructor
    · rintro (⟨_, hx⟩ | ⟨_, hx⟩) <;> exact hx
    · intro hx
      rcases mem_union.mp hxU with hxB | hxD
      · exact Or.inl ⟨hxB, hx⟩
      · exact Or.inr ⟨hxD, hx⟩

/-- Saturated cross-pairs have a unique orientation in the two endpoint classes.
Existence is enough here; their exact intersection proves injectivity below. -/
theorem cross_partner_exists {C : Family α} {p q x y : α} {B D : Finset α}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) (hC : IsCover C k 3)
    (hstar : star (star C p) q = {B,D}) (hinter : B ∩ D = {p,q})
    (hx : x ∈ B \ {p,q}) (hy : y ∈ D \ {p,q})
    (hsat : degree (star C x) y = 2) :
    ∃ A ∈ onlyBlocks C p q, ∃ E ∈ onlyBlocks C q p, A ∩ E = {x,y} := by
  have hxD := residual_not_mem_other hinter hx
  have hyB : y ∉ B := residual_not_mem_other (B := D) (D := B)
    (by simpa [inter_comm] using hinter) hy
  have hxy : x ≠ y := by intro h; subst y; exact hxD (mem_sdiff.mp hy).1
  obtain ⟨A,hAC,E,hEC,hAE,hAEStar,hunion,hAEinter⟩ :=
    saturated_pair_blocks hv hk hC hxy hsat
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

/-- One simultaneous actual-block assignment, injective on all saturated cross-pairs. -/
theorem exists_cross_assignment {C : Family α} {p q : α} {B D : Finset α}
    (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k) (hC : IsCover C k 3)
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
      obtain ⟨A,hA,E,hE,hi⟩ := cross_partner_exists hv hk hC hstar hinter hx hy hs
      exact ⟨(A,E),fun _ => ⟨hA,hE,hi⟩⟩
    · exact ⟨(∅,∅),fun h => (hz h).elim⟩
  choose f hf using hex
  refine ⟨f,hf,?_⟩
  intro z hz w hw he
  apply cross_pair_eq_of_pair_eq hdis (mem_filter.mp hz).1 (mem_filter.mp hw).1
  exact (hf z hz).2.2.symm.trans ((congrArg (fun a => a.1 ∩ a.2) he).trans
    (hf w hw).2.2)


end CoveringDesigns.TwoKMinusTwo
