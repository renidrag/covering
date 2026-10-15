import CoveringDesigns.Foundations.StarRelabelling
import CoveringDesigns.Foundations.FourSetCounting
import CoveringDesigns.Foundations.StandardAxioms
import CoveringDesigns.C11_5_2.Geometry

/-!
Structural coordinates around a triple occurring in three blocks. The common
blocks determine three triads; each minimum point supplies a row of the
Stanton structure. All arguments are finite-set identities and counting.
-/

namespace CoveringDesigns.GPPTStructural

open Finset

variable {α : Type*} [DecidableEq α]

/-- The blocks containing every point of a specified set. -/
def commonBlocks (C : Family α) (A : Finset α) : Family α := C.filter (A ⊆ ·)

/-- Restore the deleted point to a block of a link. -/
def liftBlock (p : α) (B : Finset {q : α // q ≠ p}) : Finset α :=
  insert p (B.map (Function.Embedding.subtype _))

theorem liftBlock_subtype (p : α) {B : Finset α} (hp : p ∈ B) :
    liftBlock p (B.subtype (· ≠ p)) = B := by
  ext q
  by_cases hq : q = p
  · simp [liftBlock, hq, hp]
  · simp [liftBlock, hq]

/-- The seven blocks of an induced cover recover exactly the original star. -/
theorem liftBlock_link (C : Family α) (p : α) :
    (link C p).image (liftBlock p) = star C p := by
  unfold link
  rw [image_image]
  ext B
  constructor
  · intro hB
    obtain ⟨D, hD, he⟩ := mem_image.mp hB
    rw [Function.comp_apply, liftBlock_subtype p (mem_filter.mp hD).2] at he
    exact he ▸ hD
  · intro hB
    exact mem_image.mpr ⟨B, hB, liftBlock_subtype p (mem_filter.mp hB).2⟩

omit [DecidableEq α] in
theorem root_not_mem_map (p : α) (B : Finset {q : α // q ≠ p}) :
    p ∉ B.map (Function.Embedding.subtype _) := by
  intro hp
  obtain ⟨x, _, he⟩ := mem_map.mp hp
  exact x.property he

theorem star_inter_star (C : Family α) (p q : α) :
    star C p ∩ star C q = star (star C p) q := by
  ext B
  simp [star, and_assoc, and_left_comm]

theorem three_star_inter (C : Family α) (p q r : α) :
    star C p ∩ star C q ∩ star C r = commonBlocks C {p, q, r} := by
  ext B
  simp [star, commonBlocks, insert_subset_iff, singleton_subset_iff,
    and_assoc, and_left_comm]

/-- Inclusion-exclusion accounts for all fifteen blocks when three degree-seven
points have pair degrees three and occur together three times. -/
theorem three_minimum_stars_cover (C : Family α) (p q r : α)
    (hC : C.card ≤ 15)
    (hp : degree C p = 7) (hq : degree C q = 7) (hr : degree C r = 7)
    (hpq : degree (star C p) q = 3)
    (hpr : degree (star C p) r = 3)
    (hqr : degree (star C q) r = 3)
    (ht : (commonBlocks C {p, q, r}).card = 3) :
    star C p ∪ star C q ∪ star C r = C := by
  have hc := card_union_three_balance (star C p) (star C q) (star C r)
  rw [three_star_inter, star_inter_star, star_inter_star, star_inter_star] at hc
  change (star C p ∪ star C q ∪ star C r).card + degree (star C p) q +
    degree (star C p) r + degree (star C q) r =
      degree C p + degree C q + degree C r + (commonBlocks C {p, q, r}).card at hc
  have hsize : (star C p ∪ star C q ∪ star C r).card = 15 := by omega
  apply eq_of_subset_of_card_le
  · exact union_subset (union_subset (filter_subset _ _) (filter_subset _ _))
      (filter_subset _ _)
  · omega

/-- Three disjoint triads partition the complement of the root set. -/
structure RootTriads [Fintype α] (A : Finset α) where
  triad : Fin 3 → Finset α
  triad_card : ∀ j, (triad j).card = 3
  pairwise_disjoint : Pairwise (fun i j => Disjoint (triad i) (triad j))
  disjoint_root : ∀ j, Disjoint A (triad j)
  spans : A ∪ univ.biUnion triad = univ

namespace RootTriads

variable [Fintype α] {A : Finset α} (F : RootTriads A)

def cast {B : Finset α} (h : A = B) : RootTriads B := h ▸ F

theorem cast_triad {B : Finset α} (h : A = B) (j : Fin 3) :
    (F.cast h).triad j = F.triad j := by
  subst B
  rfl

theorem triad_nonempty (j : Fin 3) : (F.triad j).Nonempty :=
  card_pos.mp (by rw [F.triad_card]; omega)

theorem triad_injective : Function.Injective F.triad := by
  intro i j he
  by_contra hn
  obtain ⟨x, hx⟩ := F.triad_nonempty i
  exact disjoint_left.mp (F.pairwise_disjoint hn) hx (he ▸ hx)

theorem marked_sdiff (j : Fin 3) : (A ∪ F.triad j) \ A = F.triad j := by
  ext x
  have hd := disjoint_left.mp (F.disjoint_root j)
  simp only [mem_sdiff, mem_union]
  tauto

theorem marked_injective : Function.Injective (fun j => A ∪ F.triad j) := by
  intro i j he
  apply F.triad_injective
  simpa only [F.marked_sdiff] using congrArg (· \ A) he

theorem marked_card : (univ.image fun j => A ∪ F.triad j).card = 3 := by
  rw [card_image_of_injective _ F.marked_injective]
  rfl

/-- A triplicate root has exactly the three marked blocks supplied by a frame. -/
theorem commonBlocks_eq {C : Family α}
    (hmarked : ∀ j, A ∪ F.triad j ∈ C)
    (hthree : (commonBlocks C A).card = 3) :
    commonBlocks C A = univ.image (fun j => A ∪ F.triad j) := by
  symm
  apply eq_of_subset_of_card_le
  · intro B hB
    obtain ⟨j, _, rfl⟩ := mem_image.mp hB
    exact mem_filter.mpr ⟨hmarked j, subset_union_left⟩
  · rw [hthree, F.marked_card]

/-- Two frames around the same triplicate root have the same triads. The
permutation only names the same three common blocks in the same order. -/
theorem alignment (G : RootTriads A) {C : Family α}
    (hF : ∀ j, A ∪ F.triad j ∈ C) (hG : ∀ j, A ∪ G.triad j ∈ C)
    (hthree : (commonBlocks C A).card = 3) :
    ∃ e : Equiv.Perm (Fin 3), ∀ j, G.triad (e j) = F.triad j := by
  classical
  have hmatch : ∀ i, ∃ j, G.triad j = F.triad i := by
    intro i
    have hm : A ∪ F.triad i ∈ commonBlocks C A :=
      mem_filter.mpr ⟨hF i, subset_union_left⟩
    rw [G.commonBlocks_eq hG hthree] at hm
    obtain ⟨j, _, he⟩ := mem_image.mp hm
    refine ⟨j, ?_⟩
    simpa only [F.marked_sdiff, G.marked_sdiff] using congrArg (· \ A) he
  choose f hf using hmatch
  have hi : Function.Injective f := by
    intro i j he
    apply F.triad_injective
    rw [← hf i, ← hf j, he]
  exact ⟨Equiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩, hf⟩

end RootTriads

/-- Lift a three-triad partition from an induced cover to the original points.
No labels other than the three triad indices are chosen. -/
def RootTriads.ofSubtype [Fintype α] (p : α)
    (K : Finset {q : α // q ≠ p})
    (T : Fin 3 → Finset {q : α // q ≠ p})
    (hcard : ∀ j, (T j).card = 3)
    (hdis : Pairwise (fun i j => Disjoint (T i) (T j)))
    (hunion : univ.biUnion T = univ \ K) :
    RootTriads (insert p (K.map (Function.Embedding.subtype _))) := by
  let f : {q : α // q ≠ p} ↪ α := Function.Embedding.subtype _
  have hmem (j : Fin 3) {x : {q : α // q ≠ p}} (hx : x ∈ T j) : x ∉ K := by
    have hu : x ∈ univ.biUnion T := mem_biUnion.mpr ⟨j, mem_univ _, hx⟩
    rw [hunion] at hu
    exact (mem_sdiff.mp hu).2
  refine ⟨fun j => (T j).map f, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa using hcard j
  · intro i j hij
    exact (disjoint_map f).mpr (hdis hij)
  · intro j
    apply disjoint_left.mpr
    intro x hx hy
    rcases mem_insert.mp hx with he | hx
    · subst x
      exact root_not_mem_map p (T j) hy
    · obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
      obtain ⟨b, hb, he⟩ := mem_map.mp hy
      have hab : b = a := f.injective he
      exact hmem j hb (hab ▸ ha)
  · ext x
    simp only [mem_union, mem_insert, mem_univ, iff_true]
    by_cases hp : x = p
    · exact Or.inl (Or.inl hp)
    · let y : {q : α // q ≠ p} := ⟨x, hp⟩
      by_cases hk : y ∈ K
      · exact Or.inl (Or.inr (mem_map.mpr ⟨y, hk, rfl⟩))
      · have hu : y ∈ univ.biUnion T := by
          rw [hunion]
          exact mem_sdiff.mpr ⟨mem_univ _, hk⟩
        obtain ⟨j, _, hj⟩ := mem_biUnion.mp hu
        exact Or.inr (mem_biUnion.mpr ⟨j, mem_univ _, mem_map.mpr ⟨y, hj, rfl⟩⟩)

open StantonGeometry

theorem univ_image_perm {ι β : Type*} [Fintype ι] [DecidableEq β]
    (e : Equiv.Perm ι) (f : ι → β) :
    univ.image (fun i => f (e i)) = univ.image f := by
  ext x
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e.symm i, by simpa using hi⟩

theorem univ_biUnion_perm {ι : Type*} [Fintype ι]
    (e : Equiv.Perm ι) (f : ι → Finset α) :
    univ.biUnion (fun i => f (e i)) = univ.biUnion f := by
  ext x
  simp only [mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e.symm i, by simpa using hi⟩

theorem markedRow_reindex (T : Fin 3 → Finset α) (s : Fin 3 → α)
    (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    markedRow (fun j => T (e j)) (fun j => s (e j)) i = markedRow T s (e i) := by
  ext x
  simp only [markedRow, mem_union, mem_singleton, mem_biUnion,
    mem_erase, mem_univ, and_true]
  constructor
  · rintro (h | ⟨j, hj, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e j, fun he => hj (e.injective he), hx⟩
  · rintro (h | ⟨j, hj, hx⟩)
    · exact Or.inl h
    · refine Or.inr ⟨e.symm j, ?_, ?_⟩
      · intro he
        exact hj (by simpa using congrArg e he)
      · simpa using hx

def RootTriads.reindex [Fintype α] {A : Finset α} (F : RootTriads A)
    (e : Equiv.Perm (Fin 3)) : RootTriads A where
  triad j := F.triad (e j)
  triad_card j := F.triad_card (e j)
  pairwise_disjoint _ _ hij := F.pairwise_disjoint (fun h => hij (e.injective h))
  disjoint_root j := F.disjoint_root (e j)
  spans := by rw [univ_biUnion_perm, F.spans]

/-- The seven blocks at a minimum point, written relative to a marking couple.
The short trace can meet the couple, as is needed in the 778 case. -/
structure RootedFrame [Fintype α] (C : Family α) (p : α) (K : Finset α)
    extends RootTriads (insert p K) where
  couple_card : K.card = 2
  root_not_mem_couple : p ∉ K
  selected : Fin 3 → α
  selected_mem : ∀ j, selected j ∈ triad j
  shortTrace : Finset α
  shortTrace_card : shortTrace.card = 5
  root_not_mem_shortTrace : p ∉ shortTrace
  selected_subset : univ.image selected ⊆ shortTrace
  selected_iff : ∀ x : {q : α // q ≠ p},
    x.val ∈ univ.image selected ↔ IsShortPoint (link C p) x
  short_iff : ∀ B : Finset {q : α // q ≠ p},
    IsShortBlock (link C p) B ↔ B.map (Function.Embedding.subtype _) = shortTrace
  star_eq : star C p = insert (insert p shortTrace)
    ((univ.image fun j => insert p (K ∪ triad j)) ∪
      (univ.image fun j => insert p (markedRow triad selected j)))

private theorem markedRow_map_embedding {β : Type*} [DecidableEq β]
    (f : α ↪ β) (T : Fin 3 → Finset α) (s : Fin 3 → α) (i : Fin 3) :
    (markedRow T s i).map f =
      markedRow (fun j => (T j).map f) (fun j => f (s j)) i := by
  simp only [markedRow, map_eq_image, image_union, biUnion_image,
    image_sdiff _ _ f.injective, image_singleton]

/-- A Stanton marking frame in the link yields the same frame on the twelve
original points, with the root restored to every block. -/
def RootedFrame.ofMarking [Fintype α] {C : Family α} (p : α)
    {K : Finset {q : α // q ≠ p}} (F : MarkingFrame (link C p) K) :
    RootedFrame C p (K.map (Function.Embedding.subtype _)) where
  toRootTriads := RootTriads.ofSubtype p K F.triads F.triad_card
    F.triads_disjoint F.triads_union
  couple_card := by simpa using F.couple_card
  root_not_mem_couple := root_not_mem_map p K
  selected j := (F.selected j).val
  selected_mem j := mem_map.mpr ⟨F.selected j, F.selected_mem j, rfl⟩
  shortTrace := F.shortBlock.map (Function.Embedding.subtype _)
  shortTrace_card := by simpa using F.shortBlock_card
  root_not_mem_shortTrace := root_not_mem_map p F.shortBlock
  selected_subset := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    exact mem_map.mpr ⟨F.selected j,
      F.selected_subset (mem_image.mpr ⟨j, mem_univ _, rfl⟩), rfl⟩
  selected_iff x := by
    rw [← F.selected_iff]
    simp only [mem_image, mem_univ, true_and, Subtype.val_inj]
  short_iff B := by
    rw [F.short_iff, map_inj]
  star_eq := by
    have he := congrArg (fun D => D.image (liftBlock p)) F.blocks_eq
    rw [liftBlock_link] at he
    simpa only [image_insert, image_union, image_image, Function.comp_def,
      liftBlock, map_union, markedRow_map_embedding, RootTriads.ofSubtype,
      Function.Embedding.coe_subtype] using he

/-- Reindex the triads and the three determined full blocks together. This is
only a choice of coordinates on an unchanged star. -/
def RootedFrame.reindex [Fintype α] {C : Family α} {p : α} {K : Finset α}
    (F : RootedFrame C p K) (e : Equiv.Perm (Fin 3)) : RootedFrame C p K where
  toRootTriads := F.toRootTriads.reindex e
  couple_card := F.couple_card
  root_not_mem_couple := F.root_not_mem_couple
  selected j := F.selected (e j)
  selected_mem j := F.selected_mem (e j)
  shortTrace := F.shortTrace
  shortTrace_card := F.shortTrace_card
  root_not_mem_shortTrace := F.root_not_mem_shortTrace
  selected_subset := by rw [univ_image_perm]; exact F.selected_subset
  selected_iff x := by rw [univ_image_perm]; exact F.selected_iff x
  short_iff := F.short_iff
  star_eq := by
    change star C p = insert (insert p F.shortTrace)
      ((univ.image fun j => insert p (K ∪ F.triad (e j))) ∪
        (univ.image fun j => insert p
          (markedRow (fun j => F.triad (e j)) (fun j => F.selected (e j)) j)))
    simp only [markedRow_reindex]
    rw [univ_image_perm e (fun j => insert p (K ∪ F.triad j)),
      univ_image_perm e (fun j => insert p (markedRow F.triad F.selected j))]
    exact F.star_eq

namespace RootedFrame

variable [Fintype α] {C : Family α} {p : α} {K : Finset α}
  (F : RootedFrame C p K)

theorem marked_mem (j : Fin 3) : insert p (K ∪ F.triad j) ∈ C := by
  have hm : insert p (K ∪ F.triad j) ∈ star C p := by
    rw [F.star_eq]
    exact mem_insert_of_mem (mem_union_left _ (mem_image.mpr ⟨j, mem_univ _, rfl⟩))
  exact (mem_filter.mp hm).1

theorem short_mem : insert p F.shortTrace ∈ C := by
  have hm : insert p F.shortTrace ∈ star C p := by
    rw [F.star_eq]
    exact mem_insert_self _ _
  exact (mem_filter.mp hm).1

theorem selected_not_mem_root (j : Fin 3) : F.selected j ∉ insert p K := by
  intro hm
  exact disjoint_left.mp (F.disjoint_root j) hm (F.selected_mem j)

theorem short_ne_marked (i : Fin 3) :
    insert p F.shortTrace ≠ insert p (K ∪ F.triad i) := by
  obtain ⟨j, hj⟩ := exists_ne i
  have hs := F.selected_subset (mem_image.mpr ⟨j, mem_univ _, rfl⟩)
  have hnA := F.selected_not_mem_root j
  have hni : F.selected j ∉ F.triad i :=
    fun hm => disjoint_left.mp (F.pairwise_disjoint hj) (F.selected_mem j) hm
  intro he
  have hm : F.selected j ∈ insert p (K ∪ F.triad i) :=
    he ▸ mem_insert_of_mem hs
  simp only [mem_insert, mem_union] at hm
  rcases hm with hm | hm | hm
  · exact hnA (mem_insert.mpr (Or.inl hm))
  · exact hnA (mem_insert_of_mem hm)
  · exact hni hm

/-- A marking-couple member of pair degree three cannot lie in the short
block. The three marked blocks already account for all its occurrences. -/
theorem couple_point_not_mem_short {q : α} (hq : q ∈ K)
    (hdegree : degree (star C p) q = 3) : q ∉ F.shortTrace := by
  let M := univ.image fun j => insert p (K ∪ F.triad j)
  have he : M = star (star C p) q := by
    apply eq_of_subset_of_card_le
    · intro B hB
      obtain ⟨j, _, rfl⟩ := mem_image.mp hB
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨F.marked_mem j, mem_insert_self _ _⟩,
        mem_insert_of_mem (mem_union_left _ hq)⟩
    · have hc : M.card = 3 := by
        have hh := F.toRootTriads.marked_card
        simpa only [M, insert_union] using hh
      change degree (star C p) q ≤ M.card
      rw [hdegree, hc]
  intro hqW
  have hm : insert p F.shortTrace ∈ M := by
    rw [he]
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨F.short_mem, mem_insert_self _ _⟩,
      mem_insert_of_mem hqW⟩
  obtain ⟨j, _, hj⟩ := mem_image.mp hm
  exact F.short_ne_marked j hj.symm

end RootedFrame

/-- One rooted Stanton row, with its triads named in the common order. -/
structure AlignedRow [Fintype α] (C : Family α) (p : α) {A : Finset α}
    (G : RootTriads A) where
  selected : Fin 3 → α
  selected_mem : ∀ j, selected j ∈ G.triad j
  shortTrace : Finset α
  shortTrace_card : shortTrace.card = 5
  root_not_mem_shortTrace : p ∉ shortTrace
  selected_subset : univ.image selected ⊆ shortTrace
  selected_iff : ∀ x : {q : α // q ≠ p},
    x.val ∈ univ.image selected ↔ IsShortPoint (link C p) x
  short_iff : ∀ B : Finset {q : α // q ≠ p},
    IsShortBlock (link C p) B ↔ B.map (Function.Embedding.subtype _) = shortTrace
  star_eq : star C p = insert (insert p shortTrace)
    ((univ.image fun j => A ∪ G.triad j) ∪
      (univ.image fun j => insert p (markedRow G.triad selected j)))

/-- Three minimum stars on a common triplicate triple. All other points form
three common triads, and each row selects one short point in each triad. -/
structure TriplicateFrame [Fintype α] (C : Family α) where
  roots : Fin 3 → α
  roots_injective : Function.Injective roots
  common : RootTriads (univ.image roots)
  row : ∀ r, AlignedRow C (roots r) common
  root_degree : ∀ r, degree C (roots r) = 7
  short_disjoint_roots : ∀ r, Disjoint (univ.image roots) (row r).shortTrace
  blocks_eq : C =
    (univ.image fun j => univ.image roots ∪ common.triad j) ∪
    (univ.biUnion fun r => univ.image fun j =>
      insert (roots r) (markedRow common.triad (row r).selected j)) ∪
    (univ.image fun r => insert (roots r) (row r).shortTrace)

theorem liftBlock_injective (p : α) : Function.Injective (liftBlock p) := by
  intro B D he
  ext x
  have hm := congrArg (fun E => x.val ∈ E) he
  simpa [liftBlock, x.property] using hm

theorem liftBlock_subset_iff (p : α) (K B : Finset {q : α // q ≠ p}) :
    liftBlock p K ⊆ liftBlock p B ↔ K ⊆ B := by
  constructor
  · intro h x hx
    have hm := h (mem_insert_of_mem (mem_map.mpr ⟨x, hx, rfl⟩))
    simpa [liftBlock, x.property] using hm
  · intro h
    exact insert_subset_insert p (map_subset_map.mpr h)

theorem commonBlocks_liftBlock (C : Family α) (p : α)
    (K : Finset {q : α // q ≠ p}) :
    (commonBlocks (link C p) K).image (liftBlock p) =
      commonBlocks C (liftBlock p K) := by
  have hfilter : commonBlocks C (liftBlock p K) =
      (star C p).filter (liftBlock p K ⊆ ·) := by
    ext B
    simp only [commonBlocks, star, mem_filter]
    constructor
    · rintro ⟨hB, hK⟩
      exact ⟨⟨hB, hK (mem_insert_self _ _)⟩, hK⟩
    · rintro ⟨⟨hB, _⟩, hK⟩
      exact ⟨hB, hK⟩
  rw [hfilter, ← liftBlock_link, filter_image]
  simp only [commonBlocks, liftBlock_subset_iff]

/-- Existence of a rooted frame follows solely from Stanton's theorem in the
link and the intrinsic assertion that the marked pair occurs three times. -/
theorem exists_rooted_frame [Fintype α] {C : Family α} {p : α} {K : Finset α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hp : degree C p = 7)
    (hpK : p ∉ K) (hK : K.card = 2)
    (htriple : 3 ≤ (commonBlocks C (insert p K)).card) :
    Nonempty (RootedFrame C p K) := by
  let L := K.subtype (· ≠ p)
  have hmap : L.map (Function.Embedding.subtype _) = K :=
    map_subtype_of_notMem p K hpK
  have hcard : L.card = 2 := by
    have hh := congrArg Finset.card hmap
    simpa only [card_map, hK] using hh
  have hcouple : IsCouple (link C p) L := by
    refine ⟨hcard, ?_⟩
    have he := commonBlocks_liftBlock C p L
    have hc := congrArg Finset.card he
    rw [card_image_of_injective _ (liftBlock_injective p)] at hc
    rw [liftBlock, hmap] at hc
    change 3 ≤ (commonBlocks (link C p) L).card
    omega
  obtain ⟨F⟩ := exists_marking_frame
    (by rw [complement_point_card, hn]) (link_isCover hC p)
    (by rw [link_card, hp]) hcouple
  have G := RootedFrame.ofMarking p F
  rw [hmap] at G
  exact ⟨G⟩

/-- Place a rooted frame in any agreed order of its three triads. -/
def RootedFrame.alignTo [Fintype α] {C : Family α} {p : α} {K A : Finset α}
    (F : RootedFrame C p K) (G : RootTriads A) (hroot : insert p K = A)
    (e : Equiv.Perm (Fin 3)) (he : ∀ j, F.triad (e j) = G.triad j) :
    AlignedRow C p G where
  selected j := F.selected (e j)
  selected_mem j := he j ▸ F.selected_mem (e j)
  shortTrace := F.shortTrace
  shortTrace_card := F.shortTrace_card
  root_not_mem_shortTrace := F.root_not_mem_shortTrace
  selected_subset := by rw [univ_image_perm]; exact F.selected_subset
  selected_iff x := by rw [univ_image_perm]; exact F.selected_iff x
  short_iff := F.short_iff
  star_eq := by
    have hh := (F.reindex e).star_eq
    have hfun : (F.reindex e).triad = G.triad := funext he
    rw [hfun] at hh
    simpa only [← insert_union, hroot, RootedFrame.reindex] using hh

/-- The common triplicate blocks align a new minimum star with previously
chosen triads. The short trace itself is unchanged. -/
theorem RootedFrame.exists_alignedRow [Fintype α] {C : Family α}
    {p : α} {K A : Finset α} (F : RootedFrame C p K) (G : RootTriads A)
    (hroot : insert p K = A) (hmarked : ∀ j, A ∪ G.triad j ∈ C)
    (hthree : (commonBlocks C A).card = 3) :
    ∃ R : AlignedRow C p G, R.shortTrace = F.shortTrace := by
  let H : RootTriads A := hroot ▸ F.toRootTriads
  have hH (j : Fin 3) : H.triad j = F.triad j := by
    subst A
    rfl
  have hm (j : Fin 3) : A ∪ H.triad j ∈ C := by
    rw [hH, ← hroot, insert_union]
    exact F.marked_mem j
  obtain ⟨e, he⟩ := G.alignment H hmarked hm hthree
  exact ⟨F.alignTo G hroot e (fun j => (hH _).symm.trans (he j)), rfl⟩

/-- Each selected short point has degree three in the rooted induced cover. -/
theorem RootedFrame.selected_pair_degree_three [Fintype α] {C : Family α}
    {p : α} {K : Finset α} (F : RootedFrame C p K) (i : Fin 3) :
    degree (star C p) (F.selected i) = 3 := by
  have hne : F.selected i ≠ p :=
    fun he => F.selected_not_mem_root i (mem_insert.mpr (Or.inl he))
  have hh := (F.selected_iff ⟨F.selected i, hne⟩).mp
    (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  simpa only [degree_link] using hh.1

/-- Every unmarked block of a rooted star meets each of the three triads.
It is either the short block, or a full row containing one selected point and
the two complementary pairs. -/
theorem RootedFrame.nonmarked_meets_triad [Fintype α] {C : Family α}
    {p : α} {K : Finset α} (F : RootedFrame C p K) {B : Finset α}
    (hB : B ∈ C) (hp : p ∈ B) (hK : ¬ K ⊆ B) (i : Fin 3) :
    (B ∩ F.triad i).Nonempty := by
  have hm : B ∈ star C p := mem_filter.mpr ⟨hB, hp⟩
  rw [F.star_eq] at hm
  rcases mem_insert.mp hm with rfl | hm
  · exact ⟨F.selected i, mem_inter.mpr
      ⟨mem_insert_of_mem (F.selected_subset (mem_image.mpr ⟨i, mem_univ _, rfl⟩)),
        F.selected_mem i⟩⟩
  rcases mem_union.mp hm with hm | hm
  · obtain ⟨j, _, rfl⟩ := mem_image.mp hm
    exact False.elim (hK (subset_union_left.trans (subset_insert _ _)))
  · obtain ⟨j, _, rfl⟩ := mem_image.mp hm
    by_cases hij : i = j
    · subst j
      exact ⟨F.selected i, mem_inter.mpr
        ⟨mem_insert_of_mem (mem_union_left _ (mem_singleton_self _)), F.selected_mem i⟩⟩
    · have hn : ((F.triad i).erase (F.selected i)).Nonempty := by
        apply card_pos.mp
        rw [card_erase_of_mem (F.selected_mem i), F.triad_card]
        decide
      obtain ⟨x, hx⟩ := hn
      obtain ⟨hne, hxt⟩ := mem_erase.mp hx
      refine ⟨x, mem_inter.mpr ⟨mem_insert_of_mem (mem_union_right _ ?_), hxt⟩⟩
      exact mem_biUnion.mpr ⟨i, mem_erase.mpr ⟨hij, mem_univ _⟩,
        mem_sdiff.mpr ⟨hxt, by simpa using hne⟩⟩

/-- Build the three-star frame from Stanton's theorem and the specified pair
and triple degrees. The pair-degree prerequisite is kept explicit here. -/
theorem exists_triplicate_frame [Fintype α] {C : Family α}
    (hn : Fintype.card α = 12) (hC : IsCover C 6 3) (hb : C.card ≤ 15)
    (roots : Fin 3 → α) (hinj : Function.Injective roots)
    (hdegree : ∀ i, degree C (roots i) = 7)
    (hpair : ∀ i j, i ≠ j → degree (star C (roots i)) (roots j) = 3)
    (hthree : (commonBlocks C (univ.image roots)).card = 3) :
    Nonempty (TriplicateFrame C) := by
  classical
  let A := univ.image roots
  have hmem (i : Fin 3) : roots i ∈ A := mem_image.mpr ⟨i, mem_univ _, rfl⟩
  have hroot (i : Fin 3) : insert (roots i) (A.erase (roots i)) = A :=
    insert_erase (hmem i)
  have hcard : A.card = 3 := by
    dsimp only [A]
    rw [card_image_of_injective _ hinj]
    rfl
  have hex (i : Fin 3) : Nonempty (RootedFrame C (roots i) (A.erase (roots i))) := by
    apply exists_rooted_frame hn hC (hdegree i) (notMem_erase _ _)
    · rw [card_erase_of_mem (hmem i), hcard]
    · rw [hroot]
      exact Nat.le_of_eq hthree.symm
  let F (i : Fin 3) := Classical.choice (hex i)
  let G : RootTriads A := (F 0).toRootTriads.cast (hroot 0)
  have hG (j : Fin 3) : G.triad j = (F 0).triad j :=
    (F 0).toRootTriads.cast_triad (hroot 0) j
  have hmarked (j : Fin 3) : A ∪ G.triad j ∈ C := by
    rw [hG]
    simpa only [← insert_union, hroot] using (F 0).marked_mem j
  have hrow (i : Fin 3) : ∃ R : AlignedRow C (roots i) G,
      R.shortTrace = (F i).shortTrace :=
    (F i).exists_alignedRow G (hroot i) hmarked hthree
  choose R hR using hrow
  have hshort (i : Fin 3) : Disjoint A (R i).shortTrace := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    rw [hR i] at hy
    by_cases hji : j = i
    · subst j
      exact (F i).root_not_mem_shortTrace hy
    · exact (F i).couple_point_not_mem_short
        (mem_erase.mpr ⟨fun he => hji (hinj he), hmem j⟩)
        (hpair i j (Ne.symm hji)) hy
  have himage : A = {roots 0, roots 1, roots 2} := by
    ext x
    simp only [A, mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hcover : star C (roots 0) ∪ star C (roots 1) ∪ star C (roots 2) = C := by
    apply three_minimum_stars_cover C (roots 0) (roots 1) (roots 2) hb
      (hdegree 0) (hdegree 1) (hdegree 2)
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))
    simpa only [← himage] using hthree
  have hcover' : univ.biUnion (fun r => star C (roots r)) = C := by
    trans star C (roots 0) ∪ star C (roots 1) ∪ star C (roots 2)
    · ext B
      simp only [mem_biUnion, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨r, hr⟩
        fin_cases r
        · exact Or.inl (Or.inl hr)
        · exact Or.inl (Or.inr hr)
        · exact Or.inr hr
      · rintro ((h | h) | h)
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
    · exact hcover
  refine ⟨⟨roots, hinj, G, R, hdegree, hshort, ?_⟩⟩
  apply hcover'.symm.trans
  ext B
  simp only [mem_biUnion, mem_univ, true_and, (R _).star_eq,
    mem_insert, mem_union, mem_image]
  constructor
  · rintro ⟨r, h | h | h⟩
    · exact Or.inr ⟨r, h.symm⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨r, h⟩)
  · rintro ((h | ⟨r, h⟩) | ⟨r, h⟩)
    · exact ⟨0, Or.inr (Or.inl h)⟩
    · exact ⟨r, Or.inr (Or.inr h)⟩
    · exact ⟨r, Or.inl h.symm⟩

#guard_standard_axioms three_minimum_stars_cover RootTriads.commonBlocks_eq
  RootTriads.alignment liftBlock_link RootedFrame.ofMarking RootedFrame.reindex
  RootedFrame.couple_point_not_mem_short exists_rooted_frame
  RootedFrame.exists_alignedRow exists_triplicate_frame
  RootedFrame.selected_pair_degree_three RootedFrame.nonmarked_meets_triad

end CoveringDesigns.GPPTStructural
