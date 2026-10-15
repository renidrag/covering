import CoveringDesigns.C13_7_4.Structural.FourPointColors
import CoveringDesigns.C13_7_4.Structural.FourPointMatching
import CoveringDesigns.C13_7_4.Structural.GPPTGeometry

/-!
Closing the proper-colouring branch of the four-minimum-point obstruction.
The actual GPPT frames give all required rows of the original covering.
Two of the three perfect matchings avoid any prescribed outside point in
its triad; their rows violate the geometry of that point's minimum link.
-/

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural StantonGeometry

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1500000

/-- Of three distinct values, two avoid any specified value. -/
theorem two_indices_avoiding (f : Fin 3 → α) (hf : Function.Injective f) (p : α) :
    ∃ e : Fin 2 ↪ Fin 3, ∀ i, f (e i) ≠ p := by
  classical
  let A := univ.filter (fun i => f i = p)
  let B := univ.filter (fun i => f i ≠ p)
  have hA : A.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    exact hf ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
  have hsum : A.card + B.card = 3 := by
    simpa only [A, B, card_univ, Fintype.card_fin] using
      card_filter_add_card_filter_not (s := (univ : Finset (Fin 3))) (fun i => f i = p)
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < B.card)
  let e : Fin 2 → Fin 3 := ![a, b]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [e]
  refine ⟨⟨e, he⟩, ?_⟩
  intro i
  fin_cases i
  · exact (mem_filter.mp ha).2
  · exact (mem_filter.mp hb).2

namespace FourPointSystem

variable [Fintype α] {C : Family α} {K : Finset α} (F : FourPointSystem C K)

/-- The three selections at root zero name the three canonical matchings. -/
noncomputable def matchingSelected (v : Fin 4 → α) (hv : Function.Injective v)
    (hmem : ∀ i, v i ∈ K) (m : Fin 3) : Fin 3 → α :=
  F.indexedSelected v hv hmem 0 m.succ

/-- Every off-diagonal indexed selection supplies its actual marked rows. -/
theorem indexed_marked_mem (v : Fin 4 → α) (hv : Function.Injective v)
    (hmem : ∀ i, v i ∈ K) {a b : Fin 4} (hab : a ≠ b) (j : Fin 3) :
    {v a, v b} ∪ markedRow F.common.triad (F.indexedSelected v hv hmem a b) j ∈ C := by
  simp only [indexedSelected, dite_eq_right hab]
  exact F.marked_mem _ _ _ _ _ j

/-- In the proper branch, the three matching selections are distinct in
any triad. -/
theorem matchingSelected_injective (v : Fin 4 → α) (hv : Function.Injective v)
    (hmem : ∀ i, v i ∈ K) (j : Fin 3)
    (hproper : K4.Proper
      (F.indexedSelected v hv hmem 0 1 j) (F.indexedSelected v hv hmem 0 2 j)
      (F.indexedSelected v hv hmem 0 3 j) (F.indexedSelected v hv hmem 1 2 j)
      (F.indexedSelected v hv hmem 1 3 j) (F.indexedSelected v hv hmem 2 3 j)) :
    Function.Injective (fun m => F.matchingSelected v hv hmem m j) := by
  have h := hproper.1
  intro m n hmn
  fin_cases m <;> fin_cases n <;> simp_all [matchingSelected, K4.Distinct]

/-- The actual marked rows on either edge of a matching use the same
selection vector, by the structural opposite-edge colour lemma. -/
theorem canonical_marked_mem_of_proper (v : Fin 4 → α) (hv : Function.Injective v)
    (hmem : ∀ i, v i ∈ K)
    (hproper : ∀ j, K4.Proper
      (F.indexedSelected v hv hmem 0 1 j) (F.indexedSelected v hv hmem 0 2 j)
      (F.indexedSelected v hv hmem 0 3 j) (F.indexedSelected v hv hmem 1 2 j)
      (F.indexedSelected v hv hmem 1 3 j) (F.indexedSelected v hv hmem 2 3 j))
    (m : Fin 3) (b : Bool) (j : Fin 3) :
    canonicalEdge v (m, b) ∪
      markedRow F.common.triad (F.matchingSelected v hv hmem m) j ∈ C := by
  have hop (k : Fin 3) := K4.proper_opposite_edges_of_mem (F.common.triad k)
    (le_of_eq (F.common.triad_card k))
    (F.indexedSelected_mem v hv hmem (by decide : (0 : Fin 4) ≠ 1) k)
    (F.indexedSelected_mem v hv hmem (by decide : (0 : Fin 4) ≠ 2) k)
    (F.indexedSelected_mem v hv hmem (by decide : (0 : Fin 4) ≠ 3) k)
    (F.indexedSelected_mem v hv hmem (by decide : (1 : Fin 4) ≠ 2) k)
    (F.indexedSelected_mem v hv hmem (by decide : (1 : Fin 4) ≠ 3) k)
    (F.indexedSelected_mem v hv hmem (by decide : (2 : Fin 4) ≠ 3) k) (hproper k)
  have h0 : F.matchingSelected v hv hmem 0 = F.indexedSelected v hv hmem 2 3 := by
    funext k
    exact (hop k).1
  have h1 : F.matchingSelected v hv hmem 1 = F.indexedSelected v hv hmem 1 3 := by
    funext k
    exact (hop k).2.1
  have h2 : F.matchingSelected v hv hmem 2 = F.indexedSelected v hv hmem 1 2 := by
    funext k
    exact (hop k).2.2
  cases b
  · fin_cases m <;> simpa [canonicalEdge, matchingSelected] using
      (F.indexed_marked_mem v hv hmem (by decide : (0 : Fin 4) ≠ _) j)
  · fin_cases m
    · change {v 2, v 3} ∪ markedRow F.common.triad (F.matchingSelected v hv hmem 0) j ∈ C
      rw [h0]
      exact F.indexed_marked_mem v hv hmem (by decide : (2 : Fin 4) ≠ 3) j
    · change {v 1, v 3} ∪ markedRow F.common.triad (F.matchingSelected v hv hmem 1) j ∈ C
      rw [h1]
      exact F.indexed_marked_mem v hv hmem (by decide : (1 : Fin 4) ≠ 3) j
    · change {v 1, v 2} ∪ markedRow F.common.triad (F.matchingSelected v hv hmem 2) j ∈ C
      rw [h2]
      exact F.indexed_marked_mem v hv hmem (by decide : (1 : Fin 4) ≠ 2) j

/-- The proper-column branch contradicts the minimum link of any point
outside the four roots. All eight obstructing rows belong to the original
covering, as witnessed by its aligned Stanton/GPPT frames. -/
theorem proper_columns_impossible
    (hn : Fintype.card α = 13) (hC : IsCover C 7 4)
    (_hK : K.card = 4) (v : Fin 4 → α) (hv : Function.Injective v)
    (hmem : ∀ i, v i ∈ K) (_himage : univ.image v = K)
    (hproper : ∀ j, K4.Proper
      (F.indexedSelected v hv hmem 0 1 j) (F.indexedSelected v hv hmem 0 2 j)
      (F.indexedSelected v hv hmem 0 3 j) (F.indexedSelected v hv hmem 1 2 j)
      (F.indexedSelected v hv hmem 1 3 j) (F.indexedSelected v hv hmem 2 3 j))
    {p : α} (hp15 : degree C p = 15) (hpNotK : p ∉ K) : False := by
  classical
  have hpall : p ∈ K ∪ univ.biUnion F.common.triad := by rw [F.common.spans]; simp
  obtain ⟨j, _, hpj⟩ := mem_biUnion.mp ((mem_union.mp hpall).resolve_left hpNotK)
  obtain ⟨r, hr⟩ := two_indices_avoiding
    (fun m => F.matchingSelected v hv hmem m j)
    (F.matchingSelected_injective v hv hmem j (hproper j)) p
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 j
  let T := fun k => F.common.triad (σ k)
  let S := fun m k => F.matchingSelected v hv hmem (r m) (σ k)
  let E := fun i : Fin 2 × Bool => canonicalEdge v (r i.1, i.2)
  have hE : Function.Injective E := by
    intro i k hik
    have he := canonicalEdge_injective hv hik
    have hfirst : r i.1 = r k.1 := congrArg (fun z : Fin 3 × Bool => z.1) he
    have hsecond : i.2 = k.2 := congrArg (fun z : Fin 3 × Bool => z.2) he
    exact Prod.ext (r.injective hfirst) hsecond
  have hop (m : Fin 2) : Disjoint (E (m, false)) (E (m, true)) :=
    canonicalEdge_opposite_disjoint hv (r m)
  have hroot (i : Fin 4) (k : Fin 3) : v i ∉ F.common.triad k :=
    fun hx => disjoint_left.mp (F.common.disjoint_root k) (hmem i) hx
  have hET (i : Fin 2 × Bool) (k : Fin 3) : Disjoint (E i) (T k) :=
    canonicalEdge_disjoint_triads v F.common.triad hroot _ _
  have hcard (k : Fin 3) : (T k).card = 3 := F.common.triad_card _
  have hdis : Pairwise fun i k => Disjoint (T i) (T k) := by
    intro i k hik
    exact F.common.pairwise_disjoint (fun he => hik (σ.injective he))
  have hs (m : Fin 2) (k : Fin 3) : S m k ∈ T k :=
    F.indexedSelected_mem v hv hmem (Ne.symm (Fin.succ_ne_zero (r m))) (σ k)
  have hp : p ∈ T 0 := by simpa [T, σ] using hpj
  have hsp (m : Fin 2) : S m 0 ≠ p := by simpa [S, σ] using hr m
  have hblocks (i : (Fin 2 × Fin 2) × Bool) : fourPointGlobalBlock E T S i ∈ C := by
    dsimp only [fourPointGlobalBlock, E, T, S]
    rw [markedRow_reindex]
    exact F.canonical_marked_mem_of_proper v hv hmem hproper (r i.1.1) i.2 (σ i.1.2.succ)
  obtain ⟨M, hcommon⟩ := exists_four_point_matching C p E T S hE hop hET
    hcard hdis hs hp hsp hblocks
  exact four_pair_geometry_obstruction M hcommon (minimum_geometry
    (by rw [complement_point_card, hn]) (link_isCover hC p) (by rw [link_card, hp15]))

end FourPointSystem

#guard_standard_axioms two_indices_avoiding FourPointSystem.canonical_marked_mem_of_proper
  FourPointSystem.proper_columns_impossible

end CoveringDesigns.C13Structural
