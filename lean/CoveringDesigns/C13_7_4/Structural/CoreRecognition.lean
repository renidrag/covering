import CoveringDesigns.C13_7_4.Structural.RootedCore

/-!
Recognition of the six full rows in an ordinary rooted GPPT overlap.
The abstract argument separates the intrinsic core invariants from the
small fixed incidence identities of Figure 1.
-/

namespace CoveringDesigns.C13Structural

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

variable {α : Type*} [DecidableEq α]

/-- Incidence properties invariant under every relabelling of a rooted
ordinary six-row core. -/
structure IsSixCore (Q : Family α) : Prop where
  card_eq : Q.card = 6
  inter_le_two : ∀ B ∈ Q, ∀ D ∈ Q, B ≠ D → (B ∩ D).card ≤ 2
  opposite_exists : ∀ B ∈ Q, ∃ D ∈ Q, B ≠ D ∧ (B ∩ D).card = 1
  opposite_unique : ∀ B ∈ Q, ∀ D ∈ Q, ∀ E ∈ Q,
    B ≠ D → B ≠ E → (B ∩ D).card = 1 → (B ∩ E).card = 1 → D = E
  singleton_degree : ∀ B ∈ Q, ∀ D ∈ Q, ∀ a,
    B ≠ D → B ∩ D = {a} → degree Q a = 2
  degree_three_mate : ∀ a, degree Q a = 3 →
    ∃ b, b ≠ a ∧ star Q b = star Q a

private theorem own_short_forbids_old_opposite
    {C Q : Family α} {S B D : Finset α}
    (hQ : IsSixCore Q) (hS : S ∈ Q) (hSC : S ∉ C)
    (hB : B ∈ Q) (hBC : B ∈ C) (hD : D ∈ Q) (hDC : D ∈ C)
    (hBD : B ≠ D)
    (hop : (B ∩ D).card = 1 → ∃ a ∈ S, B ∩ D = {a}) :
    (B ∩ D).card ≠ 1 := by
  intro h
  obtain ⟨a, haS, ha⟩ := hop h
  have haB : a ∈ B := mem_of_mem_inter_left (ha ▸ mem_singleton_self a)
  have haD : a ∈ D := mem_of_mem_inter_right (ha ▸ mem_singleton_self a)
  have hSB : S ≠ B := by intro he; exact hSC (he ▸ hBC)
  have hSD : S ≠ D := by intro he; exact hSC (he ▸ hDC)
  have hsub : ({S, B, D} : Family α) ⊆ star Q a := by
    simp [insert_subset_iff, singleton_subset_iff, star, hS, hB, hD, haS, haB, haD]
  have hcard : ({S, B, D} : Family α).card = 3 := by
    simp [hSB, hSD, hBD]
  have hle := card_le_card hsub
  have hdeg := hQ.singleton_degree B hB D hD a hBD ha
  change (star Q a).card = 2 at hdeg
  omega

/-- A competing six-row core cannot use its own completed spine.  All old
opposite pairs are then broken, so every retained old row would have to use
that single spine as its opposite partner.  At most one old row can remain,
which cannot fill a six-row core even with all three added rows. -/
theorem own_short_not_mem_sixCore
    {C Q : Family α} {S T U : Finset α}
    (hQ : IsSixCore Q) (hSC : S ∉ C)
    (hsub : Q ⊆ C ∪ {S, T, U})
    (hopp : ∀ B ∈ C, ∀ D ∈ C, B ≠ D →
      (B ∩ D).card = 1 → ∃ a ∈ S, B ∩ D = {a})
    (hT : ∀ B ∈ C, 2 ≤ (B ∩ T).card)
    (hU : ∀ B ∈ C, 2 ≤ (B ∩ U).card) : S ∉ Q := by
  intro hS
  have hpartner (B : Finset α) (hBC : B ∈ C) (hBQ : B ∈ Q) :
      B ≠ S ∧ (B ∩ S).card = 1 := by
    obtain ⟨D, hDQ, hBD, hBDcard⟩ := hQ.opposite_exists B hBQ
    have hD := mem_union.mp (hsub hDQ)
    rcases hD with hDC | hD
    · exact False.elim ((own_short_forbids_old_opposite hQ hS hSC hBQ hBC
        hDQ hDC hBD (hopp B hBC D hDC hBD)) hBDcard)
    · simp only [mem_insert, mem_singleton] at hD
      rcases hD with rfl | rfl | rfl
      · exact ⟨hBD, hBDcard⟩
      · have ht := hT B hBC
        omega
      · have hu := hU B hBC
        omega
  have hsmall : (Q ∩ C).card ≤ 1 := by
    apply card_le_one.mpr
    intro B hB D hD
    obtain ⟨hBQ, hBC⟩ := mem_inter.mp hB
    obtain ⟨hDQ, hDC⟩ := mem_inter.mp hD
    have hb := hpartner B hBC hBQ
    have hd := hpartner D hDC hDQ
    exact hQ.opposite_unique S hS B hBQ D hDQ (Ne.symm hb.1) (Ne.symm hd.1)
      (by simpa only [inter_comm] using hb.2)
      (by simpa only [inter_comm] using hd.2)
  have hsub' : Q ⊆ (Q ∩ C) ∪ {S, T, U} := by
    intro B hB
    rcases mem_union.mp (hsub hB) with hBC | hB'
    · exact mem_union_left _ (mem_inter.mpr ⟨hB, hBC⟩)
    · exact mem_union_right _ hB'
  have hshort : ({S, T, U} : Family α).card ≤ 3 := card_le_three
  have hc := card_le_card hsub'
  have hu := card_union_le (Q ∩ C) ({S, T, U} : Family α)
  have hq := hQ.card_eq
  omega

/-- Old rows incompatible with a proposed added row. -/
def incompatibleRows (C : Family α) (T : Finset α) : Family α :=
  C.filter (fun B => 3 ≤ (B ∩ T).card)

private theorem incompatibleRows_subset_deleted
    {C Q : Family α} {T : Finset α} (hQ : IsSixCore Q)
    (hTC : T ∉ C) (hTQ : T ∈ Q) : incompatibleRows C T ⊆ C \ Q := by
  intro B hB
  obtain ⟨hBC, hlarge⟩ := mem_filter.mp hB
  refine mem_sdiff.mpr ⟨hBC, ?_⟩
  intro hBQ
  have hBT : B ≠ T := by intro he; exact hTC (he ▸ hBC)
  have hle := hQ.inter_le_two B hBQ T hTQ hBT
  omega

/-- If either foreign row enters another six-row core, both must enter and
both have exactly the same two incompatible old rows. This is a counting
argument about replacements, without a search over six-subsets. -/
theorem sixCore_replacement_rigidity
    {C Q : Family α} {T U : Finset α}
    (hC : C.card = 6) (hQ : IsSixCore Q)
    (hsub : Q ⊆ C ∪ {T, U}) (hTC : T ∉ C) (hUC : U ∉ C)
    (hTU : T ≠ U)
    (hTlarge : 2 ≤ (incompatibleRows C T).card)
    (hUlarge : 2 ≤ (incompatibleRows C U).card) :
    Q = C ∨ (incompatibleRows C T = incompatibleRows C U ∧
      (incompatibleRows C T).card = 2 ∧
      Q = (C \ incompatibleRows C T) ∪ {T, U}) := by
  by_cases he : Q = C
  · exact Or.inl he
  right
  have hdiff : (C \ Q).card = (Q \ C).card :=
    card_sdiff_comm (hC.trans hQ.card_eq.symm)
  have hadd : Q \ C ⊆ {T, U} := by
    intro B hB
    obtain ⟨hBQ, hBC⟩ := mem_sdiff.mp hB
    exact (mem_union.mp (hsub hBQ)).resolve_left hBC
  have hupper : (C \ Q).card ≤ 2 := by
    rw [hdiff]
    exact (card_le_card hadd).trans (by simp [hTU])
  have hQnC : ¬ Q ⊆ C := by
    intro hs
    exact he (eq_of_subset_of_card_le hs (by rw [hC, hQ.card_eq]))
  obtain ⟨B, hBQ, hBC⟩ := not_subset.mp hQnC
  have hlower : 2 ≤ (C \ Q).card := by
    have hb := (mem_union.mp (hsub hBQ)).resolve_left hBC
    simp only [mem_insert, mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact hTlarge.trans (card_le_card (incompatibleRows_subset_deleted hQ hTC hBQ))
    · exact hUlarge.trans (card_le_card (incompatibleRows_subset_deleted hQ hUC hBQ))
  have hdel : (C \ Q).card = 2 := Nat.le_antisymm hupper hlower
  have hadd_eq : Q \ C = {T, U} := by
    apply eq_of_subset_of_card_le hadd
    simp [hTU, ← hdiff, hdel]
  have hTQ : T ∈ Q := (mem_sdiff.mp (hadd_eq.symm ▸ (by simp : T ∈ ({T, U} : Family α)))).1
  have hUQ : U ∈ Q := (mem_sdiff.mp (hadd_eq.symm ▸ (by simp : U ∈ ({T, U} : Family α)))).1
  have hTdel : incompatibleRows C T = C \ Q :=
    eq_of_subset_of_card_le (incompatibleRows_subset_deleted hQ hTC hTQ) (by omega)
  have hUdel : incompatibleRows C U = C \ Q :=
    eq_of_subset_of_card_le (incompatibleRows_subset_deleted hQ hUC hUQ) (by omega)
  refine ⟨hTdel.trans hUdel.symm, hTdel ▸ hdel, ?_⟩
  rw [hTdel, ← hadd_eq, sdiff_sdiff_self_left, inter_comm C Q,
    union_comm, sdiff_union_inter]

/-- The six-core invariant is independent of point labels. -/
theorem IsSixCore.relabel {β : Type*} [DecidableEq β]
    {Q : Family α} (hQ : IsSixCore Q) (e : α ≃ β) :
    IsSixCore (CoveringDesigns.relabel e Q) := by
  have himage : CoveringDesigns.relabel e Q = Q.image (fun B => B.map e.toEmbedding) :=
    map_eq_image _ _
  refine ⟨(relabel_card e Q).trans hQ.card_eq, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [himage, forall_mem_image, ne_eq, map_inj, ← map_inter, card_map]
      using hQ.inter_le_two
  · simpa only [himage, forall_mem_image, exists_mem_image, ne_eq, map_inj, ← map_inter, card_map]
      using hQ.opposite_exists
  · simpa only [himage, forall_mem_image, ne_eq, map_inj, ← map_inter, card_map]
      using hQ.opposite_unique
  · intro B hB D hD a hBD ha
    obtain ⟨B₀, hB₀, hBe⟩ := mem_map.mp hB
    obtain ⟨D₀, hD₀, hDe⟩ := mem_map.mp hD
    change B₀.map e.toEmbedding = B at hBe
    change D₀.map e.toEmbedding = D at hDe
    subst B D
    obtain ⟨x, rfl⟩ := e.surjective a
    rw [degree_relabel]
    apply hQ.singleton_degree B₀ hB₀ D₀ hD₀ x
    · intro he
      exact hBD (congrArg (Finset.map e.toEmbedding) he)
    · apply map_injective e.toEmbedding
      simpa only [map_inter, map_singleton, Equiv.coe_toEmbedding] using ha
  · intro a ha
    obtain ⟨x, rfl⟩ := e.surjective a
    rw [degree_relabel] at ha
    obtain ⟨y, hy, he⟩ := hQ.degree_three_mate x ha
    refine ⟨e y, fun h => hy (e.injective h), ?_⟩
    rw [star_relabel, star_relabel, he]

/-- The intrinsic six-row properties hold in the fixed Figure 1 core.
Only its six rows and eleven columns are inspected in these elementary
coordinate identities. No family of completions is enumerated. -/
theorem commonTraceFamily_isSixCore : IsSixCore commonTraceFamily := by
  refine ⟨commonTraceFamily_card, ?_, ?_, ?_, ?_, ?_⟩
  · intro B hB D hD hBD
    obtain ⟨i, _, rfl⟩ := mem_image.mp hB
    obtain ⟨j, _, rfl⟩ := mem_image.mp hD
    have h : ∀ i j : Fin 3 × Bool,
        commonTrace i.1 i.2 ≠ commonTrace j.1 j.2 →
        (commonTrace i.1 i.2 ∩ commonTrace j.1 j.2).card ≤ 2 := by decide +kernel
    exact h i j hBD
  · intro B hB
    obtain ⟨⟨m, b⟩, _, rfl⟩ := mem_image.mp hB
    refine ⟨commonTrace m (!b), mem_image.mpr ⟨(m, !b), mem_univ _, rfl⟩, ?_⟩
    have h : ∀ m b, commonTrace m b ≠ commonTrace m (!b) ∧
        (commonTrace m b ∩ commonTrace m (!b)).card = 1 := by decide +kernel
    exact h m b
  · intro B hB D hD E hE hBD hBE h1 h2
    obtain ⟨i, _, rfl⟩ := mem_image.mp hB
    obtain ⟨j, _, rfl⟩ := mem_image.mp hD
    obtain ⟨k, _, rfl⟩ := mem_image.mp hE
    have h : ∀ i j k : Fin 3 × Bool,
        (commonTrace i.1 i.2 ∩ commonTrace j.1 j.2).card = 1 →
        (commonTrace i.1 i.2 ∩ commonTrace k.1 k.2).card = 1 →
        commonTrace j.1 j.2 = commonTrace k.1 k.2 := by decide +kernel
    exact h i j k h1 h2
  · intro B hB D hD a hBD ha
    obtain ⟨i, _, rfl⟩ := mem_image.mp hB
    obtain ⟨j, _, rfl⟩ := mem_image.mp hD
    have h : ∀ (i j : Fin 3 × Bool) (a : TracePoint),
        commonTrace i.1 i.2 ∩ commonTrace j.1 j.2 = {a} →
        degree commonTraceFamily a = 2 := by decide +kernel
    exact h i j a ha
  · have h : ∀ a : TracePoint, degree commonTraceFamily a = 3 →
        ∃ b, b ≠ a ∧ star commonTraceFamily b = star commonTraceFamily a := by decide +kernel
    exact h

private theorem commonTrace_not_contains_companions :
    ∀ i : Fin 3 × Bool, ¬ companions ⊆ commonTrace i.1 i.2 := by decide +kernel

private theorem commonTrace_opposite_point :
    ∀ i j : Fin 3 × Bool,
      (commonTrace i.1 i.2 ∩ commonTrace j.1 j.2).card = 1 →
      ∃ a ∈ companions, commonTrace i.1 i.2 ∩ commonTrace j.1 j.2 = {a} := by decide +kernel

/-- A completed foreign spine, after deleting the root. -/
def foreignTrace (b : Bool) (u : TracePoint) : Finset TracePoint :=
  insert u (transverse b)

private theorem commonTrace_foreign_inter :
    ∀ (i : Fin 3 × Bool) (b : Bool) (u : TracePoint),
      2 ≤ (commonTrace i.1 i.2 ∩ foreignTrace b u).card := by decide +kernel

private theorem foreignTrace_not_mem :
    ∀ b u, foreignTrace b u ∉ commonTraceFamily := by decide +kernel

private theorem foreignTrace_ne :
    ∀ u v, foreignTrace false u ≠ foreignTrace true v := by decide +kernel

private theorem foreignTrace_incompatible_card :
    ∀ b u, u ∉ transverse b →
      2 ≤ (incompatibleRows commonTraceFamily (foreignTrace b u)).card := by decide +kernel

/-- The two foreign rows have the same two incompatible full rows only
when their added points are the same companion. -/
private theorem foreignTrace_same_incompatible :
    ∀ u v, u ∉ transverse false → v ∉ transverse true →
      incompatibleRows commonTraceFamily (foreignTrace false u) =
        incompatibleRows commonTraceFamily (foreignTrace true v) →
      (incompatibleRows commonTraceFamily (foreignTrace false u)).card = 2 →
      ∃ m : Fin 3, u = Sum.inl m ∧ v = Sum.inl m ∧
        incompatibleRows commonTraceFamily (foreignTrace false u) =
          {commonTrace m false, commonTrace m true} := by decide +kernel

private def replacedCore (m : Fin 3) : Family TracePoint :=
  (commonTraceFamily \ {commonTrace m false, commonTrace m true}) ∪
    {foreignTrace false (Sum.inl m), foreignTrace true (Sum.inl m)}

/-- Replacing an opposite pair by the two transverse halves separates
all eight degree-three columns.  A single such column already witnesses
the failure of the duplicate-column core invariant. -/
private theorem replacedCore_separates_column :
    ∀ m : Fin 3,
      degree (replacedCore m) (Sum.inr (0, false)) = 3 ∧
      ∀ y : TracePoint,
        star (replacedCore m) y = star (replacedCore m) (Sum.inr (0, false)) →
        y = Sum.inr (0, false) := by decide +kernel

/-- The six full rows are intrinsically recognizable inside the common
rooted overlap. The three additional rows are allowed arbitrary additions;
there is no enumeration of the possible completed coverings. -/
theorem sixCore_unique_in_overlap
    (Q : Family TracePoint) (S : Finset TracePoint) (u v : TracePoint)
    (hQ : IsSixCore Q) (hAS : companions ⊆ S)
    (hu : u ∉ transverse false) (hv : v ∉ transverse true)
    (hsub : Q ⊆ commonTraceFamily ∪ {S, foreignTrace false u, foreignTrace true v}) :
    Q = commonTraceFamily := by
  have hSC : S ∉ commonTraceFamily := by
    intro hS
    obtain ⟨i, _, he⟩ := mem_image.mp hS
    exact commonTrace_not_contains_companions i (he.symm ▸ hAS)
  have hSQ : S ∉ Q := own_short_not_mem_sixCore hQ hSC hsub
    (by
      intro B hB D hD _ hBD
      obtain ⟨i, _, rfl⟩ := mem_image.mp hB
      obtain ⟨j, _, rfl⟩ := mem_image.mp hD
      obtain ⟨a, ha, he⟩ := commonTrace_opposite_point i j hBD
      exact ⟨a, hAS ha, he⟩)
    (by
      intro B hB
      obtain ⟨i, _, rfl⟩ := mem_image.mp hB
      exact commonTrace_foreign_inter i false u)
    (by
      intro B hB
      obtain ⟨i, _, rfl⟩ := mem_image.mp hB
      exact commonTrace_foreign_inter i true v)
  have hsub' : Q ⊆ commonTraceFamily ∪ {foreignTrace false u, foreignTrace true v} := by
    intro B hB
    rcases mem_union.mp (hsub hB) with hBC | hB'
    · exact mem_union_left _ hBC
    · simp only [mem_insert, mem_singleton] at hB'
      rcases hB' with rfl | rfl | rfl
      · exact False.elim (hSQ hB)
      · exact mem_union_right _ (by simp)
      · exact mem_union_right _ (by simp)
  rcases sixCore_replacement_rigidity commonTraceFamily_card hQ hsub'
    (foreignTrace_not_mem false u) (foreignTrace_not_mem true v) (foreignTrace_ne u v)
    (foreignTrace_incompatible_card false u hu) (foreignTrace_incompatible_card true v hv)
    with he | ⟨hbad, hcard, he⟩
  · exact he
  · obtain ⟨m, rfl, rfl, hbadrows⟩ := foreignTrace_same_incompatible u v hu hv hbad hcard
    have hQr : Q = replacedCore m := by simpa only [replacedCore, hbadrows] using he
    rw [hQr] at hQ
    obtain ⟨y, hy, heq⟩ := hQ.degree_three_mate _ (replacedCore_separates_column m).1
    exact False.elim (hy ((replacedCore_separates_column m).2 y heq))

#guard_standard_axioms own_short_not_mem_sixCore sixCore_replacement_rigidity
  IsSixCore.relabel commonTraceFamily_isSixCore sixCore_unique_in_overlap

end CoveringDesigns.C13Structural
