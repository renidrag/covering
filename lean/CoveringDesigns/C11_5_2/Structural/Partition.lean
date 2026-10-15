import CoveringDesigns.C11_5_2.Structural.Template
import Mathlib.Data.List.Nodup

/-! Labelling an abstract Stanton partition.  Choosing the two labels in
each disjoint pair is reversible; no symmetry of a covering is imposed. -/

namespace CoveringDesigns.StantonStructural

open Finset

structure TemplatePartition {α : Type*} [Fintype α] [DecidableEq α]
    (C : Family α) where
  a : α
  s : α
  t : α
  F : Finset α
  G : Finset α
  Cpair : Finset α
  D : Finset α
  R : Finset α
  F_card : F.card = 2
  G_card : G.card = 2
  Cpair_card : Cpair.card = 2
  D_card : D.card = 2
  cells_disjoint : List.Pairwise Disjoint [{a}, {s}, {t}, F, G, Cpair, D]
  spans : {a, s, t} ∪ F ∪ G ∪ Cpair ∪ D = univ
  R_subset : R ⊆ Cpair ∪ D
  R_card : R.card = 2
  blocks_eq : C =
    {{a} ∪ F ∪ G,
     F ∪ {s} ∪ Cpair, F ∪ {t} ∪ D,
     G ∪ {s} ∪ D, G ∪ {t} ∪ Cpair,
     {a} ∪ Cpair ∪ D, {a, s, t} ∪ R}

theorem TemplatePartition.nonempty_template {α : Type*} [Fintype α] [DecidableEq α]
    {C : Family α} (h : TemplatePartition C) : Nonempty (StantonTemplate C) := by
  classical
  obtain ⟨a, s, t, F, G, Cp, D, R, hF, hG, hCp, hD, hdis, hspan, hR, hr, hblocks⟩ := h
  obtain ⟨f₀, f₁, hf, rfl⟩ := card_eq_two.mp hF
  obtain ⟨g₀, g₁, hg, rfl⟩ := card_eq_two.mp hG
  obtain ⟨c₀, c₁, hc, rfl⟩ := card_eq_two.mp hCp
  obtain ⟨d₀, d₁, hd, rfl⟩ := card_eq_two.mp hD
  let labels : List α := [a, s, t, f₀, f₁, g₀, g₁, c₀, c₁, d₀, d₁]
  have hnd : labels.Nodup := by
    simp_all [labels, List.pairwise_cons, disjoint_left]
  have hsurj : Function.Surjective labels.get := by
    intro x
    have hx : x ∈ labels := by
      have hu : x ∈ ({a, s, t} ∪ {f₀, f₁} ∪ {g₀, g₁} ∪ {c₀, c₁} ∪ {d₀, d₁} : Finset α) := by
        rw [hspan]
        exact mem_univ x
      simpa [labels, or_assoc, or_comm, or_left_comm] using hu
    exact List.mem_iff_get.mp hx
  let e : Fin 11 ≃ α := Equiv.ofBijective labels.get ⟨hnd.injective_get, hsurj⟩
  have he0 : e 0 = a := rfl
  have he1 : e 1 = s := rfl
  have he2 : e 2 = t := rfl
  have he3 : e 3 = f₀ := rfl
  have he4 : e 4 = f₁ := rfl
  have he5 : e 5 = g₀ := rfl
  have he6 : e 6 = g₁ := rfl
  have he7 : e 7 = c₀ := rfl
  have he8 : e 8 = c₁ := rfl
  have he9 : e 9 = d₀ := rfl
  have he10 : e 10 = d₁ := rfl
  have hpair : (pairC ∪ pairD).map e.toEmbedding = {c₀, c₁} ∪ {d₀, d₁} := by
    simp only [pairC, pairD, map_union, map_insert, map_singleton,
      Equiv.coe_toEmbedding, he7, he8, he9, he10]
  have hRmap : (R.map e.symm.toEmbedding).map e.toEmbedding = R := by
    simp [map_map]
  refine ⟨⟨e, R.map e.symm.toEmbedding, ?_, by simpa using hr, ?_⟩⟩
  · apply map_symm_subset.mpr
    rwa [hpair]
  · rw [hblocks]
    simp only [templateBlocks, coreSix, spine, relabel, map_insert, map_singleton]
    change insert (({0, 1, 2} ∪ R.map e.symm.toEmbedding).map e.toEmbedding)
      {(Finset.map e.toEmbedding {0, 3, 4, 5, 6}),
       (Finset.map e.toEmbedding {1, 3, 4, 7, 8}),
       (Finset.map e.toEmbedding {2, 3, 4, 9, 10}),
       (Finset.map e.toEmbedding {1, 5, 6, 9, 10}),
       (Finset.map e.toEmbedding {2, 5, 6, 7, 8}),
       (Finset.map e.toEmbedding {0, 7, 8, 9, 10})} = _
    simp only [map_insert, map_singleton, Equiv.coe_toEmbedding,
      he0, he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, hRmap,
      singleton_union, insert_union, union_insert, union_singleton]
    simp only [← insert_empty, insert_comm]

noncomputable def TemplatePartition.toStantonTemplate {α : Type*}
    [Fintype α] [DecidableEq α] {C : Family α} (h : TemplatePartition C) :
    StantonTemplate C := Classical.choice h.nonempty_template

theorem TemplatePartition.classification {α : Type*} [Fintype α] [DecidableEq α]
    {C : Family α} (h : TemplatePartition C) :
    ∃ tag, Isomorphic C (stantonRepresentative tag) :=
  h.toStantonTemplate.classification

theorem TemplatePartition.isCover {α : Type*} [Fintype α] [DecidableEq α]
    {C : Family α} (h : TemplatePartition C) : IsCover C 5 2 :=
  h.toStantonTemplate.isCover

theorem TemplatePartition.card {α : Type*} [Fintype α] [DecidableEq α]
    {C : Family α} (h : TemplatePartition C) : C.card = 7 :=
  h.toStantonTemplate.card

#guard_standard_axioms TemplatePartition.nonempty_template TemplatePartition.classification
  TemplatePartition.isCover TemplatePartition.card

end CoveringDesigns.StantonStructural
