import CoveringDesigns.C11_5_2.Structural.NormalForm

/-!
Stanton's seven-block classification, proved by structural counting and
complementary triples. The mathematical reconstruction was supplied by the
project owner; the intersecting-triples and complementary-partition steps
were shortened during its formalisation. No classification certificate is
imported. See `coverings/11-5-2/proof.md` for the argument.
-/

namespace CoveringDesigns

/-- Every minimum cover admits the seven-cell structural template. -/
theorem stanton_partition_on {α : Type*} [Fintype α] [DecidableEq α]
    (hn : Fintype.card α = 11) {C : Family α}
    (hC : IsCover C 5 2) (hb : C.card = 7) :
    Nonempty (StantonStructural.TemplatePartition C) := by
  obtain ⟨S, hS⟩ := StantonStructural.exists_six_block_frame hn hC hb
  simpa only [hS] using S.nonempty_templatePartition

/-- The intrinsic template can be labelled on eleven points. -/
theorem stanton_template_on {α : Type*} [Fintype α] [DecidableEq α]
    (hn : Fintype.card α = 11) {C : Family α}
    (hC : IsCover C 5 2) (hb : C.card = 7) :
    Nonempty (StantonStructural.StantonTemplate C) := by
  obtain ⟨P⟩ := stanton_partition_on hn hC hb
  exact P.nonempty_template

/-- Every seven-block cover belongs to one of the two explicit types. -/
theorem stanton_classification_on {α : Type*} [Fintype α] [DecidableEq α]
    (hn : Fintype.card α = 11) {C : Family α}
    (hC : IsCover C 5 2) (hb : C.card = 7) :
    ∃ tag, Isomorphic C (stantonRepresentative tag) := by
  obtain ⟨T⟩ := stanton_template_on hn hC hb
  exact T.classification

theorem stanton_classification {C : Family (Fin 11)}
    (hC : IsCover C 5 2) (hb : C.card = 7) :
    ∃ tag, Isomorphic C (stantonRepresentative tag) :=
  stanton_classification_on (by simp) hC hb

#guard_standard_axioms stanton_partition_on stanton_template_on
  stanton_classification_on stanton_classification

end CoveringDesigns
