import Mathlib.Data.Fintype.Card
import Aesop
import CoveringDesigns.Foundations.StandardAxioms

/-!
Structural edge colouring of a tetrahedron.  The six arguments have order
`ab, ac, ad, bc, bd, cd`.  Proofs use only equality, the three-colour bound,
and propagation through the four vertices; they do not enumerate colourings.
-/

namespace CoveringDesigns.C13Structural.K4

variable {α : Type*}

/-- All three edges incident at a vertex have one colour. -/
def Same (a b c : α) : Prop := a = b ∧ b = c

/-- The three edges incident at a vertex have distinct colours. -/
def Distinct (a b c : α) : Prop := a ≠ b ∧ a ≠ c ∧ b ≠ c

/-- The local GPPT condition: monochromatic or rainbow. -/
def Allowed (a b c : α) : Prop := Same a b c ∨ Distinct a b c

/-- A form of the three-colour bound that also applies to a chosen triad. -/
def ThreeColours (α : Type*) : Prop :=
  ∀ a b c d : α, a ≠ b → a ≠ c → b ≠ c → d = a ∨ d = b ∨ d = c

/-- Any three distinct elements exhaust a type of cardinality at most three. -/
theorem threeColours_of_card_le [Fintype α] (hc : Fintype.card α ≤ 3) :
    ThreeColours α := by
  classical
  intro a b c d hab hac hbc
  have hcard : ({a, b, c} : Finset α).card = 3 := by
    simp [hab, hac, hbc]
  have huniv : ({a, b, c} : Finset α) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ, hcard] using hc
  have hd : d ∈ ({a, b, c} : Finset α) := by rw [huniv]; simp
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hd

theorem allowed_swap_left {a b c : α} (h : Allowed a b c) : Allowed b a c := by
  unfold Allowed Same Distinct at *
  rcases h with h | h <;> aesop

theorem allowed_swap_right {a b c : α} (h : Allowed a b c) : Allowed a c b := by
  unfold Allowed Same Distinct at *
  rcases h with h | h <;> aesop

/-- If one vertex is monochromatic, all six edges have its colour.
If the second vertex were rainbow, the opposite triangle would demand a
fourth colour. Otherwise equality propagates along the two shared edges. -/
theorem constant_of_same_at_first (hpalette : ThreeColours α)
    {a b c d e f : α} (h0 : Same a b c)
    (h1 : Allowed a d e) (h2 : Allowed b d f) (h3 : Allowed c e f) :
    a = b ∧ a = c ∧ a = d ∧ a = e ∧ a = f := by
  rcases h0 with ⟨rfl, rfl⟩
  rcases h1 with ⟨had, hde⟩ | ⟨had, hae, hde⟩
  · subst d
    subst e
    unfold Allowed Same Distinct at h2
    aesop
  · have hf := hpalette _ _ _ f had hae hde
    unfold Allowed Same Distinct at h2 h3
    aesop

/-- The four local constraints on the six edges of a tetrahedron. -/
def LocalPattern (a b c d e f : α) : Prop :=
  Allowed a b c ∧ Allowed a d e ∧ Allowed b d f ∧ Allowed c e f

/-- All six edges have the first edge's colour. -/
def Constant (a b c d e f : α) : Prop :=
  a = b ∧ a = c ∧ a = d ∧ a = e ∧ a = f

/-- Every vertex is rainbow. -/
def Proper (a b c d e f : α) : Prop :=
  Distinct a b c ∧ Distinct a d e ∧ Distinct b d f ∧ Distinct c e f

/-- Monochromatic-or-rainbow at every vertex implies constant or proper. -/
theorem local_pattern_dichotomy (hpalette : ThreeColours α)
    {a b c d e f : α} (h : LocalPattern a b c d e f) :
    Constant a b c d e f ∨ Proper a b c d e f := by
  rcases h with ⟨h0, h1, h2, h3⟩
  rcases h0 with h0 | h0
  · exact Or.inl (constant_of_same_at_first hpalette h0 h1 h2 h3)
  right
  refine ⟨h0, ?_, ?_, ?_⟩
  · rcases h1 with h1 | h1
    · have hh := constant_of_same_at_first hpalette h1 (Or.inr h0)
        (allowed_swap_left h2) (allowed_swap_left h3)
      exact False.elim (h0.1 hh.2.2.1)
    · exact h1
  · rcases h2 with h2 | h2
    · have hh := constant_of_same_at_first hpalette h2
        (allowed_swap_left (Or.inr h0)) (allowed_swap_left h1)
        (allowed_swap_left (allowed_swap_right h3))
      exact False.elim (h0.1 hh.2.2.1.symm)
    · exact h2
  · rcases h3 with h3 | h3
    · have hh := constant_of_same_at_first hpalette h3
        (allowed_swap_left (allowed_swap_right (Or.inr h0)))
        (allowed_swap_left (allowed_swap_right h1))
        (allowed_swap_left (allowed_swap_right h2))
      exact False.elim (h0.2.1 hh.2.2.1.symm)
    · exact h3

/-- In a proper three-edge-colouring of a tetrahedron, opposite edges agree.
The three neighbours of one vertex already exhaust the colours. -/
theorem proper_opposite_edges (hpalette : ThreeColours α)
    {a b c d e f : α} (h : Proper a b c d e f) :
    a = f ∧ b = e ∧ c = d := by
  rcases h with ⟨h0, h1, h2, h3⟩
  have hd := hpalette a b c d h0.1 h0.2.1 h0.2.2
  have he := hpalette a b c e h0.1 h0.2.1 h0.2.2
  have hf := hpalette a b c f h0.1 h0.2.1 h0.2.2
  unfold Distinct at *
  aesop

/-- The dichotomy for an actual three-point colour type. -/
theorem local_pattern_dichotomy_of_card_le [Fintype α]
    (hc : Fintype.card α ≤ 3) {a b c d e f : α}
    (h : LocalPattern a b c d e f) :
    Constant a b c d e f ∨ Proper a b c d e f :=
  local_pattern_dichotomy (threeColours_of_card_le hc) h

/-- Opposite-edge equality for an actual three-point colour type. -/
theorem proper_opposite_edges_of_card_le [Fintype α]
    (hc : Fintype.card α ≤ 3) {a b c d e f : α}
    (h : Proper a b c d e f) : a = f ∧ b = e ∧ c = d :=
  proper_opposite_edges (threeColours_of_card_le hc) h

/-- A proper colouring is determined by the three colours incident at one
vertex, with the same colour on each opposite edge. -/
theorem proper_iff_distinct_and_opposite (hpalette : ThreeColours α)
    {a b c d e f : α} :
    Proper a b c d e f ↔ Distinct a b c ∧ a = f ∧ b = e ∧ c = d := by
  constructor
  · intro h
    exact ⟨h.1, proper_opposite_edges hpalette h⟩
  · rintro ⟨h, rfl, rfl, rfl⟩
    unfold Proper Distinct at *
    aesop

/-- The dichotomy when the colours are points of a specified triad in an
arbitrary ambient type. No choice of labels for the triad is required. -/
theorem local_pattern_dichotomy_of_mem [DecidableEq α]
    (T : Finset α) (hT : T.card ≤ 3) {a b c d e f : α}
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T)
    (hd : d ∈ T) (he : e ∈ T) (hf : f ∈ T)
    (h : LocalPattern a b c d e f) :
    Constant a b c d e f ∨ Proper a b c d e f := by
  have hcard : Fintype.card T ≤ 3 := by simpa using hT
  have hsub : LocalPattern (⟨a, ha⟩ : T) ⟨b, hb⟩ ⟨c, hc⟩
      ⟨d, hd⟩ ⟨e, he⟩ ⟨f, hf⟩ := by
    simpa only [LocalPattern, Allowed, Same, Distinct, ne_eq, Subtype.mk.injEq] using h
  have hout := local_pattern_dichotomy_of_card_le hcard hsub
  simpa only [Constant, Proper, Distinct, ne_eq, Subtype.mk.injEq] using hout

/-- Opposite-edge equality when all six colours belong to one triad. -/
theorem proper_opposite_edges_of_mem [DecidableEq α]
    (T : Finset α) (hT : T.card ≤ 3) {a b c d e f : α}
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T)
    (hd : d ∈ T) (he : e ∈ T) (hf : f ∈ T)
    (h : Proper a b c d e f) : a = f ∧ b = e ∧ c = d := by
  have hcard : Fintype.card T ≤ 3 := by simpa using hT
  have hsub : Proper (⟨a, ha⟩ : T) ⟨b, hb⟩ ⟨c, hc⟩
      ⟨d, hd⟩ ⟨e, he⟩ ⟨f, hf⟩ := by
    simpa only [Proper, Distinct, ne_eq, Subtype.mk.injEq] using h
  have hout := proper_opposite_edges_of_card_le hcard hsub
  simpa only [Subtype.mk.injEq] using hout

#guard_standard_axioms threeColours_of_card_le constant_of_same_at_first
  local_pattern_dichotomy proper_opposite_edges
  local_pattern_dichotomy_of_card_le proper_opposite_edges_of_card_le
  proper_iff_distinct_and_opposite local_pattern_dichotomy_of_mem
  proper_opposite_edges_of_mem

end CoveringDesigns.C13Structural.K4
