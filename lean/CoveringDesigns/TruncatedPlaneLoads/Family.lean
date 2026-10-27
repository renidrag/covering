import CoveringDesigns.TruncatedPlaneLoads.Classification

/-! The classification contract for an ordinary family of occupied supports. -/

namespace CoveringDesigns.TruncatedPlaneLoads
open Finset
variable {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable {q : ℕ} (P : Plane q V G)

/-- Every designated support is occupied with strictly positive weight.
Weights outside H are irrelevant. In particular every designated core is positive. -/
structure Admissible (H : Finset (Finset V)) (w : Finset V → ℝ) (K : ℝ) : Prop where
  core_subset : P.core ⊆ H
  uniform : ∀ S ∈ H, S.card = q+1
  intersect : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty
  positive : ∀ S ∈ H, 0 < w S
  load : ∀ x, (∑ S ∈ H, if x ∈ S then w S else 0) = K
  load_pos : 0 < K

def Description (H : Finset (Finset V)) (w : Finset V → ℝ) (t : ℝ) : Prop :=
  (H = P.core ∧ ∀ E ∈ P.core, w E = t) ∨
  ∃ c : V, ∃ s : ℝ, 0 < s ∧ s < t ∧
    (∀ S, S ∈ H ↔ S ∈ P.core ∨ ∃ i, i ≠ P.group c ∧ S = P.extra i c) ∧
    (∀ i, i ≠ P.group c → w (P.extra i c) = s) ∧
    ∀ E ∈ P.core, w E = if c ∈ E then t-s else t

/-- Complete classification relative to the supplied core, with no claim
of uniqueness of that core or of its presentation. -/
theorem real_classification (hq : 4 ≤ q) {H : Finset (Finset V)}
    {w : Finset V → ℝ} {K : ℝ} (h : Admissible P H w K) :
    Description P H w (K/q) := by
  classical
  let A := H \ P.core
  have shape (S : A) : ∃ i a, P.group a ≠ i ∧ S.val = P.extra i a := by
    exact (P.support_classification (by omega) (h.uniform S.val (mem_sdiff.mp S.property).1)
      (fun E hE => h.intersect E (h.core_subset hE) S.val (mem_sdiff.mp S.property).1)).resolve_left
        (mem_sdiff.mp S.property).2
  choose b a outside shape using shape
  let D : Internal.Loads (I := A) P K := {
    coreWeight := w
    base := b
    tip := a
    weight := fun S => w S.val
    outside := outside
    injective := by
      intro S T he
      apply Subtype.ext
      have hb : b S = b T := congrArg Prod.fst he
      have ha : a S = a T := congrArg Prod.snd he
      rw [shape S, shape T, hb, ha]
    core_pos := fun E hE => h.positive E (h.core_subset hE)
    extra_pos := fun S => h.positive S.val (mem_sdiff.mp S.property).1
    meet := by
      intro S T hST
      apply (P.extra_intersection hST).mp
      rw [← shape S, ← shape T]
      exact h.intersect S.val (mem_sdiff.mp S.property).1 T.val (mem_sdiff.mp T.property).1
    load := by
      intro x
      have he : (∑ S : A, if x ∈ P.extra (b S) (a S) then w S.val else 0) =
          ∑ S ∈ A, if x ∈ S then w S else 0 := by
        simp_rw [← shape]
        exact sum_coe_sort A (fun S => if x ∈ S then w S else 0)
      rw [he, add_comm, sum_sdiff h.core_subset]
      exact h.load x }
  rcases D.classify hq with ⟨hempty, hw⟩ | ⟨c,s,hs,hst,hex,allbases,hcore⟩
  · refine Or.inl ⟨?_, hw⟩
    apply Subset.antisymm ?_ h.core_subset
    intro S hS
    by_contra hn
    exact hempty.false ⟨S, mem_sdiff.mpr ⟨hS, hn⟩⟩
  · refine Or.inr ⟨c,s,hs,hst,?_,?_,hcore⟩
    · intro S
      constructor
      · intro hS
        by_cases hc : S ∈ P.core
        · exact Or.inl hc
        · let j : A := ⟨S,mem_sdiff.mpr ⟨hS,hc⟩⟩
          have hj := hex j
          change a j = c ∧ b j ≠ P.group c ∧ w j.val = s at hj
          exact Or.inr ⟨b j,hj.2.1, by rw [← hj.1]; exact shape j⟩
      · rintro (hS | ⟨i,hi,rfl⟩)
        · exact h.core_subset hS
        · obtain ⟨j,hj⟩ := allbases i hi
          have ha := (hex j).1
          change b j = i at hj
          change a j = c at ha
          have he := shape j
          rw [hj,ha] at he
          exact he ▸ (mem_sdiff.mp j.property).1
    · intro i hi
      obtain ⟨j,hj⟩ := allbases i hi
      have ha := (hex j).1
      have hw := (hex j).2.2
      change b j = i at hj
      change a j = c at ha
      change w j.val = s at hw
      rw [shape j,hj,ha] at hw
      exact hw

/-- The total real weight, independently of which classified form occurs. -/
theorem total_weight {H : Finset (Finset V)} {w : Finset V → ℝ} {K : ℝ}
    (h : Admissible P H w K) : (∑ S ∈ H, w S) = q*K := by
  have he : (∑ x : V, ∑ S ∈ H, if x ∈ S then w S else 0) =
      (q+1 : ℝ) * ∑ S ∈ H, w S := by
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro S hS
    rw [← sum_filter]
    simp [h.uniform S hS]
  simp_rw [h.load] at he
  simp only [sum_const, card_univ, nsmul_eq_mul, P.coordinates_card,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one] at he
  have hq : (0 : ℝ) < q+1 := by positivity
  nlinarith

end CoveringDesigns.TruncatedPlaneLoads
