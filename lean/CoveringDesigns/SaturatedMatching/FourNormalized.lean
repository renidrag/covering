import CoveringDesigns.SaturatedMatching.Pattern
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! The small-intersection calculation once the four-row signs are normalized.
Normalization from free signatures is supplied by FourNormalize and Four.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
variable {B : ι → Finset α} (P : Pattern (M := Fin 4) B)

def normalizedSigns : Fin 4 → Fin 4 → Bool :=
  ![![true,false,true,false], ![true,true,true,false],
    ![true,false,true,true], ![true,false,false,true]]

/-- Every unmatched actual point misses the selected supporting intersection.
The proof applies pointwise, without any injectivity of incidence rows. -/
theorem normalized_unmatched
    (hsign : ∀ e f, e ≠ f → P.sign e f = normalizedSigns e f)
    (hdeg : ∀ f b, indexedDegree B (P.point (f,b)) = 6)
    (hpair : ∀ x f b, x ≠ P.point (f,b) → x ≠ P.point (f,!b) →
      3 ≤ indexedSubsetDegree B {x,P.point (f,b)})
    (x : α) (hx : ∀ e b, x ≠ P.point (e,b)) :
    x ∉ B (P.block (0,true)) ∩ B (P.block (1,true)) := by
  intro hmem
  obtain ⟨h0,h1⟩ := mem_inter.mp hmem
  have hn0 : x ∉ B (P.block (0,false)) := (P.outside x hx 0).mp h0
  have hn1 : x ∉ B (P.block (1,false)) := (P.outside x hx 1).mp h1
  have lower (f : Fin 4) (b : Bool) :=
    P.four_named_lower (by simp) hdeg f b x (hpair x f b (hx f b) (hx f (!b)))
  have h3 : x ∈ B (P.block (3,true)) := by
    by_contra hn3
    have hh := lower 2 false
    simp only [Fin.sum_univ_succ,P.matched] at hh
    simp [hsign,normalizedSigns,h0,h1,hn0,hn1,hn3] at hh
    have hx2 := P.outside x hx 2
    split_ifs at hh <;> simp_all
  have hn3 : x ∉ B (P.block (3,false)) := (P.outside x hx 3).mp h3
  have h2 : x ∈ B (P.block (2,true)) := by
    by_contra hn2
    have hh := lower 3 true
    simp only [Fin.sum_univ_succ,P.matched] at hh
    simp [hsign,normalizedSigns,h0,h1,hn0,hn1,hn2,h3,hn3] at hh
  have hn2 : x ∉ B (P.block (2,false)) := (P.outside x hx 2).mp h2
  have hh := lower 0 false
  simp only [Fin.sum_univ_succ,P.matched] at hh
  simp [hsign,normalizedSigns,h0,h1,h2,h3,hn0,hn1,hn2,hn3] at hh

/-- The normalized supporting intersection consists of exactly four
matched points and no unmatched point. -/
theorem normalized_small_intersection
    (hsign : ∀ e f, e ≠ f → P.sign e f = normalizedSigns e f)
    (hdeg : ∀ f b, indexedDegree B (P.point (f,b)) = 6)
    (hpair : ∀ x f b, x ≠ P.point (f,b) → x ≠ P.point (f,!b) →
      3 ≤ indexedSubsetDegree B {x,P.point (f,b)}) :
    (B (P.block (0,true)) ∩ B (P.block (1,true))).card = 4 := by
  classical
  let S : Finset (Fin 4 × Bool) := {(0,true),(1,false),(2,true),(3,false)}
  have he : B (P.block (0,true)) ∩ B (P.block (1,true)) = S.image P.point := by
    ext x
    by_cases hx : ∃ e b, x = P.point (e,b)
    · obtain ⟨e,b,rfl⟩ := hx
      have him : P.point (e,b) ∈ S.image P.point ↔ (e,b) ∈ S := by
        constructor
        · intro h
          obtain ⟨z,hz,he⟩ := mem_image.mp h
          exact P.point_injective he ▸ hz
        · exact mem_image_of_mem _
      rw [him]
      fin_cases e <;> cases b <;>
        simp [S,mem_inter,P.matched,hsign,normalizedSigns]
    · have hn : ∀ e b, x ≠ P.point (e,b) := by simpa only [not_exists] using hx
      have hnot := normalized_unmatched P hsign hdeg hpair x hn
      have hi : x ∉ S.image P.point := by
        intro h
        obtain ⟨⟨e,b⟩,_,he⟩ := mem_image.mp h
        exact hx ⟨e,b,he.symm⟩
      simp [hnot,hi]
  rw [he,card_image_of_injective _ P.point_injective]
  decide

end CoveringDesigns.SaturatedMatching
