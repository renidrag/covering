import CoveringDesigns.PairDivisibility.Classification
import CoveringDesigns.AffineConstructions.Transformations

/-! Actual primitive points, distinct coordinate blocks and uniform replication. -/
namespace CoveringDesigns.PairConsequences
open Finset PairEquality PairDivisibility TruncatedPlaneLoads
universe u v
variable {I : Type u} [Fintype I] [DecidableEq I]

def primitiveBlock (H : Finset (Finset I)) (i : I) : Finset H :=
  univ.filter (fun E => i ∈ E.val)

def primitiveFamily (H : Finset (Finset I)) : Family H := univ.image (primitiveBlock H)

omit [Fintype I] in
@[simp] theorem mem_primitiveBlock (H : Finset (Finset I)) (i : I) (E : H) :
    E ∈ primitiveBlock H i ↔ i ∈ E.val := by simp [primitiveBlock]

theorem primitive_block_card {q : ℕ} {H : Finset (Finset I)}
    (T : IsTwistedPlane q H) (i : I) : (primitiveBlock H i).card = q+1 := by
  have he : (primitiveBlock H i).card = PairEquality.degree H i := by
    simp only [primitiveBlock,PairEquality.degree,card_eq_sum_ones,sum_filter]
    exact sum_coe_sort H (fun E : Finset I => if i ∈ E then (1 : ℕ) else 0)
  exact he.trans (T.degree_eq i)

theorem primitive_blocks_injective {q : ℕ} {H : Finset (Finset I)}
    (hq : 2 ≤ q) (T : IsTwistedPlane q H) : Function.Injective (primitiveBlock H) := by
  intro i j he
  by_contra hij
  have hmem (E : Finset I) (hE : E ∈ H) : i ∈ E ↔ j ∈ E := by
    simpa only [mem_primitiveBlock] using
      (show (⟨E,hE⟩ : H) ∈ primitiveBlock H i ↔ ⟨E,hE⟩ ∈ primitiveBlock H j by rw [he])
  have hc : codegree H i j = PairEquality.degree H i := by
    unfold codegree PairEquality.degree
    congr 1
    ext E
    simp only [mem_filter]
    constructor
    · exact fun h => ⟨h.1,h.2.1⟩
    · exact fun h => ⟨h.1,h.2,(hmem E h.1).mp h.2⟩
  rw [T.degree_eq i,T.coordinate_codegree i j hij] at hc
  split_ifs at hc <;> omega

theorem primitive_cover {q : ℕ} {H : Finset (Finset I)}
    (T : IsTwistedPlane q H) : IsCover (primitiveFamily H) (q+1) 2 := by
  refine ⟨?_,?_⟩
  · intro B hB
    obtain ⟨i,_,rfl⟩ := mem_image.mp hB
    exact primitive_block_card T i
  · intro S hS
    obtain ⟨E,F,hEF,rfl⟩ := card_eq_two.mp hS
    obtain ⟨i,hi⟩ := T.intersect E.val E.property F.val F.property
      (fun h => hEF (Subtype.ext h))
    exact ⟨primitiveBlock H i,mem_image.mpr ⟨i,mem_univ _,rfl⟩,
      by simpa only [insert_subset_iff,singleton_subset_iff,mem_primitiveBlock,mem_inter] using hi⟩

theorem primitive_parameters {q : ℕ} {H : Finset (Finset I)}
    (hq : 2 ≤ q) (T : IsTwistedPlane q H) :
    Fintype.card H = q*(q+1) ∧ (primitiveFamily H).card = q*(q+1) ∧
      IsCover (primitiveFamily H) (q+1) 2 := by
  refine ⟨by simpa using T.supports,?_,primitive_cover T⟩
  rw [primitiveFamily,card_image_of_injective _ (primitive_blocks_injective hq T),card_univ,T.coordinates]

/-- Quotient of the actual twisted branch; original coordinates remain the
block indices, and the first component of the equivalence is the actual support. -/
theorem twisted_replication {X : Type v} [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 4 ≤ q)
    (hB : Multicover.IsCover B k 2 1) (T : IsTwistedPlane q (occupied B)) :
    0 < k/(q+1) ∧
      (∀ E ∈ occupied B, multiplicity B E = k/(q+1)) ∧
      ∃ e : X ≃ (occupied B) × Fin (k/(q+1)),
        (∀ p, (e p).1.val = support B p) ∧
        ∀ p i, (e p).1 ∈ primitiveBlock (occupied B) i ↔ p ∈ B i := by
  have hm (E : occupied B) : multiplicity B E.val = k/(q+1) := by
    have he := twisted_multiplicity hq T (multiplicity B)
      (fun x => (actual_load B x).trans (hB.1 x)) E
    rw [← he]
    simp
  have hp : 0 < k/(q+1) := by
    obtain ⟨E,hE⟩ := card_pos.mp (show 0 < (occupied B).card by rw [T.supports]; positivity)
    rw [← hm ⟨E,hE⟩]
    exact multiplicity_pos B hE
  let f : Point (occupied B) (multiplicity B) ≃ (occupied B) × Fin (k/(q+1)) :=
    (Equiv.sigmaCongrRight (fun E => finCongr (hm E))).trans (Equiv.sigmaEquivProd _ _)
  let e := (actualEquiv B).trans f
  refine ⟨hp,fun E hE => hm ⟨E,hE⟩,e,fun p => rfl,?_⟩
  intro p i
  rw [mem_primitiveBlock]
  change i ∈ support B p ↔ p ∈ B i
  exact mem_support B p i

theorem primitive_quotient {X : Type v} [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hi : Fintype.card I = q*(q+1))
    (hB : Multicover.IsCover B k 2 1) (hnd : ¬ q ∣ k) :
    Fintype.card (occupied B) = q*(q+1) ∧
      (primitiveFamily (occupied B)).card = q*(q+1) ∧
      IsCover (primitiveFamily (occupied B)) (q+1) 2 ∧
      Function.Injective (primitiveBlock (occupied B)) ∧
      0 < k/(q+1) ∧ (∀ E ∈ occupied B, multiplicity B E = k/(q+1)) ∧
      ∃ e : X ≃ (occupied B) × Fin (k/(q+1)),
        (∀ p, (e p).1.val = support B p) ∧
        ∀ p i, (e p).1 ∈ primitiveBlock (occupied B) i ↔ p ∈ B i := by
  have T := (twisted_of_not_dvd hq hk hv hi hB hnd).1
  obtain ⟨hc,hf,hcover⟩ := primitive_parameters (by omega) T
  exact ⟨hc,hf,hcover,primitive_blocks_injective (by omega) T,twisted_replication hq hB T⟩

/-- The premise is a universal nonexistence theorem, never a catalogue entry. -/
theorem indexed_primitive_exclusion {X : Type v} [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hB : Multicover.IsCover B k 2 1) (hnd : ¬ q ∣ k)
    (hn : ∀ {Y : Type u} [Fintype Y], Fintype.card Y = q*(q+1) →
      ∀ C : Family Y, IsCover C (q+1) 2 → C.card ≠ q*(q+1)) :
    q*(q+1)+1 ≤ Fintype.card I := by
  have hf := incidence_floor hq hk hv hB
  have he : Fintype.card I ≠ q*(q+1) := by
    intro hi
    obtain ⟨hc,hf,hcover,_⟩ := primitive_quotient hq hk hv hi hB hnd
    exact hn hc _ hcover hf
  omega

end CoveringDesigns.PairConsequences
