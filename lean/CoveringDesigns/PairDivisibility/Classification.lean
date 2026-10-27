import CoveringDesigns.PairDivisibility.Adapter
import CoveringDesigns.PairDivisibility.TwistedLoads

namespace CoveringDesigns.PairDivisibility
open Finset TruncatedPlaneLoads PairEquality
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
variable {q k : ℕ} {B : I → Finset X}

/-- If q does not divide k, equality has the actual twisted support geometry,
and its original multiplicities satisfy (q+1)m(E)=k. -/
theorem twisted_of_not_dvd (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hi : Fintype.card I = q*(q+1))
    (hB : Multicover.IsCover B k 2 1) (hnd : ¬ q ∣ k) :
    IsTwistedPlane q (occupied B) ∧
      ∀ E ∈ occupied B, (q+1)*multiplicity B E = k := by
  rcases geometric_dichotomy hq (normalized_loads hq hk hv hi hB) with ⟨P,hP⟩|T
  · exact (hnd (actual_classification P hq (by omega) hv hB hP).1).elim
  · refine ⟨T,fun E hE => ?_⟩
    exact twisted_multiplicity hq T (multiplicity B)
      (fun x => (actual_load B x).trans (hB.1 x)) ⟨E,hE⟩

/-- Unconditional necessary divisibility at the incidence floor. No
injectivity, geometry, regularity or prime-power premise is supplied. -/
theorem divisibility (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hi : Fintype.card I = q*(q+1))
    (hB : Multicover.IsCover B k 2 1) : q ∣ k ∨ (q+1) ∣ k := by
  by_cases hqk : q ∣ k
  · exact Or.inl hqk
  · obtain ⟨T,hm⟩ := twisted_of_not_dvd hq hk hv hi hB hqk
    have hpos : 0 < (occupied B).card := by rw [T.supports]; positivity
    obtain ⟨E,hE⟩ := card_pos.mp hpos
    exact Or.inr ⟨multiplicity B E,(hm E hE).symm⟩

theorem improved_floor (hq : 4 ≤ q) (hk : q ≤ k) (hv : Fintype.card X = q*k)
    (hB : Multicover.IsCover B k 2 1) (hnd : ¬ q ∣ k) (hnd' : ¬ (q+1) ∣ k) :
    q*(q+1)+1 ≤ Fintype.card I := by
  have hf := incidence_floor hq hk hv hB
  have hn : Fintype.card I ≠ q*(q+1) := by
    intro he
    exact (divisibility hq hk hv he hB).elim hnd hnd'
  omega

omit [DecidableEq X] in
theorem family_divisibility {C : Family X} (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hc : C.card = q*(q+1)) (hC : IsCover C k 2) :
    q ∣ k ∨ (q+1) ∣ k := by
  classical
  exact divisibility hq hk hv (by simpa using hc)
    ((Multicover.ofFamily_isCover_one C k 2).mpr hC)

omit [DecidableEq X] in
theorem family_improved_floor {C : Family X} (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hC : IsCover C k 2)
    (hnd : ¬ q ∣ k) (hnd' : ¬ (q+1) ∣ k) : q*(q+1)+1 ≤ C.card := by
  classical
  simpa using improved_floor hq hk hv
    ((Multicover.ofFamily_isCover_one C k 2).mpr hC) hnd hnd'

end CoveringDesigns.PairDivisibility
