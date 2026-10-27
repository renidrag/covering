import CoveringDesigns.PairConsequences.Arithmetic

/-! General actual equality descriptions; no choice of a unique core. -/
namespace CoveringDesigns.PairConsequences
open TruncatedPlaneLoads PairEquality PairDivisibility

theorem equality_description {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {q k : ℕ} {B : I → Finset X}
    (hq : 4 ≤ q) (hk : q ≤ k) (hv : Fintype.card X = q*k)
    (hi : Fintype.card I = q*(q+1)) (hB : Multicover.IsCover B k 2 1)
    (hn : ∀ {H : Finset (Finset I)}, IsTwistedPlane q H → False) :
    ∃ P : Plane q I (Fin (q+1)), P.core ⊆ occupied B ∧
      ∃ t : ℕ, 0 < t ∧ k = q*t ∧
        NatDescription P (occupied B) (multiplicity B) t ∧
        ∃ e : X ≃ Point (occupied B) (multiplicity B),
          (∀ p, (e p).1.val = support B p) ∧
          ∀ p i, e p ∈ block (occupied B) (multiplicity B) i ↔ p ∈ B i := by
  rcases geometric_dichotomy hq (normalized_loads hq hk hv hi hB) with ⟨P,hP⟩ | T
  · obtain ⟨_,t,ht,hk',hd⟩ := actual_classification P hq (by omega) hv hB hP
    exact ⟨P,hP,t,ht,hk',hd,actualEquiv B,actualEquiv_support B,actualEquiv_incidence B⟩
  · exact (hn T).elim

theorem determinant_equality_description {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {q k : ℕ} {B : I → Finset X}
    (hq : 4 ≤ q) (hk : q ≤ k) (hv : Fintype.card X = q*k)
    (hi : Fintype.card I = q*(q+1)) (hB : Multicover.IsCover B k 2 1)
    (hn : ¬ IsSquare (determinantValue q)) :
    ∃ P : Plane q I (Fin (q+1)), P.core ⊆ occupied B ∧
      ∃ t : ℕ, 0 < t ∧ k = q*t ∧
        NatDescription P (occupied B) (multiplicity B) t ∧
        ∃ e : X ≃ Point (occupied B) (multiplicity B),
          (∀ p, (e p).1.val = support B p) ∧
          ∀ p i, e p ∈ block (occupied B) (multiplicity B) i ↔ p ∈ B i := by
  apply equality_description hq hk hv hi hB
  intro H T
  apply hn
  exact ⟨(TwistedArithmetic.squareIncidence T).det,
    by simpa [determinantValue,pow_two] using (Qk_K_2.twisted_determinant (by omega) T).symm⟩

theorem equality_converse {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    {q t : ℕ} (P : Plane q I (Fin (q+1))) {H : Finset (Finset I)} {m : Finset I → ℕ}
    (hq : 4 ≤ q) (ht : 0 < t) (hd : NatDescription P H m t)
    (hv : Fintype.card X = q*(q*t)) :
    Fintype.card (Point H m) = q*(q*t) ∧
      Multicover.IsCover (block H m) (q*t) 2 1 ∧ Function.Injective (block H m) ∧
      ∃ C : Family X, IsCover C (q*t) 2 ∧ C.card = q*(q+1) := by
  classical
  have ha := integer_converse P hq ht hd
  obtain ⟨C,hc,hC⟩ := expanded_on (by omega : 2 ≤ q) ha hv
  exact ⟨point_card ha,expanded_cover ha,blocks_injective (by omega) ha,C,hC,hc⟩

end CoveringDesigns.PairConsequences
