import CoveringDesigns.PairDivisibility

/-! Complete expected public types and transitive foundational axioms. -/
universe u_1 u_2 u_3

namespace CoveringDesigns.AuditPairDivisibility
open Finset
/-- Expanded actual-cover contract, with no geometric or regularity premise. -/
theorem divisibility_explicit {I X : Type*} [Fintype I] [Fintype X]
    {q k : ℕ} (B : I → Finset X) (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hi : Fintype.card I = q*(q+1))
    (hu : ∀ i, (B i).card = k)
    (hc : ∀ S : Finset X, S.card = 2 → ∃ i, S ⊆ B i) : q ∣ k ∨ (q+1) ∣ k := by
  classical
  exact PairDivisibility.divisibility hq hk hv hi ⟨hu,(Multicover.covers_one_iff B 2).mpr hc⟩
#guard_standard_axioms divisibility_explicit
#print axioms divisibility_explicit
end CoveringDesigns.AuditPairDivisibility


#check (@CoveringDesigns.PairDivisibility.degree_floor :
∀ {I : Type u_1} {X : Type u_2} [inst : Fintype I] [DecidableEq I] [inst_2 : Fintype X] [inst_3 : DecidableEq X]
  {q k : ℕ} {B : I → Finset X},
  2 ≤ q →
    0 < k →
      Fintype.card X = q * k →
        CoveringDesigns.Multicover.IsCover B k 2 1 →
          ∀ (p : X), q + 1 ≤ (CoveringDesigns.TruncatedPlaneLoads.support B p).card)
#guard_standard_axioms CoveringDesigns.PairDivisibility.degree_floor
#print axioms CoveringDesigns.PairDivisibility.degree_floor

#check (@CoveringDesigns.PairDivisibility.incidence_floor :
∀ {I : Type u_1} {X : Type u_2} [inst : Fintype I] [DecidableEq I] [inst_2 : Fintype X] [inst_3 : DecidableEq X]
  {q k : ℕ} {B : I → Finset X},
  4 ≤ q → q ≤ k → Fintype.card X = q * k → CoveringDesigns.Multicover.IsCover B k 2 1 → q * (q + 1) ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairDivisibility.incidence_floor
#print axioms CoveringDesigns.PairDivisibility.incidence_floor

#check (@CoveringDesigns.PairDivisibility.equality_support_size :
∀ {I : Type u_1} {X : Type u_2} [inst : Fintype I] [DecidableEq I] [inst_2 : Fintype X] [inst_3 : DecidableEq X]
  {q k : ℕ} {B : I → Finset X},
  4 ≤ q →
    q ≤ k →
      Fintype.card X = q * k →
        Fintype.card I = q * (q + 1) →
          CoveringDesigns.Multicover.IsCover B k 2 1 →
            ∀ (p : X), (CoveringDesigns.TruncatedPlaneLoads.support B p).card = q + 1)
#guard_standard_axioms CoveringDesigns.PairDivisibility.equality_support_size
#print axioms CoveringDesigns.PairDivisibility.equality_support_size

#check (@CoveringDesigns.PairDivisibility.normalized_loads :
∀ {I : Type u_1} {X : Type u_2} [inst : Fintype I] [inst_1 : DecidableEq I] [inst_2 : Fintype X]
  [inst_3 : DecidableEq X] {q k : ℕ} {B : I → Finset X},
  4 ≤ q →
    q ≤ k →
      Fintype.card X = q * k →
        Fintype.card I = q * (q + 1) →
          CoveringDesigns.Multicover.IsCover B k 2 1 →
            CoveringDesigns.PairEquality.PositiveUnitLoads q (CoveringDesigns.TruncatedPlaneLoads.occupied B) fun E =>
              ↑(CoveringDesigns.TruncatedPlaneLoads.multiplicity B E) / ↑k)
#guard_standard_axioms CoveringDesigns.PairDivisibility.normalized_loads
#print axioms CoveringDesigns.PairDivisibility.normalized_loads

#check (@CoveringDesigns.PairDivisibility.twisted_of_not_dvd :
∀ {I : Type u_1} {X : Type u_2} [inst : Fintype I] [inst_1 : DecidableEq I] [inst_2 : Fintype X]
  [inst_3 : DecidableEq X] {q k : ℕ} {B : I → Finset X},
  4 ≤ q →
    q ≤ k →
      Fintype.card X = q * k →
        Fintype.card I = q * (q + 1) →
          CoveringDesigns.Multicover.IsCover B k 2 1 →
            ¬q ∣ k →
              CoveringDesigns.PairEquality.IsTwistedPlane q (CoveringDesigns.TruncatedPlaneLoads.occupied B) ∧
                ∀ E ∈ CoveringDesigns.TruncatedPlaneLoads.occupied B,
                  (q + 1) * CoveringDesigns.TruncatedPlaneLoads.multiplicity B E = k)
#guard_standard_axioms CoveringDesigns.PairDivisibility.twisted_of_not_dvd
#print axioms CoveringDesigns.PairDivisibility.twisted_of_not_dvd

#check (@CoveringDesigns.PairDivisibility.divisibility :
∀ {I : Type u_1} {X : Type u_2} [inst : Fintype I] [DecidableEq I] [inst_2 : Fintype X] [inst_3 : DecidableEq X]
  {q k : ℕ} {B : I → Finset X},
  4 ≤ q →
    q ≤ k →
      Fintype.card X = q * k →
        Fintype.card I = q * (q + 1) → CoveringDesigns.Multicover.IsCover B k 2 1 → q ∣ k ∨ q + 1 ∣ k)
#guard_standard_axioms CoveringDesigns.PairDivisibility.divisibility
#print axioms CoveringDesigns.PairDivisibility.divisibility

#check (@CoveringDesigns.PairDivisibility.improved_floor :
∀ {I : Type u_1} {X : Type u_2} [inst : Fintype I] [DecidableEq I] [inst_2 : Fintype X] [inst_3 : DecidableEq X]
  {q k : ℕ} {B : I → Finset X},
  4 ≤ q →
    q ≤ k →
      Fintype.card X = q * k →
        CoveringDesigns.Multicover.IsCover B k 2 1 → ¬q ∣ k → ¬q + 1 ∣ k → q * (q + 1) + 1 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairDivisibility.improved_floor
#print axioms CoveringDesigns.PairDivisibility.improved_floor

#check (@CoveringDesigns.PairDivisibility.family_divisibility :
∀ {X : Type u_2} [inst : Fintype X] {q k : ℕ} {C : CoveringDesigns.Family X},
  4 ≤ q →
    q ≤ k → Fintype.card X = q * k → Finset.card C = q * (q + 1) → CoveringDesigns.IsCover C k 2 → q ∣ k ∨ q + 1 ∣ k)
#guard_standard_axioms CoveringDesigns.PairDivisibility.family_divisibility
#print axioms CoveringDesigns.PairDivisibility.family_divisibility

#check (@CoveringDesigns.PairDivisibility.family_improved_floor :
∀ {X : Type u_2} [inst : Fintype X] {q k : ℕ} {C : CoveringDesigns.Family X},
  4 ≤ q →
    q ≤ k →
      Fintype.card X = q * k → CoveringDesigns.IsCover C k 2 → ¬q ∣ k → ¬q + 1 ∣ k → q * (q + 1) + 1 ≤ Finset.card C)
#guard_standard_axioms CoveringDesigns.PairDivisibility.family_improved_floor
#print axioms CoveringDesigns.PairDivisibility.family_improved_floor

#check (@CoveringDesigns.PairDivisibility.twisted_mate_equation :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q k : ℕ} {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H) (m : Finset I → ℕ),
  (∀ (x : I), (∑ E ∈ H, if x ∈ E then m E else 0) = k) → ∀ (E : ↥H), q * m ↑E + m ↑(T.supportMate E) = k)
#guard_standard_axioms CoveringDesigns.PairDivisibility.twisted_mate_equation
#print axioms CoveringDesigns.PairDivisibility.twisted_mate_equation

#check (@CoveringDesigns.PairDivisibility.twisted_multiplicity :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q k : ℕ} {H : Finset (Finset I)},
  4 ≤ q →
    CoveringDesigns.PairEquality.IsTwistedPlane q H →
      ∀ (m : Finset I → ℕ), (∀ (x : I), (∑ E ∈ H, if x ∈ E then m E else 0) = k) → ∀ (E : ↥H), (q + 1) * m ↑E = k)
#guard_standard_axioms CoveringDesigns.PairDivisibility.twisted_multiplicity
#print axioms CoveringDesigns.PairDivisibility.twisted_multiplicity
