import CoveringDesigns.PairConstructions

/-! Complete expected public types and transitive foundational axioms. -/
universe u_1 u_2 u_3

namespace CoveringDesigns.AuditPairConstructions
/-- The output is an ordinary family on the prescribed point type. -/
theorem weighted_explicit {α : Type*} [Fintype α] {q u r : ℕ}
    (hq : IsPrimePow q) (hq2 : 2 ≤ q) (hr : 1 ≤ r) (hru : r ≤ u)
    (hv : Fintype.card α = q*(q*u+r)) :
    ∃ C : Finset (Finset α), (∀ B ∈ C, B.card = q*u+r) ∧
      (∀ S : Finset α, S.card = 2 → ∃ B ∈ C, S ⊆ B) ∧ C.card ≤ q*q+q+1 := by
  obtain ⟨C,hC,hb⟩ := PairConstructions.weighted_projective hq hq2 hr hru hv
  exact ⟨C,hC.1,hC.2,hb⟩
#guard_standard_axioms weighted_explicit
#print axioms weighted_explicit
end CoveringDesigns.AuditPairConstructions


#check (@CoveringDesigns.PairConstructions.projective_line_intersection :
∀ {F : Type u_1} [inst : Field F] [inst_1 : Fintype F]
  [inst_2 : DecidableEq (CoveringDesigns.ProjectiveHyperplanes.Point F 3)]
  (d e : CoveringDesigns.ProjectiveHyperplanes.Direction F 3),
  d ≠ e →
    (CoveringDesigns.ProjectiveHyperplanes.hyperplane d ∩ CoveringDesigns.ProjectiveHyperplanes.hyperplane e).card = 1)
#guard_standard_axioms CoveringDesigns.PairConstructions.projective_line_intersection
#print axioms CoveringDesigns.PairConstructions.projective_line_intersection

#check (@CoveringDesigns.PairConstructions.weighted_projective :
∀ {α : Type u_1} [inst : Fintype α] {q u r : ℕ},
  IsPrimePow q →
    2 ≤ q →
      1 ≤ r →
        r ≤ u →
          Fintype.card α = q * (q * u + r) →
            ∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C (q * u + r) 2 ∧ Finset.card C ≤ q * q + q + 1)
#guard_standard_axioms CoveringDesigns.PairConstructions.weighted_projective
#print axioms CoveringDesigns.PairConstructions.weighted_projective
