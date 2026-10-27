import CoveringDesigns.PairDivisibility.Adapter
import CoveringDesigns.TwistedArithmetic.OrderFour

/-! Short covering-level composition of the unchanged geometric and load
classification. Original points, supports and occurrence coordinates survive. -/
namespace CoveringDesigns.Qk_K_2
open TruncatedPlaneLoads PairEquality PairDivisibility

theorem twenty_description {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {t : ℕ} {B : I → Finset X}
    (ht : 1 ≤ t) (hv : Fintype.card X = 16*t) (hi : Fintype.card I = 20)
    (hB : Multicover.IsCover B (4*t) 2 1) :
    ∃ P : Plane 4 I (Fin 5), P.core ⊆ occupied B ∧
      NatDescription P (occupied B) (multiplicity B) t ∧
      ∃ e : X ≃ Point (occupied B) (multiplicity B),
        (∀ p, (e p).1.val = support B p) ∧
        ∀ p i, e p ∈ block (occupied B) (multiplicity B) i ↔ p ∈ B i := by
  have hv' : Fintype.card X = 4*(4*t) := by omega
  rcases geometric_dichotomy (by decide : 4 ≤ 4)
      (normalized_loads (by decide) (by omega) hv' hi hB) with ⟨P,hP⟩ | T
  · obtain ⟨_,s,hs,he,hd⟩ := actual_classification P (by decide) (by omega) hv' hB hP
    have : s = t := by omega
    subst s
    exact ⟨P,hP,hd,actualEquiv B,actualEquiv_support B,actualEquiv_incidence B⟩
  · exact (TwistedArithmetic.no_twisted_four T).elim

theorem twenty_unit_pure {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 16) (hi : Fintype.card I = 20)
    (hB : Multicover.IsCover B 4 2 1) :
    ∃ P : Plane 4 I (Fin 5), occupied B = P.core ∧
      ∀ E ∈ P.core, multiplicity B E = 1 := by
  obtain ⟨P,_,hd,_⟩ := twenty_description (t := 1) (by decide) hv hi hB
  rcases hd with hp | ⟨c,s,hs,hst,_⟩
  · exact ⟨P,hp⟩
  · omega

/-- Every prescribed form yields exactly twenty distinct blocks on arbitrary
labels. The expanded blocks and point/occurrence transports remain public. -/
theorem twenty_converse {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (P : Plane 4 I (Fin 5)) {H : Finset (Finset I)} {m : Finset I → ℕ} {t : ℕ}
    (ht : 1 ≤ t) (hd : NatDescription P H m t) (hv : Fintype.card X = 16*t) :
    Fintype.card (Point H m) = 16*t ∧
      Multicover.IsCover (block H m) (4*t) 2 1 ∧ Function.Injective (block H m) ∧
      ∃ C : Family X, IsCover C (4*t) 2 ∧ C.card = 20 := by
  classical
  have ha := integer_converse P (by decide) (by omega) hd
  obtain ⟨C,hc,hC⟩ := expanded_on (by decide : 2 ≤ 4) ha (X := X) (by omega)
  exact ⟨by simpa only [← Nat.mul_assoc] using point_card ha,
    expanded_cover ha,blocks_injective (by decide) ha,C,hC,hc⟩

end CoveringDesigns.Qk_K_2
