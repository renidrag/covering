import CoveringDesigns.PairEquality

/-! Full public types, expanded hypotheses and actual twisted incidences. -/
universe u_1 u_2 u_3

#print CoveringDesigns.PairEquality.PositiveUnitLoads
#print CoveringDesigns.PairEquality.IsTwistedPlane
#print CoveringDesigns.TruncatedPlaneLoads.Plane
#print CoveringDesigns.TruncatedPlaneLoads.Admissible

namespace CoveringDesigns.AuditPairEquality
open Finset PairEquality

/-- The five input fields, with q≥4 separate and the original-coordinate
conclusion. No geometric or independence hypothesis is hidden in the input. -/
theorem geometric_explicit {I : Type*} [Fintype I] [DecidableEq I]
    {q : ℕ} (hq : 4 ≤ q) (H : Finset (Finset I)) (w : Finset I → ℝ)
    (hn : Fintype.card I = q*(q+1))
    (hu : ∀ E ∈ H, E.card = q+1)
    (hi : ∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).Nonempty)
    (hp : ∀ E ∈ H, 0 < w E)
    (hl : ∀ x, (∑ E ∈ H, if x ∈ E then w E else 0) = 1) :
    (∃ P : TruncatedPlaneLoads.Plane q I (Fin (q+1)), P.core ⊆ H) ∨
      IsTwistedPlane q H := geometric_dichotomy hq ⟨hn,hu,hi,hp,hl⟩

/-- The small twisted record entails both actual mate relations, coverage and
maximality. In particular the coordinate pair relation is a conclusion. -/
theorem twisted_explicit {I : Type*} [Fintype I] [DecidableEq I]
    {q : ℕ} (hq : 4 ≤ q) (H : Finset (Finset I))
    (hn : Fintype.card I = q*(q+1)) (hc : H.card = q*(q+1))
    (hu : ∀ E ∈ H, E.card = q+1)
    (hd : ∀ x, (H.filter (x ∈ ·)).card = q+1)
    (hi : ∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).Nonempty) :
    ∃ (μ : H → H) (ν : I → I),
      Function.Involutive μ ∧ (∀ E, μ E ≠ E) ∧
      Function.Involutive ν ∧ (∀ x, ν x ≠ x) ∧
      (∀ E F : H, E ≠ F → (E.val ∩ F.val).card = if F = μ E then 2 else 1) ∧
      (∀ x y, x ≠ y → (H.filter (fun E => x ∈ E ∧ y ∈ E)).card =
        if y = ν x then 2 else 1) ∧
      (∀ x y, x ≠ y → ∃ E ∈ H, x ∈ E ∧ y ∈ E) ∧
      ∀ S : Finset I, S.card = q+1 → (∀ E ∈ H, (S ∩ E).Nonempty) → S ∈ H := by
  let T : IsTwistedPlane q H := ⟨hn,hc,hu,hd,hi⟩
  exact ⟨T.supportMate,T.coordinateMate,T.supportMate_involutive,T.supportMate_ne,
    T.coordinateMate_involutive,T.coordinateMate_ne,T.support_intersection,
    T.coordinate_codegree,T.pair_covered,fun _ => T.maximal hq⟩

#guard_standard_axioms geometric_explicit twisted_explicit
#print axioms geometric_explicit
#print axioms twisted_explicit
end CoveringDesigns.AuditPairEquality


#check (@CoveringDesigns.PairEquality.indicator :
{I : Type u_1} → [DecidableEq I] → Finset I → I → ℝ)
#guard_standard_axioms CoveringDesigns.PairEquality.indicator
#print axioms CoveringDesigns.PairEquality.indicator

#check (@CoveringDesigns.PairEquality.indicator_injective :
∀ {I : Type u_1} [Fintype I] [inst : DecidableEq I], Function.Injective CoveringDesigns.PairEquality.indicator)
#guard_standard_axioms CoveringDesigns.PairEquality.indicator_injective
#print axioms CoveringDesigns.PairEquality.indicator_injective

#check (@CoveringDesigns.PairEquality.indicator_sum :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] (E : Finset I),
  ∑ x, CoveringDesigns.PairEquality.indicator E x = ↑E.card)
#guard_standard_axioms CoveringDesigns.PairEquality.indicator_sum
#print axioms CoveringDesigns.PairEquality.indicator_sum

#check (@CoveringDesigns.PairEquality.PositiveUnitLoads :
{I : Type u_1} → [Fintype I] → [DecidableEq I] → ℕ → Finset (Finset I) → (Finset I → ℝ) → Prop)
#guard_standard_axioms CoveringDesigns.PairEquality.PositiveUnitLoads
#print axioms CoveringDesigns.PairEquality.PositiveUnitLoads

#check (@CoveringDesigns.PairEquality.degree :
{I : Type u_1} → [DecidableEq I] → Finset (Finset I) → I → ℕ)
#guard_standard_axioms CoveringDesigns.PairEquality.degree
#print axioms CoveringDesigns.PairEquality.degree

#check (@CoveringDesigns.PairEquality.codegree :
{I : Type u_1} → [DecidableEq I] → Finset (Finset I) → I → I → ℕ)
#guard_standard_axioms CoveringDesigns.PairEquality.codegree
#print axioms CoveringDesigns.PairEquality.codegree

#check (@CoveringDesigns.PairEquality.degree_sum :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] (H : Finset (Finset I)),
  ∑ x, CoveringDesigns.PairEquality.degree H x = ∑ E ∈ H, E.card)
#guard_standard_axioms CoveringDesigns.PairEquality.degree_sum
#print axioms CoveringDesigns.PairEquality.degree_sum

#check (@CoveringDesigns.PairEquality.PositiveUnitLoads.meets :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w → ∀ {E F : Finset I}, E ∈ H → F ∈ H → (E ∩ F).Nonempty)
#guard_standard_axioms CoveringDesigns.PairEquality.PositiveUnitLoads.meets
#print axioms CoveringDesigns.PairEquality.PositiveUnitLoads.meets

#check (@CoveringDesigns.PairEquality.PositiveUnitLoads.total_weight :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w → ∑ E ∈ H, w E = ↑q)
#guard_standard_axioms CoveringDesigns.PairEquality.PositiveUnitLoads.total_weight
#print axioms CoveringDesigns.PairEquality.PositiveUnitLoads.total_weight

#check (@CoveringDesigns.PairEquality.PositiveUnitLoads.weight_bound :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w → ∀ {E : Finset I}, E ∈ H → ↑q * w E ≤ 1)
#guard_standard_axioms CoveringDesigns.PairEquality.PositiveUnitLoads.weight_bound
#print axioms CoveringDesigns.PairEquality.PositiveUnitLoads.weight_bound

#check (@CoveringDesigns.PairEquality.PositiveUnitLoads.degree_lower :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w → ∀ (x : I), q ≤ CoveringDesigns.PairEquality.degree H x)
#guard_standard_axioms CoveringDesigns.PairEquality.PositiveUnitLoads.degree_lower
#print axioms CoveringDesigns.PairEquality.PositiveUnitLoads.degree_lower

#check (@CoveringDesigns.PairEquality.PositiveUnitLoads.card_lower :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w → q * q ≤ H.card)
#guard_standard_axioms CoveringDesigns.PairEquality.PositiveUnitLoads.card_lower
#print axioms CoveringDesigns.PairEquality.PositiveUnitLoads.card_lower

#check (@CoveringDesigns.PairEquality.PositiveUnitLoads.saturated_of_degree :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
    ∀ {x : I}, CoveringDesigns.PairEquality.degree H x = q → ∀ {E : Finset I}, E ∈ H → x ∈ E → ↑q * w E = 1)
#guard_standard_axioms CoveringDesigns.PairEquality.PositiveUnitLoads.saturated_of_degree
#print axioms CoveringDesigns.PairEquality.PositiveUnitLoads.saturated_of_degree

#check (@CoveringDesigns.PairEquality.PositiveUnitLoads.saturated_intersection :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
    ∀ {E : Finset I}, E ∈ H → ↑q * w E = 1 → ∀ {F : Finset I}, F ∈ H → E ≠ F → (E ∩ F).card = 1)
#guard_standard_axioms CoveringDesigns.PairEquality.PositiveUnitLoads.saturated_intersection
#print axioms CoveringDesigns.PairEquality.PositiveUnitLoads.saturated_intersection

#check (@CoveringDesigns.PairEquality.geometric_dichotomy :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ},
  4 ≤ q →
    ∀ {H : Finset (Finset I)} {w : Finset I → ℝ},
      CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
        (∃ P : CoveringDesigns.TruncatedPlaneLoads.Plane q I (Fin (q+1)), P.core ⊆ H) ∨ CoveringDesigns.PairEquality.IsTwistedPlane q H)
#guard_standard_axioms CoveringDesigns.PairEquality.geometric_dichotomy
#print axioms CoveringDesigns.PairEquality.geometric_dichotomy

#check (@CoveringDesigns.PairEquality.admissible_of_core :
∀ {I : Type u_1} {G : Type u_2} [inst : Fintype I] [inst_1 : DecidableEq I] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
    ∀ (P : CoveringDesigns.TruncatedPlaneLoads.Plane q I G),
      P.core ⊆ H → CoveringDesigns.TruncatedPlaneLoads.Admissible P H w 1)
#guard_standard_axioms CoveringDesigns.PairEquality.admissible_of_core
#print axioms CoveringDesigns.PairEquality.admissible_of_core

#check (@CoveringDesigns.PairEquality.admissible_or_twisted :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ},
  4 ≤ q →
    ∀ {H : Finset (Finset I)} {w : Finset I → ℝ},
      CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
        (∃ P : CoveringDesigns.TruncatedPlaneLoads.Plane q I (Fin (q+1)), CoveringDesigns.TruncatedPlaneLoads.Admissible P H w 1) ∨ CoveringDesigns.PairEquality.IsTwistedPlane q H)
#guard_standard_axioms CoveringDesigns.PairEquality.admissible_or_twisted
#print axioms CoveringDesigns.PairEquality.admissible_or_twisted

#check (@CoveringDesigns.PairEquality.plane_of_degree_q :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ},
  0 < q →
    ∀ {H : Finset (Finset I)} {w : Finset I → ℝ},
      CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
        (LinearIndependent ℝ fun E : H => CoveringDesigns.PairEquality.indicator E.val) →
          (∃ x, CoveringDesigns.PairEquality.degree H x = q) → ∃ P : CoveringDesigns.TruncatedPlaneLoads.Plane q I (Fin (q+1)), P.core = H)
#guard_standard_axioms CoveringDesigns.PairEquality.plane_of_degree_q
#print axioms CoveringDesigns.PairEquality.plane_of_degree_q

#check (@CoveringDesigns.PairEquality.Internal.degree_q_everywhere :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ},
  0 < q →
    ∀ {H : Finset (Finset I)} {w : Finset I → ℝ},
      CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
        (LinearIndependent ℝ fun E : H => CoveringDesigns.PairEquality.indicator E.val) →
          (∃ x, CoveringDesigns.PairEquality.degree H x = q) →
            H.card = q * q ∧ ∀ (x : I), CoveringDesigns.PairEquality.degree H x = q)
#guard_standard_axioms CoveringDesigns.PairEquality.Internal.degree_q_everywhere
#print axioms CoveringDesigns.PairEquality.Internal.degree_q_everywhere

#check (@CoveringDesigns.PairEquality.Examples.pureWeight :
Finset (Fin 20) → ℝ)
#guard_standard_axioms CoveringDesigns.PairEquality.Examples.pureWeight
#print axioms CoveringDesigns.PairEquality.Examples.pureWeight

#check (@CoveringDesigns.PairEquality.Examples.extendedWeight :
Finset (Fin 20) → ℝ)
#guard_standard_axioms CoveringDesigns.PairEquality.Examples.extendedWeight
#print axioms CoveringDesigns.PairEquality.Examples.extendedWeight

#check (@CoveringDesigns.PairEquality.Examples.pure_unit_loads :
CoveringDesigns.PairEquality.PositiveUnitLoads 4 CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.core
  CoveringDesigns.PairEquality.Examples.pureWeight)
#guard_standard_axioms CoveringDesigns.PairEquality.Examples.pure_unit_loads
#print axioms CoveringDesigns.PairEquality.Examples.pure_unit_loads

#check (@CoveringDesigns.PairEquality.Examples.extended_unit_loads :
CoveringDesigns.PairEquality.PositiveUnitLoads 4 (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0)
  CoveringDesigns.PairEquality.Examples.extendedWeight)
#guard_standard_axioms CoveringDesigns.PairEquality.Examples.extended_unit_loads
#print axioms CoveringDesigns.PairEquality.Examples.extended_unit_loads

#check (@CoveringDesigns.PairEquality.Examples.pure_core_branch :
∃ P : CoveringDesigns.TruncatedPlaneLoads.Plane 4 (Fin 20) (Fin 5),
  CoveringDesigns.TruncatedPlaneLoads.Admissible P CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.core
    CoveringDesigns.PairEquality.Examples.pureWeight 1)
#guard_standard_axioms CoveringDesigns.PairEquality.Examples.pure_core_branch
#print axioms CoveringDesigns.PairEquality.Examples.pure_core_branch

#check (@CoveringDesigns.PairEquality.Examples.extended_degrees :
CoveringDesigns.PairEquality.degree (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0) 0 = 8 ∧
  CoveringDesigns.PairEquality.degree (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0) 1 = 4 ∧
    CoveringDesigns.PairEquality.degree (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0) 4 = 5)
#guard_standard_axioms CoveringDesigns.PairEquality.Examples.extended_degrees
#print axioms CoveringDesigns.PairEquality.Examples.extended_degrees

#check (@CoveringDesigns.PairEquality.Examples.extended_core_branch :
∃ P : CoveringDesigns.TruncatedPlaneLoads.Plane 4 (Fin 20) (Fin 5),
  CoveringDesigns.TruncatedPlaneLoads.Admissible P (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0)
    CoveringDesigns.PairEquality.Examples.extendedWeight 1)
#guard_standard_axioms CoveringDesigns.PairEquality.Examples.extended_core_branch
#print axioms CoveringDesigns.PairEquality.Examples.extended_core_branch

#check (@CoveringDesigns.PairEquality.Examples.positive_extra_retained :
CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extra 1 0 ∈
    CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0 ∧
  CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extra 1 0 ∉
      CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.core ∧
    CoveringDesigns.PairEquality.Examples.extendedWeight
        (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extra 1 0) =
      1 / 8)
#guard_standard_axioms CoveringDesigns.PairEquality.Examples.positive_extra_retained
#print axioms CoveringDesigns.PairEquality.Examples.positive_extra_retained

#check (@CoveringDesigns.PairEquality.Examples.double_intersection_allowed :
CoveringDesigns.TruncatedPlaneLoads.Examples.coreEdge 0 ∈
    CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0 ∧
  CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extra 1 0 ∈
      CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0 ∧
    (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extra 1 0 ∩
          CoveringDesigns.TruncatedPlaneLoads.Examples.coreEdge 0).card =
      2)
#guard_standard_axioms CoveringDesigns.PairEquality.Examples.double_intersection_allowed
#print axioms CoveringDesigns.PairEquality.Examples.double_intersection_allowed

#check (@CoveringDesigns.PairEquality.independent_subfamily :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ},
  0 < q →
    ∀ {H : Finset (Finset I)} {w : Finset I → ℝ},
      CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
        ∃ J : Finset (Finset I), J ⊆ H ∧
          ∃ a : Finset I → ℝ,
            CoveringDesigns.PairEquality.PositiveUnitLoads q J a ∧
              (LinearIndependent ℝ fun E : J => CoveringDesigns.PairEquality.indicator E.val) ∧ J.card ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairEquality.independent_subfamily
#print axioms CoveringDesigns.PairEquality.independent_subfamily

#check (@CoveringDesigns.PairEquality.Internal.starGroup :
{I : Type u_1} → [Fintype I] → [DecidableEq I] → Finset (Finset I) → I → Finset I)
#guard_standard_axioms CoveringDesigns.PairEquality.Internal.starGroup
#print axioms CoveringDesigns.PairEquality.Internal.starGroup

#check (@CoveringDesigns.PairEquality.Internal.mem_starGroup :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {H : Finset (Finset I)} {x y : I},
  y ∈ CoveringDesigns.PairEquality.Internal.starGroup H x ↔ y = x ∨ CoveringDesigns.PairEquality.codegree H x y = 0)
#guard_standard_axioms CoveringDesigns.PairEquality.Internal.mem_starGroup
#print axioms CoveringDesigns.PairEquality.Internal.mem_starGroup

#check (@CoveringDesigns.PairEquality.Internal.starGroup_card :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
    ∀ {x : I},
      CoveringDesigns.PairEquality.degree H x = q → (CoveringDesigns.PairEquality.Internal.starGroup H x).card = q)
#guard_standard_axioms CoveringDesigns.PairEquality.Internal.starGroup_card
#print axioms CoveringDesigns.PairEquality.Internal.starGroup_card

#check (@CoveringDesigns.PairEquality.Internal.starGroup_codegree :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
    ∀ {x y : I},
      CoveringDesigns.PairEquality.degree H x = q →
        x ≠ y →
          CoveringDesigns.PairEquality.codegree H x y =
            if y ∈ CoveringDesigns.PairEquality.Internal.starGroup H x then 0 else 1)
#guard_standard_axioms CoveringDesigns.PairEquality.Internal.starGroup_codegree
#print axioms CoveringDesigns.PairEquality.Internal.starGroup_codegree

#check (@CoveringDesigns.PairEquality.Internal.starGroup_transversal :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
    ∀ {x : I},
      CoveringDesigns.PairEquality.degree H x = q →
        ∀ {E : Finset I}, E ∈ H → (E ∩ CoveringDesigns.PairEquality.Internal.starGroup H x).card = 1)
#guard_standard_axioms CoveringDesigns.PairEquality.Internal.starGroup_transversal
#print axioms CoveringDesigns.PairEquality.Internal.starGroup_transversal

#check (@CoveringDesigns.PairEquality.Internal.starGroup_equal_or_disjoint :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
    ∀ {x y : I},
      CoveringDesigns.PairEquality.degree H x = q →
        CoveringDesigns.PairEquality.degree H y = q →
          CoveringDesigns.PairEquality.Internal.starGroup H x = CoveringDesigns.PairEquality.Internal.starGroup H y ∨
            Disjoint (CoveringDesigns.PairEquality.Internal.starGroup H x)
              (CoveringDesigns.PairEquality.Internal.starGroup H y))
#guard_standard_axioms CoveringDesigns.PairEquality.Internal.starGroup_equal_or_disjoint
#print axioms CoveringDesigns.PairEquality.Internal.starGroup_equal_or_disjoint

#check (@CoveringDesigns.PairEquality.IsTwistedPlane :
{I : Type u_1} → [Fintype I] → [DecidableEq I] → ℕ → Finset (Finset I) → Prop)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane

#check (@CoveringDesigns.PairEquality.twisted_of_no_degree_q :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)} {w : Finset I → ℝ},
  CoveringDesigns.PairEquality.PositiveUnitLoads q H w →
    (LinearIndependent ℝ fun E : H => CoveringDesigns.PairEquality.indicator E.val) →
      (∀ (x : I), CoveringDesigns.PairEquality.degree H x ≠ q) → CoveringDesigns.PairEquality.IsTwistedPlane q H)
#guard_standard_axioms CoveringDesigns.PairEquality.twisted_of_no_degree_q
#print axioms CoveringDesigns.PairEquality.twisted_of_no_degree_q

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.supportMate :
{I : Type u_1} →
  [inst : Fintype I] →
    [inst_1 : DecidableEq I] →
      {q : ℕ} → {H : Finset (Finset I)} → CoveringDesigns.PairEquality.IsTwistedPlane q H → ↥H → ↥H)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.supportMate
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.supportMate

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.supportMate_ne :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H) (E : ↥H), T.supportMate E ≠ E)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.supportMate_ne
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.supportMate_ne

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.supportMate_intersection :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H) (E : ↥H), (E.val ∩ (T.supportMate E).val).card = 2)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.supportMate_intersection
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.supportMate_intersection

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.support_intersection :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H) (E F : ↥H),
  E ≠ F → (E.val ∩ F.val).card = if F = T.supportMate E then 2 else 1)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.support_intersection
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.support_intersection

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.support_mate_unique :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H) (E F : ↥H), E ≠ F → (E.val ∩ F.val).card = 2 → F = T.supportMate E)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.support_mate_unique
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.support_mate_unique

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.supportMate_involutive :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H), Function.Involutive T.supportMate)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.supportMate_involutive
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.supportMate_involutive

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate :
{I : Type u_1} →
  [inst : Fintype I] →
    [inst_1 : DecidableEq I] →
      {q : ℕ} → {H : Finset (Finset I)} → CoveringDesigns.PairEquality.IsTwistedPlane q H → I → I)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate_ne :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H) (x : I), T.coordinateMate x ≠ x)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate_ne
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate_ne

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate_codegree :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H) (x : I),
  CoveringDesigns.PairEquality.codegree H x (T.coordinateMate x) = 2)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate_codegree
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate_codegree

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.coordinate_mate_unique :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H) (x y : I),
  x ≠ y → CoveringDesigns.PairEquality.codegree H x y = 2 → y = T.coordinateMate x)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinate_mate_unique
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinate_mate_unique

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate_involutive :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H), Function.Involutive T.coordinateMate)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate_involutive
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinateMate_involutive

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.coordinate_codegree :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H) (x y : I),
  x ≠ y → CoveringDesigns.PairEquality.codegree H x y = if y = T.coordinateMate x then 2 else 1)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinate_codegree
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.coordinate_codegree

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.pair_covered :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)},
  CoveringDesigns.PairEquality.IsTwistedPlane q H → ∀ (x y : I), x ≠ y → ∃ E ∈ H, x ∈ E ∧ y ∈ E)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.pair_covered
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.pair_covered

#check (@CoveringDesigns.PairEquality.IsTwistedPlane.maximal :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {q : ℕ} {H : Finset (Finset I)},
  CoveringDesigns.PairEquality.IsTwistedPlane q H →
    4 ≤ q → ∀ {S : Finset I}, S.card = q + 1 → (∀ E ∈ H, (S ∩ E).Nonempty) → S ∈ H)
#guard_standard_axioms CoveringDesigns.PairEquality.IsTwistedPlane.maximal
#print axioms CoveringDesigns.PairEquality.IsTwistedPlane.maximal
