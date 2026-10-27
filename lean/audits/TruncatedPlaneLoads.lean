import CoveringDesigns.TruncatedPlaneLoads

/-! Complete declaration types and transitive axioms, including the raw incidence
contract, actual identities, converse and boundary checks. -/

universe u_1 u_2 u_3 u_4

#print CoveringDesigns.TruncatedPlaneLoads.Plane
#print CoveringDesigns.TruncatedPlaneLoads.Admissible
#print CoveringDesigns.TruncatedPlaneLoads.Description
#print CoveringDesigns.TruncatedPlaneLoads.NatAdmissible
#print CoveringDesigns.TruncatedPlaneLoads.NatDescription

namespace CoveringDesigns.AuditTruncatedPlaneLoads
open Finset TruncatedPlaneLoads

/-- Expanded primary contract: no classification or load conclusion is
hidden in the family hypotheses. The separate Plane print fixes its axioms. -/
theorem real_explicit {V G : Type*} [Fintype V] [DecidableEq V]
    [Fintype G] [DecidableEq G] {q : ℕ} (P : Plane q V G) (hq : 4 ≤ q)
    (H : Finset (Finset V)) (w : Finset V → ℝ) (K : ℝ)
    (hc : P.core ⊆ H) (hu : ∀ S ∈ H, S.card = q+1)
    (hi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty)
    (hp : ∀ S ∈ H, 0 < w S)
    (hl : ∀ x, (∑ S ∈ H, if x ∈ S then w S else 0) = K) (hK : 0 < K) :
    (H = P.core ∧ ∀ E ∈ P.core, w E = K/q) ∨
    ∃ c : V, ∃ s : ℝ, 0 < s ∧ s < K/q ∧
      (∀ S, S ∈ H ↔ S ∈ P.core ∨ ∃ i, i ≠ P.group c ∧ S = P.extra i c) ∧
      (∀ i, i ≠ P.group c → w (P.extra i c) = s) ∧
      ∀ E ∈ P.core, w E = if c ∈ E then K/q-s else K/q :=
  real_classification P hq ⟨hc,hu,hi,hp,hl,hK⟩

theorem integer_explicit {V G : Type*} [Fintype V] [DecidableEq V]
    [Fintype G] [DecidableEq G] {q : ℕ} (P : Plane q V G) (hq : 4 ≤ q)
    (H : Finset (Finset V)) (m : Finset V → ℕ) (K : ℕ)
    (hc : P.core ⊆ H) (hu : ∀ S ∈ H, S.card = q+1)
    (hi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty)
    (hp : ∀ S ∈ H, 0 < m S)
    (hl : ∀ x, (∑ S ∈ H, if x ∈ S then m S else 0) = K) (hK : 0 < K) :
    q ∣ K ∧ ∃ t : ℕ, 0 < t ∧ K = q*t ∧
      ((H = P.core ∧ ∀ E ∈ P.core, m E = t) ∨
      ∃ c : V, ∃ s : ℕ, 1 ≤ s ∧ s < t ∧
        (∀ S, S ∈ H ↔ S ∈ P.core ∨ ∃ i, i ≠ P.group c ∧ S = P.extra i c) ∧
        (∀ i, i ≠ P.group c → m (P.extra i c) = s) ∧
        ∀ E ∈ P.core, m E = if c ∈ E then t-s else t) := by
  have h : NatAdmissible P H m K := ⟨hc,hu,hi,hp,hl,hK⟩
  exact ⟨load_divisible P hq h,integer_classification P hq h⟩

#guard_standard_axioms real_explicit integer_explicit
#print axioms real_explicit
#print axioms integer_explicit
end CoveringDesigns.AuditTruncatedPlaneLoads

#check (@CoveringDesigns.TruncatedPlaneLoads.support :
{V : Type u_1} → {X : Type u_3} → [Fintype V] → [DecidableEq X] → (V → Finset X) → X → Finset V)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.support
#print axioms CoveringDesigns.TruncatedPlaneLoads.support

#check (@CoveringDesigns.TruncatedPlaneLoads.occupied :
{V : Type u_1} →
  {X : Type u_3} → [Fintype V] → [DecidableEq V] → [Fintype X] → [DecidableEq X] → (V → Finset X) → Finset (Finset V))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.occupied
#print axioms CoveringDesigns.TruncatedPlaneLoads.occupied

#check (@CoveringDesigns.TruncatedPlaneLoads.multiplicity :
{V : Type u_1} →
  {X : Type u_3} → [Fintype V] → [DecidableEq V] → [Fintype X] → [DecidableEq X] → (V → Finset X) → Finset V → ℕ)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.multiplicity
#print axioms CoveringDesigns.TruncatedPlaneLoads.multiplicity

#check (@CoveringDesigns.TruncatedPlaneLoads.mem_support :
∀ {V : Type u_1} {X : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq X] (B : V → Finset X) (p : X) (x : V),
  x ∈ CoveringDesigns.TruncatedPlaneLoads.support B p ↔ p ∈ B x)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.mem_support
#print axioms CoveringDesigns.TruncatedPlaneLoads.mem_support

#check (@CoveringDesigns.TruncatedPlaneLoads.support_occupied :
∀ {V : Type u_1} {X : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype X]
  [inst_3 : DecidableEq X] (B : V → Finset X) (p : X),
  CoveringDesigns.TruncatedPlaneLoads.support B p ∈ CoveringDesigns.TruncatedPlaneLoads.occupied B)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.support_occupied
#print axioms CoveringDesigns.TruncatedPlaneLoads.support_occupied

#check (@CoveringDesigns.TruncatedPlaneLoads.multiplicity_pos :
∀ {V : Type u_1} {X : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype X]
  [inst_3 : DecidableEq X] (B : V → Finset X) {S : Finset V},
  S ∈ CoveringDesigns.TruncatedPlaneLoads.occupied B → 0 < CoveringDesigns.TruncatedPlaneLoads.multiplicity B S)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.multiplicity_pos
#print axioms CoveringDesigns.TruncatedPlaneLoads.multiplicity_pos

#check (@CoveringDesigns.TruncatedPlaneLoads.actual_load :
∀ {V : Type u_1} {X : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype X]
  [inst_3 : DecidableEq X] (B : V → Finset X) (x : V),
  (∑ S ∈ CoveringDesigns.TruncatedPlaneLoads.occupied B,
      if x ∈ S then CoveringDesigns.TruncatedPlaneLoads.multiplicity B S else 0) =
    (B x).card)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.actual_load
#print axioms CoveringDesigns.TruncatedPlaneLoads.actual_load

#check (@CoveringDesigns.TruncatedPlaneLoads.actual_support_size :
∀ {V : Type u_1} {G : Type u_2} {X : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] [inst_4 : Fintype X] [inst_5 : DecidableEq X] {q : ℕ}
  (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {B : V → Finset X} {K : ℕ},
  2 ≤ q →
    0 < K →
      Fintype.card X = q * K →
        CoveringDesigns.Multicover.IsCover B K 2 1 →
          ∀ (p : X), (CoveringDesigns.TruncatedPlaneLoads.support B p).card = q + 1)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.actual_support_size
#print axioms CoveringDesigns.TruncatedPlaneLoads.actual_support_size

#check (@CoveringDesigns.TruncatedPlaneLoads.actual_admissible :
∀ {V : Type u_1} {G : Type u_2} {X : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] [inst_4 : Fintype X] [inst_5 : DecidableEq X] {q : ℕ}
  (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {B : V → Finset X} {K : ℕ},
  4 ≤ q →
    0 < K →
      Fintype.card X = q * K →
        CoveringDesigns.Multicover.IsCover B K 2 1 →
          P.core ⊆ CoveringDesigns.TruncatedPlaneLoads.occupied B →
            CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P (CoveringDesigns.TruncatedPlaneLoads.occupied B)
              (CoveringDesigns.TruncatedPlaneLoads.multiplicity B) K)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.actual_admissible
#print axioms CoveringDesigns.TruncatedPlaneLoads.actual_admissible

#check (@CoveringDesigns.TruncatedPlaneLoads.actual_classification :
∀ {V : Type u_1} {G : Type u_2} {X : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] [inst_4 : Fintype X] [inst_5 : DecidableEq X] {q : ℕ}
  (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {B : V → Finset X} {K : ℕ},
  4 ≤ q →
    0 < K →
      Fintype.card X = q * K →
        CoveringDesigns.Multicover.IsCover B K 2 1 →
          P.core ⊆ CoveringDesigns.TruncatedPlaneLoads.occupied B →
            q ∣ K ∧
              ∃ t,
                0 < t ∧
                  K = q * t ∧
                    CoveringDesigns.TruncatedPlaneLoads.NatDescription P
                      (CoveringDesigns.TruncatedPlaneLoads.occupied B)
                      (CoveringDesigns.TruncatedPlaneLoads.multiplicity B) t)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.actual_classification
#print axioms CoveringDesigns.TruncatedPlaneLoads.actual_classification

#check (@CoveringDesigns.TruncatedPlaneLoads.actualEquiv :
{V : Type u_1} →
  {X : Type u_3} →
    [inst : Fintype V] →
      [inst_1 : DecidableEq V] →
        [inst_2 : Fintype X] →
          [inst_3 : DecidableEq X] →
            (B : V → Finset X) →
              X ≃
                CoveringDesigns.TruncatedPlaneLoads.Point (CoveringDesigns.TruncatedPlaneLoads.occupied B)
                  (CoveringDesigns.TruncatedPlaneLoads.multiplicity B))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.actualEquiv
#print axioms CoveringDesigns.TruncatedPlaneLoads.actualEquiv

#check (@CoveringDesigns.TruncatedPlaneLoads.actualEquiv_support :
∀ {V : Type u_1} {X : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype X]
  [inst_3 : DecidableEq X] (B : V → Finset X) (p : X),
  ↑((CoveringDesigns.TruncatedPlaneLoads.actualEquiv B) p).fst = CoveringDesigns.TruncatedPlaneLoads.support B p)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.actualEquiv_support
#print axioms CoveringDesigns.TruncatedPlaneLoads.actualEquiv_support

#check (@CoveringDesigns.TruncatedPlaneLoads.actualEquiv_incidence :
∀ {V : Type u_1} {X : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype X]
  [inst_3 : DecidableEq X] (B : V → Finset X) (p : X) (x : V),
  (CoveringDesigns.TruncatedPlaneLoads.actualEquiv B) p ∈
      CoveringDesigns.TruncatedPlaneLoads.block (CoveringDesigns.TruncatedPlaneLoads.occupied B)
        (CoveringDesigns.TruncatedPlaneLoads.multiplicity B) x ↔
    p ∈ B x)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.actualEquiv_incidence
#print axioms CoveringDesigns.TruncatedPlaneLoads.actualEquiv_incidence

#check (@CoveringDesigns.TruncatedPlaneLoads.support_reindex :
∀ {V : Type u_1} {X : Type u_3} [inst : Fintype V] [DecidableEq V] [Fintype X] [inst_3 : DecidableEq X]
  (B : V → Finset X) {J : Type u_4} [inst_4 : Fintype J] [DecidableEq J] (e : J ≃ V) (p : X),
  CoveringDesigns.TruncatedPlaneLoads.support (B ∘ ⇑e) p =
    Finset.map e.symm.toEmbedding (CoveringDesigns.TruncatedPlaneLoads.support B p))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.support_reindex
#print axioms CoveringDesigns.TruncatedPlaneLoads.support_reindex

#check (@CoveringDesigns.TruncatedPlaneLoads.support_relabel :
∀ {V : Type u_1} {X : Type u_3} [inst : Fintype V] [DecidableEq V] [Fintype X] [inst_3 : DecidableEq X]
  (B : V → Finset X) {Y : Type u_4} [inst_4 : DecidableEq Y] (e : X ≃ Y) (p : X),
  CoveringDesigns.TruncatedPlaneLoads.support (fun x => Finset.map e.toEmbedding (B x)) (e p) =
    CoveringDesigns.TruncatedPlaneLoads.support B p)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.support_relabel
#print axioms CoveringDesigns.TruncatedPlaneLoads.support_relabel

#check (@CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.classify :
∀ {V : Type u_1} {G : Type u_2} {I : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] [inst_4 : Fintype I] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} {K : ℝ}
  (D : CoveringDesigns.TruncatedPlaneLoads.Internal.Loads P K),
  4 ≤ q →
    (IsEmpty I ∧ ∀ E ∈ P.core, D.coreWeight E = K / ↑q) ∨
      ∃ c s,
        0 < s ∧
          s < K / ↑q ∧
            (∀ (j : I), D.tip j = c ∧ D.base j ≠ P.group c ∧ D.weight j = s) ∧
              (∀ (i : G), i ≠ P.group c → ∃ j, D.base j = i) ∧
                ∀ E ∈ P.core, D.coreWeight E = if c ∈ E then K / ↑q - s else K / ↑q)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.classify
#print axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.classify

#check (@CoveringDesigns.TruncatedPlaneLoads.common_coordinate :
∀ {V : Type u_1} {G : Type u_2} {I : Type u_3} [inst : DecidableEq G] [inst_1 : Fintype I] (g : V → G) (b : I → G)
  (a : I → V),
  (∀ (u : I), g (a u) ≠ b u) →
    (∀ (u v : I), b u ≠ b v → g (a u) = b v ∨ g (a v) = b u ∨ a u = a v) →
      4 ≤ (Finset.image b Finset.univ).card → ∃ c, ∀ (u : I), b u = g c ∨ a u = c)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.common_coordinate
#print axioms CoveringDesigns.TruncatedPlaneLoads.common_coordinate

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extension :
{V : Type u_1} →
  {G : Type u_2} →
    [inst : Fintype V] →
      [inst_1 : DecidableEq V] →
        [inst_2 : Fintype G] →
          [inst_3 : DecidableEq G] → {q : ℕ} → CoveringDesigns.TruncatedPlaneLoads.Plane q V G → V → Finset (Finset V))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extension
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extension

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.mem_extension :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) (c : V) (S : Finset V),
  S ∈ P.extension c ↔ S ∈ P.core ∨ ∃ i, i ≠ P.group c ∧ S = P.extra i c)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.mem_extension
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.mem_extension

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extra_base_injective :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  2 ≤ q → ∀ {c : V} {i j : G}, i ≠ P.group c → j ≠ P.group c → P.extra i c = P.extra j c → i = j)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_base_injective
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_base_injective

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extension_sum :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  2 ≤ q →
    ∀ (c : V) (f : Finset V → ℝ),
      ∑ S ∈ P.extension c, f S = ∑ E ∈ P.core, f E + ∑ i with i ≠ P.group c, f (P.extra i c))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extension_sum
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extension_sum

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.core_intersects :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {E F : Finset V},
  E ∈ P.core → F ∈ P.core → (E ∩ F).Nonempty)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.core_intersects
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.core_intersects

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extension_intersects :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) (c : V) {S T : Finset V},
  S ∈ P.extension c → T ∈ P.extension c → (S ∩ T).Nonempty)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extension_intersects
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extension_intersects

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extensionWeight :
{V : Type u_1} →
  {G : Type u_2} →
    [inst : Fintype V] →
      [inst_1 : DecidableEq V] →
        [inst_2 : Fintype G] →
          [inst_3 : DecidableEq G] →
            {q : ℕ} → CoveringDesigns.TruncatedPlaneLoads.Plane q V G → V → ℝ → ℝ → Finset V → ℝ)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extensionWeight
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extensionWeight

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.pure_converse :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {t : ℝ},
  0 < t → 0 < q → CoveringDesigns.TruncatedPlaneLoads.Admissible P P.core (fun x => t) (↑q * t))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.pure_converse
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.pure_converse

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extension_converse :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  2 ≤ q →
    ∀ (c : V) {t s : ℝ},
      0 < s →
        s < t → CoveringDesigns.TruncatedPlaneLoads.Admissible P (P.extension c) (P.extensionWeight c t s) (↑q * t))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extension_converse
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extension_converse

#check (@CoveringDesigns.TruncatedPlaneLoads.description_converse :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  4 ≤ q →
    ∀ {H : Finset (Finset V)} {w : Finset V → ℝ} {t : ℝ},
      0 < t →
        CoveringDesigns.TruncatedPlaneLoads.Description P H w t →
          CoveringDesigns.TruncatedPlaneLoads.Admissible P H w (↑q * t))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.description_converse
#print axioms CoveringDesigns.TruncatedPlaneLoads.description_converse

#check (@CoveringDesigns.TruncatedPlaneLoads.real_classification_iff :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  4 ≤ q →
    ∀ {H : Finset (Finset V)} {w : Finset V → ℝ} {K : ℝ},
      0 < K →
        (CoveringDesigns.TruncatedPlaneLoads.Admissible P H w K ↔
          CoveringDesigns.TruncatedPlaneLoads.Description P H w (K / ↑q)))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.real_classification_iff
#print axioms CoveringDesigns.TruncatedPlaneLoads.real_classification_iff

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extra_group_card :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {i j : G} {a : V},
  P.group a ≠ i → {x ∈ P.extra i a | P.group x = j}.card = (if i = j then q else 0) + if P.group a = j then 1 else 0)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_group_card
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_group_card

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extra_edge_card :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {i : G} {a : V},
  P.group a ≠ i → ∀ {E : Finset V}, E ∈ P.core → (E ∩ P.extra i a).card = 1 + if a ∈ E then 1 else 0)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_edge_card
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_edge_card

#check (@CoveringDesigns.TruncatedPlaneLoads.Internal.Loads :
{V : Type u_1} →
  {G : Type u_2} →
    {I : Type u_3} →
      [inst : Fintype V] →
        [inst_1 : DecidableEq V] →
          [inst_2 : Fintype G] →
            [inst_3 : DecidableEq G] →
              {q : ℕ} →
                [Fintype I] → CoveringDesigns.TruncatedPlaneLoads.Plane q V G → ℝ → Type (max (max u_1 u_2) u_3))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads
#print axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads

#check (@CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.coreMass :
{V : Type u_1} →
  {G : Type u_2} →
    {I : Type u_3} →
      [inst : Fintype V] →
        [inst_1 : DecidableEq V] →
          [inst_2 : Fintype G] →
            [inst_3 : DecidableEq G] →
              {q : ℕ} →
                {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} →
                  [inst_4 : Fintype I] → {K : ℝ} → CoveringDesigns.TruncatedPlaneLoads.Internal.Loads P K → ℝ)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.coreMass
#print axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.coreMass

#check (@CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.extraMass :
{V : Type u_1} →
  {G : Type u_2} →
    {I : Type u_3} →
      [inst : Fintype V] →
        [inst_1 : DecidableEq V] →
          [inst_2 : Fintype G] →
            [inst_3 : DecidableEq G] →
              {q : ℕ} →
                {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} →
                  [inst_4 : Fintype I] → {K : ℝ} → CoveringDesigns.TruncatedPlaneLoads.Internal.Loads P K → ℝ)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.extraMass
#print axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.extraMass

#check (@CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.baseMass :
{V : Type u_1} →
  {G : Type u_2} →
    {I : Type u_3} →
      [inst : Fintype V] →
        [inst_1 : DecidableEq V] →
          [inst_2 : Fintype G] →
            [inst_3 : DecidableEq G] →
              {q : ℕ} →
                {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} →
                  [inst_4 : Fintype I] → {K : ℝ} → CoveringDesigns.TruncatedPlaneLoads.Internal.Loads P K → G → ℝ)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.baseMass
#print axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.baseMass

#check (@CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.tipMass :
{V : Type u_1} →
  {G : Type u_2} →
    {I : Type u_3} →
      [inst : Fintype V] →
        [inst_1 : DecidableEq V] →
          [inst_2 : Fintype G] →
            [inst_3 : DecidableEq G] →
              {q : ℕ} →
                {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} →
                  [inst_4 : Fintype I] → {K : ℝ} → CoveringDesigns.TruncatedPlaneLoads.Internal.Loads P K → G → ℝ)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.tipMass
#print axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.tipMass

#check (@CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.edgeMass :
{V : Type u_1} →
  {G : Type u_2} →
    {I : Type u_3} →
      [inst : Fintype V] →
        [inst_1 : DecidableEq V] →
          [inst_2 : Fintype G] →
            [inst_3 : DecidableEq G] →
              {q : ℕ} →
                {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} →
                  [inst_4 : Fintype I] →
                    {K : ℝ} → CoveringDesigns.TruncatedPlaneLoads.Internal.Loads P K → Finset V → ℝ)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.edgeMass
#print axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.edgeMass

#check (@CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.sum_load :
∀ {V : Type u_1} {G : Type u_2} {I : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} [inst_4 : Fintype I] {K : ℝ}
  (D : CoveringDesigns.TruncatedPlaneLoads.Internal.Loads P K) (S : Finset V),
  ↑S.card * K =
    ∑ E ∈ P.core, ↑(S ∩ E).card * D.coreWeight E + ∑ j, ↑(S ∩ P.extra (D.base j) (D.tip j)).card * D.weight j)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.sum_load
#print axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.sum_load

#check (@CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.total_mass :
∀ {V : Type u_1} {G : Type u_2} {I : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} [inst_4 : Fintype I] {K : ℝ}
  (D : CoveringDesigns.TruncatedPlaneLoads.Internal.Loads P K), D.coreMass + D.extraMass = ↑q * K)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.total_mass
#print axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.total_mass

#check (@CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.group_equation :
∀ {V : Type u_1} {G : Type u_2} {I : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} [inst_4 : Fintype I] {K : ℝ}
  (D : CoveringDesigns.TruncatedPlaneLoads.Internal.Loads P K) (i : G), ↑q * D.baseMass i + D.tipMass i = D.extraMass)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.group_equation
#print axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.group_equation

#check (@CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.core_equation :
∀ {V : Type u_1} {G : Type u_2} {I : Type u_3} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} [inst_4 : Fintype I] {K : ℝ}
  (D : CoveringDesigns.TruncatedPlaneLoads.Internal.Loads P K) {E : Finset V},
  E ∈ P.core → ↑q * D.coreWeight E + D.edgeMass E = K)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.core_equation
#print axioms CoveringDesigns.TruncatedPlaneLoads.Internal.Loads.core_equation

#check (@CoveringDesigns.TruncatedPlaneLoads.Point :
{V : Type u_1} → Finset (Finset V) → (Finset V → ℕ) → Type (max u_1 0))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Point
#print axioms CoveringDesigns.TruncatedPlaneLoads.Point

#check (@CoveringDesigns.TruncatedPlaneLoads.block :
{V : Type u_1} →
  [DecidableEq V] →
    (H : Finset (Finset V)) → (m : Finset V → ℕ) → V → Finset (CoveringDesigns.TruncatedPlaneLoads.Point H m))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.block
#print axioms CoveringDesigns.TruncatedPlaneLoads.block

#check (@CoveringDesigns.TruncatedPlaneLoads.mem_block :
∀ {V : Type u_1} [Fintype V] [inst : DecidableEq V] (H : Finset (Finset V)) (m : Finset V → ℕ) (x : V)
  (p : CoveringDesigns.TruncatedPlaneLoads.Point H m), p ∈ CoveringDesigns.TruncatedPlaneLoads.block H m x ↔ x ∈ (p.fst.val : Finset V))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.mem_block
#print axioms CoveringDesigns.TruncatedPlaneLoads.mem_block

#check (@CoveringDesigns.TruncatedPlaneLoads.point_card :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} {H : Finset (Finset V)}
  {m : Finset V → ℕ} {K : ℕ},
  CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K →
    Fintype.card (CoveringDesigns.TruncatedPlaneLoads.Point H m) = q * K)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.point_card
#print axioms CoveringDesigns.TruncatedPlaneLoads.point_card

#check (@CoveringDesigns.TruncatedPlaneLoads.block_card :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} {H : Finset (Finset V)}
  {m : Finset V → ℕ} {K : ℕ},
  CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K →
    ∀ (x : V), (CoveringDesigns.TruncatedPlaneLoads.block H m x).card = K)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.block_card
#print axioms CoveringDesigns.TruncatedPlaneLoads.block_card

#check (@CoveringDesigns.TruncatedPlaneLoads.expanded_cover :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} {H : Finset (Finset V)}
  {m : Finset V → ℕ} {K : ℕ},
  CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K →
    CoveringDesigns.Multicover.IsCover (CoveringDesigns.TruncatedPlaneLoads.block H m) K 2 1)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.expanded_cover
#print axioms CoveringDesigns.TruncatedPlaneLoads.expanded_cover

#check (@CoveringDesigns.TruncatedPlaneLoads.blocks_injective :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G},
  2 ≤ q →
    ∀ {H : Finset (Finset V)} {m : Finset V → ℕ} {K : ℕ},
      CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K →
        Function.Injective (CoveringDesigns.TruncatedPlaneLoads.block H m))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.blocks_injective
#print axioms CoveringDesigns.TruncatedPlaneLoads.blocks_injective

#check (@CoveringDesigns.TruncatedPlaneLoads.expandedFamily :
{V : Type u_1} →
  [Fintype V] →
    [DecidableEq V] →
      (H : Finset (Finset V)) →
        (m : Finset V → ℕ) → CoveringDesigns.Family (CoveringDesigns.TruncatedPlaneLoads.Point H m))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.expandedFamily
#print axioms CoveringDesigns.TruncatedPlaneLoads.expandedFamily

#check (@CoveringDesigns.TruncatedPlaneLoads.expanded_family_card :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G},
  2 ≤ q →
    ∀ {H : Finset (Finset V)} {m : Finset V → ℕ} {K : ℕ},
      CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K →
        Finset.card (CoveringDesigns.TruncatedPlaneLoads.expandedFamily H m) = q * (q + 1))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.expanded_family_card
#print axioms CoveringDesigns.TruncatedPlaneLoads.expanded_family_card

#check (@CoveringDesigns.TruncatedPlaneLoads.expanded_family_cover :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} {H : Finset (Finset V)}
  {m : Finset V → ℕ} {K : ℕ},
  CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K →
    CoveringDesigns.IsCover (CoveringDesigns.TruncatedPlaneLoads.expandedFamily H m) K 2)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.expanded_family_cover
#print axioms CoveringDesigns.TruncatedPlaneLoads.expanded_family_cover

#check (@CoveringDesigns.TruncatedPlaneLoads.expanded_on :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G},
  2 ≤ q →
    ∀ {H : Finset (Finset V)} {m : Finset V → ℕ} {K : ℕ},
      CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K →
        ∀ {X : Type u_3} [inst : Fintype X] [DecidableEq X],
          Fintype.card X = q * K → ∃ C, Finset.card C = q * (q + 1) ∧ CoveringDesigns.IsCover C K 2)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.expanded_on
#print axioms CoveringDesigns.TruncatedPlaneLoads.expanded_on

#check (@CoveringDesigns.TruncatedPlaneLoads.expanded_reindex :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} {H : Finset (Finset V)}
  {m : Finset V → ℕ} {K : ℕ},
  CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K →
    ∀ {J : Type u_3} [inst : Fintype J] (e : J ≃ V),
      Fintype.card J = q * (q + 1) ∧
        CoveringDesigns.Multicover.IsCover (CoveringDesigns.TruncatedPlaneLoads.block H m ∘ ⇑e) K 2 1)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.expanded_reindex
#print axioms CoveringDesigns.TruncatedPlaneLoads.expanded_reindex

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.coreEdge :
Fin 16 → Finset (Fin 20))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.coreEdge
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.coreEdge

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.group4 :
Fin 20 → Fin 5)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.group4
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.group4

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.core4 :
Finset (Finset (Fin 20)))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.core4
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.core4

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.plane4 :
CoveringDesigns.TruncatedPlaneLoads.Plane 4 (Fin 20) (Fin 5))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.plane4
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.plane4

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.pure4 :
CoveringDesigns.TruncatedPlaneLoads.NatAdmissible CoveringDesigns.TruncatedPlaneLoads.Examples.plane4
  CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.core (fun x => 1) 4)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.pure4
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.pure4

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.multiplicity4 :
Finset (Fin 20) → ℕ)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.multiplicity4
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.multiplicity4

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.extended4 :
CoveringDesigns.TruncatedPlaneLoads.NatAdmissible CoveringDesigns.TruncatedPlaneLoads.Examples.plane4
  (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0)
  CoveringDesigns.TruncatedPlaneLoads.Examples.multiplicity4 8)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.extended4
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.extended4

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.pure_counts :
Fintype.card
      (CoveringDesigns.TruncatedPlaneLoads.Point CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.core fun x => 1) =
    16 ∧
  Finset.card
        (CoveringDesigns.TruncatedPlaneLoads.expandedFamily CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.core
          fun x => 1) =
      20 ∧
    CoveringDesigns.IsCover
      (CoveringDesigns.TruncatedPlaneLoads.expandedFamily CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.core
        fun x => 1)
      4 2)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.pure_counts
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.pure_counts

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.extended_counts :
Fintype.card
      (CoveringDesigns.TruncatedPlaneLoads.Point (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0)
        CoveringDesigns.TruncatedPlaneLoads.Examples.multiplicity4) =
    32 ∧
  Finset.card
        (CoveringDesigns.TruncatedPlaneLoads.expandedFamily
          (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0)
          CoveringDesigns.TruncatedPlaneLoads.Examples.multiplicity4) =
      20 ∧
    CoveringDesigns.Multicover.IsCover
        (CoveringDesigns.TruncatedPlaneLoads.block (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0)
          CoveringDesigns.TruncatedPlaneLoads.Examples.multiplicity4)
        8 2 1 ∧
      CoveringDesigns.IsCover
        (CoveringDesigns.TruncatedPlaneLoads.expandedFamily
          (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0)
          CoveringDesigns.TruncatedPlaneLoads.Examples.multiplicity4)
        8 2)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.extended_counts
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.extended_counts

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.two_coordinate_intersection :
CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extra 1 0 ∈
    CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0 ∧
  CoveringDesigns.TruncatedPlaneLoads.Examples.coreEdge 0 ∈ CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.core ∧
    (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extra 1 0 ∩
          CoveringDesigns.TruncatedPlaneLoads.Examples.coreEdge 0).card =
      2)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.two_coordinate_intersection
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.two_coordinate_intersection

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.unit_case :
∀ {H : Finset (Finset (Fin 20))} {m : Finset (Fin 20) → ℕ},
  CoveringDesigns.TruncatedPlaneLoads.NatAdmissible CoveringDesigns.TruncatedPlaneLoads.Examples.plane4 H m 4 →
    H = CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.core ∧
      ∀ E ∈ CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.core, m E = 1)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.unit_case
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.unit_case

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.relabelled_extended :
∃ C : CoveringDesigns.Family (Fin 32), Finset.card C = 20 ∧ CoveringDesigns.IsCover C 8 2)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.relabelled_extended
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.relabelled_extended

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.permuted_occurrences :
CoveringDesigns.Multicover.IsCover
  (CoveringDesigns.TruncatedPlaneLoads.block (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0)
      CoveringDesigns.TruncatedPlaneLoads.Examples.multiplicity4 ∘
    ⇑(Equiv.swap 0 19))
  8 2 1)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.permuted_occurrences
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.permuted_occurrences

#check (@CoveringDesigns.TruncatedPlaneLoads.Examples.twins_exist :
∃ p r : CoveringDesigns.TruncatedPlaneLoads.Point
    (CoveringDesigns.TruncatedPlaneLoads.Examples.plane4.extension 0)
    CoveringDesigns.TruncatedPlaneLoads.Examples.multiplicity4,
  p ≠ r ∧ p.fst = r.fst)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Examples.twins_exist
#print axioms CoveringDesigns.TruncatedPlaneLoads.Examples.twins_exist

#check (@CoveringDesigns.TruncatedPlaneLoads.Admissible :
{V : Type u_1} →
  {G : Type u_2} →
    [inst : Fintype V] →
      [inst_1 : DecidableEq V] →
        [inst_2 : Fintype G] →
          [inst_3 : DecidableEq G] →
            {q : ℕ} → CoveringDesigns.TruncatedPlaneLoads.Plane q V G → Finset (Finset V) → (Finset V → ℝ) → ℝ → Prop)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Admissible
#print axioms CoveringDesigns.TruncatedPlaneLoads.Admissible

#check (@CoveringDesigns.TruncatedPlaneLoads.Description :
{V : Type u_1} →
  {G : Type u_2} →
    [inst : Fintype V] →
      [inst_1 : DecidableEq V] →
        [inst_2 : Fintype G] →
          [inst_3 : DecidableEq G] →
            {q : ℕ} → CoveringDesigns.TruncatedPlaneLoads.Plane q V G → Finset (Finset V) → (Finset V → ℝ) → ℝ → Prop)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Description
#print axioms CoveringDesigns.TruncatedPlaneLoads.Description

#check (@CoveringDesigns.TruncatedPlaneLoads.real_classification :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  4 ≤ q →
    ∀ {H : Finset (Finset V)} {w : Finset V → ℝ} {K : ℝ},
      CoveringDesigns.TruncatedPlaneLoads.Admissible P H w K →
        CoveringDesigns.TruncatedPlaneLoads.Description P H w (K / ↑q))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.real_classification
#print axioms CoveringDesigns.TruncatedPlaneLoads.real_classification

#check (@CoveringDesigns.TruncatedPlaneLoads.total_weight :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {H : Finset (Finset V)}
  {w : Finset V → ℝ} {K : ℝ}, CoveringDesigns.TruncatedPlaneLoads.Admissible P H w K → ∑ S ∈ H, w S = ↑q * K)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.total_weight
#print axioms CoveringDesigns.TruncatedPlaneLoads.total_weight

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane :
ℕ →
  (V : Type u_3) → (G : Type u_4) → [Fintype V] → [DecidableEq V] → [Fintype G] → [DecidableEq G] → Type (max u_3 u_4))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.groupSet :
{V : Type u_1} →
  {G : Type u_2} →
    [inst : Fintype V] →
      [inst_1 : DecidableEq V] →
        [inst_2 : Fintype G] →
          [inst_3 : DecidableEq G] → {q : ℕ} → CoveringDesigns.TruncatedPlaneLoads.Plane q V G → G → Finset V)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.groupSet
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.groupSet

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.mem_groupSet :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) (i : G) (x : V),
  x ∈ P.groupSet i ↔ P.group x = i)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.mem_groupSet
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.mem_groupSet

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.groupSet_card :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) (i : G),
  (P.groupSet i).card = q)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.groupSet_card
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.groupSet_card

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.coordinates_card :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G), Fintype.card V = q * (q + 1))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.coordinates_card
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.coordinates_card

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.core_size :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {E : Finset V},
  E ∈ P.core → E.card = q + 1)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.core_size
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.core_size

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.core_card :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G), P.core.card = q * q)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.core_card
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.core_card

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.same_group :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {E : Finset V},
  E ∈ P.core → ∀ {x y : V}, x ∈ E → y ∈ E → P.group x = P.group y → x = y)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.same_group
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.same_group

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.join :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {x y : V},
  P.group x ≠ P.group y → ∃ E ∈ P.core, x ∈ E ∧ y ∈ E)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.join
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.join

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.core_avoiding :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  2 ≤ q → ∀ (c : V), ∃ E ∈ P.core, c ∉ E)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.core_avoiding
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.core_avoiding

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.distinguish :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  2 ≤ q → ∀ {x y : V}, x ≠ y → ∃ E ∈ P.core, x ∈ E ∧ y ∉ E)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.distinguish
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.distinguish

#check (@CoveringDesigns.TruncatedPlaneLoads.NatAdmissible :
{V : Type u_1} →
  {G : Type u_2} →
    [inst : Fintype V] →
      [inst_1 : DecidableEq V] →
        [inst_2 : Fintype G] →
          [inst_3 : DecidableEq G] →
            {q : ℕ} → CoveringDesigns.TruncatedPlaneLoads.Plane q V G → Finset (Finset V) → (Finset V → ℕ) → ℕ → Prop)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.NatAdmissible
#print axioms CoveringDesigns.TruncatedPlaneLoads.NatAdmissible

#check (@CoveringDesigns.TruncatedPlaneLoads.NatDescription :
{V : Type u_1} →
  {G : Type u_2} →
    [inst : Fintype V] →
      [inst_1 : DecidableEq V] →
        [inst_2 : Fintype G] →
          [inst_3 : DecidableEq G] →
            {q : ℕ} → CoveringDesigns.TruncatedPlaneLoads.Plane q V G → Finset (Finset V) → (Finset V → ℕ) → ℕ → Prop)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.NatDescription
#print axioms CoveringDesigns.TruncatedPlaneLoads.NatDescription

#check (@CoveringDesigns.TruncatedPlaneLoads.NatAdmissible.toReal :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} {H : Finset (Finset V)}
  {m : Finset V → ℕ} {K : ℕ},
  CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K →
    CoveringDesigns.TruncatedPlaneLoads.Admissible P H (fun S => ↑(m S)) ↑K)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.NatAdmissible.toReal
#print axioms CoveringDesigns.TruncatedPlaneLoads.NatAdmissible.toReal

#check (@CoveringDesigns.TruncatedPlaneLoads.NatAdmissible.mass :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} {P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G} {H : Finset (Finset V)}
  {m : Finset V → ℕ} {K : ℕ}, CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K → ∑ S ∈ H, m S = q * K)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.NatAdmissible.mass
#print axioms CoveringDesigns.TruncatedPlaneLoads.NatAdmissible.mass

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.other_group :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  0 < q → ∀ (c : V), ∃ i, i ≠ P.group c)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.other_group
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.other_group

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.core_nonempty :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G), 0 < q → P.core.Nonempty)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.core_nonempty
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.core_nonempty

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extension_ne_core :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  2 ≤ q → ∀ (c : V), P.extension c ≠ P.core)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extension_ne_core
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extension_ne_core

#check (@CoveringDesigns.TruncatedPlaneLoads.integer_classification :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  4 ≤ q →
    ∀ {H : Finset (Finset V)} {m : Finset V → ℕ} {K : ℕ},
      CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K →
        ∃ t, 0 < t ∧ K = q * t ∧ CoveringDesigns.TruncatedPlaneLoads.NatDescription P H m t)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.integer_classification
#print axioms CoveringDesigns.TruncatedPlaneLoads.integer_classification

#check (@CoveringDesigns.TruncatedPlaneLoads.load_divisible :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  4 ≤ q →
    ∀ {H : Finset (Finset V)} {m : Finset V → ℕ} {K : ℕ},
      CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m K → q ∣ K)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.load_divisible
#print axioms CoveringDesigns.TruncatedPlaneLoads.load_divisible

#check (@CoveringDesigns.TruncatedPlaneLoads.unit_load_pure :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  4 ≤ q →
    ∀ {H : Finset (Finset V)} {m : Finset V → ℕ},
      CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m q → H = P.core ∧ ∀ E ∈ P.core, m E = 1)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.unit_load_pure
#print axioms CoveringDesigns.TruncatedPlaneLoads.unit_load_pure

#check (@CoveringDesigns.TruncatedPlaneLoads.integer_converse :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  4 ≤ q →
    ∀ {H : Finset (Finset V)} {m : Finset V → ℕ} {t : ℕ},
      0 < t →
        CoveringDesigns.TruncatedPlaneLoads.NatDescription P H m t →
          CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P H m (q * t))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.integer_converse
#print axioms CoveringDesigns.TruncatedPlaneLoads.integer_converse

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.naturalWeight :
{V : Type u_1} →
  {G : Type u_2} →
    [inst : Fintype V] →
      [inst_1 : DecidableEq V] →
        [inst_2 : Fintype G] →
          [inst_3 : DecidableEq G] →
            {q : ℕ} → CoveringDesigns.TruncatedPlaneLoads.Plane q V G → V → ℕ → ℕ → Finset V → ℕ)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.naturalWeight
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.naturalWeight

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.natural_pure :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  4 ≤ q → ∀ {t : ℕ}, 0 < t → CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P P.core (fun x => t) (q * t))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.natural_pure
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.natural_pure

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.natural_extension :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  4 ≤ q →
    ∀ (c : V) {t s : ℕ},
      1 ≤ s →
        s < t → CoveringDesigns.TruncatedPlaneLoads.NatAdmissible P (P.extension c) (P.naturalWeight c t s) (q * t))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.natural_extension
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.natural_extension

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extra :
{V : Type u_1} →
  {G : Type u_2} →
    [inst : Fintype V] →
      [inst_1 : DecidableEq V] →
        [inst_2 : Fintype G] →
          [inst_3 : DecidableEq G] → {q : ℕ} → CoveringDesigns.TruncatedPlaneLoads.Plane q V G → G → V → Finset V)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.mem_extra :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) (i : G) (a x : V),
  x ∈ P.extra i a ↔ x = a ∨ P.group x = i)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.mem_extra
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.mem_extra

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extra_size :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {i : G} {a : V},
  P.group a ≠ i → (P.extra i a).card = q + 1)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_size
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_size

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extra_core_meet :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {E : Finset V},
  E ∈ P.core → ∀ (i : G) (a : V), (P.extra i a ∩ E).Nonempty)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_core_meet
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_core_meet

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extra_not_core :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  2 ≤ q → ∀ {i : G} {a : V}, P.extra i a ∉ P.core)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_not_core
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_not_core

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.extra_intersection :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G) {i j : G} {a b : V},
  i ≠ j → ((P.extra i a ∩ P.extra j b).Nonempty ↔ P.group a = j ∨ P.group b = i ∨ a = b))
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_intersection
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.extra_intersection

#check (@CoveringDesigns.TruncatedPlaneLoads.Plane.support_classification :
∀ {V : Type u_1} {G : Type u_2} [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : Fintype G]
  [inst_3 : DecidableEq G] {q : ℕ} (P : CoveringDesigns.TruncatedPlaneLoads.Plane q V G),
  2 ≤ q →
    ∀ {S : Finset V},
      S.card = q + 1 → (∀ E ∈ P.core, (E ∩ S).Nonempty) → S ∈ P.core ∨ ∃ i a, P.group a ≠ i ∧ S = P.extra i a)
#guard_standard_axioms CoveringDesigns.TruncatedPlaneLoads.Plane.support_classification
#print axioms CoveringDesigns.TruncatedPlaneLoads.Plane.support_classification
