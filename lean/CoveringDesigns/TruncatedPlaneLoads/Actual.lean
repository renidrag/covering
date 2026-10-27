import CoveringDesigns.TruncatedPlaneLoads.Covering

/-! A conditional adapter for actual pair coverings carrying a positive core.
Occurrence and point identities are retained throughout. -/

namespace CoveringDesigns.TruncatedPlaneLoads
open Finset
variable {V G X : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable [Fintype X] [DecidableEq X] {q : ℕ} (P : Plane q V G)

def support (B : V → Finset X) (p : X) : Finset V := univ.filter (p ∈ B ·)
def occupied (B : V → Finset X) : Finset (Finset V) := univ.image (support B)
def multiplicity (B : V → Finset X) (S : Finset V) : ℕ :=
  (univ.filter (support B · = S)).card

omit [DecidableEq V] [Fintype X] in
@[simp] theorem mem_support (B : V → Finset X) (p : X) (x : V) :
    x ∈ support B p ↔ p ∈ B x := by simp [support]

theorem support_occupied (B : V → Finset X) (p : X) : support B p ∈ occupied B :=
  mem_image.mpr ⟨p,mem_univ _,rfl⟩

theorem multiplicity_pos (B : V → Finset X) {S : Finset V} (hS : S ∈ occupied B) :
    0 < multiplicity B S := by
  obtain ⟨p,_,rfl⟩ := mem_image.mp hS
  exact card_pos.mpr ⟨p,by simp⟩

theorem actual_load (B : V → Finset X) (x : V) :
    (∑ S ∈ occupied B, if x ∈ S then multiplicity B S else 0) = (B x).card := by
  calc
    _ = ∑ S ∈ occupied B, ∑ p : X,
        if support B p = S then (if x ∈ S then 1 else 0) else 0 := by
      apply sum_congr rfl
      intro S hS
      by_cases hx : x ∈ S
      · simp only [hx,if_true,multiplicity,card_eq_sum_ones,sum_filter]
      · simp [hx]
    _ = ∑ p : X, if x ∈ support B p then 1 else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      simp [support_occupied B p]
    _ = _ := by simp [← sum_filter]

private theorem actual_degree_floor {B : V → Finset X} {K : ℕ}
    (hq : 2 ≤ q) (hK : 0 < K) (hv : Fintype.card X = q*K)
    (hB : Multicover.IsCover B K 2 1) (p : X) : q+1 ≤ (support B p).card := by
  have sub : univ.erase p ⊆ (support B p).biUnion (fun i => (B i).erase p) := by
    intro r hr
    have hpr : p ≠ r := Ne.symm (mem_erase.mp hr).1
    obtain ⟨i,hi⟩ := (Multicover.covers_one_iff _ _).mp hB.2 {p,r} (by simp [hpr])
    simp only [insert_subset_iff,singleton_subset_iff] at hi
    exact mem_biUnion.mpr ⟨i,by simp [hi.1],mem_erase.mpr ⟨hpr.symm,hi.2⟩⟩
  have cap := (card_le_card sub).trans (card_biUnion_le)
  have sizes : (∑ i ∈ support B p, ((B i).erase p).card) = (support B p).card*(K-1) := by
    calc
      _ = ∑ _i ∈ support B p, (K-1) := by
        apply sum_congr rfl
        intro i hi
        rw [card_erase_of_mem ((mem_support B p i).mp hi), hB.1 i]
      _ = _ := by simp
  rw [sizes, card_erase_of_mem (mem_univ p), card_univ, hv] at cap
  by_contra hn
  have hd : (support B p).card ≤ q := by omega
  have hc := Nat.mul_le_mul_right (K-1) hd
  have hp : 0 < q*K := Nat.mul_pos (by omega) hK
  have hsub : K-1+1 = K := by omega
  have hsub' : q*K-1+1 = q*K := by omega
  nlinarith

/-- At q(q+1) occurrences on qK points all support sizes are forced to q+1.
No core or fractional classification is used for this elementary count. -/
theorem actual_support_size (P : Plane q V G) {B : V → Finset X} {K : ℕ}
    (hq : 2 ≤ q) (hK : 0 < K) (hv : Fintype.card X = q*K)
    (hB : Multicover.IsCover B K 2 1) (p : X) : (support B p).card = q+1 := by
  have floors := actual_degree_floor hq hK hv hB
  have he : (∑ p : X, (support B p).card) = K * Fintype.card V := by
    simp only [support,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
    have hh (i : V) : (∑ p : X, if p ∈ B i then 1 else 0) = K := by
      rw [← sum_filter]
      simpa using hB.1 i
    simp [hh,Nat.mul_comm]
  have eq : (∑ _p : X, (q+1)) = ∑ p : X, (support B p).card := by
    rw [he]
    simp [hv,P.coordinates_card]
    ring
  exact ((sum_eq_sum_iff_of_le (fun x _ => floors x)).mp eq p (mem_univ _)).symm

/-- The only geometric hypothesis is an actual occupied truncated core.
Finding that core by a fractional classification remains outside this component. -/
theorem actual_admissible {B : V → Finset X} {K : ℕ}
    (hq : 4 ≤ q) (hK : 0 < K) (hv : Fintype.card X = q*K)
    (hB : Multicover.IsCover B K 2 1) (hcore : P.core ⊆ occupied B) :
    NatAdmissible P (occupied B) (multiplicity B) K := by
  refine ⟨hcore,?_,?_,fun S hS => multiplicity_pos B hS,?_,hK⟩
  · intro S hS
    obtain ⟨p,_,rfl⟩ := mem_image.mp hS
    exact actual_support_size P (by omega) hK hv hB p
  · intro S hS T hT
    obtain ⟨p,_,rfl⟩ := mem_image.mp hS
    obtain ⟨r,_,rfl⟩ := mem_image.mp hT
    by_cases hpr : p = r
    · subst r
      rw [inter_self, ← card_pos, actual_support_size P (by omega) hK hv hB p]
      omega
    · obtain ⟨i,hi⟩ := (Multicover.covers_one_iff _ _).mp hB.2 {p,r} (by simp [hpr])
      exact ⟨i, by simpa only [mem_inter,mem_support,insert_subset_iff,singleton_subset_iff] using hi⟩
  · intro x
    rw [actual_load,hB.1 x]

theorem actual_classification {B : V → Finset X} {K : ℕ}
    (hq : 4 ≤ q) (hK : 0 < K) (hv : Fintype.card X = q*K)
    (hB : Multicover.IsCover B K 2 1) (hcore : P.core ⊆ occupied B) :
    q ∣ K ∧ ∃ t : ℕ, 0 < t ∧ K = q*t ∧
      NatDescription P (occupied B) (multiplicity B) t := by
  have ha := actual_admissible P hq hK hv hB hcore
  exact ⟨load_divisible P hq ha,integer_classification P hq ha⟩

/-- A bijection to the expanded presentation, not an identification of twins. -/
noncomputable def actualEquiv (B : V → Finset X) : X ≃ Point (occupied B) (multiplicity B) :=
  let f : X → occupied B := fun p => ⟨support B p,support_occupied B p⟩
  (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight (fun S =>
    Fintype.equivOfCardEq (α := {p : X // f p = S}) (β := Fin (multiplicity B S.val)) (by
      simp [Fintype.card_subtype, multiplicity, f, Subtype.ext_iff]
      exact (Fintype.card_fin _).symm)))

theorem actualEquiv_support (B : V → Finset X) (p : X) :
    (actualEquiv B p).1.val = support B p := rfl

theorem actualEquiv_incidence (B : V → Finset X) (p : X) (x : V) :
    actualEquiv B p ∈ block (occupied B) (multiplicity B) x ↔ p ∈ B x := by
  rw [mem_block,actualEquiv_support,mem_support]

theorem support_reindex (B : V → Finset X) {J : Type*} [Fintype J] [DecidableEq J]
    (e : J ≃ V) (p : X) :
    support (B ∘ e) p = (support B p).map e.symm.toEmbedding := by
  ext j
  simp [support,Function.comp_def]

theorem support_relabel (B : V → Finset X) {Y : Type*} [DecidableEq Y]
    (e : X ≃ Y) (p : X) : support (fun x => (B x).map e.toEmbedding) (e p) = support B p := by
  ext x
  simp

end CoveringDesigns.TruncatedPlaneLoads
