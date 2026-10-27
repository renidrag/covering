import CoveringDesigns.TruncatedPlaneLoads.Converse

/-! Natural multiplicities and divisibility of the common load. -/

namespace CoveringDesigns.TruncatedPlaneLoads
open Finset
variable {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable {q : ℕ} (P : Plane q V G)

structure NatAdmissible (H : Finset (Finset V)) (m : Finset V → ℕ) (K : ℕ) : Prop where
  core_subset : P.core ⊆ H
  uniform : ∀ S ∈ H, S.card = q+1
  intersect : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty
  positive : ∀ S ∈ H, 0 < m S
  load : ∀ x, (∑ S ∈ H, if x ∈ S then m S else 0) = K
  load_pos : 0 < K

def NatDescription (H : Finset (Finset V)) (m : Finset V → ℕ) (t : ℕ) : Prop :=
  (H = P.core ∧ ∀ E ∈ P.core, m E = t) ∨
  ∃ c : V, ∃ s : ℕ, 1 ≤ s ∧ s < t ∧
    (∀ S, S ∈ H ↔ S ∈ P.core ∨ ∃ i, i ≠ P.group c ∧ S = P.extra i c) ∧
    (∀ i, i ≠ P.group c → m (P.extra i c) = s) ∧
    ∀ E ∈ P.core, m E = if c ∈ E then t-s else t

namespace NatAdmissible
variable {P} {H : Finset (Finset V)} {m : Finset V → ℕ} {K : ℕ}

theorem toReal (h : NatAdmissible P H m K) : Admissible P H (fun S => (m S : ℝ)) K := by
  refine ⟨h.core_subset,h.uniform,h.intersect,?_,?_,?_⟩
  · intro S hS
    exact_mod_cast h.positive S hS
  · intro x
    exact_mod_cast h.load x
  · exact_mod_cast h.load_pos

theorem mass (h : NatAdmissible P H m K) : (∑ S ∈ H, m S) = q*K := by
  have hr := total_weight P h.toReal
  exact_mod_cast hr

end NatAdmissible

namespace Plane
theorem other_group (hq : 0 < q) (c : V) : ∃ i : G, i ≠ P.group c := by
  have hc : 1 < Fintype.card G := by rw [P.groups_card]; omega
  letI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp hc
  exact exists_ne (P.group c)

theorem core_nonempty (hq : 0 < q) : P.core.Nonempty := by
  rw [← card_pos, P.core_card]
  exact Nat.mul_pos hq hq

/-- The extended description has genuine additional supports. -/
theorem extension_ne_core (hq : 2 ≤ q) (c : V) : P.extension c ≠ P.core := by
  obtain ⟨i,hi⟩ := P.other_group (by omega) c
  intro he
  have hm : P.extra i c ∈ P.extension c := (P.mem_extension c _).mpr (Or.inr ⟨i,hi,rfl⟩)
  rw [he] at hm
  exact P.extra_not_core hq hm
end Plane

/-- Every positive natural equal-load extension has integral parameters t,s.
In particular the common load is q*t, with 1 ≤ s < t in the extended case. -/
theorem integer_classification (hq : 4 ≤ q) {H : Finset (Finset V)}
    {m : Finset V → ℕ} {K : ℕ} (h : NatAdmissible P H m K) :
    ∃ t : ℕ, 0 < t ∧ K = q*t ∧ NatDescription P H m t := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have extract (E : Finset V) (hE : E ∈ P.core) (he : (m E : ℝ) = (K : ℝ)/q) :
      0 < m E ∧ K = q*m E := by
    refine ⟨h.positive E (h.core_subset hE), ?_⟩
    have hr := (eq_div_iff (ne_of_gt hqr)).mp he
    have hr' : (K : ℝ) = (q : ℝ)*(m E : ℝ) := by nlinarith
    exact_mod_cast hr'
  rcases real_classification P hq h.toReal with ⟨hH,hw⟩ | ⟨c,s,hs,hst,hH,hw,hcore⟩
  · obtain ⟨E,hE⟩ := P.core_nonempty (by omega)
    have ht := extract E hE (hw E hE)
    refine ⟨m E,ht.1,ht.2,Or.inl ⟨hH,?_⟩⟩
    intro F hF
    have hr : (m F : ℝ) = (m E : ℝ) := (hw F hF).trans (hw E hE).symm
    exact_mod_cast hr
  · obtain ⟨E,hE,hcE⟩ := P.core_avoiding (by omega) c
    have he : (m E : ℝ) = (K : ℝ)/q := by simpa [hcE] using hcore E hE
    have ht := extract E hE he
    obtain ⟨i,hi⟩ := P.other_group (by omega) c
    let r := m (P.extra i c)
    have hr : (r : ℝ) = s := hw i hi
    have hrpos : 1 ≤ r := by
      have hp : (0 : ℝ) < r := by rw [hr]; exact hs
      have hp' : 0 < r := by exact_mod_cast hp
      omega
    have hrlt : r < m E := by
      have hl : (r : ℝ) < m E := by rw [hr,he]; exact hst
      exact_mod_cast hl
    refine ⟨m E,ht.1,ht.2,Or.inr ⟨c,r,hrpos,hrlt,hH,?_,?_⟩⟩
    · intro j hj
      have hh : (m (P.extra j c) : ℝ) = (r : ℝ) := (hw j hj).trans hr.symm
      exact_mod_cast hh
    · intro F hF
      have hh := hcore F hF
      rw [← he,← hr] at hh
      by_cases hcF : c ∈ F
      · simp only [if_pos hcF] at hh ⊢
        exact_mod_cast (show (m F : ℝ) = ((m E - r : ℕ) : ℝ) by
          rw [Nat.cast_sub hrlt.le]; exact hh)
      · simpa [hcF] using (show m F = m E by exact_mod_cast (by simpa [hcF] using hh))

theorem load_divisible (hq : 4 ≤ q) {H : Finset (Finset V)}
    {m : Finset V → ℕ} {K : ℕ} (h : NatAdmissible P H m K) : q ∣ K := by
  obtain ⟨t,ht,hK,hform⟩ := integer_classification P hq h
  exact ⟨t,hK⟩

theorem unit_load_pure (hq : 4 ≤ q) {H : Finset (Finset V)}
    {m : Finset V → ℕ} (h : NatAdmissible P H m q) :
    H = P.core ∧ ∀ E ∈ P.core, m E = 1 := by
  obtain ⟨t,ht,hK,hform⟩ := integer_classification P hq h
  have he : t = 1 := by nlinarith
  subst t
  rcases hform with hform | ⟨c,s,hs,hst,_⟩
  · exact hform
  · omega

theorem integer_converse (hq : 4 ≤ q) {H : Finset (Finset V)}
    {m : Finset V → ℕ} {t : ℕ} (ht : 0 < t) (h : NatDescription P H m t) :
    NatAdmissible P H m (q*t) := by
  have hd : Description P H (fun S => (m S : ℝ)) (t : ℝ) := by
    rcases h with ⟨hH,hw⟩ | ⟨c,s,hs,hst,hH,hw,hcore⟩
    · exact Or.inl ⟨hH, fun E hE => by dsimp only; exact_mod_cast hw E hE⟩
    · refine Or.inr ⟨c,(s : ℝ),?_,?_,hH,?_,?_⟩
      · exact_mod_cast (show 0 < s by omega)
      · exact_mod_cast hst
      · intro i hi
        dsimp only
        exact_mod_cast hw i hi
      · intro E hE
        dsimp only
        rw [hcore E hE]
        split_ifs
        · exact Nat.cast_sub hst.le
        · rfl
  have hr := description_converse P hq (by exact_mod_cast ht) hd
  refine ⟨hr.core_subset,hr.uniform,hr.intersect,?_,?_,?_⟩
  · intro S hS
    exact_mod_cast hr.positive S hS
  · intro x
    exact_mod_cast hr.load x
  · exact_mod_cast hr.load_pos

namespace Plane

def naturalWeight (c : V) (t s : ℕ) (S : Finset V) : ℕ :=
  if S ∈ P.core then (if c ∈ S then t-s else t) else s

theorem natural_pure (hq : 4 ≤ q) {t : ℕ} (ht : 0 < t) :
    NatAdmissible P P.core (fun _ => t) (q*t) :=
  integer_converse P hq ht (Or.inl ⟨rfl,fun _ _ => rfl⟩)

theorem natural_extension (hq : 4 ≤ q) (c : V) {t s : ℕ}
    (hs : 1 ≤ s) (hst : s < t) :
    NatAdmissible P (P.extension c) (P.naturalWeight c t s) (q*t) := by
  apply integer_converse P hq (by omega)
  refine Or.inr ⟨c,s,hs,hst,fun S => P.mem_extension c S,?_,?_⟩
  · intro i hi
    simp [naturalWeight,P.extra_not_core (by omega)]
  · intro E hE
    simp [naturalWeight,hE]

end Plane

end CoveringDesigns.TruncatedPlaneLoads
