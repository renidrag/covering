import CoveringDesigns.TruncatedPlaneLoads.Family

/-! Both classified descriptions have the required positive equal loads. -/

namespace CoveringDesigns.TruncatedPlaneLoads
open Finset
variable {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable {q : ℕ} (P : Plane q V G)

namespace Plane

def extension (c : V) : Finset (Finset V) :=
  P.core ∪ (univ.filter (· ≠ P.group c)).image (fun i => P.extra i c)

@[simp] theorem mem_extension (c : V) (S : Finset V) :
    S ∈ P.extension c ↔ S ∈ P.core ∨ ∃ i, i ≠ P.group c ∧ S = P.extra i c := by
  simp [extension, eq_comm]

theorem extra_base_injective (hq : 2 ≤ q) {c : V} {i j : G}
    (hi : i ≠ P.group c) (hj : j ≠ P.group c) (he : P.extra i c = P.extra j c) : i = j := by
  have hh := congrArg (fun S : Finset V => (S.filter (P.group · = i)).card) he
  rw [P.extra_group_card (Ne.symm hi), P.extra_group_card (Ne.symm hj)] at hh
  simp only [ite_true, if_neg (Ne.symm hi), add_zero] at hh
  by_contra hn
  rw [if_neg (Ne.symm hn)] at hh
  omega

theorem extension_sum (hq : 2 ≤ q) (c : V) (f : Finset V → ℝ) :
    (∑ S ∈ P.extension c, f S) = (∑ E ∈ P.core, f E) +
      ∑ i ∈ univ.filter (· ≠ P.group c), f (P.extra i c) := by
  rw [extension, sum_union]
  · congr 1
    apply sum_image
    intro i hi j hj he
    exact P.extra_base_injective hq (mem_filter.mp hi).2 (mem_filter.mp hj).2 he
  · apply disjoint_left.mpr
    intro S hS hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact P.extra_not_core hq hS

theorem core_intersects {E F : Finset V} (hE : E ∈ P.core) (hF : F ∈ P.core) :
    (E ∩ F).Nonempty := by
  by_cases he : E = F
  · subst F
    rw [inter_self, ← card_pos, P.core_size hE]
    omega
  · rw [← card_pos, P.intersection E hE F hF he]
    omega

theorem extension_intersects (c : V) {S T : Finset V}
    (hS : S ∈ P.extension c) (hT : T ∈ P.extension c) : (S ∩ T).Nonempty := by
  rw [mem_extension] at hS hT
  rcases hS with hS | ⟨i,hi,rfl⟩ <;> rcases hT with hT | ⟨j,hj,rfl⟩
  · exact P.core_intersects hS hT
  · simpa [inter_comm] using P.extra_core_meet hS j c
  · exact P.extra_core_meet hT i c
  · exact ⟨c, by simp⟩

def extensionWeight (c : V) (t s : ℝ) (S : Finset V) : ℝ :=
  if S ∈ P.core then (if c ∈ S then t-s else t) else s

theorem pure_converse {t : ℝ} (ht : 0 < t) (hq : 0 < q) :
    Admissible P P.core (fun _ => t) (q*t) := by
  refine ⟨Subset.rfl, fun E hE => P.core_size hE,
    fun E hE F hF => P.core_intersects hE hF, fun _ _ => ht, ?_, ?_⟩
  · intro x
    rw [← sum_filter]
    simp [P.degree, mul_comm]
  · have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    exact mul_pos hqr ht

private theorem reweighted_core_load (c x : V) (t s : ℝ) :
    (∑ E ∈ P.core, if x ∈ E then (if c ∈ E then t-s else t) else 0) =
      q*t - ((P.core.filter (fun E => x ∈ E ∧ c ∈ E)).card : ℝ)*s := by
  calc
    _ = ∑ E ∈ P.core, ((if x ∈ E then t else 0) -
        (if x ∈ E ∧ c ∈ E then s else 0)) := by
      apply sum_congr rfl
      intro E hE
      split_ifs <;> simp_all <;> ring
    _ = _ := by
      rw [sum_sub_distrib, ← sum_filter, ← sum_filter]
      simp [P.degree]

private theorem added_load (c x : V) (s : ℝ) :
    (∑ i ∈ univ.filter (· ≠ P.group c), if x ∈ P.extra i c then s else 0) =
      if x = c then q*s else if P.group x = P.group c then 0 else s := by
  by_cases hx : x = c
  · subst x
    have he : univ.filter (fun i : G => i ≠ P.group c) = univ.erase (P.group c) := by
      ext i
      simp [ne_eq]
    simp [he, P.groups_card]
  · simp only [mem_extra, hx, false_or, if_neg hx]
    by_cases hg : P.group x = P.group c
    · simp [hg, sum_filter]
    · simp [hg, sum_filter]

theorem extension_converse (hq : 2 ≤ q) (c : V) {t s : ℝ}
    (hs : 0 < s) (hst : s < t) :
    Admissible P (P.extension c) (P.extensionWeight c t s) (q*t) := by
  have ht : 0 < t := lt_trans hs hst
  refine ⟨subset_union_left, ?_, fun S hS T hT => P.extension_intersects c hS hT, ?_, ?_, ?_⟩
  · intro S hS
    rw [mem_extension] at hS
    rcases hS with hS | ⟨i,hi,rfl⟩
    · exact P.core_size hS
    · exact P.extra_size (Ne.symm hi)
  · intro S hS
    unfold extensionWeight
    split_ifs <;> linarith
  · intro x
    rw [P.extension_sum hq]
    have hcore : (∑ E ∈ P.core, if x ∈ E then P.extensionWeight c t s E else 0) =
        ∑ E ∈ P.core, if x ∈ E then (if c ∈ E then t-s else t) else 0 := by
      apply sum_congr rfl
      intro E hE
      simp [extensionWeight, hE]
    have hextra : (∑ i ∈ univ.filter (· ≠ P.group c),
        if x ∈ P.extra i c then P.extensionWeight c t s (P.extra i c) else 0) =
        ∑ i ∈ univ.filter (· ≠ P.group c), if x ∈ P.extra i c then s else 0 := by
      apply sum_congr rfl
      intro i hi
      simp [extensionWeight, P.extra_not_core hq]
    rw [hcore,hextra,P.reweighted_core_load,P.added_load]
    by_cases hx : x = c
    · subst x
      simp [P.degree]
    · rw [P.codegree x c hx]
      by_cases hg : P.group x = P.group c <;> simp [hx,hg]
  · have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    exact mul_pos hqr ht

end Plane

/-- Every family and weight function with either description is admissible. -/
theorem description_converse (hq : 4 ≤ q) {H : Finset (Finset V)}
    {w : Finset V → ℝ} {t : ℝ} (ht : 0 < t) (h : Description P H w t) :
    Admissible P H w (q*t) := by
  rcases h with ⟨rfl,hw⟩ | ⟨c,s,hs,hst,hH,hw,hcore⟩
  · have h := P.pure_converse ht (by omega)
    refine ⟨h.core_subset,h.uniform,h.intersect,?_,?_,h.load_pos⟩
    · intro S hS
      rw [hw S hS]
      exact ht
    · intro x
      rw [← h.load x]
      apply sum_congr rfl
      intro S hS
      rw [hw S hS]
  · have eq : H = P.extension c := by ext S; rw [hH, P.mem_extension]
    subst H
    have h := P.extension_converse (by omega) c hs hst
    have heq (S : Finset V) (hS : S ∈ P.extension c) : w S = P.extensionWeight c t s S := by
      unfold Plane.extensionWeight
      by_cases hc : S ∈ P.core
      · simpa [hc] using hcore S hc
      · obtain ⟨i,hi,rfl⟩ := ((P.mem_extension c S).mp hS).resolve_left hc
        simpa [P.extra_not_core (by omega)] using hw i hi
    refine ⟨h.core_subset,h.uniform,h.intersect,?_,?_,h.load_pos⟩
    · intro S hS
      rw [heq S hS]
      exact h.positive S hS
    · intro x
      rw [← h.load x]
      apply sum_congr rfl
      intro S hS
      rw [heq S hS]

theorem real_classification_iff (hq : 4 ≤ q) {H : Finset (Finset V)}
    {w : Finset V → ℝ} {K : ℝ} (hK : 0 < K) :
    Admissible P H w K ↔ Description P H w (K/q) := by
  constructor
  · exact real_classification P hq
  · intro h
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hd := description_converse P hq (div_pos hK hqpos) h
    simpa [mul_div_cancel₀ K (ne_of_gt hqpos)] using hd

end CoveringDesigns.TruncatedPlaneLoads
