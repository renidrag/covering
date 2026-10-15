import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
Seven-point caps in the four-dimensional binary vector space are contained in
an affine hyperplane. The proof chooses four independent points of the cap;
the only finite case distinctions are the sixteen coordinate vectors in that
arbitrary basis.
-/

namespace CoveringDesigns.BinaryCap

open Finset

abbrev V := Fin 4 → ZMod 2

def dot (n x : V) : ZMod 2 := ∑ i, n i * x i

private def combine (a b c d : V) : V →ₗ[ZMod 2] V where
  toFun x := x 0 • a + x 1 • b + x 2 • c + x 3 • d
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' k x := by
    simp only [Pi.smul_apply, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

private theorem binary_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  exact (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) x

private theorem add_eq_zero (x y : V) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    exact CharTwo.add_eq_zero.mp (congrFun h i)
  · rintro rfl
    funext i
    exact CharTwo.add_self_eq_zero (x i)

private theorem zero_of_coords (x : V)
    (h0 : x 0 = 0) (h1 : x 1 = 0) (h2 : x 2 = 0) (h3 : x 3 = 0) :
    x = 0 := by
  funext i
  fin_cases i <;> assumption

private theorem choose_four (S : Finset V) (hcard : S.card = 7) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      d ≠ a + b + c := by
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < S.card by omega)
  obtain ⟨b, hb, hba⟩ := exists_mem_notMem_of_card_lt_card
    (show ({a} : Finset V).card < S.card by simp [hcard])
  have htwo : ({a, b} : Finset V).card ≤ 2 := by
    simpa using card_insert_le a {b}
  obtain ⟨c, hc, hcabc⟩ := exists_mem_notMem_of_card_lt_card
    (show ({a, b} : Finset V).card < S.card by omega)
  have hfour : ({a, b, c, a + b + c} : Finset V).card ≤ 4 := by
    have h₁ := card_insert_le a ({b, c, a + b + c} : Finset V)
    have h₂ := card_insert_le b ({c, a + b + c} : Finset V)
    have h₃ := card_insert_le c ({a + b + c} : Finset V)
    simp only [card_singleton] at h₃
    omega
  obtain ⟨d, hd, hdabc⟩ := exists_mem_notMem_of_card_lt_card
    (show ({a, b, c, a + b + c} : Finset V).card < S.card by omega)
  simp only [mem_singleton, mem_insert, not_or] at hba hcabc hdabc
  exact ⟨a, ha, b, hb, c, hc, d, hd, Ne.symm hba, Ne.symm hcabc.1,
    Ne.symm hdabc.1, Ne.symm hcabc.2, Ne.symm hdabc.2.1,
    Ne.symm hdabc.2.2.1, hdabc.2.2.2⟩

private theorem combine_injective (S : Finset V) (hzero : (0 : V) ∉ S)
    (hcap : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∉ S)
    (a b c d : V) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hdabc : d ≠ a + b + c) :
    Function.Injective (combine a b c d) := by
  have hne (x : V) (hx : x ∈ S) : x ≠ 0 := by
    intro h
    exact hzero (h ▸ hx)
  have htriple (x y z : V) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
      (hxy : x ≠ y) : x + y + z ≠ 0 := by
    rw [ne_eq, add_eq_zero]
    intro h
    exact hcap x hx y hy hxy (h.symm ▸ hz)
  have hab0 : a + b ≠ 0 := by simpa only [ne_eq, add_eq_zero] using hab
  have hac0 : a + c ≠ 0 := by simpa only [ne_eq, add_eq_zero] using hac
  have had0 : a + d ≠ 0 := by simpa only [ne_eq, add_eq_zero] using had
  have hbc0 : b + c ≠ 0 := by simpa only [ne_eq, add_eq_zero] using hbc
  have hbd0 : b + d ≠ 0 := by simpa only [ne_eq, add_eq_zero] using hbd
  have hcd0 : c + d ≠ 0 := by simpa only [ne_eq, add_eq_zero] using hcd
  have habc0 := htriple a b c ha hb hc hab
  have habd0 := htriple a b d ha hb hd hab
  have hacd0 := htriple a c d ha hc hd hac
  have hbcd0 := htriple b c d hb hc hd hbc
  have habcd0 : a + b + c + d ≠ 0 := by
    simpa only [ne_eq, add_eq_zero, eq_comm] using hdabc
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  rcases binary_cases (x 0) with h0 | h0 <;>
    rcases binary_cases (x 1) with h1 | h1 <;>
    rcases binary_cases (x 2) with h2 | h2 <;>
    rcases binary_cases (x 3) with h3 | h3
  all_goals
    simp only [combine, LinearMap.coe_mk, AddHom.coe_mk, h0, h1, h2, h3,
      zero_smul, one_smul, zero_add, add_zero] at hx
  all_goals first
    | exact zero_of_coords x h0 h1 h2 h3
    | exact False.elim (hne a ha hx)
    | exact False.elim (hne b hb hx)
    | exact False.elim (hne c hc hx)
    | exact False.elim (hne d hd hx)
    | contradiction

private theorem cap_sum_free (S : Finset V) (hzero : (0 : V) ∉ S)
    (hcap : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∉ S) :
    ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S := by
  intro x hx y hy
  by_cases h : x = y
  · subst y
    rwa [(add_eq_zero x x).mpr rfl]
  · exact hcap x hx y hy h

private theorem fourfold_not_mem (S : Finset V) (hcard : S.card = 7)
    (hzero : (0 : V) ∉ S)
    (hsum : ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S)
    (a b c d : V) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hsurj : Function.Surjective (combine a b c d)) : a + b + c + d ∉ S := by
  intro hq
  have hab := hsum a ha b hb
  have hac := hsum a ha c hc
  have had := hsum a ha d hd
  have hbc := hsum b hb c hc
  have hbd := hsum b hb d hd
  have hcd := hsum c hc d hd
  have habc : a + b + c ∉ S := fun h => hsum (a + b + c) h d hd hq
  have habd : a + b + d ∉ S := by
    intro h
    apply hsum (a + b + d) h c hc
    convert hq using 1
    abel
  have hacd : a + c + d ∉ S := by
    intro h
    apply hsum (a + c + d) h b hb
    convert hq using 1
    abel
  have hbcd : b + c + d ∉ S := by
    intro h
    apply hsum a ha (b + c + d) h
    simpa only [add_assoc] using hq
  have hsub : S ⊆ {a, b, c, d, a + b + c + d} := by
    intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    rcases binary_cases (x 0) with h0 | h0 <;>
      rcases binary_cases (x 1) with h1 | h1 <;>
      rcases binary_cases (x 2) with h2 | h2 <;>
      rcases binary_cases (x 3) with h3 | h3
    all_goals
      simp only [combine, LinearMap.coe_mk, AddHom.coe_mk, h0, h1, h2, h3,
        zero_smul, one_smul, zero_add, add_zero] at hy ⊢
    all_goals first | contradiction | simp
  have hbound : ({a, b, c, d, a + b + c + d} : Finset V).card ≤ 5 := by
    have h₁ := card_insert_le a ({b, c, d, a + b + c + d} : Finset V)
    have h₂ := card_insert_le b ({c, d, a + b + c + d} : Finset V)
    have h₃ := card_insert_le c ({d, a + b + c + d} : Finset V)
    have h₄ := card_insert_le d ({a + b + c + d} : Finset V)
    simp only [card_singleton] at h₄
    omega
  have := card_le_card hsub
  omega

private def parity : V →ₗ[ZMod 2] ZMod 2 where
  toFun x := x 0 + x 1 + x 2 + x 3
  map_add' x y := by
    simp only [Pi.add_apply]
    abel
  map_smul' k x := by
    simp only [Pi.smul_apply, smul_add, RingHom.id_apply]

private theorem parity_eq_one (S : Finset V) (hzero : (0 : V) ∉ S)
    (hsum : ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S)
    (a b c d : V) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hq : a + b + c + d ∉ S) (x : V) (hx : combine a b c d x ∈ S) :
    parity x = 1 := by
  have hab := hsum a ha b hb
  have hac := hsum a ha c hc
  have had := hsum a ha d hd
  have hbc := hsum b hb c hc
  have hbd := hsum b hb d hd
  have hcd := hsum c hc d hd
  rcases binary_cases (x 0) with h0 | h0 <;>
    rcases binary_cases (x 1) with h1 | h1 <;>
    rcases binary_cases (x 2) with h2 | h2 <;>
    rcases binary_cases (x 3) with h3 | h3
  all_goals
    simp only [combine, parity, LinearMap.coe_mk, AddHom.coe_mk, h0, h1, h2, h3,
      zero_smul, one_smul, zero_add, add_zero] at hx ⊢
  all_goals first | rfl | contradiction

/-- Every binary linear functional is a dot product with its values on the
standard coordinate vectors. -/
theorem linear_eq_dot (f : V →ₗ[ZMod 2] ZMod 2) (x : V) :
    f x = dot (fun i => f (Pi.single i 1)) x := by
  have hsingle (i : Fin 4) : Pi.single i (x i) = x i • (Pi.single i 1 : V) := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne h]
  calc
    f x = f (∑ i, Pi.single i (x i)) := by rw [univ_sum_single]
    _ = ∑ i, f (Pi.single i (x i)) := map_sum f _ _
    _ = dot (fun i => f (Pi.single i 1)) x := by
      unfold dot
      apply sum_congr rfl
      intro i hi
      rw [hsingle, map_smul]
      exact mul_comm _ _

/-- A zero-free seven-point cap in `F₂⁴` lies in an affine hyperplane.

Four cap points form a basis. Pair sums cannot belong to the cap. If the sum
of all four basis points belonged to it, neither could any triple sum, leaving
at most five points. Thus every cap point has odd weight in this basis. -/
theorem seven_cap_affine_hyperplane (S : Finset V) (hcard : S.card = 7)
    (hzero : (0 : V) ∉ S)
    (hcap : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∉ S) :
    ∃ n : V, n ≠ 0 ∧ ∀ x ∈ S, dot n x = 1 := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hac, had, hbc, hbd, hcd, hdabc⟩ :=
    choose_four S hcard
  have hinj := combine_injective S hzero hcap a b c d ha hb hc hd
    hab hac had hbc hbd hcd hdabc
  have hsurj := Finite.surjective_of_injective hinj
  have hsum := cap_sum_free S hzero hcap
  have hq := fourfold_not_mem S hcard hzero hsum a b c d ha hb hc hd hsurj
  let e : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (combine a b c d) ⟨hinj, hsurj⟩
  let f : V →ₗ[ZMod 2] ZMod 2 := parity.comp e.symm.toLinearMap
  let n : V := fun i => f (Pi.single i 1)
  have hf (x : V) (hx : x ∈ S) : f x = 1 := by
    apply parity_eq_one S hzero hsum a b c d ha hb hc hd hq (e.symm x)
    change e (e.symm x) ∈ S
    simpa only [LinearEquiv.apply_symm_apply] using hx
  have hn (x : V) (hx : x ∈ S) : dot n x = 1 := by
    rw [← linear_eq_dot]
    exact hf x hx
  refine ⟨n, ?_, hn⟩
  intro hnzero
  have hone := hn a ha
  rw [hnzero] at hone
  simp [dot] at hone

#guard_standard_axioms seven_cap_affine_hyperplane

#print axioms seven_cap_affine_hyperplane

private theorem cardinality : Fintype.card V = 16 := by
  simp [V, ZMod.card]

/-- Three independent binary vectors extend to a basis. The independence
conditions are precisely that their seven nonempty sums are nonzero. -/
theorem extend_three (a b c : V) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (habc : a + b + c ≠ 0) :
    ∃ e : V ≃ₗ[ZMod 2] V,
      e (Pi.single 0 1) = a ∧ e (Pi.single 1 1) = b ∧ e (Pi.single 2 1) = c := by
  let T : Finset V := [0, a, b, c, a + b, a + c, b + c, a + b + c].toFinset
  have hT : T.card ≤ 8 := List.toFinset_card_le _
  obtain ⟨d, _, hd⟩ := exists_mem_notMem_of_card_lt_card
    (show T.card < (univ : Finset V).card by rw [card_univ, cardinality]; omega)
  simp only [T, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases hd with ⟨hd0, hda, hdb, hdc, hdab, hdac, hdbc, hdabc⟩
  have hab0 : a + b ≠ 0 := by simpa only [ne_eq, add_eq_zero] using hab
  have hac0 : a + c ≠ 0 := by simpa only [ne_eq, add_eq_zero] using hac
  have hbc0 : b + c ≠ 0 := by simpa only [ne_eq, add_eq_zero] using hbc
  have had0 : a + d ≠ 0 := by simpa only [ne_eq, add_eq_zero] using Ne.symm hda
  have hbd0 : b + d ≠ 0 := by simpa only [ne_eq, add_eq_zero] using Ne.symm hdb
  have hcd0 : c + d ≠ 0 := by simpa only [ne_eq, add_eq_zero] using Ne.symm hdc
  have habd0 : a + b + d ≠ 0 := by simpa only [ne_eq, add_eq_zero] using Ne.symm hdab
  have hacd0 : a + c + d ≠ 0 := by simpa only [ne_eq, add_eq_zero] using Ne.symm hdac
  have hbcd0 : b + c + d ≠ 0 := by simpa only [ne_eq, add_eq_zero] using Ne.symm hdbc
  have habcd0 : a + b + c + d ≠ 0 := by
    simpa only [ne_eq, add_eq_zero] using Ne.symm hdabc
  have hinj : Function.Injective (combine a b c d) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    rcases binary_cases (x 0) with h0 | h0 <;>
      rcases binary_cases (x 1) with h1 | h1 <;>
      rcases binary_cases (x 2) with h2 | h2 <;>
      rcases binary_cases (x 3) with h3 | h3
    all_goals
      simp only [combine, LinearMap.coe_mk, AddHom.coe_mk, h0, h1, h2, h3,
        zero_smul, one_smul, zero_add, add_zero] at hx
    · exact zero_of_coords x h0 h1 h2 h3
    · exact (hd0 hx).elim
    · exact (hc hx).elim
    · exact (hcd0 hx).elim
    · exact (hb hx).elim
    · exact (hbd0 hx).elim
    · exact (hbc0 hx).elim
    · exact (hbcd0 hx).elim
    · exact (ha hx).elim
    · exact (had0 hx).elim
    · exact (hac0 hx).elim
    · exact (hacd0 hx).elim
    · exact (hab0 hx).elim
    · exact (habd0 hx).elim
    · exact (habc hx).elim
    · exact (habcd0 hx).elim
  let e : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (combine a b c d)
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨e, ?_, ?_, ?_⟩ <;> simp [e, combine]

/-- An invertible linear change of coordinates sends any two distinct
nonzero binary vectors to the first two standard coordinate vectors. -/
theorem pair_normalize (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ e : V ≃ₗ[ZMod 2] V, e a = Pi.single 0 1 ∧ e b = Pi.single 1 1 := by
  let T : Finset V := [0, a, b, a + b].toFinset
  have hT : T.card ≤ 4 := List.toFinset_card_le _
  obtain ⟨c, _, hc⟩ := exists_mem_notMem_of_card_lt_card
    (show T.card < (univ : Finset V).card by rw [card_univ, cardinality]; omega)
  simp only [T, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  obtain ⟨e, hea, heb, _⟩ := extend_three a b c ha hb hc.1 hab (Ne.symm hc.2.1)
    (Ne.symm hc.2.2.1) (by simpa only [ne_eq, add_eq_zero] using Ne.symm hc.2.2.2)
  exact ⟨e.symm, by rw [← hea, LinearEquiv.symm_apply_apply],
    by rw [← heb, LinearEquiv.symm_apply_apply]⟩

private theorem normal_of_independent_three (a b c : V)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (habc : a + b + c ≠ 0) :
    ∃ n : V, n ≠ 0 ∧ dot n a = 1 ∧ dot n b = 1 ∧ dot n c = 1 := by
  obtain ⟨e, hea, heb, hec⟩ := extend_three a b c ha hb hc hab hac hbc habc
  let f : V →ₗ[ZMod 2] ZMod 2 := parity.comp e.symm.toLinearMap
  let n : V := fun i => f (Pi.single i 1)
  have hunit (i : Fin 4) : parity (Pi.single i 1) = 1 := by
    fin_cases i <;> rfl
  have hfa : dot n a = 1 := by
    rw [← linear_eq_dot]
    change parity (e.symm a) = 1
    rw [← hea, LinearEquiv.symm_apply_apply]
    exact hunit 0
  have hfb : dot n b = 1 := by
    rw [← linear_eq_dot]
    change parity (e.symm b) = 1
    rw [← heb, LinearEquiv.symm_apply_apply]
    exact hunit 1
  have hfc : dot n c = 1 := by
    rw [← linear_eq_dot]
    change parity (e.symm c) = 1
    rw [← hec, LinearEquiv.symm_apply_apply]
    exact hunit 2
  refine ⟨n, ?_, hfa, hfb, hfc⟩
  intro hn
  rw [hn] at hfa
  simp [dot] at hfa

/-- Three distinct projective points meeting every projective hyperplane
are collinear: over `F₂`, their vector sum is zero. -/
theorem three_point_blocking_collinear (a b c : V)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hblock : ∀ n : V, n ≠ 0 → dot n a = 0 ∨ dot n b = 0 ∨ dot n c = 0) :
    a + b + c = 0 := by
  by_contra habc
  obtain ⟨n, hn, hna, hnb, hnc⟩ :=
    normal_of_independent_three a b c ha hb hc hab hac hbc habc
  have := hblock n hn
  simp [hna, hnb, hnc] at this

#guard_standard_axioms linear_eq_dot extend_three pair_normalize
  three_point_blocking_collinear

#print axioms three_point_blocking_collinear

end CoveringDesigns.BinaryCap
