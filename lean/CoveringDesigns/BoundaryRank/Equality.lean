import CoveringDesigns.BoundaryRank.Nullity
import Mathlib.Data.Fintype.EquivFin

/-!
# Equality in the component-coordinate boundary rank argument

The rank bound is retained together with the component injection. Equality
forces all deficits to vanish and every support component to have two vertices.
Existing boundary results remain unchanged. Rob Gardiner, with AI assistance.
-/

namespace CoveringDesigns.BoundaryRank
open Finset Matrix Module

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
private theorem propagate_zero (G : SimpleGraph ι) (x : ι → ℝ)
    (he : ∀ i j, G.Adj i j → x i + x j = 0) {i j : ι}
    (h : G.Reachable i j) (hi : x i = 0) : x j = 0 := by
  obtain ⟨w⟩ := h
  revert hi
  induction w with
  | nil => exact id
  | @cons a b c hab w ih =>
    intro ha
    apply ih
    have hh := he a b hab
    linarith

/-- Equality retains all intermediate component counts. The equivalence
exhibits two vertices per component; edges cannot cross its labelled pairs.
The empty case is included. -/
theorem component_pairing
    (G : SimpleGraph ι) (Z : Finset ι) (K : Submodule ℝ (ι → ℝ))
    (hneigh : ∀ i ∈ Z, ∃ j, G.Adj i j)
    (hzero : ∀ x ∈ K, ∀ i, i ∉ Z → x i = 0)
    (hedge : ∀ x ∈ K, ∀ i j, G.Adj i j → x i + x j = 0)
    (hcard : Fintype.card ι = 2 * Fintype.card κ)
    (hlower : Fintype.card κ ≤ finrank ℝ K) :
    Z = univ ∧ ∃ e : κ × Bool ≃ ι,
      ∀ i j, G.Adj (e i) (e j) → i.1 = j.1 := by
  classical
  let Active := {c : G.ConnectedComponent // ∀ i, i ∈ c.supp → i ∈ Z}
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let : Fintype Active := Fintype.ofFinite _
  let rep : Active → ι := fun c => c.val.nonempty_supp.choose
  have hrep (c : Active) : rep c ∈ c.val.supp := c.val.nonempty_supp.choose_spec
  let L : K →ₗ[ℝ] (Active → ℝ) :=
    LinearMap.pi fun c => (LinearMap.proj (rep c)).comp K.subtype
  have hL : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro x hx
      have hx0 : L x = 0 := hx
      have hxval : (x : ι → ℝ) = 0 := by
        funext i
        let c := G.connectedComponentMk i
        by_cases hc : ∀ j, j ∈ c.supp → j ∈ Z
        · let a : Active := ⟨c, hc⟩
          have hxr : x.val (rep a) = 0 := congr_fun hx0 a
          exact propagate_zero G x (hedge x x.property)
            (c.reachable_of_mem_supp (hrep a) rfl) hxr
        · push Not at hc
          obtain ⟨j, hjc, hjZ⟩ := hc
          exact propagate_zero G x (hedge x x.property)
            (c.reachable_of_mem_supp hjc rfl) (hzero x x.property j hjZ)
      exact Subtype.ext hxval
    · exact bot_le
  have hdim : finrank ℝ K ≤ Fintype.card Active := by
    simpa using LinearMap.finrank_le_finrank_of_injective hL
  have hneighbor (c : Active) : ∃ j, G.Adj (rep c) j :=
    hneigh (rep c) (c.property _ (hrep c))
  let next : Active → ι := fun c => (hneighbor c).choose
  have hnext (c : Active) : G.Adj (rep c) (next c) := (hneighbor c).choose_spec
  have hnextmem (c : Active) : next c ∈ c.val.supp :=
    c.val.mem_supp_of_adj_mem_supp (hrep c) (hnext c)
  let pick : Active × Bool → {i // i ∈ Z} := fun t =>
    if t.2 then ⟨next t.1, t.1.property _ (hnextmem t.1)⟩
    else ⟨rep t.1, t.1.property _ (hrep t.1)⟩
  have hpickmem (t : Active × Bool) : (pick t).val ∈ t.1.val.supp := by
    dsimp [pick]
    split
    · exact hnextmem t.1
    · exact hrep t.1
  have hpick : Function.Injective pick := by
    rintro ⟨c, b⟩ ⟨d, e⟩ h
    have hc : c.val = d.val :=
      SimpleGraph.ConnectedComponent.eq_of_common_vertex
        (hpickmem (c, b)) (h ▸ hpickmem (d, e))
    have hcd : c = d := Subtype.ext hc
    subst d
    have hv := congr_arg Subtype.val h
    cases b <;> cases e
    · rfl
    · have hne := (hnext c).ne
      simp only [pick, Bool.false_eq_true, ↓reduceIte] at hv
      exact False.elim (hne hv)
    · have hne := (hnext c).ne
      simp only [pick, Bool.false_eq_true, ↓reduceIte] at hv
      exact False.elim (hne hv.symm)
    · rfl
  have htwice : 2 * Fintype.card Active ≤ Z.card := by
    simpa [Fintype.card_prod, Nat.mul_comm] using Fintype.card_le_of_injective pick hpick
  have hzle : Z.card ≤ Fintype.card ι := card_le_univ Z
  have ha : Fintype.card Active = Fintype.card κ := by omega
  have hzcard : Z.card = Fintype.card ι := by omega
  have hZ : Z = univ := eq_of_subset_of_card_le (subset_univ Z) (by simpa using hzcard.ge)
  let pick' : Active × Bool → ι := fun t => (pick t).val
  have hpick' : Function.Injective pick' := fun x y h => hpick (Subtype.ext h)
  have hpc : Fintype.card (Active × Bool) = Fintype.card ι := by
    simp [Fintype.card_prod, ha, hcard, Nat.mul_comm]
  let e₀ : Active × Bool ≃ ι :=
    Equiv.ofBijective pick' ((Fintype.bijective_iff_injective_and_card pick').mpr ⟨hpick', hpc⟩)
  let a : κ ≃ Active := Fintype.equivOfCardEq ha.symm
  let e : κ × Bool ≃ ι := (Equiv.prodCongr a (Equiv.refl Bool)).trans e₀
  have he (t : κ × Bool) : e t ∈ (a t.1).val.supp := hpickmem (a t.1, t.2)
  refine ⟨hZ, e, ?_⟩
  intro i j hij
  have hj : e j ∈ (a i.1).val.supp :=
    (a i.1).val.mem_supp_of_adj_mem_supp (he i) hij
  exact a.injective (Subtype.ext (SimpleGraph.ConnectedComponent.eq_of_common_vertex hj (he j)))

/-- At twice as many Gram rows as columns, the support is a perfect matching
of weight ρ and every deficit is zero. All rank, balance and PSD hypotheses
are explicit; no conclusion is inferred just from the final nullity bound. -/
theorem gram_equality [DecidableEq κ]
    (R : Matrix ι κ ℝ) (ρ : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ)
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    (hgram : R * R.transpose = Matrix.diagonal (fun _ => ρ) + E + P)
    (hcard : Fintype.card ι = 2 * Fintype.card κ) :
    (∀ i, δ i = 0) ∧ ∃ e : κ × Bool ≃ ι,
      (∀ i j, i ≠ j → ∀ b c, E (e (i,b)) (e (j,c)) = 0) ∧
      (∀ i, E (e (i,false)) (e (i,true)) = ρ) := by
  classical
  let K := LinearMap.ker (Matrix.diagonal (fun _ => ρ) + E).mulVecLin
  let Z := univ.filter fun i => δ i = 0
  have hpsd := signless_posSemidef (fun _ => ρ) δ E hs hn hδ hrow
  have hker := ker_add_le_of_posSemidef hpsd hP
  rw [← hgram] at hker
  have hdim := Submodule.finrank_mono hker
  have hrank : (R * R.transpose).rank ≤ Fintype.card κ :=
    (Matrix.rank_mul_le_left R R.transpose).trans R.rank_le_card_width
  have htotal : (R * R.transpose).rank +
      finrank ℝ (LinearMap.ker (R * R.transpose).mulVecLin) = Fintype.card ι := by
    simpa [Matrix.rank] using
      LinearMap.finrank_range_add_finrank_ker (R * R.transpose).mulVecLin
  have hlower : Fintype.card κ ≤ finrank ℝ K := by dsimp [K]; omega
  have hneigh : ∀ i ∈ Z, ∃ j, (supportGraph E hs hz).Adj i j := by
    intro i hi
    have hdi : δ i = 0 := (mem_filter.mp hi).2
    have hr := hrow i
    rw [hdi, add_zero] at hr
    by_contra hnone
    have hall : ∀ j, E i j = 0 := by
      intro j
      exact le_antisymm (le_of_not_gt (fun h => hnone ⟨j,h⟩)) (hn i j)
    have hsum : (∑ j, E i j) = 0 := sum_eq_zero fun j _ => hall j
    linarith
  have hzero : ∀ x ∈ K, ∀ i, i ∉ Z → x i = 0 := by
    intro x hx i hi
    have hdi : δ i ≠ 0 := by simpa [Z] using hi
    exact (kernel_restrictions (fun _ => ρ) δ E hs hn hδ hrow hx).1 i
      (lt_of_le_of_ne (hδ i) (Ne.symm hdi))
  have hedge : ∀ x ∈ K, ∀ i j, (supportGraph E hs hz).Adj i j → x i + x j = 0 := by
    intro x hx i j hij
    exact (kernel_restrictions (fun _ => ρ) δ E hs hn hδ hrow hx).2 i j hij
  obtain ⟨hZ,e,he⟩ := component_pairing (supportGraph E hs hz) Z K
    hneigh hzero hedge hcard hlower
  have hd : ∀ i, δ i = 0 := by
    intro i
    have hi : i ∈ Z := hZ.symm ▸ mem_univ i
    exact (mem_filter.mp hi).2
  have hcross : ∀ i j, i ≠ j → ∀ b c, E (e (i,b)) (e (j,c)) = 0 := by
    intro i j hij b c
    exact le_antisymm (le_of_not_gt (fun h => hij (he (i,b) (j,c) h))) (hn _ _)
  refine ⟨hd,e,hcross,?_⟩
  intro i
  have hsum : (∑ z, E (e (i,false)) z) = E (e (i,false)) (e (i,true)) := by
    rw [← e.sum_comp (fun z => E (e (i,false)) z)]
    apply sum_eq_single (i,true)
    · rintro ⟨j,c⟩ _ hne
      by_cases hij : i=j
      · subst j
        cases c
        · exact hz _
        · exact False.elim (hne rfl)
      · exact hcross i j hij false c
    · simp
  have hr := hrow (e (i,false))
  rw [hd, add_zero, hsum] at hr
  exact hr

end CoveringDesigns.BoundaryRank
