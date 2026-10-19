import CoveringDesigns.BoundaryRank.Signless
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# A component-coordinate bound for a boundary signless kernel

One coordinate determines a vector on a support component. Components meeting
a positive deficit contribute no coordinates; every remaining component has
at least two vertices. This gives the needed nullity bound without a
bipartite-component classification. Formalisation: Rob Gardiner with AI
assistance.
-/

namespace CoveringDesigns.BoundaryRank

open Finset Matrix Module

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem zero_of_reachable (G : SimpleGraph ι) (x : ι → ℝ)
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

/-- A finite support graph bounds the dimension of any space of vectors that
alternate along its edges and vanish outside `Z`.  Non-isolation is required
only on `Z`; components may be disconnected and need not be bipartite. -/
theorem two_mul_finrank_le_card_of_component_constraints
    (G : SimpleGraph ι) (Z : Finset ι) (K : Submodule ℝ (ι → ℝ))
    (hneigh : ∀ i ∈ Z, ∃ j, G.Adj i j)
    (hzero : ∀ x ∈ K, ∀ i, i ∉ Z → x i = 0)
    (hedge : ∀ x ∈ K, ∀ i j, G.Adj i j → x i + x j = 0) :
    2 * finrank ℝ K ≤ Z.card := by
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
          have hreach : G.Reachable (rep a) i :=
            c.reachable_of_mem_supp (hrep a) rfl
          exact zero_of_reachable G x (hedge x x.property) hreach hxr
        · push Not at hc
          obtain ⟨j, hjc, hjZ⟩ := hc
          have hxj : x.val j = 0 := hzero x x.property j hjZ
          have hreach : G.Reachable j i := c.reachable_of_mem_supp hjc rfl
          exact zero_of_reachable G x (hedge x x.property) hreach hxj
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
  have hcard := Fintype.card_le_of_injective pick hpick
  have htwice : 2 * Fintype.card Active ≤ Z.card := by
    simpa [Fintype.card_prod, Nat.mul_comm] using hcard
  omega

/-- The loopless positive support graph of a symmetric nonnegative matrix. -/
def supportGraph (E : Matrix ι ι ℝ) (hs : ∀ i j, E i j = E j i)
    (hz : ∀ i, E i i = 0) : SimpleGraph ι where
  Adj i j := 0 < E i j
  symm := ⟨fun i j h => by rwa [hs j i]⟩
  loopless := ⟨fun i h => by simpa [hz i] using h⟩

/-- At positive constant diagonal, twice the nullity is at most the number
of zero-deficit vertices. Weighted edges and disconnected support are allowed. -/
theorem two_mul_nullity_le_zero_count (ρ : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ) :
    2 * finrank ℝ (LinearMap.ker (Matrix.diagonal (fun _ => ρ) + E).mulVecLin) ≤
      (univ.filter fun i => δ i = 0).card := by
  classical
  apply two_mul_finrank_le_card_of_component_constraints (supportGraph E hs hz)
  · intro i hi
    have hdi : δ i = 0 := (mem_filter.mp hi).2
    have hr := hrow i
    rw [hdi, add_zero] at hr
    by_contra hnone
    have hall : ∀ j, E i j = 0 := by
      intro j
      have hnot : ¬ 0 < E i j := fun h => hnone ⟨j, h⟩
      exact le_antisymm (le_of_not_gt hnot) (hn i j)
    have hsum : (∑ j, E i j) = 0 := sum_eq_zero fun j _ => hall j
    linarith
  · intro x hx i hi
    have hdi : δ i ≠ 0 := by simpa using hi
    exact (kernel_restrictions (fun _ => ρ) δ E hs hn hδ hrow hx).1 i
      (lt_of_le_of_ne (hδ i) (Ne.symm hdi))
  · intro x hx i j hij
    exact (kernel_restrictions (fun _ => ρ) δ E hs hn hδ hrow hx).2 i j hij

/-- A Gram decomposition at the positive signless boundary.  The explicitly
proved PSD kernel inclusion combines with rank-nullity and the column bound. -/
theorem gram_card_bound [Fintype κ]
    (R : Matrix ι κ ℝ) (ρ : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ)
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    (hgram : R * R.transpose = Matrix.diagonal (fun _ => ρ) + E + P) :
    2 * Fintype.card ι ≤ 2 * Fintype.card κ + (univ.filter fun i => δ i = 0).card := by
  have hnull := two_mul_nullity_le_zero_count ρ E δ hρ hs hn hz hδ hrow
  have hpsd := signless_posSemidef (fun _ => ρ) δ E hs hn hδ hrow
  have hker := ker_add_le_of_posSemidef hpsd hP
  rw [← hgram] at hker
  have hdim := Submodule.finrank_mono hker
  have hrank : (R * R.transpose).rank ≤ Fintype.card κ :=
    (Matrix.rank_mul_le_left R R.transpose).trans R.rank_le_card_width
  have hnullity := LinearMap.finrank_range_add_finrank_ker (R * R.transpose).mulVecLin
  have htotal : (R * R.transpose).rank +
      finrank ℝ (LinearMap.ker (R * R.transpose).mulVecLin) = Fintype.card ι := by
    simpa [Matrix.rank] using hnullity
  omega

end CoveringDesigns.BoundaryRank
