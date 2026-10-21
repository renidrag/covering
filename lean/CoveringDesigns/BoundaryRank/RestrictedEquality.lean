import CoveringDesigns.BoundaryRank.Equality

/-! Equality after restriction to the zero-deficit vertices. This classifies
the excess graph only; an arbitrary PSD remainder does not imply equal rows.
Formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.BoundaryRank
open Finset Matrix Module
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Restrict a space vanishing off a closed vertex set before invoking the
component equality theorem. Cardinality and dimension equality are explicit. -/
theorem restricted_component_pairing
    (G : SimpleGraph ι) (Z : Finset ι) (K : Submodule ℝ (ι → ℝ))
    (hneigh : ∀ i ∈ Z, ∃ j, G.Adj i j)
    (hclosed : ∀ i ∈ Z, ∀ j, G.Adj i j → j ∈ Z)
    (hzero : ∀ x ∈ K, ∀ i, i ∉ Z → x i = 0)
    (hedge : ∀ x ∈ K, ∀ i j, G.Adj i j → x i + x j = 0)
    (hcard : Z.card = 2 * Fintype.card κ)
    (hdim : Fintype.card κ ≤ finrank ℝ K) :
    ∃ e : κ × Bool ≃ ↥Z,
      ∀ i j, G.Adj (e i).val (e j).val → i.1 = j.1 := by
  classical
  let L : K →ₗ[ℝ] (↥Z → ℝ) :=
    LinearMap.pi fun i => (LinearMap.proj i.val).comp K.subtype
  have hL : Function.Injective L := by
    intro x y he
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ Z
    · exact congr_fun he ⟨i,hi⟩
    · exact (hzero x x.property i hi).trans (hzero y y.property i hi).symm
  let GZ : SimpleGraph ↥Z := G.induce (Z : Set ι)
  have hn : ∀ i ∈ (univ : Finset ↥Z), ∃ j, GZ.Adj i j := by
    intro i _
    obtain ⟨j,hj⟩ := hneigh i.val i.property
    exact ⟨⟨j,hclosed i.val i.property j hj⟩,hj⟩
  have he : ∀ x ∈ LinearMap.range L, ∀ i j, GZ.Adj i j → x i + x j = 0 := by
    intro x hx i j hij
    obtain ⟨y,rfl⟩ := hx
    exact hedge y y.property i.val j.val hij
  obtain ⟨_,e,he⟩ := component_pairing (κ := κ) GZ univ (LinearMap.range L)
    hn (by simp) he (by simpa using hcard)
    (by rwa [LinearMap.finrank_range_of_inj hL])
  exact ⟨e,he⟩

/-- Tight restricted kernel dimension forces paired zero-deficit components
of weight ρ. The complement must have no edges into the zero set. -/
theorem restricted_kernel_pairing
    (ρ : ℝ) (E : Matrix ι ι ℝ) (δ : ι → ℝ)
    (hρ : 0 < ρ) (hs : ∀ i j, E i j = E j i)
    (hn : ∀ i j, 0 ≤ E i j) (hz : ∀ i, E i i = 0)
    (hδ : ∀ i, 0 ≤ δ i) (hrow : ∀ i, (∑ j, E i j) + δ i = ρ)
    (hclosed : ∀ i j, δ i = 0 → δ j ≠ 0 → E i j = 0)
    (hcard : (univ.filter (fun i => δ i = 0)).card = 2 * Fintype.card κ)
    (hdim : Fintype.card κ ≤
      finrank ℝ (LinearMap.ker (Matrix.diagonal (fun _ => ρ) + E).mulVecLin)) :
    ∃ e : κ × Bool ≃ ↥(univ.filter (fun i => δ i = 0)),
      (∀ i j, i ≠ j → ∀ b c, E (e (i,b)).val (e (j,c)).val = 0) ∧
      (∀ i, E (e (i,false)).val (e (i,true)).val = ρ) := by
  classical
  let Z := univ.filter fun i => δ i = 0
  let G := supportGraph E hs hz
  let K := LinearMap.ker (Matrix.diagonal (fun _ => ρ) + E).mulVecLin
  have hneigh : ∀ i ∈ Z, ∃ j, G.Adj i j := by
    intro i hi
    have hr := hrow i
    rw [(mem_filter.mp hi).2, add_zero] at hr
    by_contra hnone
    have hall : ∀ j, E i j = 0 := fun j =>
      le_antisymm (le_of_not_gt (fun h => hnone ⟨j,h⟩)) (hn i j)
    have hsum : (∑ j, E i j) = 0 := sum_eq_zero fun j _ => hall j
    linarith
  have hc : ∀ i ∈ Z, ∀ j, G.Adj i j → j ∈ Z := by
    intro i hi j hij
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    by_contra hj
    have he := hclosed i j (mem_filter.mp hi).2 hj
    change 0 < E i j at hij
    linarith
  have hzero : ∀ x ∈ K, ∀ i, i ∉ Z → x i = 0 := by
    intro x hx i hi
    have hdi : δ i ≠ 0 := by simpa [Z] using hi
    exact (kernel_restrictions (fun _ => ρ) δ E hs hn hδ hrow hx).1 i
      (lt_of_le_of_ne (hδ i) (Ne.symm hdi))
  have hedge : ∀ x ∈ K, ∀ i j, G.Adj i j → x i + x j = 0 := by
    intro x hx i j hij
    exact (kernel_restrictions (fun _ => ρ) δ E hs hn hδ hrow hx).2 i j hij
  obtain ⟨e,he⟩ := restricted_component_pairing (κ := κ) G Z K
    hneigh hc hzero hedge hcard hdim
  have hcross : ∀ i j, i ≠ j → ∀ b c, E (e (i,b)).val (e (j,c)).val = 0 := by
    intro i j hij b c
    exact le_antisymm (le_of_not_gt (fun h => hij (he (i,b) (j,c) h))) (hn _ _)
  refine ⟨e,hcross,?_⟩
  intro i
  have hdi : δ (e (i,false)).val = 0 := (mem_filter.mp (e (i,false)).property).2
  have hsumZ : (∑ z, E (e (i,false)).val z) =
      ∑ z : ↥Z, E (e (i,false)).val z.val := by
    rw [sum_coe_sort]
    symm
    apply sum_subset (subset_univ _)
    intro z _ hzZ
    exact hclosed _ z hdi (by simpa [Z] using hzZ)
  have hsum : (∑ z, E (e (i,false)).val z) =
      E (e (i,false)).val (e (i,true)).val := by
    rw [hsumZ, ← e.sum_comp (fun z => E (e (i,false)).val z.val)]
    apply sum_eq_single (i,true)
    · rintro ⟨j,c⟩ _ hne
      by_cases hij : i=j
      · subst j
        cases c
        · exact hz _
        · exact False.elim (hne rfl)
      · exact hcross i j hij false c
    · simp
  have hr := hrow (e (i,false)).val
  rw [hdi, add_zero, hsum] at hr
  exact hr

end CoveringDesigns.BoundaryRank
