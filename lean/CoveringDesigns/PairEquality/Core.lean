import CoveringDesigns.PairEquality.Dimension

/-! Construction of the unchanged Plane interface on the original coordinates. -/

namespace CoveringDesigns.PairEquality
open Finset Internal
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The reduced minimum-degree branch supplies every field of the existing
truncated-plane contract, with exactly the actual reduced support family. -/
theorem plane_of_degree_q {q : ℕ} (hq : 0 < q)
    {H : Finset (Finset I)} {w : Finset I → ℝ} (h : PositiveUnitLoads q H w)
    (hli : LinearIndependent ℝ (fun E : H => indicator E.val))
    (hex : ∃ x, degree H x = q) :
    ∃ P : TruncatedPlaneLoads.Plane q I (Fin (q+1)), P.core = H := by
  classical
  obtain ⟨hcard,hd⟩ := degree_q_everywhere hq h hli hex
  let G := univ.image (starGroup H)
  have memG (x : I) : starGroup H x ∈ G := mem_image.mpr ⟨x,mem_univ _,rfl⟩
  have hgsize (C : Finset I) (hC : C ∈ G) : C.card = q := by
    obtain ⟨x,_,rfl⟩ := mem_image.mp hC
    exact starGroup_card h (hd x)
  have hdisj (C : Finset I) (hC : C ∈ G) (D : Finset I) (hD : D ∈ G)
      (hCD : C ≠ D) : Disjoint C D := by
    obtain ⟨x,_,rfl⟩ := mem_image.mp hC
    obtain ⟨y,_,rfl⟩ := mem_image.mp hD
    exact (starGroup_equal_or_disjoint h (hd x) (hd y)).resolve_left hCD
  have hcover : G.biUnion id = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_biUnion.mpr ⟨starGroup H x,memG x,by simp⟩
  have hgcard : Fintype.card G = q+1 := by
    have he := card_biUnion (s := G) (t := id) hdisj
    simp only [id_eq] at he
    rw [hcover,card_univ,sum_congr rfl hgsize] at he
    simp only [sum_const,nsmul_eq_mul] at he
    have hc : G.card = q+1 := by rw [h.coordinates] at he; nlinarith
    simpa using hc
  let e : G ≃ Fin (q+1) := Fintype.equivFinOfCardEq hgcard
  let g : I → Fin (q+1) := fun x => e ⟨starGroup H x,memG x⟩
  have fibre (x y : I) : g y = g x ↔ y ∈ starGroup H x := by
    change e ⟨starGroup H y,memG y⟩ = e ⟨starGroup H x,memG x⟩ ↔ _
    rw [e.injective.eq_iff,Subtype.mk.injEq]
    constructor
    · intro he
      rw [← he]
      simp
    · intro hy
      rcases starGroup_equal_or_disjoint h (hd x) (hd y) with he | he
      · exact he.symm
      · exact False.elim (disjoint_left.mp he hy (by simp))
  have hsurj : Function.Surjective g := by
    intro i
    obtain ⟨x,_,hx⟩ := mem_image.mp (e.symm i).property
    refine ⟨x,?_⟩
    change e ⟨starGroup H x,memG x⟩ = i
    have he : (⟨starGroup H x,memG x⟩ : G) = e.symm i := Subtype.ext hx
    rw [he,e.apply_symm_apply]
  have filter_group (x : I) : univ.filter (g · = g x) = starGroup H x := by
    ext y
    simp [fibre]
  have filter_edge (E : Finset I) (x : I) : E.filter (g · = g x) = E ∩ starGroup H x := by
    ext y
    simp [fibre]
  let P : TruncatedPlaneLoads.Plane q I (Fin (q+1)) := {
    group := g
    core := H
    groups_card := Fintype.card_fin _
    group_card := by
      intro i
      obtain ⟨x,rfl⟩ := hsurj i
      rw [filter_group]
      exact starGroup_card h (hd x)
    transversal := by
      intro E hE i
      obtain ⟨x,rfl⟩ := hsurj i
      rw [filter_edge]
      exact starGroup_transversal h (hd x) hE
    degree := hd
    codegree := by
      intro x y hxy
      change codegree H x y = _
      rw [starGroup_codegree h (hd x) hxy]
      by_cases he : g x = g y
      · rw [ite_eq_left he,ite_eq_left ((fibre x y).mp he.symm)]
      · rw [ite_eq_right he,ite_eq_right (fun hy => he ((fibre x y).mpr hy).symm)]
    intersection := by
      intro E hE F hF hEF
      obtain ⟨x,hx⟩ := card_pos.mp (by rw [h.uniform E hE]; omega : 0 < E.card)
      exact h.saturated_intersection hE (h.saturated_of_degree (hd x) hE hx) hF hEF }
  exact ⟨P,rfl⟩

end CoveringDesigns.PairEquality
