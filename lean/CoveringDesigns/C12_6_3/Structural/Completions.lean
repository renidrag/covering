import CoveringDesigns.C12_6_3.Structural.CompletionChecks

/-!
Every completion of GPPT Figure 1 is isomorphic to one of catalogue entries 0–66.

An explicit automorphism first sends the added pair at spine 0 to {4,5} or {4,8}.
The other two added pairs each have 28 choices. The resulting 1,568 cases carry
explicit isomorphisms to the displayed catalogue, checked by the Lean kernel.
This theorem assumes only the Figure 1 shape; the reduction of arbitrary minimum
coverings to that shape belongs to the structural GPPT argument.
-/

namespace CoveringDesigns.GPPTStructural
namespace CompletionVerification

open Finset

theorem autAt_good (i : Fin 256) :
    GoodAut (pointMap (autAt i).1) (fibreMap (autAt i).2.2) := by
  apply autCheck_sound
  exact List.all_eq_true.mp automorphisms_checked _ (List.getElem_mem _)

theorem choice_complete {i : Fin 3} {R : Finset (Fin 12)}
    (hs : R ⊆ univ \ spine i) (hc : R.card = 2) :
    ∃ j : Fin 28, R = pairSet (choice i j) := by
  have hm : R ∈ (univ \ spine i).powersetCard 2 := mem_powersetCard.mpr ⟨hs, hc⟩
  rw [choices_checked] at hm
  obtain ⟨j, _, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  exact ⟨j, he.symm⟩

theorem normalizer_sound (j : Fin 28) :
    fibreMap (autAt (normalizer j).2).2.2 0 = 0 ∧
      (pairSet (choice 0 j)).image (pointMap (autAt (normalizer j).2).1) =
        pairSet (firstPair (normalizer j).1) := by
  have h := List.all_eq_true.mp normalizers_checked j (by simp)
  simp only [normalizerCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, (image_pairSet _ _).trans (pairEq_sound h.2)⟩

theorem exists_normalization {R : Fin 3 → Finset (Fin 12)} (hR : ValidAdditions R) :
    ∃ x : NormalInput, Isomorphic (templateBlocks R) (templateBlocks (normalAdditions x)) := by
  obtain ⟨j₀, hj₀⟩ := choice_complete (hR 0).1 (hR 0).2
  let n := normalizer j₀
  let a := autAt n.2
  have ha := autAt_good n.2
  let f : Equiv.Perm (Fin 3) := Equiv.ofBijective (fibreMap a.2.2)
    ⟨ha.fibre_injective, Finite.surjective_of_injective ha.fibre_injective⟩
  have haf : GoodAut (pointMap a.1) f := ha
  let S := transportedAdditions (pointMap a.1) f R
  have hS : ValidAdditions S := valid_transported haf hR
  have hf0 : f 0 = 0 := (normalizer_sound j₀).1
  have hfi0 : f.symm 0 = 0 := by
    apply f.injective
    simpa only [Equiv.apply_symm_apply] using hf0.symm
  have hS0 : S 0 = pairSet (firstPair n.1) := by
    change (R (f.symm 0)).image (pointMap a.1) = _
    rw [hfi0, hj₀]
    exact (normalizer_sound j₀).2
  obtain ⟨j, hj⟩ := choice_complete (hS 1).1 (hS 1).2
  obtain ⟨k, hk⟩ := choice_complete (hS 2).1 (hS 2).2
  refine ⟨(n.1, j, k), ?_⟩
  have he : S = normalAdditions (n.1, j, k) := by
    funext i
    fin_cases i
    · exact hS0
    · exact hj
    · exact hk
  exact he ▸ template_isomorphic_transported haf R

theorem normalInput_mem (x : NormalInput) : x ∈ allNormalInputs := by
  rcases x with ⟨b, j, k⟩
  apply List.mem_flatMap.mpr
  refine ⟨b, by cases b <;> simp, ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨j, by simp, List.mem_map.mpr ⟨k, by simp, rfl⟩⟩

theorem completionRow_exists (x : NormalInput) :
    ∃ r ∈ completionRows, r.1 = x := by
  have hm : x ∈ completionRows.map Prod.fst := by
    rw [completion_inputs_checked]
    exact normalInput_mem x
  exact List.mem_map.mp hm

theorem target_eq_catalogue (c : Fin 67) :
    templateBlocks (targetAdditions c) = linkRepresentative c.castSucc := by
  exact of_decide_eq_true (List.all_eq_true.mp targets_checked c (by simp))

theorem completionCheck_sound {r : CompletionRow} (h : completionCheck r = true) :
    Isomorphic (templateBlocks (normalAdditions r.1)) (linkRepresentative r.2.2.castSucc) := by
  rw [← target_eq_catalogue]
  apply isomorphic_of_image (pointMap (autAt r.2.1).1) (autAt_good r.2.1).point_injective
  apply image_template (autAt_good r.2.1)
  intro i
  exact (image_pairSet _ _).trans (pairEq_sound (List.all_eq_true.mp h i (by simp)))

theorem normalized_classification (x : NormalInput) :
    ∃ c : Fin 67, Isomorphic (templateBlocks (normalAdditions x))
      (linkRepresentative c.castSucc) := by
  obtain ⟨r, hr, he⟩ := completionRow_exists x
  refine ⟨r.2.2, ?_⟩
  rw [← he]
  exact completionCheck_sound (List.all_eq_true.mp completions_checked r hr)

end CompletionVerification

open CompletionVerification in
/-- Figure 1 completions need only the first 67 members of the 68-cover catalogue. -/
theorem template_classification {R : Fin 3 → Finset (Fin 12)} (hR : ValidAdditions R) :
    ∃ c : Fin 67, Isomorphic (templateBlocks R) (linkRepresentative c.castSucc) := by
  obtain ⟨x, hx⟩ := exists_normalization hR
  obtain ⟨c, hc⟩ := normalized_classification x
  exact ⟨c, hx.trans hc⟩

theorem IsTemplateCompletion.classification {C : Family (Fin 12)}
    (h : IsTemplateCompletion C) : ∃ c : Fin 68, Isomorphic C (linkRepresentative c) := by
  obtain ⟨R, hR, rfl⟩ := h
  obtain ⟨c, hc⟩ := template_classification hR
  exact ⟨c.castSucc, hc⟩

theorem IsomorphicTemplateCompletion.classification {C : Family (Fin 12)}
    (h : IsomorphicTemplateCompletion C) : ∃ c : Fin 68, Isomorphic C (linkRepresentative c) := by
  obtain ⟨D, hD, hCD⟩ := h
  obtain ⟨c, hc⟩ := hD.classification
  exact ⟨c, hCD.trans hc⟩

#guard_standard_axioms template_classification IsTemplateCompletion.classification
  IsomorphicTemplateCompletion.classification
#print axioms template_classification

end CoveringDesigns.GPPTStructural
