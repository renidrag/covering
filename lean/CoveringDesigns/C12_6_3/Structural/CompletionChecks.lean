import CoveringDesigns.C12_6_3.Structural.CompletionData
import CoveringDesigns.C12_6_3.Structural.CompletionSupport
import CoveringDesigns.C12_6_3.Catalogue

/-!
Kernel verification of explicit isomorphism witnesses for Figure 1 completions.
There is no search for coverings here. Each check is equality of small finite data.
The four synchronous chunks keep peak memory bounded when Lake builds in parallel.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option cbv.maxSteps 10000000
set_option Elab.async false

namespace CoveringDesigns.GPPTStructural.CompletionVerification

theorem aut0_checked : autChunk0.all autCheck = true := by decide_cbv
theorem aut1_checked : autChunk1.all autCheck = true := by decide_cbv
theorem aut2_checked : autChunk2.all autCheck = true := by decide_cbv
theorem aut3_checked : autChunk3.all autCheck = true := by decide_cbv

theorem automorphisms_checked : autList.all autCheck = true := by
  simp [autList, List.all_append, aut0_checked, aut1_checked, aut2_checked, aut3_checked]

theorem completion0_checked : completionChunk0.all completionCheck = true := by decide_cbv
theorem completion1_checked : completionChunk1.all completionCheck = true := by decide_cbv
theorem completion2_checked : completionChunk2.all completionCheck = true := by decide_cbv
theorem completion3_checked : completionChunk3.all completionCheck = true := by decide_cbv

theorem completions_checked : completionRows.all completionCheck = true := by
  simp [completionRows, List.all_append, completion0_checked, completion1_checked,
    completion2_checked, completion3_checked]

theorem completion_inputs_checked : completionRows.map Prod.fst = allNormalInputs := by
  decide_cbv

theorem normalizers_checked : (List.finRange 28).all normalizerCheck = true := by
  decide_cbv

theorem targets_checked : (List.finRange 67).all (fun c => decide
    (templateBlocks (targetAdditions c) = linkRepresentative c.castSucc)) = true := by
  decide +kernel

theorem choices_checked : ∀ i : Fin 3,
    (Finset.univ \ spine i).powersetCard 2 =
      ((List.finRange 28).map (fun j => pairSet (choice i j))).toFinset := by
  decide +kernel

#guard_standard_axioms automorphisms_checked completions_checked completion_inputs_checked
  normalizers_checked targets_checked choices_checked

end CoveringDesigns.GPPTStructural.CompletionVerification
