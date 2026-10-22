import CoveringDesigns.QuadrupleAssembly.WitnessData.V25.Data
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000
namespace CoveringDesigns.QuadrupleAssembly.WitnessData.V25
theorem forward5 : selectorCoverAt id 3 rows ownerIndex 5 = true := by decide +kernel
end CoveringDesigns.QuadrupleAssembly.WitnessData.V25
