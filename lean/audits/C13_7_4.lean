import CoveringDesigns.C13_7_4
import Lean.Util.FoldConsts

/-! Audit the public theorem's explicit statement, foundational axioms, and
actual prerequisites. GPPT's structural reduction and Stanton's classification
must occur in the proof. Catalogue and completion-classification declarations
must be absent even from the imported environment. -/

namespace CoveringDesigns.Audit13
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for forbidden in #[`CoveringDesigns.linkCatalogue,
      `CoveringDesigns.linkRepresentative,
      `CoveringDesigns.gppt_classification,
      `CoveringDesigns.GPPTStructural.template_classification] do
    if env.contains forbidden then
      throwError m!"Unexpected catalogue/classification import: {forbidden}"
  logInfo "C13 import boundary: no catalogue or completion-classification declarations."

private def projectName (n : Name) : Bool :=
  n.toString.startsWith "CoveringDesigns." ||
    n.toString.startsWith "_private.CoveringDesigns."

private partial def dependencies (env : Environment) (n : Name)
    (seen : NameSet) : NameSet := Id.run do
  if seen.contains n || !projectName n then return seen
  let mut seen := seen.insert n
  if let some info := env.find? n then
    for dep in info.getUsedConstantsAsSet do
      seen := dependencies env dep seen
  return seen

elab "#guard_structural_dependencies " id:ident : command => do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← Lean.collectAxioms target
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axs.size == 3 && expected.all axs.contains do
    throwErrorAt id m!"Expected exactly the three standard axioms; found {axs}"
  let used := dependencies (← getEnv) target {}
  for prerequisite in #[`CoveringDesigns.gppt_structural_reduction,
      `CoveringDesigns.StantonStructural.template_classification] do
    unless used.contains prerequisite do
      throwErrorAt id m!"The proof did not reach the prerequisite {prerequisite}"
  let forbidden := used.toArray.filter fun n =>
    n == `CoveringDesigns.linkCatalogue ||
    n == `CoveringDesigns.linkRepresentative ||
    n == `CoveringDesigns.gppt_classification ||
    n == `CoveringDesigns.GPPTStructural.template_classification ||
    n.toString.startsWith "CoveringDesigns.GPPTStructural.CompletionVerification."
  unless forbidden.isEmpty do
    throwErrorAt id m!"Forbidden completion-enumeration dependencies: {forbidden}"
  logInfo m!"{target}: exactly three standard axioms; {used.size} project declarations inspected; structural GPPT and Stanton prerequisites reached; no completion enumeration."

/-- The result stated directly in terms of finite subsets and coverage. -/
theorem covering_number_explicit :
    (∃ C : Finset (Finset (Fin 13)),
      (∀ B ∈ C, B.card = 7) ∧
      (∀ T : Finset (Fin 13), T.card = 4 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 30) ∧
    (∀ C : Finset (Finset (Fin 13)),
      (∀ B ∈ C, B.card = 7) →
      (∀ T : Finset (Fin 13), T.card = 4 → ∃ B ∈ C, T ⊆ B) → 30 ≤ C.card) := by
  constructor
  · obtain ⟨C, hC, hcard⟩ := CoveringDesigns.covering_number_13_7_4.1
    exact ⟨C, hC.1, hC.2, hcard⟩
  · intro C hu hc
    exact CoveringDesigns.lower_bound_30 ⟨hu, hc⟩

#guard_structural_dependencies CoveringDesigns.covering_number_13_7_4
#guard_structural_dependencies covering_number_explicit
#guard_standard_axioms C13Structural.minimum_pair_degree_seven
  C13Structural.bad_quadruple_excluded CoveringDesigns.lower_bound_30
  CoveringDesigns.upper_bound_30

#print covering_number_explicit
#print CoveringDesigns.covering_number_13_7_4
#print axioms covering_number_explicit
#print axioms CoveringDesigns.covering_number_13_7_4
#print axioms CoveringDesigns.lower_bound_30
#print axioms CoveringDesigns.upper_bound_30
#print axioms C13Structural.minimum_pair_degree_seven
#print axioms C13Structural.bad_quadruple_excluded
#print axioms CoveringDesigns.gppt_structural_reduction
#print axioms CoveringDesigns.StantonStructural.template_classification

end CoveringDesigns.Audit13
