import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
A build guard on the transitive axioms of named declarations.  The allowed
axioms are an upper bound: a theorem needing fewer axioms also passes.
-/

namespace CoveringDesigns

open Lean Elab Command

/-- Reject a declaration using an axiom other than `propext`,
`Classical.choice`, or `Quot.sound`, including through imported theorems. -/
elab "#guard_standard_axioms " ids:ident+ : command => do
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless forbidden.isEmpty do
      let names := String.intercalate ", " (forbidden.toList.map Name.toString)
      throwErrorAt id "{name}: forbidden axioms: {names}"

end CoveringDesigns
