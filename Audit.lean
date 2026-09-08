import Kourovka
import Tests
import Lean.Util.CollectAxioms

/-!
# Transitive axiom audit

Audit every declaration in the project namespace, including dependencies
introduced by generated instances and private auxiliary declarations.
`collectAxioms` traverses proof dependencies, so an admitted intermediate lemma
cannot hide behind a successfully compiled final theorem.
-/

open Lean in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, _) in environment.constants.toList do
    if (`Kourovka).isPrefixOf name || (`Tests).isPrefixOf name ||
        name.toString.startsWith "_private.Kourovka." ||
        name.toString.startsWith "_private.Tests." then
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      count := count + 1
  unless count > 0 do
    throwError "No project declarations were imported"
  logInfo m!"Axiom audit passed for {count} project declarations."

#print axioms Kourovka.MetabelianEnumeration.Paper.certificateCheck_primrec
#print axioms Kourovka.MetabelianEnumeration.Paper.metabelian_iff_certificate
#print axioms Kourovka.MetabelianEnumeration.Paper.metabelian_presentations_re
