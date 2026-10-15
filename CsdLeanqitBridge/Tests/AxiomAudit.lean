/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLeanqitBridge

/-!
# Axiom audit for the bridge

Every declaration of the bridge, and the Lean-QIT theorems it rests on, depend on the
foundational triple only. Each export is pinned by name below; a final inventory check then walks
every declaration under `CsdLeanqitBridge`, so one added later cannot escape the audit, and pins
their number. `lake build CsdLeanqitBridgeTests` fails if any pin drifts.
-/

/-- info: 'CsdLeanqitBridge.fidelity_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.fidelity_eq

/-- info: 'CsdLeanqitBridge.traceDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.traceDist_eq

/-- info: 'CsdLeanqitBridge.fidelity_le_one_of_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.fidelity_le_one_of_posSemidef

/-- info: 'CsdLeanqitBridge.fuchs_van_de_graaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.fuchs_van_de_graaf

/-- info: 'QIT.State.fidelity_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QIT.State.fidelity_le_one

/-- info: 'QIT.State.fuchs_van_de_graaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QIT.State.fuchs_van_de_graaf

/-- info: 'CsdLeanqitBridge.fidelity_le_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.fidelity_le_apply

/-- info: 'QIT.State.squaredFidelity_le_applyState_squaredFidelity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QIT.State.squaredFidelity_le_applyState_squaredFidelity

/-- info: 'CsdLeanqitBridge.fidelity_preparation_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.fidelity_preparation_le_one

/-- info: 'CsdLeanqitBridge.fuchs_van_de_graaf_preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.fuchs_van_de_graaf_preparation

/-- info: 'CsdLeanqitBridge.fidelity_preparation_le_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.fidelity_preparation_le_apply

/-- info: 'CsdLeanqitBridge.fidelity_le_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.fidelity_le_flow

/-- info: 'CsdLeanqitBridge.fidelity_preparation_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.fidelity_preparation_flow

/-- info: 'CsdLeanqitBridge.sqrtMat_eq_psdSqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.sqrtMat_eq_psdSqrt

/-- info: 'CsdLeanqitBridge.sqrtMat_eq_sqrtMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.sqrtMat_eq_sqrtMatrix

/-- info: 'CsdLeanqitBridge.traceNorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.traceNorm_eq

/-- info: 'CsdLeanqitBridge.toQITChannel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.toQITChannel

/-- info: 'CsdLeanqitBridge.toQITChannel_applyState_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.toQITChannel_applyState_matrix

/-- info: 'CsdLeanqitBridge.fidelity_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.fidelity_congr

/-- info: 'CsdLeanqitBridge.fidelity_unitary_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CsdLeanqitBridge.fidelity_unitary_conj

/-- info: inventory: 17 declarations, all on the foundational triple -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ours := env.constants.fold (fun (acc : Array Name) n _ ↦
    if (`CsdLeanqitBridge).isPrefixOf n && !n.isInternal then acc.push n else acc) #[]
  for n in ours do
    let extra := (← collectAxioms n).filter fun a ↦ !standard.contains a
    unless extra.isEmpty do throwError m!"{n} uses axioms outside the standard three: {extra}"
  logInfo m!"inventory: {ours.size} declarations, all on the foundational triple"
