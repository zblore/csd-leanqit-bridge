/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLeanqitBridge

/-!
# Axiom audit for the bridge

Every exported theorem, and the Lean-QIT theorems it rests on, depend on the foundational triple
only. `lake build CsdLeanqitBridgeTests` fails if any pin drifts.
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
