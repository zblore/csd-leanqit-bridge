/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLeanqitBridge.Fidelity
public import CsdLean4.Mathlib.QuantumInfo.Channel
public import QIT.States.Purification.Uhlmann

/-!
# Fidelity cannot decrease under a channel

`csd-lean4`'s channels are in Kraus form, `Φ(ρ) = ∑ᵢ Kᵢ ρ Kᵢᴴ` with `∑ᵢ Kᵢᴴ Kᵢ = 1`
(`QuantumInfo.Channel`). Lean-QIT's are linear maps that are completely positive (Choi
matrix positive semidefinite) and trace preserving (`QIT.Channel`). Lean-QIT's `ofKraus` uses
the same convention, `X ↦ ∑ᵢ Kᵢ X Kᵢᴴ`, and proves Kraus-form maps completely positive, so every
`csd-lean4` channel is a Lean-QIT channel (`CsdLeanqitBridge.toQITChannel`) acting the same way
on states (`CsdLeanqitBridge.toQITChannel_applyState_matrix`).

Lean-QIT proves that squared fidelity cannot decrease under a channel
(`QIT.State.squaredFidelity_le_applyState_squaredFidelity`, via Uhlmann's theorem and a
Stinespring dilation). With `CsdLeanqitBridge.fidelity_eq` this reads in `csd-lean4`'s
vocabulary as `F(ρ, σ) ≤ F(Φ ρ, Φ σ)` (`CsdLeanqitBridge.fidelity_le_apply`), the monotonicity
`csd-lean4`'s fidelity module lists as not attempted.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace CsdLeanqitBridge

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-- A `csd-lean4` channel in Kraus form, as a Lean-QIT channel. -/
noncomputable def toQITChannel (Φ : QuantumInfo.Channel n m ι) : QIT.Channel n m where
  map := QIT.MatrixMap.ofKraus Φ.kraus
  completelyPositive := QIT.MatrixMap.ofKraus_completelyPositive Φ.kraus
  tracePreserving := fun X => Φ.apply_trace X
  mapsPositive := fun _ hX => Φ.apply_posSemidef hX

/-- The Lean-QIT channel acts on a state's matrix exactly as the `csd-lean4` channel does. -/
theorem toQITChannel_applyState_matrix (Φ : QuantumInfo.Channel n m ι) (ρ : QIT.State n) :
    ((toQITChannel Φ).applyState ρ).matrix = Φ.apply ρ.matrix :=
  rfl

/-- **Fidelity cannot decrease under a channel**, in `csd-lean4`'s vocabulary: for density
matrices `ρ, σ` and a channel `Φ` in Kraus form, `F(ρ, σ) ≤ F(Φ ρ, Φ σ)`. -/
theorem fidelity_le_apply (Φ : QuantumInfo.Channel n m ι) {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    QuantumInfo.fidelity hρ hσ ≤
      QuantumInfo.fidelity (Φ.apply_posSemidef hρ) (Φ.apply_posSemidef hσ) := by
  let R : QIT.State n := ⟨ρ, hρ, hρ1⟩
  let S : QIT.State n := ⟨σ, hσ, hσ1⟩
  have hmono := QIT.State.squaredFidelity_le_applyState_squaredFidelity (toQITChannel Φ) R S
  rw [QIT.State.squaredFidelity_eq_fidelity_sq, QIT.State.squaredFidelity_eq_fidelity_sq,
    pow_le_pow_iff_left₀ (QIT.State.fidelity_nonneg _ _) (QIT.State.fidelity_nonneg _ _)
      two_ne_zero] at hmono
  rw [fidelity_eq R S] at *
  exact hmono.trans_eq
    (fidelity_eq ((toQITChannel Φ).applyState R) ((toQITChannel Φ).applyState S)).symm

end CsdLeanqitBridge
