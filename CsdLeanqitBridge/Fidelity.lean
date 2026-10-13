/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Fidelity
public import QIT.States.Geometry.FuchsVdG

/-!
# Fidelity: `csd-lean4` and Lean-QIT agree

`csd-lean4` defines the Uhlmann fidelity spectrally, `F(ρ, σ) = ∑ᵢ √λᵢ(√ρ σ √ρ)`
(`QuantumInfo.fidelity`). Lean-QIT defines it as a trace norm, `F(ρ, σ) = ‖√ρ √σ‖₁`
(`QIT.State.fidelity`). This file proves they are the same number on every density state
(`CsdLeanqitBridge.fidelity_eq`). The hinge is
`‖√ρ √σ‖₁ = Tr √((√ρ √σ)ᴴ (√ρ √σ)) = Tr √(√σ ρ √σ)`, which is `csd-lean4`'s `F(σ, ρ)`;
`csd-lean4`'s own symmetry theorem `QuantumInfo.fidelity_comm` turns it into `F(ρ, σ)`.

With that, Lean-QIT's `fidelity_le_one`, which holds for all density states, gives
`csd-lean4`'s fidelity bound without the positive-definiteness hypothesis `csd-lean4`'s own
`QuantumInfo.fidelity_le_one` needs (`CsdLeanqitBridge.fidelity_le_one_of_posSemidef`).
-/

@[expose] public section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace CsdLeanqitBridge

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The two square roots agree: `csd-lean4`'s `sqrtMat` (the Hermitian functional calculus
of `Real.sqrt`) is Lean-QIT's `psdSqrt` (Mathlib's `CFC.sqrt`) on positive semidefinite
matrices. -/
theorem sqrtMat_eq_psdSqrt {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    QuantumInfo.sqrtMat hρ.1 = QIT.psdSqrt ρ := by
  rw [QuantumInfo.sqrtMat, QIT.psdSqrt,
    CFC.sqrt_eq_real_sqrt ρ (Matrix.nonneg_iff_posSemidef.mpr hρ), cfcₙ_eq_cfc]
  exact (Matrix.IsHermitian.cfc_eq hρ.1 Real.sqrt).symm

/-- A state's square root, `csd-lean4` style, is Lean-QIT's `State.sqrtMatrix`. -/
theorem sqrtMat_eq_sqrtMatrix (ρ : QIT.State n) :
    QuantumInfo.sqrtMat ρ.pos.1 = ρ.sqrtMatrix :=
  sqrtMat_eq_psdSqrt ρ.pos

/-- **The two fidelities agree** on every pair of density states. -/
theorem fidelity_eq (ρ σ : QIT.State n) :
    QuantumInfo.fidelity ρ.pos σ.pos = ρ.fidelity σ := by
  have hA : (ρ.sqrtMatrix)ᴴ = ρ.sqrtMatrix := by
    rw [← sqrtMat_eq_sqrtMatrix]; exact QuantumInfo.sqrtMat_isHermitian ρ.pos.1
  have hB : (σ.sqrtMatrix)ᴴ = σ.sqrtMatrix := by
    rw [← sqrtMat_eq_sqrtMatrix]; exact QuantumInfo.sqrtMat_isHermitian σ.pos.1
  have hAA : ρ.sqrtMatrix * ρ.sqrtMatrix = ρ.matrix := by
    rw [← sqrtMat_eq_sqrtMatrix]; exact QuantumInfo.sqrtMat_mul_self ρ.pos
  have key : (ρ.sqrtMatrix * σ.sqrtMatrix)ᴴ * (ρ.sqrtMatrix * σ.sqrtMatrix) =
      σ.sqrtMatrix * ρ.matrix * σ.sqrtMatrix := by
    rw [conjTranspose_mul, hA, hB, ← hAA]
    simp only [Matrix.mul_assoc]
  rw [QuantumInfo.fidelity_comm, QuantumInfo.fidelity_eq_re_trace,
    sqrtMat_eq_psdSqrt (QuantumInfo.posSemidef_sandwich σ.pos ρ.pos),
    QIT.State.fidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix, QIT.traceNorm, key,
    sqrtMat_eq_sqrtMatrix]
  rfl

/-- **`F(ρ, σ) ≤ 1` for all density matrices**, in `csd-lean4`'s vocabulary. `csd-lean4`'s
own `QuantumInfo.fidelity_le_one` needs `ρ` and `σ` positive definite; Lean-QIT's bound
needs only positive semidefinite and trace one. -/
theorem fidelity_le_one_of_posSemidef {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    QuantumInfo.fidelity hρ hσ ≤ 1 :=
  (fidelity_eq ⟨ρ, hρ, hρ1⟩ ⟨σ, hσ, hσ1⟩).le.trans (QIT.State.fidelity_le_one _ _)

end CsdLeanqitBridge
