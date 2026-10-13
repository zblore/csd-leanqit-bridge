/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLeanqitBridge.Fidelity
public import CsdLean4.Mathlib.QuantumInfo.TraceDistance

/-!
# Trace distance, and Fuchs–van de Graaf

`csd-lean4`'s trace distance is `½ ∑ᵢ |λᵢ(ρ − σ)|` (`QuantumInfo.traceDist`); Lean-QIT's is
`½ ‖ρ − σ‖₁` with `‖M‖₁ = Tr √(Mᴴ M)` (`QIT.State.normalizedTraceDistance`). For a Hermitian
`H`, `√(Hᴴ H) = |H|`, whose trace is `∑ᵢ |λᵢ(H)|`, so the two agree
(`CsdLeanqitBridge.traceDist_eq`).

With fidelity and trace distance identified, Lean-QIT's Fuchs–van de Graaf inequalities read
in `csd-lean4`'s vocabulary as `1 − F ≤ D ≤ √(1 − F²)`
(`CsdLeanqitBridge.fuchs_van_de_graaf`). `csd-lean4`'s fidelity module lists Fuchs–van de Graaf
as not attempted.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace CsdLeanqitBridge

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `csd-lean4`'s trace norm of a Hermitian matrix is Lean-QIT's `traceNorm`. -/
theorem traceNorm_eq {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    QuantumInfo.traceNorm hH = QIT.traceNorm H := by
  have habs : CFC.abs H = cfc (fun x : ℝ => |x|) H := by
    rw [CFC.abs_eq_cfc_norm H hH.isSelfAdjoint]
    rfl
  rw [show QIT.traceNorm H = RCLike.re (CFC.abs H).trace from rfl, habs,
    QuantumInfo.re_trace_cfc hH]
  rfl

/-- **The two trace distances agree** on every pair of density states. -/
theorem traceDist_eq (ρ σ : QIT.State n) (h : (ρ.matrix - σ.matrix).IsHermitian) :
    QuantumInfo.traceDist h = ρ.normalizedTraceDistance σ := by
  rw [QuantumInfo.traceDist, traceNorm_eq, QIT.State.normalizedTraceDistance,
    QIT.normalizedTraceDistance, QIT.traceNormDistance]
  ring

/-- **Fuchs–van de Graaf** in `csd-lean4`'s vocabulary: for density matrices `ρ, σ`,
`1 − F(ρ, σ) ≤ D(ρ, σ) ≤ √(1 − F(ρ, σ)²)`. -/
theorem fuchs_van_de_graaf {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (h : (ρ - σ).IsHermitian) :
    1 - QuantumInfo.fidelity hρ hσ ≤ QuantumInfo.traceDist h ∧
      QuantumInfo.traceDist h ≤ Real.sqrt (1 - QuantumInfo.fidelity hρ hσ ^ 2) := by
  have hF := fidelity_eq ⟨ρ, hρ, hρ1⟩ ⟨σ, hσ, hσ1⟩
  have hD := traceDist_eq ⟨ρ, hρ, hρ1⟩ ⟨σ, hσ, hσ1⟩ h
  have hFvdG := QIT.State.fuchs_van_de_graaf ⟨ρ, hρ, hρ1⟩ ⟨σ, hσ, hσ1⟩
  rw [QIT.State.squaredFidelity_eq_fidelity_sq] at hFvdG
  dsimp only at hF hD
  rw [hF, hD]
  exact hFvdG

end CsdLeanqitBridge
