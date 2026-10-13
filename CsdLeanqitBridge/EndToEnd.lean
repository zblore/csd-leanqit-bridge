/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLeanqitBridge.Monotonicity
public import CsdLeanqitBridge.TraceDistance
public import CsdLean4.LF2.PreparationQdensity
public import CsdLean4.LF2.FlowChannel

/-!
# End to end: from preparations and flows on `Σ` to Lean-QIT's fidelity theorems

`csd-lean4` builds the density operator of a preparation on `Σ` (`CSD.LF2.preparationDensity`,
the Gleason witness of the preparation's operational package, equal to the barycentre of its
projective law by `CSD.LF2.preparationDensity_eq_barycenter`), and builds channels from ontic
flows on `Σ` (`CSD.LF2.FlowChannel`). This file composes that chain with the identifications of
`CsdLeanqitBridge.Fidelity`, `CsdLeanqitBridge.TraceDistance` and `CsdLeanqitBridge.Monotonicity`,
so Lean-QIT's fidelity theorems apply to preparations and flows on `Σ` directly.

* **Preparations.** For two preparations `μprep, μprep'` on `Σ`: `F ≤ 1`
  (`fidelity_preparation_le_one`), Fuchs–van de Graaf (`fuchs_van_de_graaf_preparation`), and
  `F(ρ, ρ') ≤ F(Φ ρ, Φ ρ')` for any `csd-lean4` channel `Φ` (`fidelity_preparation_le_apply`).
* ★ **Open system.** If an ontic flow on the joint sector lifts a unitary `U` and both
  preparations are products with the environment in the ready vector `e₀`, the reduced density
  operators of the flowed preparations are at least as close in fidelity as the system
  preparations (`fidelity_le_flow`). The channel is the one the flow produces
  (`CSD.LF2.traceRight_barycenter_flow`), not a posited one.
* ★ **Closed system, no lift hypothesis.** On the projective sector, an ontic flow that projects
  to the action of a unitary leaves the fidelity of any two preparations unchanged
  (`fidelity_preparation_flow`). The lift is supplied by `CSD.LF2.isUnitaryLift_unitSection`.

## Honest scope

The `csd-lean4` side keeps its hypotheses: the sector, the measure bridge and the representative
are posited data (`csd-lean4`'s `specs/POSITS.md`), and the open-system theorem assumes the lift
`IsUnitaryLift` and the product form of the preparations. The quantum-information content is
Lean-QIT's: Uhlmann's theorem and a Stinespring dilation behind monotonicity.
-/

@[expose] public section

open MeasureTheory Matrix CSD.LF2
open scoped ComplexOrder Kronecker LinearAlgebra.Projectivization

namespace CsdLeanqitBridge

/-- `csd-lean4`'s fidelity depends only on the matrices, not on the positivity proofs. -/
theorem fidelity_congr {n : Type*} [Fintype n] [DecidableEq n] {A A' B B' : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hA' : A'.PosSemidef) (hB' : B'.PosSemidef)
    (h₁ : A = A') (h₂ : B = B') :
    QuantumInfo.fidelity hA hB = QuantumInfo.fidelity hA' hB' := by
  subst h₁ h₂
  rfl

/-- **Fidelity is unitarily invariant**, in `csd-lean4`'s vocabulary: monotonicity under the
unitary channels of `U` and of `Uᴴ`. -/
theorem fidelity_unitary_conj {n : Type*} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1)
    (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hUρ : (U * ρ * Uᴴ).PosSemidef) (hUσ : (U * σ * Uᴴ).PosSemidef) :
    QuantumInfo.fidelity hUρ hUσ = QuantumInfo.fidelity hρ hσ := by
  have htr : ∀ {A : Matrix n n ℂ}, A.trace = 1 → (U * A * Uᴴ).trace = 1 := fun h => by
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, h]
  have hUH : Uᴴᴴ * Uᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact hU'
  have hback : ∀ A : Matrix n n ℂ, Uᴴ * (U * A * Uᴴ) * Uᴴᴴ = A := fun A => by
    rw [conjTranspose_conjTranspose]
    simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  apply le_antisymm
  · exact (fidelity_le_apply (QuantumInfo.Channel.unitaryChannel.{_, 0} Uᴴ hUH) hUρ hUσ (htr hρ1)
      (htr hσ1)).trans_eq (fidelity_congr _ _ hρ hσ
        (by rw [QuantumInfo.Channel.unitaryChannel_apply, hback])
        (by rw [QuantumInfo.Channel.unitaryChannel_apply, hback]))
  · exact (fidelity_le_apply (QuantumInfo.Channel.unitaryChannel.{_, 0} U hU) hρ hσ hρ1 hσ1).trans_eq
      (fidelity_congr _ _ hUρ hUσ (QuantumInfo.Channel.unitaryChannel_apply U hU ρ)
        (QuantumInfo.Channel.unitaryChannel_apply U hU σ))

/-! ### Preparations on `Σ` -/

section Preparation

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]
  {N : ℕ}

variable (D : SectorData SigmaSpace P G) (μFS : Measure P) [IsProbabilityMeasure μFS]
  (bridge : MeasureBridgeData D μFS)
  (μprep μprep' : Measure SigmaSpace) [IsProbabilityMeasure μprep] [IsProbabilityMeasure μprep']
  (rep : P → EuclideanSpace ℂ (Fin N))
  (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)

/-- The fidelity of two preparations on `Σ` is at most one. -/
theorem fidelity_preparation_le_one :
    QuantumInfo.fidelity
        (preparationDensity_posSemidef D μFS bridge μprep rep hrep_unit hrep_meas)
        (preparationDensity_posSemidef D μFS bridge μprep' rep hrep_unit hrep_meas) ≤ 1 :=
  fidelity_le_one_of_posSemidef _ _
    (preparationDensity_trace_one D μFS bridge μprep rep hrep_unit hrep_meas)
    (preparationDensity_trace_one D μFS bridge μprep' rep hrep_unit hrep_meas)

/-- **Fuchs–van de Graaf for two preparations on `Σ`**: `1 − F ≤ D ≤ √(1 − F²)` between their
density operators. -/
theorem fuchs_van_de_graaf_preparation :
    1 - QuantumInfo.fidelity
          (preparationDensity_posSemidef D μFS bridge μprep rep hrep_unit hrep_meas)
          (preparationDensity_posSemidef D μFS bridge μprep' rep hrep_unit hrep_meas)
        ≤ QuantumInfo.traceDist
          ((preparationDensity_isHermitian D μFS bridge μprep rep hrep_unit hrep_meas).sub
            (preparationDensity_isHermitian D μFS bridge μprep' rep hrep_unit hrep_meas)) ∧
      QuantumInfo.traceDist
          ((preparationDensity_isHermitian D μFS bridge μprep rep hrep_unit hrep_meas).sub
            (preparationDensity_isHermitian D μFS bridge μprep' rep hrep_unit hrep_meas))
        ≤ Real.sqrt (1 - QuantumInfo.fidelity
          (preparationDensity_posSemidef D μFS bridge μprep rep hrep_unit hrep_meas)
          (preparationDensity_posSemidef D μFS bridge μprep' rep hrep_unit hrep_meas) ^ 2) :=
  fuchs_van_de_graaf _ _
    (preparationDensity_trace_one D μFS bridge μprep rep hrep_unit hrep_meas)
    (preparationDensity_trace_one D μFS bridge μprep' rep hrep_unit hrep_meas) _

/-- **No channel lowers the fidelity of two preparations on `Σ`.** -/
theorem fidelity_preparation_le_apply {m κ : Type*} [Fintype m] [DecidableEq m] [Fintype κ]
    (Φ : QuantumInfo.Channel (Fin N) m κ) :
    QuantumInfo.fidelity
        (preparationDensity_posSemidef D μFS bridge μprep rep hrep_unit hrep_meas)
        (preparationDensity_posSemidef D μFS bridge μprep' rep hrep_unit hrep_meas)
      ≤ QuantumInfo.fidelity
        (Φ.apply_posSemidef
          (preparationDensity_posSemidef D μFS bridge μprep rep hrep_unit hrep_meas))
        (Φ.apply_posSemidef
          (preparationDensity_posSemidef D μFS bridge μprep' rep hrep_unit hrep_meas)) :=
  fidelity_le_apply Φ _ _
    (preparationDensity_trace_one D μFS bridge μprep rep hrep_unit hrep_meas)
    (preparationDensity_trace_one D μFS bridge μprep' rep hrep_unit hrep_meas)

end Preparation

/-! ### Flows on `Σ` -/

section Flow

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- ★ **Open system: a `Σ`-flow cannot lower fidelity.** The joint sector carries a
representative `rep : P → ℂⁿ ⊗ ℂᵉ`; both preparations are products with the environment in the
ready vector `e₀` (a.e., at the projector level, with system representative `repS`); the ontic
flow `Φ` lifts the unitary `U`. Then the reduced density operators of the flowed preparations
are at least as close in fidelity as the density operators of the system preparations. -/
theorem fidelity_le_flow {n e : Type*} [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e]
    (D : SectorData SigmaSpace P G)
    (μprep μprep' : Measure SigmaSpace) [IsProbabilityMeasure μprep] [IsProbabilityMeasure μprep']
    (Φ : SigmaSpace → SigmaSpace) (hΦ : Measurable Φ)
    (rep : P → EuclideanSpace ℂ (n × e)) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep) (repS : P → EuclideanSpace ℂ n)
    (hrepS_unit : ∀ p, ‖repS p‖ = 1) (hrepS_meas : Measurable repS)
    (U : Matrix (n × e) (n × e) ℂ) (hU : Uᴴ * U = 1) (e₀ : EuclideanSpace ℂ e) (he₀ : ‖e₀‖ = 1)
    (hlift : IsUnitaryLift D Φ rep U)
    (hprod : ∀ᵐ x ∂μprep,
      outerProduct (rep (D.π x)) = outerProduct (repS (D.π x)) ⊗ₖ outerProduct e₀)
    (hprod' : ∀ᵐ x ∂μprep',
      outerProduct (rep (D.π x)) = outerProduct (repS (D.π x)) ⊗ₖ outerProduct e₀) :
    QuantumInfo.fidelity
        (barycenterMatrix_posSemidef repS hrepS_unit hrepS_meas (Measure.map D.π μprep))
        (barycenterMatrix_posSemidef repS hrepS_unit hrepS_meas (Measure.map D.π μprep'))
      ≤ QuantumInfo.fidelity
        (barycenterMatrix_posSemidef rep hrep_unit hrep_meas
          (Measure.map D.π (Measure.map Φ μprep))).traceRight
        (barycenterMatrix_posSemidef rep hrep_unit hrep_meas
          (Measure.map D.π (Measure.map Φ μprep'))).traceRight := by
  have := isProbabilityMeasure_projectiveLaw D μprep
  have := isProbabilityMeasure_projectiveLaw D μprep'
  exact (fidelity_le_apply (stinespringChannel U hU e₀ he₀) _ _
    (barycenterMatrix_trace repS hrepS_unit hrepS_meas _)
    (barycenterMatrix_trace repS hrepS_unit hrepS_meas _)).trans_eq
    (fidelity_congr _ _ _ _
      (traceRight_barycenter_flow D μprep Φ hΦ rep hrep_unit hrep_meas repS hrepS_meas U hU e₀
        he₀ hlift hprod).symm
      (traceRight_barycenter_flow D μprep' Φ hΦ rep hrep_unit hrep_meas repS hrepS_meas U hU e₀
        he₀ hlift hprod').symm)

/-- ★ **Closed system: a `Σ`-flow conserves fidelity, with no lift hypothesis.** On the
projective sector `P = ℙ(ℂᴺ)`, with the canonical unit section as representative, an ontic flow
that projects to the action of a unitary `U` leaves the fidelity of the density operators of any
two preparations unchanged. -/
theorem fidelity_preparation_flow {N : ℕ}
    [MulAction G (ℙ ℂ (EuclideanSpace ℂ (Fin N)))]
    [MulAction.IsPretransitive G (ℙ ℂ (EuclideanSpace ℂ (Fin N)))]
    (D : SectorData SigmaSpace (ℙ ℂ (EuclideanSpace ℂ (Fin N))) G)
    (μFS : Measure (ℙ ℂ (EuclideanSpace ℂ (Fin N)))) [IsProbabilityMeasure μFS]
    (bridge : MeasureBridgeData D μFS)
    (μprep μprep' : Measure SigmaSpace) [IsProbabilityMeasure μprep] [IsProbabilityMeasure μprep']
    (Φ : SigmaSpace → SigmaSpace) (hΦ : Measurable Φ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (hproj : ∀ x, D.π (Φ x) = U • D.π x) :
    haveI := Measure.isProbabilityMeasure_map' (hΦ.aemeasurable (μ := μprep))
    haveI := Measure.isProbabilityMeasure_map' (hΦ.aemeasurable (μ := μprep'))
    QuantumInfo.fidelity
        (preparationDensity_posSemidef D μFS bridge (Measure.map Φ μprep)
          Projectivization.unitSection Projectivization.norm_unitSection
          Projectivization.measurable_unitSection)
        (preparationDensity_posSemidef D μFS bridge (Measure.map Φ μprep')
          Projectivization.unitSection Projectivization.norm_unitSection
          Projectivization.measurable_unitSection)
      = QuantumInfo.fidelity
        (preparationDensity_posSemidef D μFS bridge μprep
          Projectivization.unitSection Projectivization.norm_unitSection
          Projectivization.measurable_unitSection)
        (preparationDensity_posSemidef D μFS bridge μprep'
          Projectivization.unitSection Projectivization.norm_unitSection
          Projectivization.measurable_unitSection) := by
  have hlift := isUnitaryLift_unitSection D Φ U hproj
  have hM : ∀ (μ : Measure SigmaSpace) [IsProbabilityMeasure μ],
      (preparationDensity D μFS bridge μ Projectivization.unitSection
        Projectivization.norm_unitSection Projectivization.measurable_unitSection).M
        = barycenterMatrix Projectivization.unitSection (Measure.map D.π μ) := fun μ _ => by
    rw [preparationDensity_eq_barycenter]
    rfl
  have hMΦ : ∀ (μ : Measure SigmaSpace) [IsProbabilityMeasure μ],
      haveI := Measure.isProbabilityMeasure_map' (hΦ.aemeasurable (μ := μ))
      (preparationDensity D μFS bridge (Measure.map Φ μ) Projectivization.unitSection
        Projectivization.norm_unitSection Projectivization.measurable_unitSection).M
        = U.val * (preparationDensity D μFS bridge μ Projectivization.unitSection
          Projectivization.norm_unitSection Projectivization.measurable_unitSection).M
          * U.valᴴ := fun μ _ => by
    rw [hM, hM, barycenter_flow D μ Φ hΦ _ Projectivization.norm_unitSection
      Projectivization.measurable_unitSection _ hlift]
  have hU : U.valᴴ * U.val = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.UnitaryGroup.star_mul_self U
  have hU' : U.val * U.valᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem U.2
  have hpos := fun (μ : Measure SigmaSpace) [IsProbabilityMeasure μ] =>
    (preparationDensity_posSemidef D μFS bridge μ Projectivization.unitSection
      Projectivization.norm_unitSection Projectivization.measurable_unitSection
      ).mul_mul_conjTranspose_same U.val
  rw [fidelity_congr _ _ (hpos μprep) (hpos μprep') (hMΦ μprep) (hMΦ μprep')]
  exact fidelity_unitary_conj _ _ (preparationDensity_trace_one _ _ _ _ _ _ _)
    (preparationDensity_trace_one _ _ _ _ _ _ _) U.val hU hU' _ _

end Flow

end CsdLeanqitBridge
