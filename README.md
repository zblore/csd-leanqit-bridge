# csd-leanqit-bridge

A bridge package that reads fidelity and trace-distance results from QuAIR's
[Lean-QIT](https://github.com/QuAIR/Lean-QIT) into
[`csd-lean4`](https://github.com/zblore/csd-lean4)'s vocabulary. Neither library is modified;
`csd-lean4` keeps its Mathlib-only footprint. The Physlib counterpart, for strong subadditivity
and data processing, is [`csd-qit-bridge`](https://github.com/zblore/csd-qit-bridge).

## What it proves (`CsdLeanqitBridge`)

| Theorem | Statement |
|---|---|
| `fidelity_eq` | `csd-lean4`'s spectral fidelity `∑ᵢ √λᵢ(√ρ σ √ρ)` equals Lean-QIT's `‖√ρ √σ‖₁` on every density state. |
| `traceDist_eq` | `csd-lean4`'s trace distance `½ ∑ᵢ |λᵢ(ρ − σ)|` equals Lean-QIT's `½ ‖ρ − σ‖₁`. |
| `fidelity_le_one_of_posSemidef` | `F(ρ, σ) ≤ 1` for all density matrices. `csd-lean4`'s own `fidelity_le_one` needs `ρ, σ` positive definite. |
| `fuchs_van_de_graaf` | `1 − F(ρ, σ) ≤ D(ρ, σ) ≤ √(1 − F(ρ, σ)²)`, in `csd-lean4`'s `fidelity` and `traceDist`. |
| `fidelity_le_apply` | `F(ρ, σ) ≤ F(Φ ρ, Φ σ)` for every `csd-lean4` channel `Φ` in Kraus form: fidelity cannot decrease under a channel. |

The matching lemmas `sqrtMat_eq_psdSqrt` and `traceNorm_eq` identify the two libraries' square
roots and trace norms, and `toQITChannel` turns a `csd-lean4` Kraus channel into a Lean-QIT
channel (Lean-QIT's `ofKraus` uses the same convention, `X ↦ ∑ᵢ Kᵢ X Kᵢᴴ`). The bound,
Fuchs–van de Graaf and the monotonicity are Lean-QIT's (`QIT.State.fidelity_le_one`,
`QIT.State.fuchs_van_de_graaf`, `QIT.State.squaredFidelity_le_applyState_squaredFidelity`);
this package proves that `csd-lean4` and Lean-QIT mean the same thing by fidelity, trace
distance and channels, so those results apply to `csd-lean4`.

### End to end (`CsdLeanqitBridge.EndToEnd`)

`csd-lean4` builds the density operator of a preparation on `Σ` (`CSD.LF2.preparationDensity`)
and builds channels from ontic flows on `Σ` (`CSD.LF2.FlowChannel`). These theorems compose that
chain with the identifications above, so Lean-QIT's results apply to preparations and flows
directly.

| Theorem | Statement |
|---|---|
| `fidelity_preparation_le_one` | `F ≤ 1` for the density operators of any two preparations on `Σ`. |
| `fuchs_van_de_graaf_preparation` | Fuchs–van de Graaf for any two preparations on `Σ`. |
| `fidelity_preparation_le_apply` | No `csd-lean4` channel lowers the fidelity of two preparations. |
| `fidelity_le_flow` | Open system: if an ontic flow lifts a joint unitary and both preparations are products with a ready environment, the reduced states after the flow are at least as close in fidelity as the system preparations. The channel is the one the flow produces. |
| `fidelity_preparation_flow` | Closed system, no lift hypothesis: on the projective sector, a flow that projects to a unitary's action leaves the fidelity of any two preparations unchanged. |

The `csd-lean4` side keeps its hypotheses. The sector, the measure bridge and the
representative are posited data, and `fidelity_le_flow` assumes the lift (`IsUnitaryLift`) and
the product form of the preparations. `fidelity_preparation_flow` needs neither: the lift comes
from `CSD.LF2.isUnitaryLift_unitSection`.

Axioms are checked by `CsdLeanqitBridge/Tests/AxiomAudit.lean` (`lake build
CsdLeanqitBridgeTests`): all 17 declarations of the bridge, and the three Lean-QIT theorems they
rest on, use only `propext`, `Classical.choice` and `Quot.sound`. Each is pinned by name, and an
inventory check walks every declaration under `CsdLeanqitBridge`, so a new one cannot escape it.

## Pins

`lakefile.toml` requires each library by pinned git revision. They must agree on Lean and
Mathlib; at the current pins all of them resolve Mathlib to
`5ed2965256430c3649e86755f9576b54eca72435` (tag `v4.34.0`) on Lean `v4.34.0`. Bump them
together, never one alone.

| | Revision |
|---|---|
| Mathlib | `5ed2965` (tag `v4.34.0`) |
| `csd-lean4` | `13b5d16` |
| Lean-QIT | `15a0a5e` (`main`, 5 Oct 2026) |

## Building

```
lake exe cache get
lake build CsdLeanqitBridge
lake build CsdLeanqitBridgeTests
```

The first build compiles the parts of `csd-lean4` and Lean-QIT it imports.

## Licence

Apache 2.0. Lean-QIT is Apache 2.0, © QuAIR.
