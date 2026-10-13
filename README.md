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

The matching lemmas `sqrtMat_eq_psdSqrt` and `traceNorm_eq` identify the two libraries' square
roots and trace norms. The bound and Fuchs–van de Graaf themselves are Lean-QIT's
(`QIT.State.fidelity_le_one`, `QIT.State.fuchs_van_de_graaf`); this package proves that
`csd-lean4` and Lean-QIT mean the same thing by fidelity and trace distance, so those results
apply to `csd-lean4`.

Axioms are checked by `CsdLeanqitBridge/Tests/AxiomAudit.lean` (`lake build
CsdLeanqitBridgeTests`): every export, and the two Lean-QIT theorems, use only `propext`,
`Classical.choice` and `Quot.sound`.

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
