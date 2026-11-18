# Broad Siegel E-values

This Lean library proves that the units of the ring of broad Siegel E-values
are exactly $a\exp(b)$ with $a$ and $b$ algebraic and $a\ne 0$.

## Main theorem

The main theorem is [`WideE.isUnit_valueSubring_iff_algebraicScalarExp`](WideE/CharacterClassification.lean).

```lean
∀ u : WideE.valueSubring, IsUnit u ↔ WideE.IsAlgebraicScalarExp (u : ℂ)
```

The proof lifts the inverse relation along a pointed Kummer cover by descending
two opposite character weights of the connected Picard–Vessiot group.

## Reproducibility

Requires Git and elan. The project pins Lean 4.19.0, Mathlib, and
[Hatsuwr's strict E-unit formalization](https://github.com/Hatsuwr/strict-e-unit-classification/tree/340c7435608e0f1aa1d9b08a0100721a4fd23005).

```sh
git clone https://github.com/Niklas-Fraccaro/wide-e-values-lean.git
cd wide-e-values-lean
lake exe cache get
./build.sh build WideE +WideE.Audit
```

The final command builds the library and checks that the audited declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
See [WideE/Audit.lean](WideE/Audit.lean).

## Verification

[![Lean verification](https://github.com/Niklas-Fraccaro/wide-e-values-lean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/Niklas-Fraccaro/wide-e-values-lean/actions/workflows/lean.yml)

The workflow starts from a fresh Linux checkout and uses the Mathlib cache.
It builds the library and runs its axiom audit.
