# Wide Siegel E-values

This Lean library reduces the unit classification for wide Siegel E-values to a
torsor section theorem. Its main result characterizes the units as
$a\exp(b)$ with $a$ and $b$ algebraic and $a\ne 0$.

## Assumption

The classification takes `WideE.PianzolaForKummerAlgebras WideE.AlgebraicComplex`
as an explicit hypothesis. It asserts that torsors under smooth connected affine
algebraic groups over the Laurent rings of the Kummer covers have sections.
See the [Lean statement](WideE/PianzolaReduction.lean) and
[Pianzola, Proposition 5(ii)(b)](https://arxiv.org/pdf/math/0203277v2#page=5).

The main theorem is
[`WideE.isUnit_valueSubring_iff_algebraicScalarExp_of_pianzola`](WideE/KummerSections.lean).

```lean
WideE.PianzolaForKummerAlgebras WideE.AlgebraicComplex →
  ∀ u : WideE.valueSubring, IsUnit u ↔ WideE.IsAlgebraicScalarExp (u : ℂ)
```

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
