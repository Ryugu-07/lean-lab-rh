# Audited PrimeNumberTheoremAnd Subset

This directory is a source snapshot of the minimal Abel-continuation dependency graph used by
`LeanLab.Riemann.BaezDuarteMellin`.

- upstream: `https://github.com/AlexKontorovich/PrimeNumberTheoremAnd`
- upstream commit: `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`
- license: Apache-2.0; see `LICENSE` and the headers in each Lean source file
- snapshot scope: 13 Lean modules, ending at
  `Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation`

Every snapshotted module was compiled individually against this project's pinned Lean 4.31 and
mathlib `v4.31.0`. The final theorem `riemannZeta_eq_zetaAbelContinuationFormula` reports only
`propext`, `Classical.choice`, and `Quot.sound` in its trusted-dependency closure.

The upstream repository contains many unrelated modules and is intentionally not a package
dependency of this project. Updating this snapshot requires repeating the module-by-module build,
source-keyword scan, and trusted-dependency audit recorded in
`research/m1_fractional_kernel_mellin_20260710.md`.
