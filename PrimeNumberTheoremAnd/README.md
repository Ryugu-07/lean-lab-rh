# Audited PrimeNumberTheoremAnd Subset

This directory is a source snapshot of the audited upstream modules used by the fixed-gap RH
formalization modules.

- upstream: `https://github.com/AlexKontorovich/PrimeNumberTheoremAnd`
- upstream commit: `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`
- snapshot introduced: `2026-07-10`
- snapshot last expanded: `2026-07-15`
- license: Apache-2.0; see `LICENSE` and the headers in each Lean source file
- snapshot scope: the 13-module Abel-continuation dependency graph ending at
  `Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation`, plus the standalone
  `Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries` module, plus the 11-module finite-order
  expansion ending at `Mathlib.NumberTheory.LSeries.ZetaFiniteOrder`, plus the 37 missing modules
  that complete the 61-module recursive custom dependency closure ending at
  `Mathlib.NumberTheory.LSeries.RiemannZetaHadamard`

Every snapshotted module was compiled individually against this project's pinned Lean 4.31 and
mathlib `v4.31.0`. Representative final theorems are checked in
`LeanLab.Riemann.AxiomsAudit`.

The upstream repository contains many unrelated modules and is intentionally not a package
dependency of this project. Updating this snapshot requires repeating the module-by-module build,
source-keyword scan, and trusted-dependency audit recorded in
`research/m1_fractional_kernel_mellin_20260710.md` and
`research/m1_zeta_ratio_digamma_20260711.md`, and
`research/m1_zeta_convexity_midpoint_20260711.md`.
