# Mathlib Upstream Queue

Date: 2026-07-17

Status: engineering inventory; no pull request is claimed open or ready.

The queue separates reusable mathlib-scale components from project-specific RH assemblies. Before
submission, each item needs dependency minimization, naming/API review, documentation, standalone
tests, licensing/provenance review, and a human author who understands and owns the contribution.
Current [mathlib contribution policy](https://leanprover-community.github.io/contribute/how-to-contribute.html)
requires disclosure of substantial AI assistance and does not permit AI-authored GitHub or Zulip
comments; all public prose must be written by the human contributor.

## Q1 Weighted logarithmic L2 equivalence

- Project source: `LeanLab/Riemann/FourierMellin.lean`.
- Candidate extraction: the generic positive-half-line weighted logarithmic change of variables,
  its quasi-measure-preserving result, `L2` isometry/equivalence, and inverse formulas.
- Required split: remove Baez-Duarte naming/imports and expose a domain-neutral API.
- Readiness: highest-ranked extraction, not PR-ready.

## Q2 Generic truncated Perron kernel

- Project source: `LeanLab/Riemann/TruncatedPerron.lean`.
- Candidate extraction: rectangle contour identity, scalar truncated kernel, crossing-pole term,
  and generic quantitative kernel bounds.
- Required split: separate the generic analytic layer from the Mobius specialization and reduce
  the current large module into reviewable units.
- Readiness: valuable after Q1.

## Q3 Analytic logarithm and reciprocal-growth helpers

- Project sources: `LeanLab/Riemann/AnalyticLogBranch.lean` and
  `LeanLab/Riemann/ReciprocalZetaSubpower.lean`.
- Candidate extraction: source-independent holomorphic logarithm branches and reusable
  Borel-Caratheodory/three-lines growth interfaces.
- Required split: remove RH/zeta-specific conditional endpoints and audit overlap with current
  complex-analysis APIs.
- Readiness: API audit required.

## Q4 Xi divisor and Li stack

- Project sources: `LiScaffold.lean`, `LiHadamard.lean`, `LiZeroFormula.lean`,
  `LiSymmetricZeroFormula.lean`, `LiReverseCriterion.lean`, and `LiWeilGram.lean`.
- Candidate sequence: xi definition/alignment; divisor/Hadamard surface; coefficient and paired
  zero formula; reverse criterion; finite Gram packaging.
- Required split: finish independent definition review, isolate PNT+ dependencies, and avoid one
  monolithic RH PR.
- Readiness: blocked only for upstreaming by review/API work, not blocked as research.

## Q5 Compact explicit-formula infrastructure

- Project sources: `WeilCompactLaplaceZeroCutoff.lean` and
  `WeilCompactLaplaceArithmeticFormula.lean`.
- Candidate first piece: generic compact-support Laplace/Fourier integration by parts, finite-order
  decay, and inversion lemmas.
- Later piece: source-specific complete explicit formula after sign/definition review.
- Readiness: split and generalization required.

## Next engineering action

Extract Q1 into a project-local generic module with minimal imports, prove API equivalence with the
existing RH consumer, and run the full trust gates. That extraction is engineering/publication
work and must not be labeled an RH theorem.
