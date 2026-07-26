# H12 Levinson--Montgomery Paired-Mass Density Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-PAIRED-MASS-DENSITY-01`

Selected node: `H12-LM-PAIRED-MASS-DENSITY-01`

Mode: `LITERATURE / PROOF-ATTEMPT`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Primary source

Norman Levinson and Hugh L. Montgomery, *Zeros of the derivatives of the Riemann zeta-function*,
Acta Mathematica 133 (1974), 49--65, Theorem 1 and equations `(2.2)`--`(2.3)`.

- DOI: <https://doi.org/10.1007/BF02392141>
- Full text:
  <https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6174-11511_2006_Article_BF02392141.pdf>

The source was checked from the rendered original pages, not only from an OCR summary.

## Exact mathematical object

Let `rho=beta+i*gamma` run through nontrivial zeta zeros with analytic multiplicity. For
`s=sigma+i*t` with `sigma<1/2`, pair every left zero with
`1-conj(rho)=1-beta+i*gamma`. Define the source mass

```text
I1(s)
  = 2 * sum_(beta<1/2)
      ((t-gamma)^2 + (sigma-1/2)^2 - (1/2-beta)^2)
      / (|s-rho|^2 * |s-(1-conj(rho))|^2)
    + sum_(beta=1/2) 1 / |s-rho|^2.
```

Both sums retain analytic multiplicity. The infinite sum must be implemented through the actual
`RiemannXiDivisorZeroIndex`, not through a set of distinct values.

The source algebra is

```text
Re sum_rho 1/(s-rho) = -(1/2-sigma) * I1(s),
```

with the left side interpreted by the same functional-equation pairing, rather than as an
unjustified absolutely convergent raw reciprocal sum.

## Proposed Lean statements

The intended module is
`LeanLab/Riemann/LevinsonMontgomeryPairedMassDensity.lean`.

It will define source-aligned objects with names of the following form:

```lean
levinsonMontgomeryLeftPairKernel
levinsonMontgomeryCriticalLineKernel
levinsonMontgomeryPairedZeroMass
LevinsonMontgomeryPairedMassNegativeAtIntegers
```

The mandatory endpoints are:

```lean
theorem levinsonMontgomery_real_paired_zero_sum_eq
    {s : ℂ} (hs : s.re < 1 / 2) (hxi : riemannXi s != 0) :
    levinsonMontgomeryRealPairedZeroSum s =
      -(1 / 2 - s.re) * levinsonMontgomeryPairedZeroMass s

theorem exists_upperLeft_zero_abs_im_sub_lt_half_of_pairedMass_neg
    {s : ℂ} (hsRe : s.re < 1 / 2) (hsIm : 1 <= s.im)
    (hxi : riemannXi s != 0)
    (hmass : levinsonMontgomeryPairedZeroMass s < 0) :
    exists rho, IsNontrivialZero rho /\
      0 < rho.re /\ rho.re < 1 / 2 /\
      abs (s.im - rho.im) < 1 / 2

theorem levinsonMontgomeryDenseBranch_of_pairedMassNegativeAtIntegers
    (hmass : LevinsonMontgomeryPairedMassNegativeAtIntegers) :
    exists T0, forall T, T0 <= T ->
      T / 2 < (speiserUpperLeftZetaZeroCount T : ℝ)
```

Spelling may adapt to Lean conventions, but statement strength, actual-zero indexing,
multiplicity, strict boundaries, and the final existing count must not weaken.

## Position in the hard-gap DAG

```text
Hadamard xi zero sum + reciprocal-square summability
  -> functional-equation paired real zero mass (2.2)-(2.3)
  -> negative mass localizes a left zero within 1/2
  -> eventual integer-height negative mass
  -> N^-(T) > T/2 eventually
  -> dense branch of LevinsonMontgomeryCountDichotomy
  -> exact-count consumer
  -> Speiser equivalence
```

This campaign attacks the middle three arrows through the dense branch. It does not assume any
later node.

## Assumption frontier

Available unconditional inputs:

- the multiplicity-bearing xi divisor index and its actual zero-value theorem;
- reciprocal-square summability of the xi divisor;
- locally uniform summability of compensated xi logarithmic-derivative terms away from zeros;
- multiplicity-preserving `rho -> 1-rho` and conjugation permutations;
- the actual finite upper-left zeta-zero count;
- equality of zeta and xi analytic multiplicities at every nontrivial zero;
- critical-strip bounds `0<Re(rho)<1`;
- finite norm-ball zero cutoffs and the H7 Jensen count infrastructure.

Unavailable and prohibited as premises:

- `LevinsonMontgomeryLogCountBound`;
- `LevinsonMontgomeryCountDichotomy`;
- `LevinsonMontgomeryExactCountSequence`;
- the desired dense count conclusion;
- a raw absolutely summable `sum 1/(s-rho)`;
- RH or `SpeiserDerivativeZeroFree`.

## Registered attacks

### Attack A: explicit paired kernel

1. Construct the multiplicity-preserving global permutation
   `rho -> 1-conj(rho)`.
2. Prove absolute summability of the real paired reciprocal term by rewriting it as two
   compensated Hadamard terms minus the real reciprocal constants.
3. Bound the reciprocal constants by the existing reciprocal-square mass using
   `0<Re(rho)<1` and permutation invariance.
4. Split left and critical-line indices and prove the exact source rational identities.
5. Use nonnegativity under `|t-gamma|>=1/2` to derive the near-zero witness from negative mass.
6. Select one witness per sufficiently large integer and prove injectivity from the strict
   half-unit neighborhoods.
7. Compare the resulting finite image with `speiserUpperLeftZetaZeroFinset T`, retain
   multiplicity, and derive the eventual `T/2` lower bound.

### Attack B: finite-cutoff limit

If subtype `tsum` reindexing blocks Attack A, use symmetric xi norm-ball cutoffs, prove the
source identity at every finite cutoff closed under both involutions, and pass to the limit using
the compiled reciprocal-square tail. The endpoint and actual count conclusion remain unchanged.

## Success criteria

`FULL_PAIRED_MASS_DENSITY_SUCCESS` requires:

- all three mandatory endpoints;
- actual multiplicity-bearing xi zeros and the existing Speiser count;
- a proven Target and exact TargetChecks;
- selected transitive axiom prints;
- empty forbidden scans;
- direct warning-as-error compilation and full `lake build`;
- frozen implementation, immutable-evidence, and final-ledger public CI.

No helper-only theorem, finite toy ensemble, or abstract sequence version counts as success.

## Falsification and stopping criteria

- `PAIRING_MISMATCH`: source pairing or critical-line normalization double-counts multiplicity.
  Compile the corrected finite identity and stop the advertised claim.
- `RAW_SUM_DIVERGENCE`: a proposed raw reciprocal sum is not summable. Retain only the paired or
  compensated interpretation and record the exact rejected signature.
- `DENSITY_ASSEMBLY_BLOCKED`: the actual localizer compiles but the selected witnesses cannot be
  embedded into the existing multiplicity count without a new source-equivalent premise.
  Record the complete missing theorem.
- `SOURCE_BOUNDARY_MISMATCH`: strict/open height or real-part conventions change the final
  `T/2` branch.
- `local_stop`: full public closure or the first exact obstruction after both registered attacks.
  Local stop returns to `ROUTE_SELECTION`; the global RH Goal remains active.

## Known obstacles

- Raw `sum 1/(s-rho)` is not absolutely summable; only real functional-equation pairs have the
  required reciprocal-square decay.
- The paired index `1-conj(rho)` must preserve analytic multiplicity copy by copy.
- Critical-line zeros are fixed in value by the pairing and therefore receive one kernel term,
  not the left-pair factor two.
- `tsum` over real-part subtypes must be reconciled with the global compensated Hadamard sum.
- One zero cannot lie in two strict half-unit neighborhoods of distinct integers; the strict
  inequality is essential.
- The existing count is over distinct zero values weighted by zeta multiplicity, while the
  source mass is indexed by multiplicity copies.
- Nat floor and real-height bookkeeping must prove the conclusion for every sufficiently large
  real `T`, not only integer cutoffs.

## Claim boundary

This is a known-source bridge, not an unconditional RH theorem. Even on success, the Gamma
estimate, low-height certificate, indented contour, logarithmic count bound, full count
dichotomy, Speiser equivalence, and RH remain open.

Expected classification on success:

- `source_analytic_bridge_delta=1`;
- `historical_route_coverage_delta=1`;
- `known_theorem_formalization_delta=0` until the full Levinson--Montgomery theorem is compiled;
- `hard_gap_delta=0` for RH;
- `rh_frontier_delta=0`.

## Mechanical and publication gates

No `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or resource-limit
relaxation. Require direct module compilation, exact TargetChecks, selected `#print axioms`,
empty forbidden scans, `git diff --check`, full `lake build`, frozen implementation CI,
immutable-evidence CI, and final-ledger CI.

The six inherited user/exposure files remain untouched and unstaged.
