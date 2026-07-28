# H11 Triangular Pair-Mass Preregistration

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H11-TRIANGULAR-PAIR-MASS-01`

Selected node: `H11-GALLAGHER-MUELLER-TRIANGULAR-MASS-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_PENDING`

## Selection reason

The Farey--Mobius--Weyl campaign is publicly closed at final ledger
`8a84e18a30e95bf1be423a949438deb0fdfafabb`, Lean Action run `30215281290`,
build job `89828323462`, in `1m35s`. Fresh route selection compared the ordered Franel
successor, Hardy's original oscillatory transform, the mollifier moment frontier, H7 spectral
convergence, H10 number-field transfer, H11 pair correlation, H12 global counting, and direct
actual-zeta proof attempts.

H11 is selected without inheriting momentum from H9. The project has already compiled the finite
horizontal-multiplicity inequality and its actual-zeta cofinal exact-count consumer, but it has
not compiled the source identity that inserts horizontal multiplicity into the pair-correlation
second moment. This missing mechanism is equations `(5.3)`--`(5.4)` and their proof in Section 9
of Goldston--Lee--Schettler--Suriajaya. It originates in the Gallagher--Mueller short-interval
method.

The endpoint is omission-sensitive: it must expose the equal-ordinate term exactly, preserve
ordered pairs and analytic multiplicity, and prove the integral representation of the positive
gap contribution. A detached finite counting lemma or an assumed pair-correlation asymptotic is
not accepted.

## Locked primary sources

1. Daniel A. Goldston, Junghun Lee, Jordan Schettler, and Ade Irma Suriajaya,
   "Pair Correlation Conjecture for the Zeros of the Riemann Zeta-function I: Simple and Critical
   Zeros," arXiv:2503.15449v4, 2026-03-30.
   <https://arxiv.org/abs/2503.15449v4>
2. P. X. Gallagher and Julia H. Mueller, "Primes and zeros in short intervals,"
   *Journal fuer die reine und angewandte Mathematik* 303/304 (1978), 205--220.
   <https://eudml.org/doc/152055>
3. H. L. Montgomery, "The pair correlation of zeros of the zeta function," 1973.
   <https://websites.umich.edu/~hlm/paircor1.pdf>

The first source fixes the exact modern no-RH horizontal-multiplicity conventions and supplies a
complete proof of the finite pair decomposition. The second is the historical method anchor. The
third fixes the original pair-correlation family and its weighted Fourier-statistic context.

## Source-exact mechanism

For the multiplicity-bearing ordinates `gamma` with `0 < gamma <= T`, define

```text
N(T,u) = number of ordered pairs with 0 < gamma' - gamma <= u
N*(T)  = number of ordered pairs with gamma' = gamma.
```

For `U > 0`, the source proves

```text
sum_{|gamma'-gamma| <= U} (U - |gamma'-gamma|)
  = U * N*(T)
      + 2 * sum_{0 < gamma'-gamma <= U}
          (U - (gamma'-gamma))
  = U * N*(T) + 2 * integral_0^U N(T,u) du.
```

The first equality splits ordered pairs into zero, positive, and negative gaps and uses the swap
`(gamma,gamma') <-> (gamma',gamma)`. The second equality is the finite layer-cake identity: a
fixed positive gap `d` contributes the length of `{u in [0,U] | d <= u}`, namely `U-d` when
`d <= U` and zero otherwise.

The diagonal term is not the ordinary number of zeros when multiple copies or distinct zeros
share an ordinate. It is exactly the project's existing `horizontalPairCount`, hence exactly the
quantity that detects a functional-equation reflected off-line pair.

## Fixed Lean endpoint

Create `LeanLab/Riemann/PairCorrelationTriangularMass.lean`, importing
`LeanLab.Riemann.PairCorrelationHorizontalMultiplicity`, and compile all of the following without
placeholders.

1. Define the directed ordinate gap, positive short-gap count, equal-ordinate ordered-pair count,
   triangular pair mass, and positive-gap mass for an arbitrary finite multiplicity-copy
   population.
2. Prove the exact filtered source form of triangular mass for `0 <= U`; pairs outside
   `|gap| <= U` contribute zero and boundary pairs contribute weight zero.
3. Prove the ordered-pair sign partition and swap identity
   ```text
   triangularMass U =
     U * equalOrdinatePairCount + 2 * positiveGapMass U.
   ```
4. Prove the actual interval-integral identity
   ```text
   integral u in 0..U, (positiveGapCount u : Real)
     = positiveGapMass U
   ```
   and combine it with block 3 to obtain the source equation `(5.4)`.
5. For a complex population `z`, prove that the equal-ordinate count of `im (z i)` is exactly
   `horizontalPairCount z`, with no set/multiset or ordered/unordered conversion.
6. Instantiate the complete identity on `PccPositiveZetaZeroIndex T` and
   `pccPositiveZetaZeroValue T`, thereby preserving the existing xi analytic multiplicity.
7. Bundle the finite and actual-zeta statements in one aggregate endpoint certificate.

Proposed declaration names:

- `pairCorrelationGap`
- `positiveGapPairCount`
- `equalOrdinatePairCount`
- `triangularPairMass`
- `positiveGapMass`
- `triangularPairMass_eq_horizontal_add_positive`
- `integral_positiveGapPairCount_eq_positiveGapMass`
- `triangularPairMass_eq_horizontal_add_integral`
- `equalOrdinatePairCount_im_eq_horizontalPairCount`
- `pccPositiveZeta_triangularPairMass_eq`
- `pairCorrelationTriangularMass_endpoint`

Names may change to match local APIs, but the mathematical endpoint may not be weakened silently.

## M0 alignment and adversarial cases

- `pair orientation`: `gamma' - gamma`, not its absolute value, in `N(T,u)`.
- `pair convention`: ordered pairs, including all analytic-multiplicity copies.
- `zero gap`: belongs only to `N*(T)`, never to the strict positive-gap count.
- `upper boundary`: `gap = U` is counted by `N(T,U)` but contributes zero triangular weight.
- `U = 0`: admitted as a normalization test for the finite identity, though the source analytic
  application assumes `U > 0`.
- `negative U`: outside the fixed endpoint.
- `duplicate ordinates`: two distinct indices at the same ordinate contribute four ordered
  horizontal pairs, not two.
- `single point`: triangular mass is exactly `U` for `0 <= U`.
- `reflected off-line pair`: the two same-height copies contribute four horizontal pairs before
  normalization.

## Success and falsification criteria

`FULL_SUCCESS` requires all seven endpoint blocks, an aggregate proven Target, exact TargetChecks,
selected transitive axiom prints, an empty forbidden scan, warning-as-error compilation, a full
build, and independent public CI for preregistration, frozen implementation, immutable evidence,
and final ledger.

`MEANINGFUL_PARTIAL` requires the complete finite source identity and an exact named obstruction
to the actual-zeta instantiation. The endpoint may not be replaced by a theorem that assumes the
integral identity.

`SOURCE_FALSIFIED` requires a Lean counterexample under the exact ordered-pair and endpoint
conventions, or a proved mismatch between the source's `N*(T)` and the project's
`horizontalPairCount`.

## Known obstacles and strict boundary

- Finite sums must be moved through an interval integral with measurable step functions.
- The proof must distinguish strict `0 < gap` from weak `gap <= u`; endpoint changes are
  measure-zero analytically but are not definitionally interchangeable.
- The negative-gap contribution must be obtained by an explicit swap of ordered indices.
- The actual-zeta finite index already expands analytic multiplicity; no second multiplicity
  factor may be inserted.
- Equations `(5.2)` and `(5.3)` also contain an analytic boundary error `O(L^2)` when the moving
  interval reaches `T+U`. That asymptotic boundary analysis is outside this fixed finite
  `(5.4)` endpoint.
- Fujii's second-moment estimate for `Delta_U S`, Montgomery's PCC, HMH, any absolute-error
  improvement, sparse-exception amplification, RH, and every direct zero exclusion remain open.

## Mechanical gates

Before proof-source editing:

- publish this docs-only preregistration;
- require public Lean Action CI to pass;
- keep the six inherited protected files untouched and unstaged.

Before accepting any theorem:

- register one aggregate target in `Targets.lean`;
- add exact witnesses in `TargetChecks.lean`;
- print selected transitive axioms in `AxiomsAudit.lean`;
- scan for `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, and `unsafe`;
- run the new module with warnings as errors and run the full build;
- freeze the implementation before publishing evidence.

## Stop and successor rule

Stop this local campaign at the first of:

1. `FULL_SUCCESS`;
2. `MEANINGFUL_PARTIAL` at an exact finite-integral or actual-zeta API obstruction;
3. `SOURCE_FALSIFIED`;
4. proof that the complete endpoint already exists in production Lean.

Local stop returns the active RH Goal to cross-family historical route selection. H11 remains
open at Fujii's analytic second moment, PCC, absolute-error control, and last-exception
amplification. Direct RH attacks and original conjectures remain open throughout.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a compacted live state; reread the canonical governance
  pointers, live worktree, historical census, ranked atlas, H11 prior campaign, exact source
  equations `(5.3)`--`(5.5)`, and existing actual-zeta multiplicity API before selection.
- `global_goal`: active.

## Implementation result

- `preregistration`: commit `1b9c9ce00d578ba69db3f3dc8a5db369458c9b1c` passed public
  Lean Action run `30331731095`, build job `90188198625`, in `2m21s`.
- `frozen_implementation`: commit `15381a49ff4dfb92a0ab4e29d5e76383f9789139` passed public
  Lean Action run `30333046948`, build job `90192073198`, in `2m11s`.
- `module`: `LeanLab/Riemann/PairCorrelationTriangularMass.lean`, 357 lines.
- `compiled_endpoint`: all seven preregistered blocks compile. The aggregate theorem is
  `pairCorrelationTriangularMass_endpoint`.
- `local_audit`: 12 exact TargetChecks including the `U=0`, singleton, duplicate-ordinate,
  upper-boundary, and reflected-pair controls; seven selected axiom prints; standard axioms
  only; empty new-module forbidden scan; warning-as-error module compile; full `8776/8776`
  build.
- `strict_result`: the finite source identity is now connected to the actual
  analytic-multiplicity-expanded zeta cutoff. No second-moment estimate, PCC, HMH, sparse
  exception exclusion, or RH statement was assumed or proved.
- `next_gate`: publish this docs-only immutable evidence and require public CI; keep all
  `LeanLab/` proof sources frozen.
