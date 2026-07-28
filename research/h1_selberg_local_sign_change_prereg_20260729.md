# H1 Selberg Local Sign-Change Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-SELBERG-LOCAL-SIGN-CHANGE-01`

Node: `H1-SELBERG-LOCAL-SIGN-CHANGE-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Primary-source anchor

The canonical source is Atle Selberg, *On the zeros of Riemann's zeta-function*,
Skr. Norske Vid. Akad. Oslo, No. 10 (1942), 1--59.

The method is distinct from Levinson's method. It studies sign changes on the critical line
after multiplying the real Hardy coordinate by a mollifier of the form

```text
M(s) = |N(s)|^2,
```

where a finite Dirichlet polynomial `N` models `1/sqrt(zeta)`. The square preserves signs on
the critical line. Later mean-value estimates produce many intervals on which both signs occur.

Source cross-checks:

- J. B. Conrey, D. W. Farmer, C.-H. Kwan, Y. Lin, and C. L. Turnage-Butterbaugh,
  *Short mollifiers of the Riemann zeta-function* (2025), arXiv:2508.11108, introduction;
- Henryk Iwaniec, *The critical zeros -- 100% sometimes* (2014 lecture notes), Section 2,
  "Selberg's sign changes."

The production statement uses the project's actual real critical-line xi coordinate. This is a
positive real renormalization of the classical Hardy coordinate at the zero-detection level.
M0 definition alignment must record exactly which zero dictionary is used; no equality with a
particular textbook normalization of Hardy's `Z` is claimed.

## Exact fixed endpoint

The production module must prove the following without `sorry`.

1. Define a finite complex root mollifier from coefficients, a natural cutoff, and the actual
   critical-line point.
2. Define the Selberg mollified Hardy-xi coordinate

   ```text
   F(t) = hardyXi(t) * normSq(N(1/2+i*t)).
   ```

3. Prove continuity and the exact source-square facts: the multiplier is nonnegative; a
   positive or negative value of `F` forces the same strict sign for `hardyXi`.
4. For a continuous real function on `a < b`, prove that

   ```text
   abs (integral a..b F) < integral a..b (abs F)
   ```

   forces the existence of one positive and one negative value in `[a,b]`.
5. Specialize clause 4 to the actual Selberg coordinate and prove the existence of
   `t in (a,b)` such that

   ```text
   IsNontrivialZero (1/2+i*t).
   ```

   The proof must pass through opposite strict signs of `hardyXi`, not through an arbitrary
   zero of the mollified product.
6. For a finite family of strongly separated nondegenerate intervals, each satisfying the
   local detector, construct an injective family of actual critical-line zero ordinates, one
   inside each interval.
7. Compile a countermodel showing that if the nonnegative square is replaced by an arbitrary
   sign-changing multiplier, the product can have opposite endpoint signs while the base
   function is everywhere nonzero.
8. Package an aggregate endpoint with only proved assumptions and conclusions.

Exact declaration names may follow local style. Interval-integral orientation must be fixed by
`a < b`; totalized complex powers at the `n=0` term must be avoided by summing only over
positive natural indices.

## Success criteria

`FULL_LOCAL_SIGN_CHANGE_PRODUCER_SUCCESS` requires all eight clauses, one proven Target, one
exact open successor Target, exact TargetChecks, selected transitive axiom prints with standard
axioms only, empty forbidden scans, warning-as-error compilation, a full build, and every public
CI gate.

`MEANINGFUL_PARTIAL` requires clauses 1--5, 7, and 8, with the separated-interval assembly or
first unavailable measure-theoretic lemma stated exactly.

`FALSIFIED` applies if the strict integral gap does not force both signs under the stated
continuity and interval assumptions, or if nonnegative squared multiplication can create
opposite signs without opposite signs of the actual Hardy coordinate. The failed implication
and a counterexample must be recorded.

## Negative controls and claim boundary

- `PRODUCT_ZERO`: `F(t)=0` does not by itself imply `hardyXi(t)=0`; the root mollifier may
  vanish.
- `STRICT_TWO_SIGNS`: the detector must produce strict positive and strict negative values.
  Merely producing a product zero is insufficient.
- `SQUARE_ROLE`: the multiplier is `normSq(N) >= 0`. An arbitrary real or complex multiplier
  may introduce a false sign change.
- `ENDPOINT_NONZERO`: strict product signs automatically make the squared multiplier positive
  at the selected endpoints; no global nonvanishing assumption on the mollifier is added.
- `INTERVAL_ORIENTATION`: all local integral statements assume `a < b`.
- `DISJOINTNESS`: distinct-zero assembly uses strongly ordered open intervals, not merely
  pairwise disjoint closed sets with ambiguous shared endpoints.
- `ACTUAL_ZERO_DICTIONARY`: the endpoint uses
  `hardyXi_eq_zero_iff_isNontrivialZero`; it does not replace the actual zeta predicate by an
  abstract zero.
- `NO_PROPORTION_PROMOTION`: finitely many detected intervals do not imply `T log T` zeros or a
  positive proportion.
- `NO_MOMENT_INPUT`: no Selberg first-, second-, or fourth-moment asymptotic is assumed or
  registered as proved.
- `NO_RH`: positive critical-line density would still allow off-line zeros. H1 and RH remain
  open.

Expected classification:

- `historical_subroute_coverage_delta=1`;
- `selberg_sign_detector_delta=1`;
- `actual_zeta_zero_delta=1`;
- `selberg_moment_delta=0`;
- `critical_zero_proportion_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Production gate

No production Lean source, Target, TargetCheck, axiom-audit entry, or aggregate import may be
created or edited until this docs-only preregistration passes public Lean Action CI.

The persistent RH Goal remains active. A local stop returns to fresh historical route selection
after the full evidence chain.
