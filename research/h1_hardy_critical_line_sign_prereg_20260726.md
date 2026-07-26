# H1 Hardy Critical-Line Sign Bridge Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H1-HARDY-CRITICAL-LINE-SIGN-01`

Selected node: `H1-HARDY-CRITICAL-LINE-REAL-SIGN-BRIDGE-01`

Mode: `LITERATURE`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Selection rationale

The Riesz Mellin-boundary node is publicly closed. Fresh route selection compares the open
Riesz decay and continuation, H1's arbitrary-length mollifier moment, H2's actual-zeta bow
exclusion, H7's ground-state limit, H9's Farey criterion, H10's curve geometry, H11's
sparse-exception amplifier, and H12's global Speiser contour.

The repository's H1 card begins with Hardy's theorem, yet production Lean has no direct
formalization of the real critical-line xi coordinate or the sign-change consumer on which
the classical argument depends. Existing project theorems already provide the exact xi
functional equation, conjugation symmetry, entire analyticity, and xi-zero/nontrivial-zero
equivalence. This makes the missing first Hardy hinge bounded, source-aligned, and decidable.

This campaign does not optimize a numerical proportion. It opens a historically prior mechanism
and forces later source reconstruction to distinguish two facts:

1. xi is real on the critical line;
2. xi actually takes opposite signs on suitable intervals.

The first is compiled here. The second remains an explicit input to the interval consumer until
Hardy's transform estimates are reconstructed.

## Primary-source anchors

G. H. Hardy, *Sur les zeros de la fonction zeta(s) de Riemann*, Comptes rendus de
l'Academie des sciences 158 (1914), 1012--1014, states the infinitude of critical-line zeros:

`https://gallica.bnf.fr/ark:/12148/bpt6k3111d.image.f1014.langEN`

G. H. Hardy and J. E. Littlewood, *Contributions to the theory of the Riemann
zeta-function and the theory of the distribution of primes*, Acta Mathematica 41,
119--196, gives the later full source account:

`https://doi.org/10.1007/BF02422942`

The campaign's real-valuedness identity is normalized against the project's actual
`riemannXi`, not against an independently postulated Hardy `Z` phase.

## Exact fixed endpoint

Use the project xi function and the literal critical-line embedding. The implementation must
prove all of the following.

1. Define

   ```text
   criticalLinePoint(t) = 1/2 + i*t
   criticalXi(t) = riemannXi(criticalLinePoint(t))
   hardyXi(t) = Re(criticalXi(t)).
   ```

2. Prove the exact geometric identities

   ```text
   conj(criticalLinePoint(t)) = 1 - criticalLinePoint(t)
   criticalLinePoint(-t) = 1 - criticalLinePoint(t).
   ```

3. From `riemannXi_conj` and `riemannXi_one_sub`, prove without a real-valuedness hypothesis

   ```text
   criticalXi(t) = ofReal(hardyXi(t)).
   ```

   A proof that only shows zero imaginary part is acceptable only if the exact `ofReal`
   reconstruction is also registered.

4. Prove `hardyXi` is even and continuous.

5. Prove both exact zero dictionaries:

   ```text
   hardyXi(t) = 0 <-> criticalXi(t) = 0
   hardyXi(t) = 0 <-> IsNontrivialZero(criticalLinePoint(t)).
   ```

6. Prove the point is literally on the project critical line for every real `t`.

7. For `a<=b`, prove both interval orientations:

   ```text
   hardyXi(a) <= 0 <= hardyXi(b)
     -> exists t in [a,b], IsNontrivialZero(criticalLinePoint(t))

   hardyXi(b) <= 0 <= hardyXi(a)
     -> exists t in [a,b], IsNontrivialZero(criticalLinePoint(t)).
   ```

   The witness must retain its interval membership and critical-line fact.

8. Compile a sequence consumer. For every increasing real sequence whose adjacent selected
   endpoints have alternating weak signs, produce one actual nontrivial critical-line zero
   witness in every corresponding closed interval. The theorem need not choose pairwise
   distinct zeros in this campaign.

The primary Target must aggregate real-valuedness, evenness, exact zero equivalence, and the
sequence interval witness. Definitions alone, generic intermediate-value lemmas detached from
`riemannXi`, or an assumed xi zero do not satisfy the endpoint.

## Proposed Lean surface

Names may change only to match project style; mathematical content may not weaken.

```lean
def hardyCriticalLinePoint (t : Real) : Complex :=
  (1 / 2 : Complex) + Complex.I * t

def hardyCriticalXi (t : Real) : Complex :=
  riemannXi (hardyCriticalLinePoint t)

def hardyXi (t : Real) : Real :=
  (hardyCriticalXi t).re

theorem hardyCriticalXi_eq_ofReal (t : Real) :
    hardyCriticalXi t = (hardyXi t : Complex) := ...

theorem hardyXi_even :
    Function.Even hardyXi := ...

theorem continuous_hardyXi :
    Continuous hardyXi := ...

theorem hardyXi_eq_zero_iff_isNontrivialZero (t : Real) :
    hardyXi t = 0 <-> IsNontrivialZero (hardyCriticalLinePoint t) := ...

theorem exists_hardyXi_zero_of_sign_change
    {a b : Real} (hab : a <= b)
    (ha : hardyXi a <= 0) (hb : 0 <= hardyXi b) :
    exists t in Set.Icc a b,
      IsNontrivialZero (hardyCriticalLinePoint t) /\
      OnCriticalLine (hardyCriticalLinePoint t) := ...
```

The sequence consumer may use a sign-orientation predicate if that keeps both orientations
explicit.

## Intended proof route

1. Import the smallest existing project module that exposes `riemannXi_conj`,
   `riemannXi_one_sub`, `differentiable_riemannXi`, and
   `isNontrivialZero_iff_riemannXi_eq_zero`.
2. Normalize `conj(1/2+i*t)` and `1-(1/2+i*t)` by extensionality on real and imaginary parts.
3. Rewrite xi first by conjugation and then by the functional equation to prove that the
   critical-line value equals its own conjugate.
4. Convert self-conjugacy into exact `Complex.ofReal` reconstruction; define the real coordinate
   only after this normalization is fixed.
5. Obtain continuity by composing the continuous critical-line embedding with
   `differentiable_riemannXi.continuous` and `Complex.continuous_re`.
6. Apply the real intermediate value theorem on `Set.Icc a b`; transport the real zero through
   the exact zero dictionary and register `OnCriticalLine` by direct simplification.
7. Apply the interval theorem pointwise to the sequence hypothesis. Do not claim distinctness
   without a disjoint-interval or strict-separation proof.

## Falsification tests

- `NORMALIZATION`: the embedded point is exactly `1/2+i*t`; no independent theta phase or
  alternative completed-zeta normalization is introduced.
- `CONJUGATE_REFLECTION`: conjugation on the critical line is exactly `s -> 1-s`.
- `REAL_NOT_OSCILLATORY`: real-valuedness alone does not imply any sign change.
- `ENDPOINT_ZERO`: weak endpoint inequalities must correctly admit a zero at `a` or `b`.
- `ORIENTATION`: both negative-to-positive and positive-to-negative orderings compile.
- `INTERVAL_MEMBERSHIP`: every witness remains in the registered closed interval.
- `ACTUAL_XI`: the consumer concludes `IsNontrivialZero` for the project point, not a zero of an
  abstract surrogate.
- `CRITICAL_LINE`: `OnCriticalLine` is proved from the actual point definition.
- `DISTINCTNESS_NOT_SMUGGLED`: interval witnesses are not called distinct unless separation is
  separately compiled.
- `HARDY_THEOREM_NOT_CLAIMED`: no infinitude, lower count, or positive proportion is inferred
  from this node.

## Success and classification

Success requires every fixed endpoint, one proven aggregate Target, exact TargetChecks, selected
transitive axiom prints with standard axioms only, empty forbidden scans, warning-as-error
compilation, full build, and all public CI gates.

Expected classification:

- `result=HARDY_CRITICAL_LINE_REAL_SIGN_BRIDGE_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `critical_line_real_coordinate_delta=1`;
- `sign_change_consumer_delta=1`;
- `hardy_transform_delta=0`;
- `critical_line_infinitude_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

If exact real-valuedness or the actual-xi interval witness cannot be compiled, record the
strongest theorem and first precise obstruction as `PARTIAL / BLOCKER_EXPOSED`. Do not relabel a
generic intermediate-value theorem or a conditional xi-zero premise as success.

## Production and stopping gates

No production Lean source may be created or edited until this docs-only preregistration passes
public Lean Action CI.

The local campaign stops when the fixed endpoint is proved, falsified, or reduced to a precise
Mathlib or mathematical obstruction. A successful endpoint returns to fresh cross-family route
selection before choosing between Hardy's original transform, Farey--Franel--Landau, or another
historical family. Local STOP does not close H1 or the active RH Goal.
