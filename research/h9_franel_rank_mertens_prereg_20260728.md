# H9 Franel Rank--Mertens Quadratic Preregistration

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H9-FRANEL-RANK-MERTENS-01`

Selected node: `H9-FRANEL-RANK-MERTENS-QUADRATIC-01`

Mode: `LITERATURE`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_PENDING`

## Parent and materially new angle

The H0 Chebyshev--Mellin campaign is publicly closed at final-ledger commit
`71705474e8d38968c39400a2455745c519a31818`, Lean Action run `30343150121`, build job
`90223131928`, in `2m0s`.

The nearest H9 predecessor is `LITERATURE-20260726-H9-FAREY-MOBIUS-WEYL-01`, publicly closed at
final-ledger commit `8a84e18a30e95bf1be423a949438deb0fdfafabb`. It proves the actual
duplicate-free positive Farey pair set and the exact arbitrary-test Mertens transform, but
deliberately contains no ordering, rank, or discrepancy.

This campaign is materially different: it reconstructs the rational-value ordering and the
one-based rank that enter Franel's source discrepancy, specializes the existing transform to
the counting function, and attempts the complete squared Mertens/gcd identity.

## Locked primary sources

1. J. Franel, "Les suites de Farey et le probleme des nombres premiers," *Nachrichten von der
   Gesellschaft der Wissenschaften zu Goettingen, Mathematisch-Physikalische Klasse* (1924),
   198--201. Original scan and metadata:
   <https://eudml.org/doc/59156>
2. E. Landau, "Bemerkungen zu der vorstehenden Abhandlung von Herrn Franel," immediately
   following Franel, 202--206. Original Goettingen scan:
   <https://gdz.sub.uni-goettingen.de/dms/resolveppn/?PPN=GDZPPN002506548>
3. S. Kanemitsu and M. Yoshimoto, "Farey series and the Riemann hypothesis,"
   *Acta Arithmetica* 75 (1996), 351--374. Definition on pp. 351--352, Lemma 3, and Theorem 3
   on pp. 371--372:
   <https://matwbn.icm.edu.pl/ksiazki/aa/aa75/aa7544.pdf>

The 1996 Theorem 3 is the exact fixed formula. The 1924 papers are the historical route anchors.

## Source conventions and alignment

For natural order `N`, the source positive Farey sequence consists of all reduced fractions

```text
0 < a <= q <= N
```

in increasing rational order. Let

```text
Phi(N) = sum_{1<=q<=N} phi(q).
```

The positive fractions are indexed `rho_1,...,rho_Phi(N)`. The source supplements `rho_0=0`
for recurrence and counting arguments, but Theorem 3 sums only indices `1,...,Phi(N)`.
The last positive term is `rho_Phi(N)=1`.

This matches the compiled project definitions:

```text
fareyPairs N   = {(q,a) | 0<a<=q<=N and gcd(a,q)=1},
fareyValue(q,a)= a/q.
```

The project excludes `0/1`, includes `1/1` exactly once, and already proves rational-value
injectivity. No parallel fraction convention may be introduced.

## Exact mathematical endpoint

Define

```text
fareyPhi(N) = card(fareyPairs N),

fareyRank(N,p)
  = card {r in fareyPairs N | fareyValue(r) <= fareyValue(p)},

fareyDiscrepancy(N,p)
  = fareyValue(p) - fareyRank(N,p) / fareyPhi(N),

fareySquaredDiscrepancy(N)
  = sum_{p in fareyPairs N} fareyDiscrepancy(N,p)^2.
```

For the complete numerator block define

```text
fareyCompleteCount(n,xi)
  = card {a | 1<=a<=n and a/n<=xi},

fareyBlockRemainder(n,xi)
  = n*xi - fareyCompleteCount(n,xi).
```

For `N>=1` and `p in fareyPairs N`, prove

```text
fareyRank(N,p)
  = sum_{1<=n<=N} M(N/n) * fareyCompleteCount(n,fareyValue(p)),

fareyPhi(N)
  = sum_{1<=n<=N} M(N/n) * n,

fareyDiscrepancy(N,p)
  = 1/fareyPhi(N) *
      sum_{1<=n<=N} M(N/n) *
        fareyBlockRemainder(n,fareyValue(p)).
```

Define the exact finite remainder correlation

```text
fareyRemainderCorrelation(N,m,n)
  = sum_{p in fareyPairs N}
      fareyBlockRemainder(m,fareyValue(p)) *
      fareyBlockRemainder(n,fareyValue(p)).
```

Then prove the exact quadratic expansion

```text
fareyPhi(N)^2 * fareySquaredDiscrepancy(N)
  = sum_{1<=m,n<=N}
      M(N/m) * M(N/n) * fareyRemainderCorrelation(N,m,n).
```

Finally prove Kanemitsu--Yoshimoto Theorem 3 over the rationals:

```text
fareySquaredDiscrepancy(N)
  = 1 / (12 * fareyPhi(N)) *
      (sum_{1<=m,n<=N}
        M(N/m) * M(N/n) * gcd(m,n)^2 / (m*n) - 1).
```

All `M` values are cast from the compiled integer `finiteMertens`. All divisions occur in
`Rat`. The final formula requires `1<=N`, so `fareyPhi(N)` and all summation denominators are
nonzero.

## Proposed Lean surface

Names may change to match local APIs, but the mathematical surface may not weaken.

```lean
def fareyOrderedPairs (N : Nat) : List (Nat x Nat) :=
  (fareyPairs N).sort fun p q => fareyValue p <= fareyValue q

def fareyPhi (N : Nat) : Nat :=
  (fareyPairs N).card

def fareyRank (N : Nat) (p : Nat x Nat) : Nat :=
  ((fareyPairs N).filter fun q => fareyValue q <= fareyValue p).card

def fareyDiscrepancy (N : Nat) (p : Nat x Nat) : Rat :=
  fareyValue p - (fareyRank N p : Rat) / (fareyPhi N : Rat)

def fareySquaredDiscrepancy (N : Nat) : Rat :=
  sum p in fareyPairs N, fareyDiscrepancy N p ^ 2

def fareyCompleteCount (n : Nat) (xi : Rat) : Nat := ...

def fareyBlockRemainder (n : Nat) (xi : Rat) : Rat :=
  (n : Rat) * xi - fareyCompleteCount n xi

def fareyRemainderCorrelation (N m n : Nat) : Rat := ...

def fareyMertensGcdKernel (N : Nat) : Rat := ...

theorem fareyDiscrepancy_eq_mertens_remainder ... := ...

theorem fareySquaredDiscrepancy_eq_mertens_correlation ... := ...

theorem fareySquaredDiscrepancy_eq_franel ... := ...
```

The ordered list must be connected to `fareyRank`: for every valid list index, the rank of its
entry is exactly the one-based index. Merely defining a sort and never using or checking its
order does not satisfy the endpoint.

## Fixed Lean blocks

Create `LeanLab/Riemann/FareyFranel.lean`, importing
`LeanLab.Riemann.FareyMobiusWeyl`, and compile as many of the following as the source proof
supports.

1. Define the actual rational-value ordered Farey list and prove its elements, nodup property,
   length, nondecreasing values, and strict increase of distinct successive values.
2. Define one-based rank by lower-set cardinality. Prove positivity, upper bound, injectivity,
   and that rank is exactly index plus one on the ordered list.
3. Prove ranks of the Farey pairs form exactly `1,...,fareyPhi(N)`.
4. Define the exact rational discrepancy and squared discrepancy; prove the `1/1` endpoint has
   rank `fareyPhi(N)` and discrepancy zero.
5. Define complete block counts and block remainders. Prove endpoint formulas for `xi=0`, `xi=1`,
   and `xi=fareyValue p`.
6. Specialize `farey_sum_eq_mertens_transform` to the lower-interval indicator and prove the
   exact rank/count Mertens identity.
7. Specialize the same transform to the constant-one function and prove
   `fareyPhi(N)=sum M(N/n)*n`.
8. Combine blocks 6 and 7 into the pointwise discrepancy--Mertens remainder identity.
9. Square and exchange only finite sums to prove the exact Mertens remainder-correlation
   quadratic expansion.
10. Reconstruct the finite Bernoulli/sawtooth correlation needed by the source proof, with all
    integer-point endpoint values explicit.
11. Collapse the correlation quadratic to the source double gcd kernel and prove the complete
    Franel Theorem 3 identity.
12. Compile exact controls at `N=0,1,2,3`, including both sides of the final formula for every
    positive test order.
13. Bundle the strongest source endpoint in one aggregate certificate and register it honestly.

## Adversarial and falsification cases

- `N=0`: `fareyPhi(0)=0`; no theorem may divide by it.
- `N=1`: the ordered list is `[1]`, its only discrepancy is zero, and the kernel-minus-one is
  zero.
- `N=2`: the ordered list is `[1/2,1]`; both discrepancies and the final right side are zero.
- `N=3`: the ordered list is `[1/3,1/2,2/3,1]`; the nonzero discrepancies are `1/12` and
  `-1/12`, so the squared sum is `1/72`.
- `ORDER_KEY`: sort by `fareyValue`, never lexicographically by `(q,a)`.
- `ONE_BASED_RANK`: the first positive fraction has rank one, not zero.
- `SOURCE_ZERO`: `0/1` remains excluded from the Theorem 3 sum.
- `SOURCE_ONE`: `1/1` remains included once and has zero discrepancy.
- `RATIONAL_EXACTNESS`: no floating-point ordering or numerical equality may enter a theorem.
- `INTEGER_POINT_REMAINDER`: the sawtooth/Bernoulli convention at integer arguments must match
  the source correction term.
- `NO_ASYMPTOTIC_SMUGGLE`: the exact identity supplies no decay estimate.
- `NO_RH_PROMOTION`: neither the pointwise formula nor the complete finite identity proves H9
  or RH without the separate RH-equivalent asymptotic bound.

If the final formula fails at `N=1`, `N=2`, or `N=3`, first classify whether the error is a
source transcription, endpoint convention, rank convention, or coercion error. Do not repair it
by changing the registered source objects.

## Success, partial success, and falsification

`FULL_SUCCESS` requires all thirteen blocks, the exact Kanemitsu--Yoshimoto Theorem 3 formula,
one aggregate proven Target, exact TargetChecks, selected transitive axiom prints, empty
forbidden/resource scans, warning-as-error compilation, full build, and independent public CI
for preregistration, frozen implementation, immutable evidence, and final ledger.

`MEANINGFUL_PARTIAL` requires blocks 1--9 and 12: the actual ordering/rank, exact pointwise
Mertens discrepancy formula, and exact squared remainder-correlation expansion. The first
unproved source correlation theorem must be recorded in theorem-shaped form.

`SOURCE_CONVENTION_CORRECTION` is recorded if the published displayed formula is valid only
after a source-exact endpoint or Bernoulli convention change. The original and corrected
statements must both be tested at the finite control orders.

`FALSIFICATION` is recorded only if Lean proves that the source-aligned formula is false at a
concrete finite order after all conventions have been checked.

## Known obstacles and strict boundary

- Mathlib has finite sorting and rational linear order, but the exact theorem connecting a
  sorted finset index to lower-set cardinality may require a reusable local rank lemma.
- The existing Farey transform is complex-valued. Count identities must either use exact casts
  and injectivity into `Complex` or prove an equivalent rational/integer specialization without
  duplicating the Mobius inversion argument unsafely.
- Mathlib contains periodized Bernoulli polynomials but no located finite generalized Dedekind
  sum or the source three-term relation. The full gcd-kernel collapse may require proving the
  relevant finite sawtooth correlation from first principles.
- Rational floor and integer-point conventions must agree with the positive terminal numerator
  block `1<=a<=n`.
- The exact Franel identity is a known finite theorem. It does not prove its RH-equivalent
  asymptotic estimate, Mertens square-root cancellation, H9, or RH.

## Mechanical gates and stopping rule

Before proof-source editing:

- publish this docs-only preregistration and route-selection record;
- require public Lean Action CI to pass;
- keep the six inherited protected files untouched and unstaged.

Before accepting any theorem:

- register one aggregate Target in `Targets.lean`;
- add exact witnesses in `TargetChecks.lean`;
- print selected transitive axioms in `AxiomsAudit.lean`;
- scan for `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, `unsafe`, and relaxed
  resource options;
- compile with warnings as errors and run the full build;
- freeze the implementation before publishing immutable evidence.

Stop locally at `FULL_SUCCESS`, `MEANINGFUL_PARTIAL`, a source-convention correction, or a
kernel-checked falsification. Local stop returns to fresh cross-family `ROUTE_SELECTION`; it
does not stop H9 or the global RH Goal. Direct proof attempts and conjecture verification remain
open throughout.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: continued from the public H0 closure; reread current governance, HANDOFF,
  Targets/TargetChecks, hard-gap DAG, historical ruling, Farey predecessor preregistration and
  implementation, and the locked primary-source statements before selection.
- `global_goal`: active.

