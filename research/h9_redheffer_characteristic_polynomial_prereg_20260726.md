# H9 Redheffer Characteristic Polynomial Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-REDHEFFER-CHARPOLY-01`

Selected node: `H9-REDHEFFER-CHARACTERISTIC-POLYNOMIAL-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_REQUIRED`

## Selection rationale

The parent Redheffer campaign publicly closed the exact determinant identity but found no
additional Mertens estimate in the first-row Mobius elimination. A fresh comparison against the
current H0, H1, H2, H7, H8, H11, and H12 frontiers shows that those branches presently require
new global analytic, spectral, or sparse-exception inputs. Vaughan's adjacent characteristic
polynomial is instead a source-exact unformalized edge that determines whether the Redheffer
route genuinely compresses all arithmetic information into only logarithmically many non-unit
roots.

This is not numerical bound optimization and not another RH-equivalent slogan. It reconstructs
the algebraic object on which every later dominant-root, small-root, and joint-product argument
depends. A failure will identify an exact indexing, support, or denominator-clearing obstruction;
a success will make the remaining spectral estimates auditable without hiding the matrix-to-
polynomial transition.

## Primary-source anchor

R. C. Vaughan, *On the Eigenvalues of Redheffer's Matrix, I* (1993), equations `(7)`--`(12)`:

- define a first-row transform for `A_N-lambda*I`;
- express its coefficients through ordered factorizations
  `D_k(m) = #{(m_1,...,m_k) : m_i >= 2, product m_i = m}`;
- set `S_k(N)=sum_{m<=N} D_k(m)`;
- prove
  `det(lambda*I-A_N)=(lambda-1)^(N-L-1) P_N(lambda)`,
  where `L=floor(log_2 N)` and
  `P_N(lambda)=(lambda-1)^(L+1)
    - sum_{k=1}^L S_k(N)(lambda-1)^(L-k)`;
- deduce that exactly `N-L-1` eigenvalues, with algebraic multiplicity, equal one.

The displayed multiplicity statement requires `N >= 2`. At `N=1`, the source matrix is `[1]`,
so its characteristic polynomial is `lambda-1` and the root one has multiplicity one, whereas
`N-floor(log_2 N)-1=0`. The production theorem must expose this order-one boundary separately
instead of silently extending the generic formula.

Source:
`https://personal.science.psu.edu/rcv4/personal/Publications/REDCONF.pdf`.

Barrett--Jarvis (1992) and Vaughan II (1996) remain successor sources for dominant and remaining
root estimates. Their asymptotic conclusions are not premises of this campaign.

## Exact fixed endpoint

Use the existing positive-order matrix `redhefferMatrix (N-1)` and work over `Z[X]`. Let
`z=X-1`. The implementation must prove all of the following.

1. Define the ordered-factorization counts `D_k(m)` by an exact finite recursion through proper
   divisors, and define `S_k(N)` on positive integers `m<=N`.
2. Prove the recursion needed by Vaughan's row transform and the support theorem
   `D_k(m)=0` when `m<2^k`.
3. Prove the logarithmic boundary:
   `D_k(m)=0` for `m<=N` and `Nat.log 2 N<k`, while the depth
   `L=Nat.log 2 N` has a nonzero witness at `m=2^L`.
4. Define a denominator-free polynomial first-row eliminator. Its first row is the source
   transform multiplied by a sufficient power of `z`; later rows are the identity.
5. Prove its determinant, the exact matrix-product shape, and the polynomial determinant
   identity without evaluating at a special scalar and without dividing by `z`.
6. Deduce the source characteristic-polynomial factorization over `Z[X]`.
7. Prove that the reduced factor is nonzero at `lambda=1`, hence the multiplicity of the
   polynomial root `1` is exactly `N-Nat.log 2 N-1`.
8. Compile exact characteristic polynomials for orders one through four and check compatibility
   at `lambda=0` with the already compiled Mertens determinant.

The primary Target must be the generic characteristic-polynomial factorization or the exact
root-multiplicity theorem. A low-order computation, definition-only theorem, or conditional
statement does not satisfy the endpoint.

## Intended polynomial route

The proof should clear denominators before matrix multiplication. If `K` is the selected
factorization depth, define

```text
q_j(z) = sum_{k=1}^K D_k(j) z^(K-k).
```

For `j>1`, the proper-divisor recursion gives

```text
z*q_j(z) = z^K + sum_{i|j, 1<i<j} q_i(z)
```

once the next factor count vanishes beyond the support boundary. This cancels every nonfirst
entry in the transformed first row. The first pivot is the reduced source polynomial, and the
remaining block contributes a pure power of `-z`.

No proof may cancel a scalar denominator under an unstated `lambda != 1` hypothesis. Polynomial
domain cancellation must retain the root at one and its exact multiplicity.

## Falsification tests

- `DENOMINATOR_AT_ONE`: a proof valid only for `lambda != 1` does not establish the polynomial
  identity or algebraic multiplicity.
- `D0_BOUNDARY`: the empty factorization counts only `m=1`; it may not add a spurious term for
  positive `k`.
- `ORDERED_NOT_UNORDERED`: `D_k` counts ordered tuples, not multiplicative partitions.
- `PROPER_DIVISOR_ORIENTATION`: the recurrence must split off a factor at least two and exclude
  the unchanged product.
- `LOG_FLOOR_BOUNDARY`: both `2^L<=N` and `N<2^(L+1)` must be proved for positive `N`.
- `ALGEBRAIC_NOT_GEOMETRIC`: kernel dimension alone does not prove the source's algebraic
  multiplicity statement.
- `CHARPOLY_SIGN`: use `det(lambda*I-A_N)` and check orders one through four.
- `SPECTRAL_BOUNDARY`: the factorization does not locate the non-unit roots or bound their joint
  product.
- `MERTENS_BOUNDARY`: the false square-root Mertens conjecture remains prohibited, and no
  RH-equivalent Mertens growth estimate may be imported.

## Success and classification

Success requires every fixed endpoint, one proven Target, exact generic and low-order
TargetChecks, selected transitive axiom prints with standard axioms only, empty forbidden scans,
warning-as-error compilation, full build, and all public CI gates.

Expected classification:

- `result=REDHEFFER_CHARACTERISTIC_POLYNOMIAL_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `spectral_compression_interface_delta=1`;
- `unit_root_multiplicity_delta=1`;
- `source_boundary_correction_delta=1`;
- `nonunit_root_location_delta=0`;
- `mertens_growth_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

If the generic source factorization cannot be compiled, record the strongest compiled support or
cleared-eliminator theorem as `PARTIAL / BLOCKER_EXPOSED`; do not promote it to success.

## Production gate

No production Lean source may be created or edited until this docs-only preregistration passes
public Lean Action CI. Local STOP returns the active global Goal to `ROUTE_SELECTION`; it does
not close the Redheffer spectral route, H9, or RH.

The production gate passed at preregistration commit
`0b0654a53272104e64bfba6f18d36b9c362e1028`, public Lean Action run `30208450587`,
build job `89810511648`, in `1m59s`.

## Local result

`LeanLab/Riemann/RedhefferCharacteristicPolynomial.lean` is a 725-line no-sorry
implementation of the fixed endpoint. It proves:

- exact ordered-factor recursion and the support bound `D_k(m)=0` for `m<2^k`;
- vanishing above `floor(log_2 N)` and a positive witness at the logarithmic boundary;
- a denominator-free polynomial first-row eliminator, its determinant, and its exact product
  with the characteristic matrix;
- Vaughan's generic characteristic-polynomial factorization over `Z[X]`;
- nonvanishing of the reduced factor at one and exact algebraic multiplicity
  `N-floor(log_2 N)-1` for `N>=2`;
- the separate order-one multiplicity `1`, correcting the unrestricted reading of the source
  formula;
- compatibility at zero with `det A_N=M(N)` and exact characteristic polynomials for orders one
  through four.

The proven Target, eight exact TargetChecks, seven selected axiom prints,
warning-as-error production/registry/check/audit compilation, empty forbidden scans,
`git diff --check`, and full `8772/8772` build pass locally. Every selected theorem depends only
on `propext`, `Classical.choice`, and `Quot.sound`.

The exact logarithmic compression is therefore real: for every order `N>=2`, all but
`floor(log_2 N)+1` roots are exactly one. It supplies no location, separation, or joint-product
bound for the remaining roots. In particular, it proves no new Mertens estimate and does not
advance the RH frontier.

Local classification:

- `result=REDHEFFER_CHARACTERISTIC_POLYNOMIAL_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `spectral_compression_interface_delta=1`;
- `unit_root_multiplicity_delta=1`;
- `source_boundary_correction_delta=1`;
- `nonunit_root_location_delta=0`;
- `mertens_growth_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

The next gate is to freeze and publish the implementation. Dominant-root asymptotics,
remaining-root disks, joint non-unit-root product control, Mertens growth, H9, and RH remain
open.

## Frozen implementation

Implementation commit `4fbad00c4c24c8a5ae9b9885b0a23da82744665b` passed public Lean
Action run `30209691871`, build job `89813735900`, in `2m24s`. The production module, proven
Target, eight exact TargetChecks, and seven selected axiom prints are frozen at that hash.

Docs-only immutable-evidence commit `ada5bb11085378fb8c1def1e3e9924a4a6b672a9` passed public
Lean Action run `30209857664`, build job `89814144474`, in `1m47s`. There is no `LeanLab/`
difference between the frozen implementation and evidence commits.

The next gate is a docs-only final ledger and its public CI. Dominant-root asymptotics,
remaining-root disks, joint non-unit-root product control, Mertens growth, H9, and RH remain
open.
