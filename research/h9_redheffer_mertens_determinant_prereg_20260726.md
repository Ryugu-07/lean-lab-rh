# H9 Redheffer--Mertens Determinant Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-REDHEFFER-MERTENS-DETERMINANT-01`

Selected node: `H9-REDHEFFER-MERTENS-DETERMINANT-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_REQUIRED`

## Selection rationale

Fresh cross-family selection compares H0 sharp prime-error terms, H2 actual-zeta bow exclusion,
H8 actual canonical-system limits, H9 arithmetic criteria, and the open H1/H7/H11/H12 source
edges. H2, H8, H11, and the current H1/H7/H12 frontiers require a new global analytic or
spectral input. H0 has substantial project support through truncated Perron and the exact
Guinand--Weil formula, while H9's Redheffer matrix branch is absent from the repository.

This branch is not merely a new name for the Mertens criterion. Vaughan's source performs an
explicit integer row elimination, turns the summatory Mobius function into one determinant
pivot, and then develops a characteristic polynomial with only logarithmically many non-unit
roots. The finite elimination is the first exact interface needed before the spectral claims can
be audited for an omitted estimate.

## Primary-source anchors

- R. C. Vaughan, *On the Eigenvalues of Redheffer's Matrix, I*, in *Number Theory with an
  Emphasis on the Markoff Spectrum* (1993), pages 283--296. Equations `(3)`--`(6)` give the
  matrix, Mobius row eliminator, determinant identity, RH-strength Mertens bound, and reciprocal
  zeta integral; equations `(7)`--`(12)` begin the characteristic-polynomial reduction:
  `https://personal.science.psu.edu/rcv4/personal/Publications/REDCONF.pdf`.
- W. W. Barrett and T. J. Jarvis, *Spectral Properties of a Matrix of Redheffer*, Linear
  Algebra and its Applications 162--164 (1992), 673--683. This gives the characteristic
  polynomial and asymptotics of the two large eigenvalues:
  `https://doi.org/10.1016/0024-3795(92)90401-U`.
- R. C. Vaughan, *On the Eigenvalues of Redheffer's Matrix, II*, Journal of the Australian
  Mathematical Society 60 (1996), 260--273. This studies the remaining eigenvalues in punctured
  disks around one:
  `https://doi.org/10.1017/S1446788700037654`.

The fixed source dependency is:

```text
divisor relation + Mobius divisor cancellation
  -> exact first-row eliminator
  -> one Mertens pivot and an upper-triangular complementary block
  -> det Redheffer(n) = M(n)
  -> spectral product reformulation
  -> characteristic-polynomial and non-unit-root estimates.
```

This campaign fixes the first three arrows and the determinant identity. It does not import the
RH-equivalent Mertens growth bound as a premise and does not yet formalize the full
characteristic polynomial.

## Exact fixed endpoint

Use `Fin (n + 1)` to represent the positive integers `1,...,n+1`; this makes the zero-size
boundary explicit and prevents accidental evaluation of the Mobius function at zero.

The production module must prove all of the following.

1. Define the integer Redheffer matrix with entry one exactly when row index divides column index
   or the column represents one.
2. Define the finite Mertens sum and Vaughan's eliminator: the identity matrix with its first row
   replaced by the Mobius values `mu(1),...,mu(n+1)`.
3. Prove the eliminator has determinant one.
4. Prove the exact matrix product identity. Its first row is the Mertens sum in column one and
   zero elsewhere; every later row is the corresponding Redheffer row.
5. Prove that the complementary successor-index divisibility block is upper triangular with
   unit diagonal and determinant one.
6. Deduce the exact source theorem
   `det (redhefferMatrix n) = finiteMertens (n+1)`.
7. Derive exact determinant-zero and nonzero criteria, with scalar extension to `Q` if needed to
   state matrix nonsingularity without changing the integer identity.
8. Compile exact small-order checks for orders one through four without `native_decide`.

Exact declaration names may follow local style. The primary Target must be the determinant
identity, not a finite numeral check or a definition-only theorem.

## Proposed Lean surface

```lean
def finiteMertens (N : Nat) : Int
def redhefferMatrix (n : Nat) : Matrix (Fin (n + 1)) (Fin (n + 1)) Int
def redhefferEliminator (n : Nat) : Matrix (Fin (n + 1)) (Fin (n + 1)) Int

theorem det_redhefferEliminator ...
theorem redhefferEliminator_mul_redhefferMatrix ...
theorem det_redhefferMatrix_eq_finiteMertens ...
theorem det_redhefferMatrix_eq_zero_iff ...
```

## Falsification tests

- `INDEX_SHIFT`: no matrix entry or Mertens sum may use `mu(0)`.
- `OR_NOT_ADDITION`: the `(1,1)` entry is one, not two; the defining disjunction is Boolean.
- `ROW_COLUMN_ORIENTATION`: divisor cancellation belongs to the replaced first row. A transposed
  identity must not pass under a symmetric-looking finite check.
- `EMPTY_BOUNDARY`: the public theorem uses positive matrix order; any `0 x 0` auxiliary is
  separated from the source statement.
- `MERTENS_CONJECTURE_BOUNDARY`: the false claim `|M(n)| < sqrt(n)` is prohibited.
- `RH_EQUIVALENCE_BOUNDARY`: `M(n)=O(n^(1/2+epsilon))` is RH-strength and remains unproved here.
- `SPECTRAL_BOUNDARY`: a determinant identity controls only an eigenvalue product. It does not
  prove normality, self-adjointness, individual eigenvalue location, or the Vaughan
  characteristic-polynomial estimates.

## Success and classification

Success requires:

- every fixed endpoint above;
- one proven Target and exact TargetChecks for the generic identity and low orders;
- selected transitive axiom prints with standard axioms only;
- empty placeholder, custom-declaration, and resource-relaxation scans;
- warning-as-error production compilation, full build, and all public CI gates.

Expected classification:

- `result=REDHEFFER_MERTENS_ELIMINATION_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `arithmetic_spectral_interface_delta=1`;
- `characteristic_polynomial_delta=0`;
- `mertens_growth_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Production gate

No production Lean source may be created or edited until this docs-only preregistration passes
public Lean Action CI. Local STOP returns the active global Goal to `ROUTE_SELECTION`; it does
not close H9, the Redheffer spectral branch, or RH.

The production gate passed at preregistration commit
`1b535d265bdd186bbcd1e5e5c67cf69b441259f2`, public Lean Action run `30207301448`,
build job `89807491114`, in `2m11s`.

## Local result

`LeanLab/Riemann/RedhefferMertensDeterminant.lean` is a 257-line no-sorry implementation of
the fixed endpoint. It proves:

- a checked bijection from zero-based `Fin N` indices to the positive divisors used by the
  Mobius convolution, with no `mu(0)` evaluation;
- determinant one for Vaughan's first-row eliminator;
- exact elimination of every nonfirst entry in the replaced row;
- a unit upper-triangular successor divisibility block;
- `det (redhefferMatrix n) = finiteMertens (n+1)` for every `n`;
- exact determinant-zero and nonzero criteria and orders one through four.

The proven Target, eight exact TargetChecks, six selected axiom prints, warning-as-error
production/registry/check/audit compilation, empty forbidden scans, `git diff --check`, and full
`8771/8771` build pass locally. Every selected theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

The source elimination is correct but exposes no extra determinant slack: every arithmetic
cancellation is concentrated in the pivot `finiteMertens (n+1)`. The next source-bearing
question is the full characteristic polynomial and its logarithmically many non-unit roots, not
another restatement of the determinant identity.

Local classification:

- `result=REDHEFFER_MERTENS_ELIMINATION_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `arithmetic_spectral_interface_delta=1`;
- `characteristic_polynomial_delta=0`;
- `mertens_growth_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Frozen implementation

Implementation commit `2003f912dfb0627b1c41d4b80db1abc6eb24e5d3` passed public Lean
Action run `30207909320`, build job `89809080863`, in `2m6s`. The production module, proven
Target, exact TargetChecks, and selected axiom prints are frozen at that hash.

The next gate is a docs-only immutable-evidence commit. No `LeanLab/` file may change between
the frozen implementation and that evidence commit. The full characteristic polynomial, joint
control of its logarithmically many non-unit roots, the RH-equivalent Mertens growth estimate,
reciprocal-zeta continuation, H9, and RH remain open.
