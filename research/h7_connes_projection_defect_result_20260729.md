# H7 Connes Nested-Projection Positive-Type Result

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H7-CONNES-PROJECTION-DEFECT-01`

Node: `H7-CONNES-NESTED-PROJECTION-POSITIVE-TYPE-01`

Classification: `FULL_SUCCESS / SOURCE_POSITIVE_TYPE_HINGE_FORMALIZED`

Public state: `PUBLICLY_CLOSED / TARGET_PROVEN`

## Source question

Connes 1998 Theorem 5 equations `(23)`--`(25)` pass from the cutoff-subspace containment

```text
Q'_Lambda <= S_Lambda
```

to positivity of

```text
Trace((S_Lambda-Q'_Lambda) V(f*f*)).
```

This campaign asks whether that implication is exact finite algebra and whether nesting can be
removed.

## Compiled result

The new module `LeanLab/Riemann/ConnesProjectionDefect.lean` defines finite complex matrices
`P`, `Q`, and `A`, with the six source-style laws

```text
Pᴴ=P, P*P=P, Qᴴ=Q, Q*Q=Q, P*Q=Q, Q*P=Q.
```

Lean proves:

1. `H=P-Q` is self-adjoint and idempotent.
2. The exact identity

   ```text
   Trace(H*(A*Aᴴ)) = coe(sum_i sum_j normSq((H*A) i j)).
   ```

3. The trace has zero imaginary part and nonnegative real part.
4. The trace vanishes exactly when `H*A=0`.
5. All positive results and the negative control are packaged in
   `connesProjectionDefect_endpoint`.

The proven Target is `H7.connes.nested-projection-defect-positive-type`.

## Falsification boundary

Lean also checks the `1 x 1` matrices

```text
P=0, Q=1, A=1.
```

Both `P` and `Q` are individually self-adjoint idempotents, but they are not nested and

```text
re Trace((P-Q)*(A*Aᴴ)) = -1.
```

Thus nesting is not cosmetic. It is the exact finite hypothesis protecting positive type.

## Omission reading

No omitted finite algebraic step was found: once the source containment is available, the sign
is a rigid norm-square identity. The useful relocation is sharper:

```text
actual adèle cutoff containment
  -> trace-class and normalization control
  -> uniform distributional limit
  -> complete Weil positivity
  -> RH.
```

The historical omission search should therefore inspect whether the number-field construction
already contains, or nearly contains, a stronger usable form of the first three arrows. Repeating
finite positivity arguments has low value.

## Audit

- preregistration commit: `59a6d8aa74fb48c3123e391e50e2e932408bcf66`;
- preregistration CI: run `30411132179`, build job `90447227409`, passed in `1m33s`;
- production module: 192 lines;
- exact TargetChecks: eight;
- selected axiom prints: seven, each only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden and resource-relaxation scans: empty;
- warning-as-error compiles: pass;
- `git diff --check`: pass;
- full project build: `8793/8793`.

## Claim boundary

This result does not construct `Q'_Lambda` or `S_Lambda` on the adèle class space, prove an
infinite-dimensional trace-class statement, establish the source cutoff asymptotics, identify a
limit with the Weil distribution, prove unconditional Weil positivity, construct a
Hilbert--Polya operator, prove H7, or prove RH.

Deltas: historical route coverage `+1`, source-logic map `+1`, hard gap `0`, RH frontier `0`.

The persistent RH Goal remains active. After public closure, route selection must compare all
historical families and may also select an original conjecture or direct RH attack.

## Public implementation evidence

Frozen implementation commit `25c18e31cd882f9ad2f43fe26900e450d98c0500` passed public Lean
Action run `30411787173`, build job `90449324931`, in `2m1s`.

The frozen proof and registration set is:

- `LeanLab/Riemann/ConnesProjectionDefect.lean`;
- `LeanLab/Riemann/Targets.lean`;
- `LeanLab/Riemann/TargetChecks.lean`;
- `LeanLab/Riemann/AxiomsAudit.lean`;
- `LeanLab.lean`.

The immutable-evidence and final-ledger commits must leave this set unchanged from the frozen
implementation.

Immutable-evidence commit `78f1810d722e9b846a4fb7c4b40c8d78b3edf95a` passed public Lean
Action run `30411999399`, build job `90450005443`, in `1m31s`. The frozen-set diff from
`25c18e31cd882f9ad2f43fe26900e450d98c0500` is empty.

## Final ledger

Close exactly:

```text
H7.connes.nested-projection-defect-positive-type
```

as `FULL_SUCCESS / SOURCE_POSITIVE_TYPE_HINGE_FORMALIZED`.

Keep open:

1. construction of the actual number-field adèle-class Hilbert space and cutoff projections;
2. proof of the exact source containment `Q'_Lambda <= S_Lambda`;
3. trace-class and normalization control for the cutoff products;
4. prolate and archimedean cutoff asymptotics;
5. a uniform distributional limit equal to the complete Weil distribution;
6. unconditional Weil positivity on an RH-equivalent test class;
7. an actual Hilbert--Polya or absorption-spectrum realization;
8. H7 and RH.

The durable conclusion is that the finite sign is completely rigid after projection
containment: it is an exact norm-square identity. Historical omission work in this route should
therefore inspect the infinite and arithmetic producers, not repeat the finite positivity
consumer.

After final-ledger public CI, publish one closure receipt and return the active RH Goal to fresh
cross-family historical omission selection; the final-ledger gate is complete below.

Final-ledger commit `6ad4a77323b3fa163fe415d26fd01b0ce1073c92` passed public Lean
Action run `30412182228`, build job `90450618374`, in `1m32s`. The frozen-set diff remains
empty. The closure receipt records the complete public chain.
