# H9 Franel Rank--Mertens Correlation Result

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H9-FRANEL-RANK-MERTENS-01`

Classification: `MEANINGFUL_PARTIAL / FRANEL_MERTENS_CORRELATION_FORMALIZED`

## Compiled result

`LeanLab/Riemann/FareyFranel.lean` reconstructs the actual source positive Farey ordering. It
proves strict ordering, exact one-based rank and rank image, terminal zero discrepancy, rank and
cardinality Mertens transforms, the pointwise remainder and source-centered discrepancy, the
exact squared finite correlation quadratic, and the source Lemma 7 Dedekind-block transform.

The endpoint test proves `sum M(floor(N/n))=1`, deriving the source `+1/2` rather than inserting
it. The aggregate certificate is `fareyFranelCorrelation_endpoint`.

## Finite controls

Lean proves:

```text
fareyPhi(0,1,2,3) = (0,1,2,4),
fareySquaredDiscrepancy(0,1,2,3) = (0,0,0,1/72),
fareyMertensGcdKernel(1,2,3) = (1,1,5/3).
```

The published formula is checked at `N=1,2,3`. The source three-term relation is checked at
`(1,1,1)`, `(1,2,3)`, and noncoprime `(2,2,2)`. These reject convention and gcd-factor errors;
they are not a general proof.

## First open source theorem

The exact unproved proposition is `FareyDedekindThreeTerm`, the endpoint-sensitive modified
Dedekind three-term relation from Kanemitsu--Yoshimoto Lemma 8. It is deliberately absent from
`FareyFranelCorrelationCertificate`.

The complete Theorem 3 gcd-kernel identity remains open. The RH-equivalent Franel asymptotic is
a further separate edge even after the finite identity.

## Mechanical audit

- standalone and warning-as-error module compiles: pass;
- Targets and TargetChecks, including warning-as-error: pass;
- AxiomsAudit: pass;
- selected axioms: `propext`, `Classical.choice`, `Quot.sound`;
- `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, `unsafe`: absent;
- resource-limit relaxations: absent;
- `git diff --check`: pass;
- full build: `8780/8780`.
- frozen implementation: `e672420574994819213da3999e8c2e962e6c903c`;
- public Lean Action: run `30372189487`, attempt 2, job `90319104548`, passed in `2m29s`;
- infrastructure record: attempt 1 failed before build on GitHub's Elan-download HTTP 500;
  no source change was made before the successful rerun.
- immutable evidence: `10f45b94f4844baa6e4883b86f6cea4299fc40d3`;
- evidence Lean Action: run `30372716950`, job `90320456175`, passed in `2m20s`;
- proof freeze: the evidence commit has an empty `LeanLab/` diff from the frozen implementation.

## Claim boundary

This is a finite historical interface and a localization of its first missing source identity.
It does not prove the general three-term relation, complete Franel gcd-kernel formula,
discrepancy decay, Mertens square-root cancellation, H9, or RH.

The proof source and immutable evidence are public-green. One docs-only final ledger remains.
After its CI, local STOP returns to fresh cross-family `ROUTE_SELECTION`; direct proof attempts
and conjecture testing remain open.
