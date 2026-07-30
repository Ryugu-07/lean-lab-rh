# H0 Chebyshev Reverse Zero-Exclusion Immutable Evidence

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H0-CHEBYSHEV-REVERSE-ZERO-EXCLUSION-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Public Implementation Receipt

- commit: `247ea4c176505b9186faa51a69f5c53bbdbe80f2`;
- Lean Action run: `30524180060`;
- build job: `90811183408`;
- duration: `2m16s`;
- result: pass.

## Frozen Lean Set

At the public implementation commit:

| file | git blob |
| --- | --- |
| `LeanLab/Riemann/ChebyshevReverseZeroExclusion.lean` | `2d0f9fc9db6d5aab25bb3d46f1c46e20773968b7` |
| `LeanLab/Riemann/Targets.lean` | `9dd6b6e075ed8a27a840faf9dfc0e42050878344` |
| `LeanLab/Riemann/TargetChecks.lean` | `ac14beacc9513e1f569a88f3e1d36964293e6bad` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `0ccc7bc13b843e18d42acf04f500393c7e7d6784` |
| `LeanLab.lean` | `f3df63e2215a312a621c24c11b172a3b0d55a65d` |

This evidence commit is docs-only and must leave every frozen blob unchanged.

## Proven Endpoint

Lean proves:

1. a natural-number `O(N^r)` Chebyshev error estimate gives the corresponding power bound
   for the real-axis floor-error cutoff;
2. the cutoff is locally integrable and its Mellin transform is complex differentiable on
   `Re(s)>r`;
3. the resulting continuation is the existing Chebyshev error L-series on `Re(s)>1`;
4. the pole-removed equation
   `(s-1)Z'=Z*(1-(s-1)E-Z)` continues analytically across `Re(s)>r`;
5. analytic zero order forbids a zero of `Z` in that half-plane;
6. every nontrivial zeta zero satisfies `Re(rho)<=r`;
7. all positive-epsilon Chebyshev error estimates imply `Mathlib.RiemannHypothesis`;
8. one fixed exponent `r=3/4` does not force the critical line.

## Audit Receipt

- standalone warning-as-error module compilation: pass;
- warning-as-error `Targets.lean`: pass;
- warning-as-error `TargetChecks.lean`: pass;
- warning-as-error `AxiomsAudit.lean`: pass;
- exact campaign TargetChecks: eight;
- selected campaign axiom prints: nine, each exactly within
  `[propext, Classical.choice, Quot.sound]`;
- placeholder scan: empty;
- custom `axiom`/`opaque`/`unsafe` scan on the new module: empty;
- resource-relaxation scan: empty;
- `git diff --check`: empty;
- full local build: `8814/8814`, inherited warnings only;
- public implementation build: pass.

## Claim Boundary

This evidence freezes the conditional reverse Chebyshev--von Koch implication. It does not
prove the every-positive-epsilon error estimate, an unconditional new zero-free region, H0,
or RH. The source error estimate remains the open producer.
