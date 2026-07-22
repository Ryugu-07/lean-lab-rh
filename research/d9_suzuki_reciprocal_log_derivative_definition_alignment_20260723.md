# D9 Suzuki Reciprocal-Log-Derivative Definition Alignment

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-D9-SUZUKI-RECIPROCAL-LIMIT-01`

Lean module: `LeanLab/Riemann/SuzukiReciprocalLogDerivativeAudit.lean`

Status: `LOCAL_IMPLEMENTATION_COMPLETE / IMPLEMENTATION_CI_REQUIRED`

## Source dictionary

| Source object | Lean object | Alignment |
| --- | --- | --- |
| Finite-interval characteristic function `W(a,theta;z)` | `suzukiAuditFiniteW n z = 1` | Generic zero-free stand-in only. It is not constructed from Suzuki's canonical system. |
| Normalizer `exp(phi(a,z))` | `exp (suzukiAuditFinitePhi n z)` | `phi_n` is the principal complex logarithm of a nowhere-zero punctured approximation. It is finite-valued but deliberately nonregular at `z=I`. |
| Compact-uniform convergence | `TendstoUniformlyOn ... atTop K` | The countermodel proves the stronger statement for every set `K`, hence in particular for every compact set. |
| Real-zero conclusion | `suzukiAuditHasOnlyRealZeros` | Every complex zero has imaginary part zero. Multiplicity is irrelevant to this falsification endpoint. |
| Scaled reciprocal logarithmic derivative `z^2*f/f'` | `SuzukiAuditHasFiniteReciprocalLogDerivativeExtension f f'` | Encoded without division as existence of a finite-valued global `F` satisfying `f'(z)*F(z)=z^2*f(z)` everywhere. |

## Literal finite-valued interpretation

`suzukiAuditPuncturedApproximation n` equals `z-I` away from `I` and equals `1/(n+1)` at `I`.
Lean proves it is nowhere zero and converges uniformly on every set to `z-I`. Setting `W_n=1` and
`phi_n=log(puncturedApproximation_n)` gives the exact source-shaped identity

`exp(phi_n(z))*W_n(z) = puncturedApproximation_n(z)`.

Thus every `W_n` has only real zeros vacuously, while the limit has the nonreal zero `I`. The
compiled negation applies only to the schema with no continuity, holomorphy, or other regularity
condition on `phi` or the normalized functions.

## Entire-function repair

`suzukiAuditQuartic(z)=(z^2-(1/5)^2)*(z^2-(7/5)^2)` is symmetric and has only real zeros. Lean
proves its complex derivative is `4*z^3-4*z`. At the nonzero point `z=1`, the derivative vanishes
and the quartic does not. Consequently no finite-valued global function `F` can satisfy

`quarticDerivative(z)*F(z)=z^2*quartic(z)`

for every complex `z`. This is the algebraic signature of a nonremovable reciprocal-log-derivative
pole. It does not assert that the actual Riemann xi derivative has such a nonzero critical point.

## Meromorphic interpretation

No meromorphic function, divisor, punctured-domain convergence predicate, or Hurwitz theorem is
defined in this campaign. A reformulation using meromorphic convergence on compact subsets away
from poles remains open and needs a separate zero-transfer theorem. It cannot reuse the ordinary
entire compact-uniform limit argument across omitted poles without proof.

## Deliberately absent claims

- No source characteristic function `W(a,theta;z)` is formalized.
- No convergence theorem for Suzuki's actual finite canonical systems is claimed.
- No critical point or pole of the actual Riemann xi function is asserted.
- Suzuki's unconditional finite-interval real-zero theorem is not challenged.
- The generic witnesses do not refute a correctly specified meromorphic version of the proposal.
- RH remains open.

The surviving D9 task is to construct the actual normalization and prove a regular or meromorphic
limit with every possible pole and the corresponding zero-transfer mechanism handled explicitly.
