# Height-ten Riemann--Siegel endpoint-mass structural evidence

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Classification: `STRUCTURAL_SOURCE_ENVELOPE / MEANINGFUL_PARTIAL /
ENDPOINT_MASS_OPEN / GLOBAL_GOAL_ACTIVE`

## Frozen implementation

Implementation commit: `5cc6e43fad122b1bf40c1ff614183183ff4ccf53`

Public Lean Action:

- run: `30721026723`;
- build job: `91424754896`;
- result: passed;
- duration: `2m59s`.

Frozen production blobs:

| file | blob |
| --- | --- |
| `LeanLab.lean` | `fb8674d26436775e0adaa2fdd9a51f54947bf06a` |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenRiemannSiegelEndpointMass.lean` | `69daf1b05206992b2253036b41380544942bdb21` |
| `LeanLab/Riemann/Targets.lean` | `de4ef7c42e2cf5a52605d0dc790a79ba4759d7db` |
| `LeanLab/Riemann/TargetChecks.lean` | `5d9bde8926cd01fb0c8f9ea67995425339e16f30` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `51d0adc1c5a532f7b49eb0697e3aab586b5a9d93` |

This evidence commit is docs only. Its CI and a post-CI `git ls-tree` check must preserve every
blob in this table.

## Immutable evidence verification

Docs-only evidence commit `650c11dd157be5ba6c8da5d9bc14273c568fd6ea` passed Lean Action run
`30721199125`, build job `91425204813`, in `2m1s`. A post-CI `git ls-tree` check confirms that
all five production blobs remain exactly equal to the frozen table.

## Compiled claim boundary

The frozen implementation proves exact quartic compact denominator growth, an actual compact
reciprocal-denominator polynomial envelope, exponential reciprocal-denominator tail decay, exact
principal-argument formulas, cubic compact phase bounds, rational distance-power bounds, an exact
actual-integrand norm factorization, and explicit compact pointwise envelopes at both fixed endpoint
heights.

The implementation also records a falsified intermediate candidate: the selected generic inverse-
square-root envelope does not hold throughout `x<=21/20`. Only the corrected `x<=51/50` theorem is
compiled, together with proof that the actual contour parameter lies in that interval.

## Audit boundary

- the new module and registration files pass warning-as-error;
- full local build passes `8832/8832`;
- five selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`;
- focused forbidden scans and `git diff --check` are empty.

## Strict limits

The frozen implementation does not prove either endpoint integral, total endpoint mass `<=3/5`,
the literal Riemann--Siegel remainder margin, critical-line interval nonvanishing, any unconditional
vertical boundary zone, the complete height-ten certificate, H12, or RH. The exact next work is
proof-producing compact exponential integration plus phase-sensitive tail integration. Historical
replay remains omission search, while original conjectures and direct attacks remain open.
