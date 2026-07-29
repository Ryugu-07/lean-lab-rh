# H1 Hardy--Littlewood Source Normalization Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-LITTLEWOOD-SOURCE-NORMALIZATION-01`

Node: `H1-HARDY-LITTLEWOOD-SOURCE-NORMALIZATION-ETA-LOWER-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`

Status: `PREREGISTERED / PUBLIC_CI_PENDING`

## Parent and selection

- `parent_closure`: Hardy--Littlewood finite count receipt
  `3dda5779e156771e873485f1128446fcc1508d70`, Lean Action run `30465646740`.
- `selected_node`: `H1-HARDY-LITTLEWOOD-SOURCE-NORMALIZATION-ETA-LOWER-01`.
- `selection_reason`: the finite count consumer is closed, and the compiled H6 explicit
  Stieltjes--Stirling remainder can repair the first source-specific normalization premise.
- `material_difference`: this campaign neither optimizes a count constant nor attempts either
  second-moment theorem. It identifies the actual source coordinate and moves the absolute
  eta-window lower estimate from an abstract hypothesis into Lean.

## Source lock

Primary source:

- G. H. Hardy and J. E. Littlewood, *The zeros of Riemann's Zeta-Function on the critical
  line*, Mathematische Zeitschrift 10 (1921), Lemma 7, section 2.6, equation `(2.61)`,
  Lemma 11, equations `(2.81)`--`(2.87)`, and section 2.9:
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0010/LOG_0029.pdf>.

Compiled cross-route input:

- `deBruijnNewmanPolymathGammaStirlingR2_norm_le_three` from
  `LeanLab/Riemann/DeBruijnNewmanPolymathStieltjesScaledGamma.lean`.

The fixed source chain is:

```text
exact critical-line xi/Gamma/zeta identity
-> explicit Gamma lower estimate for z = 1/4 + i*t/2, t >= 8
-> A_zeta * |zeta(1/2+i*t)| <= |X(t)|
-> |eta(1/2+i*t)| <= 3*|zeta(1/2+i*t)|
-> A_eta * |eta(1/2+i*t)| <= |X(t)|
-> A_eta*H - |etaWindowError(H,t)|
     <= integral_[t,t+H] |X(u)| du.
```

## Fixed definitions

Create `LeanLab/Riemann/HardyLittlewoodSourceNormalization.lean` only after preregistration
public CI. Names may be adjusted to local style, but the statements may not be weakened
silently.

1. Define `sourceRadius(t)=max |t| 1`.
2. Define
   `sourceWeight(t)=sourceRadius(t)^(1/4)*exp(pi*sourceRadius(t)/4)/(t^2+1/4)`.
3. Define `sourceX(t)=-sourceWeight(t)*hardyXi(t)`.
4. Define analytic eta by
   `eta(s)=(1-2^(1-s))*riemannZeta(s)` and restrict it to the critical line.
5. Define
   `etaPrimitive(t)=integral_[0,t](Re eta(1/2+i*u)-1) du`.
6. Define
   `etaWindowError(H,t)=A_eta*(etaPrimitive(t+H)-etaPrimitive(t))`.
7. Define the raw unextended source weight separately for the zero-height negative control.

## Fixed Lean endpoint

`FULL_SUCCESS` requires all of the following.

1. Prove continuity and strict positivity of the extended source weight and continuity of
   `sourceX`.
2. Prove `sourceX(t)=0` iff `hardyXi(t)=0`, then construct an exact
   `HardyLittlewoodZeroCoordinate sourceX`.
3. Prove that for `t >= 1` the extension reduces to the literal source scaling.
4. Prove the exact project identity expressing `|hardyXi(t)|` through
   `|Gamma(1/4+i*t/2)|` and `|zeta(1/2+i*t)|`.
5. Using the compiled H6 remainder, prove an explicit Gamma lower estimate for `t >= 8`.
   The numerical constant is only a witness and is not an optimization target.
6. Prove a positive explicit constant `A_zeta` with
   `A_zeta*|zeta(1/2+i*t)| <= |sourceX(t)|` for `t >= 8`.
7. Prove continuity of critical-line eta and
   `|eta(1/2+i*t)| <= 3*|zeta(1/2+i*t)|`.
8. Prove a positive `A_eta` and the pointwise estimate
   `A_eta*|eta(1/2+i*t)| <= |sourceX(t)|` for `t >= 8`.
9. Prove continuity of the eta primitive and window error, the exact primitive interval
   identity, and
   `A_eta*H-|etaWindowError(H,t)| <= integral_[t,t+H]|sourceX(u)|du`
   whenever `t >= 8` and `H >= 0`.
10. Compile a theorem supplying item 9 on `[T,2T]` in the exact lower-premise shape of
    `hardyLittlewood_source_finite_count`.
11. Compile an aggregate endpoint certificate and the raw-weight zero-height negative control.

Register one proven Target and exact TargetChecks. Add selected standard-only axiom prints to
`AxiomsAudit.lean`. Import the module from `LeanLab.lean`.

## Success, partial, and obstruction criteria

`FULL_SUCCESS` requires all eleven items, no placeholders, warning-as-error compiles, exact
TargetChecks, standard-only selected axiom prints, empty forbidden/resource scans,
`git diff --check`, a full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires the global exact zero adapter and project-xi/Gamma/zeta identity,
plus the first exact unavailable inequality in the Gamma-to-eta chain.

`SOURCE_NORMALIZATION_FALSIFIED` requires a compiled contradiction between the proposed
positive-height source scaling and the project definitions, or a compiled counterexample to
the claimed lower estimate with all side conditions satisfied.

`BLOCKED_API` is not mathematical failure. It requires the exact missing Mathlib theorem for
complex powers, Gamma remainder conversion, or interval integrals while retaining every
compiled source subtheorem.

## Negative controls

- The literal positive-height source factor contains `t^(1/4)`. Its naive all-real extension
  has weight zero at `t=0`; it cannot be used to infer a global exact-zero adapter merely by
  cancelling a positive factor.
- A real coordinate with the right zeros but an arbitrary positive rescaling does not inherit
  the source moment estimates.
- Defining an eta primitive by an integral does not prove its equality to Hardy--Littlewood's
  Lemma 7 Dirichlet series or its square-mean bound.
- The absolute-window lower estimate alone does not prove a linear critical-zero count. The
  eta-error moment, source-window moment, and parameter budget remain required.
- A successful endpoint is not a positive-proportion theorem, H1, or RH.

## Successor obstacle map

- `OBS-H1-HARDY-LITTLEWOOD-ETA-SERIES-IDENTIFICATION-01`: identify the integral primitive with
  the relevant real component of the Lemma 7 Dirichlet series.
- `OBS-H1-HARDY-LITTLEWOOD-ETA-ERROR-MEAN-SQUARE-01`: prove the source-uniform error
  square-mean estimate.
- `OBS-H1-HARDY-LITTLEWOOD-X-MEAN-SQUARE-01`: prove Lemma 11 for the actual source coordinate.
- `OBS-H1-HARDY-LITTLEWOOD-PARAMETER-BUDGET-01`: choose `H`, `n`, and `b` to instantiate the
  finite count theorem uniformly.
- `OBS-H1-SELBERG-GLOBAL-MOMENT-01`: produce the later positive-proportion mollified moment
  family.
- `OBS-H1-SPARSE-EXCEPTION-01`: no critical-line proportion theorem alone excludes all
  off-line zeros.

## Audit gates

Before implementation publication:

1. no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, or `unsafe`;
2. no heartbeat, recursion-depth, or resource relaxation;
3. exact checks for every registered theorem;
4. selected `#print axioms` output contains only accepted standard foundations;
5. warning-as-error compile of the new module and registration files;
6. full project build;
7. protected inherited files remain untouched and unstaged.

After frozen implementation public CI, publish immutable evidence, final ledger, and closure
receipt through separate public-green commits. Then stop only this local campaign and rerank the
historical routes. The persistent RH Goal remains active.
