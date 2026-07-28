# H8 Conrey--Li Hardy-RKHS Half-Strip Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H8-CONREY-LI-HALF-STRIP-01`

Node: `H8-CONREY-LI-HALF-STRIP-EXTENSION-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Primary source and exact inference

The fixed source is Conrey--Li 1998, Theorem 2 and its proof:

<https://arxiv.org/abs/math/9812166>

The preceding compiled campaign proves the theorem's first stage: the RKHS shift premise makes
the source Cayley transform analytic and contractive on the upper half-plane. This campaign
attacks the second stage, which extends that same transform to `Im z>-1/2`.

## M0 definition alignment

1. The half-strip is the open subtype `{z : Complex // -1/2 < z.im}`.
2. The upper half-plane embeds into it by the identity on complex coordinates.
3. The source Hardy kernel is exactly
   `1 / (2*pi*I*(conj(w)-z-I))`.
4. Kernel centers used to define the initial multiplier are restricted to embedded upper
   points, not all half-strip points.
5. The source operator sends the kernel at `w` to `conj(B(w))` times that kernel. The
   conjugation is tied to Mathlib's inner-product convention and will be checked explicitly.
6. The extension value is extracted from the adjoint applied to a fixed half-strip kernel.
7. Analytic continuation and the norm bound are separate outputs. Neither is inferred from
   upper-half-plane boundedness alone.

## Proposed Lean spine

Names may change to match local conventions, but the statement strength may not be weakened:

```lean
def conreyLiHalfStrip := {z : Complex // -(1 / 2 : Real) < z.im}

def conreyLiHardyKernel
    (w z : conreyLiHalfStrip) : Complex :=
  1 / (2 * Real.pi * Complex.I *
    (conj (w : Complex) - (z : Complex) - Complex.I))

theorem dense_span_conreyLiHardyKernel_upper
    (H : Type*) [Hilbert hypotheses] [RKHS Complex H conreyLiHalfStrip Complex]
    (hkernel : exact source-kernel alignment)
    (hanalytic : every H element is analytic on the half-strip) :
    closure (span Complex
      {RKHS.kerFun H (upperEmbedding w) 1 | w : UpperHalfPlane}) = univ

theorem exists_conreyLiCayley_halfStrip_extension
    (H : Type*) [source Hardy-RKHS hypotheses]
    (P : H ->L[Complex] H)
    (hPnorm : ‖P‖ <= 1)
    (hPker : for every upper center, P maps its kernel by conj(B)) :
    exists Bext : conreyLiHalfStrip -> Complex,
      AnalyticOnNhd Complex Bext univ /\
      (forall w : UpperHalfPlane, Bext (upperEmbedding w) = B w) /\
      forall z, ‖Bext z‖ <= 1
```

`FULL_SUCCESS` additionally constructs the concrete source Hardy RKHS and `P` from the positive
kernel produced by the preceding campaign. A theorem that merely assumes the extension or its
norm bound is not success.

## Success criteria

`FULL_SUCCESS` requires:

1. exact half-strip and upper embedding;
2. exact source kernel and its Hermitian/diagonal identities;
3. the source analytic Hardy RKHS realization;
4. density of upper kernel centers in that larger space;
5. a well-defined contraction on the dense kernel span from source positive definiteness;
6. continuous extension and adjoint;
7. analytic continuation of the actual upper Cayley transform;
8. norm at most one everywhere in the half-strip;
9. exact TargetChecks, selected standard-only axiom prints, forbidden scans,
   warning-as-error compiles, `git diff --check`, and a full build.

`MEANINGFUL_PARTIAL` requires items 1--2, restricted-center density under an explicit analytic
RKHS interface, and items 6--8 under an explicit contractive kernel-multiplier premise. It must
state the first unavailable theorem in items 3--5 exactly. Pure domain or denominator algebra is
not a meaningful partial.

## Falsification and controls

The attack must stop or narrow if:

- the printed positive kernel does not yield the source contraction inequality;
- the restricted upper centers are not dense without an additional Hardy uniqueness premise;
- the source multiplier is not well-defined on finite kernel combinations;
- Mathlib's inner-product convention changes `B` to `conj(B)` at the adjoint step;
- the fixed-center continuation denominator can vanish in the half-strip;
- the source proves only a local or almost-everywhere bound rather than pointwise `|B|<=1`;
- an attempted theorem promotes an arbitrary bounded upper function to the half-strip.

The mandatory negative control is that an arbitrary bounded analytic function on the upper
half-plane has no specified continuation across its boundary. The Hardy multiplier and adjoint
structure may not be erased from the statement.

## Known obstacles and available infrastructure

- `ConreyLiRKHSShift.lean` supplies the actual upper Cayley transform, the finite positive
  shifted kernel, and its upper-half-plane norm bound.
- Mathlib supplies generic scalar RKHS kernel vectors, density of all kernel centers, continuous
  operator adjoints, and norm-controlled extension APIs from dense domains.
- Mathlib does not supply a named Hardy space on the shifted half-plane.
- The concrete source Hardy realization, restricted-center density, and positive-kernel
  multiplier construction therefore require new formal infrastructure.

## Assumption and implication frontier

Before and after preregistration:

- the actual `F(W)` space and positive shift for `W=1/xi(1-i*z)` are not constructed;
- no actual-xi half-strip nonvanishing result is known;
- the Conrey--Li phase obstruction remains conditional on its value-distribution inputs;
- H8 and RH remain open.

Success closes a historical functional-analytic source inference. Unless an unstated premise is
found, `rh_frontier_delta=0`.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1; no serving token budget is exposed.
- `compaction_state`: resumed from a generated summary during the parent H12 campaign; current
  governance, census, Targets, attempts, hard-gap DAG, the preceding H8 module, and the fixed
  primary source were rechecked.
- `global_goal`: active.
- `protected_files`: the six inherited user/exposure files remain untouched and unstaged.

## Publication gate

Commit and push this docs-only preregistration first. Public Lean Action CI must pass before
editing any `LeanLab/` proof source, target registry, exact check, or axiom-audit file.
