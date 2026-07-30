# Route Selection after H11 PCC Slow-Window Diagonal

Date: 2026-07-30

Status: `H0_REVERSE_ZERO_EXCLUSION_IMPLEMENTATION_PUBLIC_GREEN / EVIDENCE_PENDING`

## Governing interpretation

Historical coverage is omission search, not a checklist. A route is not exhausted when its
name, first lemma, or a convenient finite analogue has been formalized. The comparison asks:

1. how the historical argument came closest to RH;
2. which premise, continuation step, or limiting passage stopped it;
3. whether that premise can be weakened or repaired by another compiled route;
4. whether a discarded branch or source ambiguity has escaped scrutiny;
5. whether the exact missing inference can now be made kernel-checkable.

Original conjectures, their falsification, and direct RH proof attempts remain open at every
stage. They need not wait for the historical survey to finish. The survey controls the main
allocation of attention until the historical dependency graph is substantially reconstructed.

## Closed parent

Campaign `LITERATURE-20260730-H11-PCC-SLOW-WINDOW-DIAGONAL-01` is public-green through
immutable-evidence commit `48c192cf84996c4719e763369a1bf466773657f5`, Lean Action run
`30520586053`, build job `90799814346`, in `1m53s`.

It closes only the logical diagonal passage from fixed compact-window convergence to one
sufficiently slow moving window. Pair correlation, the source asymptotic, HMH, sparse-exception
control, H11, and RH remain open.

## Fresh cross-family comparison

Proof convenience is not a ranking field. The ranking uses historical omission value, proximity
to an actual RH implication, source precision, cross-route leverage, and whether failure will
sharpen the obstacle map.

| candidate | closest open historical edge | omission value | decision |
| --- | --- | --- | --- |
| H0 Chebyshev/von Koch | Turn `psi(N)-N=O(N^r)` into a holomorphic error Mellin continuation, a pole-removed zeta differential identity, and zero exclusion on `Re(s)>r`; then derive RH from all `r=1/2+epsilon`. | The positive Mellin entrance already compiles, but the decisive reverse implication has never been formalized. It is the exact classical bridge recorded by DLMF 25.16.4 and exposes three auditable analytic hinges. | **Select.** |
| H8 de Branges/RKHS | Construct the concrete source Hilbert space and positivity mechanism rather than an abstract RKHS implication. | High structural omission value, but the source measure, entire-function class, and positivity producer still form a broad coupled stack. | Retain open; prioritize after a bounded source reconstruction is identified. |
| H9 arithmetic successors | Repair Conrey's flat branch for all primes `q=3 mod 8`, or prove an RH-strength Riesz/Mertens estimate. | The exact flat-branch issue is real, but finite search through `q<10000` found no main-family flat prefix and supplied no general producer. Fixed-prime proofs would not close the source gap. | Retain for a source-backed uniform argument or a genuine counterexample. |
| H12 Speiser/counting | Complete the global argument-principle count and Levinson--Montgomery comparison. | Direct value is high; current blockers remain a global admissible contour and top-edge variation rather than an omitted local identity. | Retain open. |
| H1/H2 mollifier and density | Produce the missing long moment or sparse-zero exclusion input. | Direct RH value is maximal, but the recently reconstructed consumers already identify the unresolved estimates precisely. | Retain open without returning to constant optimization. |
| H7 spectral | Realize the actual number-field operator and prove trace/positivity convergence. | High conceptual value; the continuum realization and trace-class passage remain much broader than one campaign. | Retain open. |
| H10 function field transfer | Find a number-field replacement for finite Frobenius/cohomological positivity. | The analogy is mapped, but no source supplies the missing number-field object. | Retain open. |

H0 is a non-adjacent move from H11 and is not selected because its preliminary module is easy to
extend. It is selected because the project stopped immediately before the historically decisive
reverse inference. A successful campaign closes a complete conditional RH implication; a failed
campaign identifies whether the missing formal obstruction is Mellin holomorphy, analytic
continuation of the differential identity, or analytic zero-order exclusion.

## Source finding

Helge von Koch's primary paper is:

- Helge von Koch, *Ueber die Riemann'sche Primzahlfunction*, Mathematische Annalen 55
  (1902), 441--464;
- stable catalogue and full-text entry: `https://eudml.org/doc/158044`.

DLMF Section 25.16(i), equation 25.16.4, records the modern exact endpoint:

```text
RH iff psi(x) = x + O(x^(1/2+epsilon)) for every epsilon > 0.
```

Source: `https://dlmf.nist.gov/25.16#E4`.

The already compiled module `LeanLab/Riemann/ChebyshevMellin.lean` supplies the exact
von-Mangoldt coefficients, their Chebyshev partial sums, the floor-error Mellin integral, and
the ordered convergence consequence of an `O(N^r)` partial-sum bound. It does not prove that the
Mellin value is holomorphic or exclude a zeta zero.

## Fixed next campaign

- `campaign`: `LITERATURE-20260730-H0-CHEBYSHEV-REVERSE-ZERO-EXCLUSION-01`;
- `node`: `H0-VON-KOCH-REVERSE-ZERO-EXCLUSION-01`;
- `mode`: `LITERATURE / OMISSION-AUDIT / PROOF-ATTEMPT`;
- `full_endpoint`: an `O(N^r)`, `0<=r<1` Chebyshev-error hypothesis gives a holomorphic error
  continuation and excludes every nontrivial zeta zero with real part greater than `r`; the
  family of bounds for every positive epsilon implies `Mathlib.RiemannHypothesis`;
- `negative_control`: one fixed exponent `r>1/2` confines a reflection-symmetric real part to a
  band but does not force `Re(s)=1/2`;
- `strict_boundary`: no Chebyshev error estimate is proved unconditionally. The campaign proves
  a conditional reverse implication and RH only from the full source error hypothesis;
- `production_gate`: no `LeanLab/` or theorem-registration edit before the docs-only
  preregistration passes public Lean Action CI.

## Local campaign result

The preregistration gate passed at commit
`c9c561aaeeff665db804828663719ee9be0745ae`, Lean Action run `30522338862`, build job
`90805348547`, in `1m57s`.

The complete fixed endpoint now compiles locally in
`LeanLab/Riemann/ChebyshevReverseZeroExclusion.lean`. The result closes the historical reverse
inference

```text
all positive-epsilon Chebyshev error bounds -> RiemannHypothesis
```

through genuine Mellin holomorphy, a pole-removed analytic ODE, and zero-order exclusion. It
does not supply the Chebyshev error bounds. Public implementation CI and immutable evidence
remain before campaign closure.

Frozen implementation commit `247ea4c176505b9186faa51a69f5c53bbdbe80f2` passed Lean Action
run `30524180060`, build job `90811183408`, in `2m16s`. The five proof and registration blobs
are frozen while docs-only immutable evidence is published.
