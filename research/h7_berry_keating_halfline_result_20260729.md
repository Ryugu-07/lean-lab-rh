# H7 Berry--Keating Naive Half-Line Result

Date: 2026-07-29

Campaign: `FALSIFICATION-20260729-H7-BERRY-KEATING-HALFLINE-01`

Node: `H7-BERRY-KEATING-NAIVE-HALFLINE-01`

Classification: `FULL_SUCCESS / LOCAL_AUDIT_GREEN`

## Compiled result

The 93-line module `LeanLab/Riemann/BerryKeatingHalfLine.lean` defines

```text
s_E = -1/2 + i E
psi_E(x) = x^s_E
H_BK(f)(x) = -i (x f'(x) + f(x)/2)
```

with `E` and `x` real. Lean proves, for every real `E`:

1. `s_E` is nonzero and has real part `-1/2`;
2. for every `x>0`,
   `psi_E'(x)=s_E*x^(s_E-1)`;
3. for every `x>0`,
   `H_BK(psi_E)(x)=E*psi_E(x)`;
4. for every `x>0`,
   `|psi_E(x)|^2=x^-1`;
5. `psi_E` is not in `L^2((0,+infinity),dx)`.

The aggregate theorem is:

```text
berryKeatingHalfLine_endpoint
```

and Target `H7.berry-keating.naive-halfline-mode-obstruction` is registered as proven.

## Proof audit

- `berryKeatingFormal_mode_eq` uses Mathlib's real derivative of complex powers and performs
  the `x*x^-1` and `i^2=-1` cancellations explicitly.
- `norm_berryKeatingMode_sq` reduces the complex-power norm to the real power with exponent
  `-1/2`, squares it, and obtains `x^-1`.
- `not_memLp_two_berryKeatingMode` converts `MemLp` at exponent `2` into integrability of the
  squared norm for Lebesgue measure restricted to `Set.Ioi 0`; the exact norm law would make
  `x^-1` integrable there, contradicting Mathlib's improper-integral theorem.
- The production forbidden scan for `sorry`, `admit`, `native_decide`, custom `axiom`,
  `opaque`, and `unsafe` is empty.
- Five exact TargetChecks compile.
- Five selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`.
- The production module compiles with `-DwarningAsError=true`.
- Full build passes `8791/8791`.

## What the result changes

The obstruction is energy-independent. The imaginary part `iE` changes only the phase of the
mode; every real energy has the same squared norm `1/x`. The naive positive-half-line model
therefore cannot be repaired by selecting special energy values alone.

This identifies the first missing object in the original scaling-Hamiltonian route: a
confinement, quotient, boundary, or absorption mechanism that changes the spectral type while
preserving the arithmetic zero count. The project had not previously separated this
Berry--Keating boundary from its distinct finite-prime Weil ground-state work.

## Strict boundary

This result does not:

- prove that every generalized solution is proportional to `psi_E`;
- define an unbounded operator domain or prove self-adjointness;
- prove Endres--Steiner's full pure-continuity theorem;
- formalize compact quantum graphs or their Weyl no-go theorem;
- rule out energy-dependent cutoffs, noncompact arithmetic quotients, regularized traces, or
  Connes' absorption spectrum;
- construct a Hilbert--Polya operator, prove H7, or prove RH.

Accordingly:

- `historical_subroute_coverage_delta=1`;
- `obstruction_map_delta=1`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Successor question

The next H7 omission audit should compare named primary-source repairs against both established
failure boundaries:

```text
half-line:
  generalized modes are not L2 and the spectrum is continuous;

fixed compact graph:
  discrete spectrum exists but has the wrong Weyl growth;

required repair:
  global arithmetic confinement or absorption with multiplicity and T log T counting.
```

Connes' semilocal trace framework is the leading historical successor, but it must be selected
afresh against other families after this campaign is publicly closed.

