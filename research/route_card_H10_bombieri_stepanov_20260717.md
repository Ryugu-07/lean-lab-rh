# Route Card H10: Bombieri-Stepanov and Function-Field RH

Date: 2026-07-17

Status: `H10_B_PUBLICLY_CLOSED`

## Exact endpoint

For a smooth projective geometrically connected curve `X/F_q` of genus `g`, write

`Z(X,T) = P(T) / ((1-T)(1-q*T))`

and factor `P(T)=product_i (1-alpha_i*T)`. Then

`#X(F_(q^n)) = q^n + 1 - sum_i alpha_i^n`.

The function-field RH is `|alpha_i|=sqrt(q)` for every `i`. Thus a square-root point-count bound
for all extensions is an aggregate power-sum bound, not a termwise eigenvalue estimate. The final
spectral step must show that persistent cancellation cannot hide an eigenvalue of larger modulus;
the functional equation then turns the upper bound into equality through reciprocal pairing.

## Primary sources and proof mechanism

- S. A. Stepanov, *On the number of points of a hyperelliptic curve over a finite prime field*,
  Math. USSR-Izv. 3 (1969), 1103-1114, introduced the auxiliary-function/high-multiplicity method
  in special cases.
- Enrico Bombieri,
  [*Counting points on curves over finite fields (d'apres S. A. Stepanov)*](https://www.numdam.org/item/SB_1972-1973__15__234_0.pdf),
  Seminaire Bourbaki 430 (1973), gives the general Riemann-Roch/Frobenius presentation used here.
- Kiran Kedlaya,
  [*Two approaches to RH for curves*](https://kskedlaya.org/weil-cohom/chapter-5.html), gives a
  modern statement-level cross-check, including the finite power-sum rigidity lemma.

The Bombieri-Stepanov chain is:

1. Riemann-Roch supplies large finite-dimensional spaces of rational functions with one controlled
   pole.
2. Frobenius turns selected coefficients into high powers without proportional growth of the pole
   budget.
3. A dimension count produces a nonzero auxiliary function in the kernel of a Frobenius-twisted
   linear map.
4. That function vanishes to high multiplicity at every rational point but has controlled total
   pole degree, giving an upper point-count bound.
5. A Galois closure and Frobenius-substitution count recover the required lower bound.
6. Applying the bounds over all suitable extensions controls every aggregate power sum; finite
   spectral rigidity and the functional equation put every `alpha_i` on `|z|=sqrt(q)`.

Bombieri's displayed upper-bound stage assumes `q` is an even power and sufficiently large relative
to `g`, and obtains `#X(F_q) <= q+1+(2g+1)*sqrt(q)`. Base extension and the lower-bound argument
remove those local conveniences from the final RH conclusion.

## Exact number-field transfer gap

The reusable mechanism is not merely "positivity". It uses a finite Frobenius spectrum, point
counts over every finite extension, characteristic-`p` high powers, finite-dimensional
Riemann-Roch spaces, and a functional-equation reciprocal pairing. For the Riemann zeta function:

- the nontrivial zero divisor is infinite rather than a fixed finite spectrum;
- the explicit formula has archimedean and prime-distribution terms rather than finite rational
  point counts;
- there is no known finite-dimensional Frobenius operator whose traces are those prime terms;
- a finite-height power-sum bound does not exclude one off-line zero without a uniform tail
  mechanism.

Consequently the function-field theorem is an analogy and a source of structural lemmas, not a
premise for number-field RH.

## Formalization fit

Mathlib contains finite fields, Frobenius, schemes, function fields, divisors, projective spectra,
and substantial algebraic-geometry infrastructure, but the fixed tree has no source-ready
Riemann-Roch theorem for smooth projective curves, curve zeta function, Frobenius trace formula,
or Hasse-Weil bound. The project does contain a stronger immediately relevant analytic tool:
`exists_even_gt_forall_circle_pow_dist_one_lt`, which simultaneously returns every phase in a
finite complex family near `1` at arbitrarily large powers.

## Candidate H10-B: finite spectral rigidity

**Exact proposition.** Let `alpha_i` be a finite complex family. If `R>0`, `C>=0`, and

`norm(sum_i alpha_i^n) <= C*R^n`

for every natural `n`, then `norm(alpha_i)<=R` for every `i`. If additionally `q>0`,
`R=sqrt(q)`, and a permutation pairs the family with `alpha_i*alpha_(sigma i)=q`, then every
`norm(alpha_i)=sqrt(q)`.

**DAG and strength.** This formalizes the final spectral implication in the function-field proof.
It is neither number-field RH nor an implication toward RH without a finite-spectrum/trace bridge.

**Adversarial tests.** Repeated eigenvalues, zero entries, exact phase cancellation such as
`{a,-a}`, non-involutive permutations, `R=0`, negative `C`, and bounds on only a subsequence of
powers must not be silently accepted.

**Implementation result.** `FinitePowerSumRigidity.lean` proves the full proposition. The proof
normalizes every nonzero entry to `Circle`, applies simultaneous finite phase recurrence at an
arbitrarily large power, and forces every term into the nonnegative real half-plane. If one entry
has norm above `R`, its positive real contribution alone eventually exceeds `C*R^n`, contradicting
the aggregate bound. Product norms and the paired upper bounds then force the exact square-root
circle.

**Verdict:** `COMPLETE` as `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`.

## Candidate H10-Q: auxiliary zero-versus-pole lemma

**Exact proposition.** On a complete nonsingular curve, a nonzero rational function with pole
divisor degree at most `P` and zero multiplicity at least `m` on every point of a finite set `S`
satisfies `m*|S|<=P`.

**DAG and strength.** This is the divisor-counting core before the Frobenius/Riemann-Roch
construction. It is known infrastructure and has no number-field RH implication by itself.

**Adversarial tests.** Projective completeness, identically zero functions, poles inside `S`,
inseparability, and multiplicity conventions.

**Verdict:** `FORMALIZE_LATER`; current curve-divisor prerequisites are much larger than H10-B.

## Candidate H10-X: uniform finite-spectrum truncation for xi

**Exact proposed bridge.** Construct finite symmetric xi-zero spectra whose power sums have a
uniform square-root-scale bound and whose omitted tails are uniformly smaller than every possible
off-line dominant orbit.

**Relation to RH.** With exact reciprocal symmetry and a valid tail bound this would exclude every
off-line zero and hence imply RH. The tail clause carries essentially the unresolved number-field
content.

**Adversarial tests.** One isolated off-line orbit, cutoff-boundary multiplicity, phase
cancellation, dependence of constants on the cutoff, and nonuniform limits.

**Verdict:** `UNVERIFIED_STRONG_CONJECTURE_SHAPE`; not admitted to the conjecture pool or as a
premise because no noncircular tail mechanism is known.

## Recommendation

H10-B is publicly complete as the exact finite spectral rigidity interface, and its proof records
where finiteness enters. Return to fresh route selection. Do not begin a full
algebraic-geometry development until route selection finds a number-field-relevant consumer for
the Frobenius/Riemann-Roch layers.
