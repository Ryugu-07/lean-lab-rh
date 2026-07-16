# H10 Finite Power-Sum Spectral Rigidity Pre-Registration

Campaign: `CAMPAIGN-20260717-H10-FINITE-SPECTRAL-RIGIDITY-01`

Mode: `LITERATURE`

Status: `PREREGISTERED`

## Exact indivisible endpoint

For a finite complex family `alpha`, prove both of the following without replacing the aggregate
power-sum hypothesis by termwise bounds.

1. If `R>0`, `C>=0`, and `norm(sum_i alpha_i^n)<=C*R^n` for every natural `n`, then every
   `norm(alpha_i)<=R`.
2. If `q>0`, `R=sqrt(q)`, and a permutation pairs every two entries with complex product `q`, then
   the same power-sum bound forces every `norm(alpha_i)=sqrt(q)`.

Clause 2 is the functional-equation closure of clause 1 and may not be deferred. The endpoint is
the finite spectral-rigidity step in the function-field RH proof, not the Hasse-Weil point-count
bound itself.

## Proposed Lean surface

Names may adjust to local style, but the hypotheses and conclusions may not weaken:

```lean
def finiteComplexPowerSum {ι : Type*} [Fintype ι]
    (alpha : ι -> Complex) (n : Nat) : Complex :=
  Finset.univ.sum (fun i => alpha i ^ n)

theorem norm_le_of_forall_norm_finiteComplexPowerSum_le
    {ι : Type*} [Fintype ι] (alpha : ι -> Complex)
    {R C : Real} (hR : 0 < R) (hC : 0 <= C)
    (hbound : forall n, norm (finiteComplexPowerSum alpha n) <= C * R ^ n) :
    forall i, norm (alpha i) <= R

theorem norm_eq_sqrt_of_powerSum_bound_and_reciprocal
    {ι : Type*} [Fintype ι] (alpha : ι -> Complex) (sigma : Equiv.Perm ι)
    {q C : Real} (hq : 0 < q) (hC : 0 <= C)
    (hpair : forall i, alpha (sigma i) * alpha i = (q : Complex))
    (hbound : forall n,
      norm (finiteComplexPowerSum alpha n) <= C * Real.sqrt q ^ n) :
    forall i, norm (alpha i) = Real.sqrt q
```

## Proof route and falsification boundary

For every nonzero entry, normalize its phase into `Circle`. Reuse the compiled simultaneous phase
recurrence theorem to choose arbitrarily large powers for which all nonzero phases are near `1`.
At those powers every summand has nonnegative real part and any entry of modulus greater than `R`
forces the real part of the aggregate sum to exceed `C*R^n`, contradicting the hypothesis. The
reciprocal product and the two upper bounds then force equality at `sqrt(q)`.

The campaign records `DEPENDENCY_GAP_IDENTIFIED` if the existing phase recurrence cannot be
transported to zero-containing finite families without a new compactness theorem. It records
`ENDPOINT_FALSIFIED` if an explicit finite complex family satisfies the full all-`n` aggregate
bound while containing an entry outside the radius. Results for only real spectra, only distinct
entries, only a subsequence of powers, or only the maximum modulus do not close the endpoint.

## Source and DAG position

- Primary source: Bombieri, Bourbaki 430 (1973), especially the point-count-to-RH transition.
- Modern exact cross-check: Kedlaya, *Two approaches to RH for curves*, Lemma 5.1.4.
- `node_id`: `H10-B`
- `relation_to_RH`: finite-spectrum analogue and bridge; no implication to number-field RH without
  a finite trace model or a uniform infinite-tail theorem.
- `assumption_frontier_before`: finite simultaneous phase recurrence is public and Lean-checked;
  no generic finite power-sum spectral-radius theorem exists in the pinned project/mathlib tree.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open.
- `expected_hard_gap_delta`: 0.
- `expected_route_infrastructure_delta`: 1 only if both clauses compile.

## Route selection

The selection compared direct H6-E/H6-Q, H6-H2, H6-X, W2/G7, M2/G3, H1-B, H2-B, and the required
H10 census card. No materially new unconditional mechanism was found in the three hard-gap routes.
H6-H2 and H6-X would continue a heavily formalized equivalence route. H10-B instead opens the
required structural route, has a primary-source exact endpoint, reuses a nontrivial compiled phase
tool, and yields a precise finite-versus-infinite transfer boundary on failure.

## Mechanical gate

Success requires a diagnostic-free module, exact Targets and TargetChecks, selected transitive
standard-only axiom prints, empty forbidden scans, a full local build, and public CI. No curve,
Frobenius, or number-field theorem may be claimed from the abstract finite-spectrum result alone.
