# H7 Finite Dictionary Explicit Formula Result

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H7-WEIL-FINITE-DICTIONARY-EXPLICIT-FORMULA-01`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_REQUIRED`

## Result

The fixed weak-regularity Guinand--Weil endpoint compiles for every `2 <= C`, every finite band
`N`, every real coefficient vector `u`, and every contour line `c>1`. The zero side is the
absolutely convergent `tsum` over `RiemannXiDivisorZeroIndex`, so analytic multiplicity is
retained.

The literal source-coordinate theorem is

```text
sum*_{rho} g_u((rho-1/2)/i)
  = -(1/pi) * sum_{q in [2,C]}
      Lambda(q)/sqrt(q) * ghat_u(log(q)/(2*pi))
    + 2*g_u(i/2)
    + (1/(2*pi)) * integral_R h_+(r)*g_u(r) dr.
```

Lean also identifies the finite prime sum with the existing prime-source matrix quadratic.

## Main Lean Theorems

- `tendsto_dictionaryXiTopHorizontalIntegral`
- `tendsto_dictionaryXiRightVerticalIntegral`
- `tendsto_dictionaryXiPrimeIntegral`
- `tendsto_dictionaryXiPoleIntegral`
- `tendsto_dictionaryXiArchimedeanIntegral`
- `symmetrizedFiniteDictionaryXi_arithmetic_explicit_formula`
- `weilFiniteDictionaryTest_arithmetic_explicit_formula`
- `tsum_compactSymmetrizedVonMangoldtWeight_dictionary_eq_neg_pi_mul_primeQuadratic`
- `compactSymmetrizedXiArchimedeanIntegral_dictionary_eq_source`
- `weilFiniteDictionary_source_arithmetic_explicit_formula`
- `weilFiniteDictionary_primeMatrix_archimedean_zeroSum`

## Analytic Mechanism

The preregistration identified a real mismatch: the existing generic selected-height bound
`logDeriv riemannXi = O(R^4)` does not combine with the dictionary test's `O(R^-2)` horizontal
decay.

Attack A succeeds by changing the selected-height construction. Jensen's formula and the
order-one growth of `riemannXi` give a cofinal zero-count bound `O(R^(5/4))`. Finite-set
avoidance then chooses a long zero-free height, where the Hadamard logarithmic-derivative sum is
`O(R^(7/4))`. Multiplication by the test decay gives `O(R^(-1/4))`, which closes the top
horizontal limit.

On the arithmetic side, weak Fourier inversion is proved at the actual continuity and compact
support regularity. The prime sum is finite by support. Pole convergence is direct. The Gamma
term is integrable from logarithmic growth times inverse-square decay, and a holomorphic line
shift proves independence of `c>1` and alignment with the source's middle-line density.

Attack B, compact `C^6` approximation, was not needed.

## Mechanical Evidence

- direct compile of `WeilFiniteDictionaryExplicitFormula.lean`: pass, warning-free;
- source length: 3,213 lines;
- `Targets.lean`, `TargetChecks.lean`, and `AxiomsAudit.lean`: pass;
- selected transitive axioms: only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden token/declaration/resource scan: empty;
- full `lake build`: pass, `8762/8762`.

Preregistration commit `002a775afd9dbfa5d5d2006b531523b6a0e84414` passed public Lean
Action run `30185492253`, build job `89749281543`. Frozen implementation commit
`f0d76ee081c22381f6ffc208b024268b090fc35c` passed run `30187598839`, build job
`89754974406`, in `2m48s`. Docs-only immutable-evidence commit
`0a15b1d951c978ece49da9b477686cc1e61d6939` passed run `30187720024`, build job
`89755296426`, in `1m33s`; proof source remained frozen. Final-ledger CI is pending.

## Claim Boundary

This independently formalizes the source's finite-dictionary explicit formula and exact
normalization. It does not prove positivity of the resulting quadratic form, inverse/density of
the finite dictionary in the full Weil class, a limit as `C` or `N` tends to infinity,
simple-even ground states, H7, or RH.

Recorded deltas:

- `source_analytic_bridge_delta=1`;
- `historical_route_coverage_delta=1`;
- `hard_gap_delta=0` for RH;
- `rh_frontier_delta=0`.
