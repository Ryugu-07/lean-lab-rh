# H9 Conrey Rationality Definition Alignment

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-H9-CONREY-RATIONALITY-GAP-01`

Primary source: Brian Conrey, *Character sums and the Riemann Hypothesis*, Acta Arithmetica 214
(2024), 327-342, DOI `10.4064/aa230530-13-11`.

## Item-by-item alignment

| Source object or step | Lean object | Alignment and boundary |
| --- | --- | --- |
| `chi_q(n)` on a fixed prefix | `chi : Nat -> Int` | The finite algebra uses only integer values. No quadratic-character law is assumed. |
| `m=floor(y)` and `1<=n<=m` | `Finset.Icc 1 m` | The floor is external to the fixed-prefix theorem; applications select the corresponding natural `m`. |
| `A_m=sum_{n<=m} chi_q(n)` | `conreyPrefixMass chi m` | Exact integer finite sum over the aligned prefix. |
| `B_m=sum_{n<=m} n*chi_q(n)` | `conreyPrefixMoment chi m` | Exact integer first moment over the same prefix. |
| `S_q(y)=sum chi_q(n)*(1-n/y)` | `conreyWeightedPrefix chi m y` | Exact real-valued weighted sum on a fixed prefix. The Lean identity also holds at `y=0` under totalized division; the source application has `y>0`. |
| `S_q(y)=A_m-B_m/y` | `conreyWeightedPrefix_eq_mass_sub_moment_div` | Unconditional finite identity; no analytic or numerical premise. |
| `B_m=0` gives a flat prefix | `conreyWeightedPrefix_eq_mass_of_moment_eq_zero` | Proves constancy in every real scale parameter for the fixed index set. It does not prove an actual character prefix has zero moment. |
| `A-B/(q*x)=H` | hypothesis of `conreyAffineFraction_eq_dichotomy` | This is the exact algebraic equation used after the source reduction with scale `y=q*x`. |
| source rationality conclusion | `conreyAffineFraction_eq_rat_or_flat` | Rationality is certified only after separating the flat branch `B=0,A=H`. |
| omitted generic inference | `conreyAffineRationalityInference_counterexample` | Rational parameters and `x=sqrt(2)` satisfy the flat branch. This falsifies the generic inference, not the actual quadratic-character proposition. |

## Non-alignment boundaries

- The module does not define the Kronecker symbol or prove that its values instantiate `chi`.
- It does not formalize the positive prefactor relating `f_q(x)` to
  `S_q(q/2)-S_q(q*x)`.
- It neither constructs nor assumes a squarefree `q congruent to 3 mod 8` with a flat prefix.
- Therefore Proposition 1 remains `SOURCE_PROOF_GAP_CANDIDATE`, not `FALSIFIED`.
