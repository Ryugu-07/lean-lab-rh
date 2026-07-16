# H6 de Bruijn-Newman Time-Zero Bridge Pre-Registration

Campaign: `CAMPAIGN-20260717-H6-H0-XI-BRIDGE-01`

Mode: `LITERATURE`

Status: `PREREGISTERED`

## Exact source endpoint

For `n >= 1` and real `u`, define

`phi_n(u) = (2*pi^2*n^4*exp(9*u) - 3*pi*n^2*exp(5*u))
            * exp(-pi*n^2*exp(4*u))`,

`Phi(u) = sum_(n>=1) phi_n(u)`, and for real `t` and complex `z`,

`H_t(z) = integral_(0,infinity) exp(t*u^2) * Phi(u) * cos(z*u) du`.

The indivisible mathematical endpoint is

`forall z : C, H_0(z) = (1/8) * riemannXi((1 + i*z)/2)`.

The `riemannXi` on the right is exactly `LeanLab.Riemann.riemannXi`; no new xi definition may be
chosen to make the theorem tautological.

## Proposed Lean surface

```lean
def deBruijnNewmanPhiTerm (n : Nat) (u : Real) : Real :=
  let m : Real := n + 1
  (2 * Real.pi ^ 2 * m ^ 4 * Real.exp (9 * u) -
      3 * Real.pi * m ^ 2 * Real.exp (5 * u)) *
    Real.exp (-Real.pi * m ^ 2 * Real.exp (4 * u))

def deBruijnNewmanPhi (u : Real) : Real :=
  sum' fun n : Nat => deBruijnNewmanPhiTerm n u

def deBruijnNewmanH (t : Real) (z : Complex) : Complex :=
  integral fun u in Set.Ioi 0 =>
    (Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : Complex) *
      Complex.cos (z * u)

theorem deBruijnNewmanH_zero (z : Complex) :
    deBruijnNewmanH 0 z =
      (1 / 8 : Complex) * riemannXi ((1 + Complex.I * z) / 2)
```

The exact binder syntax for the restricted integral may change to match mathlib, but the
mathematical definitions and constants may not.

## Success and falsification

Success requires:

1. pointwise summability of `Phi` and integrability of the `t=0` complex cosine transform;
2. source-aligned equality with the existing project xi for every complex `z`;
3. an exact `TargetChecks.lean` witness and transitive `AxiomsAudit.lean` entry;
4. no `sorry`, `admit`, `native_decide`, custom axioms, `opaque`, `unsafe`, or resource relaxation;
5. full local build and public CI.

Falsification or obstruction is recorded if the displayed normalization is inconsistent with the
project xi, or if the proof reduces to a precise absent theta-Mellin/Poisson theorem that cannot be
closed from current mathlib and pinned PNT+ sources. In that case the campaign stops as
`DEPENDENCY_GAP_IDENTIFIED`; helper lemmas alone do not count as completion.

## Source and DAG position

- Primary modern source: D. H. J. Polymath,
  [arXiv:1904.12438](https://arxiv.org/abs/1904.12438), definition of `H_t` and the displayed
  `H_0` relation.
- Canonical predecessors: de Bruijn and Newman, as mapped in the H6 route card.
- `node_id`: `H6-B`
- `relation_to_RH`: source-aligned bridge; at `t=0`, real-rootedness of `H_0` is equivalent to RH.
- `assumption_frontier_before`: exact project xi is compiled; the de Bruijn-Newman family and its
  theta integral are absent.
- `hard_gap_before`: `Lambda <= 0`, W2/G7, M2/G3, and RH are open.
- `expected_rh_frontier_delta`: 0
- `expected_route_infrastructure_delta`: 1 only if the complete displayed identity compiles.
- `expected_engineering_delta`: not promoted to mathematical progress.

## Known obstacles and attack order

The local source inventory found no existing theorem expressing project xi or completed zeta as
this Fourier-cosine integral. The fixed likely obstacle is the Mellin transform of the Jacobi
theta tail plus two differentiations and the logarithmic change of variables.

Attempt order:

1. prove a reusable super-exponential majorant for `phi_n(u)` and justify the `n`-sum;
2. rewrite `Phi` through derivatives of the one-variable Jacobi theta series;
3. derive the completed-zeta theta-Mellin integral from existing Jacobi functional equations and
   Poisson summation;
4. integrate by parts/change variables to obtain the exact cosine transform and constants;
5. align with `riemannXi_eq_complex_riemannXi` and audit the endpoint.

Do not open a separate campaign for each helper. If Step 3 cannot be completed after bounded source
and theorem search, record that exact theorem as the dependency gap and return to route selection.
