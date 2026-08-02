# H12 Height-Ten Top Endpoint Transport Evidence

Date: 2026-08-02

Implementation commit: `38105ab4fffb2b99dd9ebe1dd13e02ba22d296e4`

Public Lean Action run: `30734001479`

Build job: `91459212576`

Result: passed in `3m12s`.

## Frozen Lean blobs

- `LeanLab.lean`: `4c26c10be069288c31f802b206ead1a526e2a9e3`
- `LeanLab/Riemann/LevinsonMontgomeryHeightTenTopTransport.lean`:
  `d725b89a2d22665805a150f9dac7cfc67b5d7be4`
- `LeanLab/Riemann/Targets.lean`: `60fb27bb72575e14abeb7d7404a136956157e23e`
- `LeanLab/Riemann/TargetChecks.lean`: `726f0e900fea0ecd25c42872c3eeb8be05417494`
- `LeanLab/Riemann/AxiomsAudit.lean`: `2c810778017de7b8ffbacf2074c3a365a2a34486`

These blobs contain the project import, the phase-preserving finite second-derivative evaluator,
the Cauchy error bridge, the actual endpoint theorem, exact target registration, exact statement
witnesses, and selected axiom prints used by the passing public run.

## Immutable verification

Pending a docs-only evidence commit and public Lean Action run.

## Compiled result

Lean proves an explicit formula for the second derivative of the second-corrected
Euler--Maclaurin center, encloses its thirty squared-log terms at `1/2-10i`, and verifies the
rational center norm is below `1/4` with explicit-formula error at most `1/1000000`. The complete
radius-`1/4` circle has first-derivative remainder at most `1/10`; Cauchy's estimate gives
actual-to-finite second-derivative error at most `2/5`. Consequently,

```lean
theorem norm_deriv_deriv_riemannZeta_heightTenReflectedEndpoint_lt :
    ‖deriv (deriv riemannZeta) heightTenReflectedEndpoint‖ < (33 / 50 : ℝ)
```

## Axiom and claim boundary

The six selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The
production module contains no forbidden placeholder, custom axiom, unsafe declaration, or
relaxed resource option.

This is a one-point actual-curvature certificate. It does not prove a uniform second-derivative
bound on the reflected half-segment, a new positive-width top interval, the complete horizontal,
the height-ten certificate, H12, or RH. The complete-boundary campaign and global RH Goal remain
active.
