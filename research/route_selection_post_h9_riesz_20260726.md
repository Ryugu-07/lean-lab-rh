# Route Selection after H9 Riesz Mellin Boundary

Date: 2026-07-26

Status: `RERANK_COMPLETE / H1_HARDY_CRITICAL_LINE_SIGN_SELECTED`

## Closed parent

Campaign `LITERATURE-20260726-H9-RIESZ-MELLIN-BOUNDARY-01` is publicly closed at
final-ledger commit `18110c4a553e710fcb67fbe5617562fc573eca45`, Lean Action run
`30212583915`, build job `89821224995`, in `1m31s`.

Its frozen Lean source proves the actual `k=2` Mobius-exponential kernel, the ordinary
Mellin identity on `-1/2<Re(s)<0`, divergence at the source's displayed point `s=1/2`,
and the explicit decay-conditional Mellin extension. It does not prove the
RH-equivalent Riesz decay or exclude any zeta zero.

## Fresh cross-family comparison

The comparison is historical-coverage first. A route is not ranked down because its endpoint
is open; it is ranked by whether the current audit exposes a fixed source hinge that Lean can
decide without importing that endpoint.

| candidate | live edge | omission value | decision |
| --- | --- | --- | --- |
| H1 Hardy 1914 | Build the real critical-line xi coordinate and the exact sign-change-to-zero bridge before reconstructing Hardy's transform argument. | The repository cites Hardy's theorem but has no production theorem for this classical entry mechanism. The existing xi functional equation and analyticity make the first source hinge exact and falsifiable. | **Select.** |
| H1 mollifier | Prove Farmer's arbitrary-length mollified moment estimate. | The complete Bettin--Gonek consumer is compiled; no new source premise for the moment estimate appeared in this rerank. | Retain open. |
| H2 density/moments | Exclude an actual-zeta bow or one sparse off-line orbit. | Direct RH value, but the audited sources do not yet supply the required arithmetic localizer. | Retain open. |
| H7 spectral/trace | Prove simple-even finite ground states and identify their limit with the true xi ground state. | The finite Herglotz, prime, pole, and archimedean interfaces are already deeply formalized; no new limit premise appeared. | Retain open. |
| H9 Farey--Franel--Landau | Reconstruct ordered Farey discrepancy and its exact Mobius bridge. | A genuinely missing classical branch with high historical value. Its first exact statement requires ordered rational enumeration and normalization infrastructure not yet present. | Queue after the bounded H1 entry node. |
| H9 Riesz successor | Prove RH-strength decay or continue the product identity into a zero-detecting strip. | Directly relevant, but immediate continuation would remain in the just-used branch. | Rotate away. |
| H10 function field | Build the actual Riemann--Roch dimension and curve-polar-order layer. | The finite Frobenius and polar-injectivity consumers are compiled; the next source hinge needs the geometric object itself. | Retain open. |
| H11 pair correlation | Turn limiting pair statistics into an absolute sparse-exception eliminator. | The generic sparse countermodel is compiled, and no new arithmetic amplifier was identified. | Retain open. |
| H12 Speiser | Complete the global argument-principle count after the local boundary and indentation lemmas. | Source-exact and still open, but already extensively reconstructed. | Retain open. |

## Selected historical hinge

Hardy's 1914 theorem proves infinitely many zeta zeros on the critical line. The first full
account was incorporated into Hardy--Littlewood's later work. Before formalizing its Fourier or
integral estimates, the project needs a normalization-safe real coordinate whose zeros are
definitionally tied to the project xi function.

For real `t`, set

```text
criticalXi(t) = riemannXi(1/2 + i*t)
hardyXi(t)    = Re(criticalXi(t)).
```

The functional equation `xi(1-s)=xi(s)` and conjugation symmetry imply that
`criticalXi(t)` is real. Hence `criticalXi(t)=0` exactly when `hardyXi(t)=0`.
Continuity then turns opposite weak endpoint signs into a genuine nontrivial xi zero in the
closed interval. Functional symmetry also makes `hardyXi` even.

This node does not prove that sign changes occur, let alone that they occur in arbitrarily high
intervals. It fixes the consumer that every later Hardy integral or transform estimate must
feed. That separation is the omission audit: any proposed reconstruction must produce actual
endpoint signs rather than silently treat real-valuedness as oscillation.

## Source anchors

- G. H. Hardy, *Sur les zeros de la fonction zeta(s) de Riemann*, Comptes rendus de
  l'Academie des sciences 158 (1914), 1012--1014:
  `https://gallica.bnf.fr/ark:/12148/bpt6k3111d.image.f1014.langEN`.
- G. H. Hardy and J. E. Littlewood, *Contributions to the theory of the Riemann
  zeta-function and the theory of the distribution of primes*, Acta Mathematica 41,
  119--196, DOI `10.1007/BF02422942`:
  `https://doi.org/10.1007/BF02422942`.

## Fixed next campaign

- `campaign`: `LITERATURE-20260726-H1-HARDY-CRITICAL-LINE-SIGN-01`.
- `node`: `H1-HARDY-CRITICAL-LINE-REAL-SIGN-BRIDGE-01`.
- `mode`: `LITERATURE`.
- `positive_endpoint`: actual project-xi critical-line coordinate, real-valuedness, evenness,
  continuity, exact xi-zero equivalence, and both orientations of the interval sign bridge.
- `aggregate_endpoint`: from an increasing sequence with alternating weak signs, produce one
  actual `IsNontrivialZero` witness on the critical line in every registered interval.
- `negative_controls`: a complex-valued placeholder, an assumed real-valuedness premise, an
  abstract continuous function detached from xi, endpoint signs without an interval witness,
  or a theorem that assumes the desired xi zero does not satisfy the campaign.
- `strict_boundary`: proving arbitrarily many sign changes, Hardy's theta/Fourier transform,
  the Hardy--Littlewood lower count, a positive critical-line proportion, H1, and RH remain open.
- `production_gate`: no Lean proof-source edit before this docs-only preregistration passes
  public Lean Action CI.
