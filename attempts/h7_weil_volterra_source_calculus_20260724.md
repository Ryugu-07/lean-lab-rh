# H7 Weil Volterra Source Calculus Campaign

Date: 2026-07-24

Campaign: `LITERATURE-20260724-H7-WEIL-FINITE-DICTIONARY-01`

Selected node: `H7-WEIL-VOLTERRA-SOURCE-CALCULUS-01`

Status: `FROZEN_IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_PENDING`

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `ROUTE_SELECTION` | Compared H7 finite dictionary transport, H1 inverse Mellin/convolution, H7 total assembly, H2/H11 sparse-exception amplification, and D7 function-field transfer. | H7 has actual source matrices but lacks the exact vector-to-test transport that makes their quadratic values zeta-zero tests. This is more discriminating than a definition-only three-block sum and alternates away from three consecutive H1 source campaigns. | Select the Volterra source-calculus layer. |
| `SOURCE_RECONSTRUCTION` | Read the original TeX for arXiv:2607.02828, Lemma 2.3 and Theorem 2.5. | The fixed mechanism is a single-frequency divided-difference identity with a nonoptional diagonal branch, followed by finite von Mangoldt superposition and the coordinate `xi=log(q)/(2*pi)`. | Freeze these objects and normalization guards. |
| `API_AUDIT` | Inspected centered frequencies, reflection parity, the literal prime atom/source matrices, finite matrix quadratic APIs, interval integrals, and complex exponential integral support. | Existing infrastructure supplies both sides of the source-calculus identity; no compiled `T_u`, `K_u`, or Fourier-weight transport currently exists. | Publish preregistration before proof-source editing. |
| `PREREGISTRATION` | Fixed seven items from the literal trigonometric polynomial through the actual prime explicit-formula side. | Production Lean remains gated on public preregistration CI. | Commit, push, and require public CI. |
| `PRODUCTION_GATE` | Published preregistration commit `b98925631116a204240b210a4f181438413700c2`. | Public Lean Action run `30070385819`, build job `89409815046`, passed in `1m41s`. | Open production proof-source editing. |
| `PAIR_INTEGRAL` | Expanded the literal Volterra integrand into centered exponential pairs and evaluated `i=j` and `i!=j` separately. | The diagonal is exactly `2*omega*exp(2*pi*i*m_i*omega)`; the off-diagonal denominator is `pi*(m_i-m_j)*I`. No factor or orientation mismatch. | Sum the pair identity into the matrix quadratic. |
| `REFLECTION_REALITY` | Reindexed by `Fin.rev`, used centered-frequency negation, and commuted `Complex.imCLM` through the actual interval integral. | Reflection-even real coefficients make both `T_u` and `K_u` real-valued; the source's complex equality follows rather than being assumed. | Instantiate the generic sine source. |
| `SOURCE_QUADRATIC` | Matched diagonal derivatives and off-diagonal sine divided differences, then proved generic and finite-superposition quadratic identities. | `u dot (Q_(alpha,omega)*u)=alpha*re(K_u(omega))`, with the literal complex equality for even `u`. | Reuse the actual project prime atoms. |
| `PRIME_INSTANTIATION` | Identified `weilFinitePrimeAtomMatrix` with the generic source at the existing coefficient and frequency, then summed over `2<=q<=C`. | The coefficient's existing minus sign and every normalization agree with the source. | Audit the Fourier cutoff coordinate. |
| `FOURIER_CUTOFF` | Defined `Delta=log(C)/(2*pi)` and the piecewise induced Fourier weight. | Evenness, outside-band vanishing, `xi_q` membership, `1-xi_q/Delta=omega_q`, and the literal finite prime-side rewrite compile. | Register and run all local gates. |
| `LOCAL_INTERFACE` | Added the seven-part certificate, proven Target, exact TargetCheck, selected axiom prints, and definition alignment. | Source module, Targets, TargetChecks, and AxiomsAudit compile. Full build and scans remain. | Run freeze gates before publication. |
| `LOCAL_GATES` | Ran warning-as-error source and interface checks, selected transitive axiom audit, forbidden scan, `git diff --check`, and full build. | All checks pass; every selected declaration uses only `propext`, `Classical.choice`, and `Quot.sound`; the full build completes `8758/8758`. | Publish and freeze the implementation commit. |
| `FROZEN_IMPLEMENTATION` | Published commit `e5f011dbbf9f7c40a802ab88f9a91aa6aea3f370`. | Public Lean Action run `30072543069`, build job `89416248542`, passed in `2m6s`; proof source is frozen. | Publish these coordinates in a docs-only immutable-evidence commit. |

## Claim boundary

The campaign closes at the actual finite Volterra/prime transport. It does not assume or prove
the full zero-sum dictionary, the remaining source transports, an inverse/density theorem, any
total spectral sign, H7, or RH.
