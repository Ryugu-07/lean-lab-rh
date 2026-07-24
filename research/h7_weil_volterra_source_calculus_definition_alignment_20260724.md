# H7 Weil Volterra Source Calculus Definition Alignment

Date: 2026-07-24

Campaign: `LITERATURE-20260724-H7-WEIL-FINITE-DICTIONARY-01`

Primary source: Groskin, arXiv:2607.02828, Lemma 2.3 and the prime part of Theorem 2.5.

Lean source: `LeanLab/Riemann/WeilFiniteDictionarySourceCalculus.lean`

## Source-to-Lean map

| source object | Lean declaration | alignment |
| --- | --- | --- |
| centered index `m in {-N,...,N}` | `weilFiniteCenteredFrequency N i` | `i.rev` is proved to represent `-m` |
| `exp(2*pi*i*m*t)` | `weilFiniteTrigMonomial N i t` | complex exponential has exactly the source phase |
| `T_u(t)=sum_m u_m exp(2*pi*i*m*t)` | `weilFiniteTrigPolynomial N u t` | finite sum over all centered indices |
| `K_u(omega)=2*integral_0^omega T_u(t)T_u(omega-t)dt` | `weilFiniteVolterraKernel N u omega` | literal oriented interval integral and factor `2` |
| `psi_(alpha,omega)(x)=alpha/pi*sin(2*pi*omega*x)` | `weilFiniteSineAtomSource alpha omega x` | exact source normalization |
| `psi'_(alpha,omega)(x)` | `weilFiniteSineAtomSourceDerivative alpha omega x` | proved derivative `2*alpha*omega*cos(2*pi*omega*x)` |
| source divided difference | `weilFiniteSineAtomMatrix N alpha omega` | derivative on the diagonal, quotient off the diagonal |
| `alpha_q=-Lambda(q)/sqrt(q)` | `weilPrimeAtomCoefficient q` | reused from the literal project prime source |
| `omega_q=1-log(q)/log(C)` | `weilPrimeFrequency C q` | reused without sign or orientation change |
| `Delta=log(C)/(2*pi)` | `weilFiniteDictionaryBandwidth C` | exact source half-bandwidth |
| induced `hat(g_u)` | `weilFiniteDictionaryFourierWeight C N u xi` | `pi*re(K_u(1-abs(xi)/Delta))` inside the band and zero outside |

## Normalization checks

- The diagonal pair integral is retained separately:
  `K_(i,i)(omega)=2*omega*exp(2*pi*i*m_i*omega)`.
- The off-diagonal denominator is
  `pi*(m_i-m_j)*I`; taking its real part produces the source sine divided difference.
- The generic matrix quadratic is
  `u dot (Q_(alpha,omega)*u)=alpha*re(K_u(omega))`.
- Reflection-even real coefficients pair `m` with `-m`. Lean derives that both `T_u` and `K_u`
  have zero imaginary part, and therefore proves the source's complex-valued equality without
  assuming real-valuedness.
- The actual project prime coefficient already contains the minus sign. No second minus sign is
  inserted.
- For `2<=q<=C`, `xi_q=log(q)/(2*pi)` lies inside the source band and Lean proves
  `1-xi_q/Delta=omega_q`.
- Substitution in the actual finite source gives the literal finite Fourier prime side with no
  residual factor `2`, `pi`, or sign discrepancy.

## Result and boundary

`weilFiniteDictionarySourceCalculus_endpoint` packages all seven preregistered source-calculus
items. The alignment probe found no source mismatch.

The endpoint does not establish admissibility or decay of the induced test in the project's
explicit-formula class. It also does not provide the zero, pole, or archimedean transports, a
cutoff-free limit, inverse/density, a sign for the total matrix, H7, or RH.

## Public freeze

Frozen implementation commit `e5f011dbbf9f7c40a802ab88f9a91aa6aea3f370` passed public Lean
Action run `30072543069`, build job `89416248542`, in `2m6s`.
