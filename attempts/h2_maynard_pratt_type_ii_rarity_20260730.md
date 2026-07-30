# H2 Maynard--Pratt Type-II Rarity Attempts

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-MAYNARD-PRATT-TYPE-II-RARITY-01`

Node: `H2-MAYNARD-PRATT-TYPE-II-RARITY-01`

Status: `CONDITIONAL_REDUCTION_PUBLIC_GREEN / PRODUCTION_OPEN`

## Fixed question

Can Maynard--Pratt Lemma 24 be proved for the project's actual Type-II shifted integral and
literal source mollifier, and does its required fixed-mollifier fourth moment admit a smaller
upper-bound proof than the general twisted fourth-moment asymptotics cited by the authors?

## Attempt ledger

| round | mode | observation | decision |
| --- | --- | --- | --- |
| 1 | `PARENT_CLOSURE` | H1 eta-primitive mean-square receipt `dd593af9c0a838016f4ca954221dc7408a9d662a` passed run `30500121527`, job `90737729961`, in `1m56s`. | Stop only that local H1 campaign and rerank all historical families. |
| 2 | `CROSS_FAMILY_SELECTION` | H1 source-X, H10 curve geometry, H11 sparse amplification, H12 global counting, and spectral concrete-object producers remain open. H2 alone has a newly compiled actual source dichotomy whose next named lemma is a complete rarity branch. | Select H2 Type-II rarity without treating its source description as proof. |
| 3 | `PRIMARY_SOURCE_AUDIT` | Maynard--Pratt Lemma 24 charges each Type-II zero to a local fourth moment, extracts `(log T)^3`-separated ordinates, and applies a global twisted fourth moment. Section 8's bow obstruction concerns the Type-I/clustering branch. | Freeze Lemma 24 and retain bow exclusion outside the endpoint. |
| 4 | `OMISSION_HYPOTHESIS` | The source cites arbitrary-polynomial asymptotics valid beyond length `T^(1/11-epsilon)`, but uses only an upper bound for the fixed Mobius polynomial of length `2*T^(1/100)`. | Test a short-mollifier upper-bound-only proof before reconstructing the full cited asymptotic. |
| 5 | `MULTIPLICITY_AUDIT` | A distinct-point finset would undercount repeated zeros, while the source density count is multiplicity-bearing. The project already exposes xi analytic multiplicity and compact zero finiteness. | Require a weighted count and make local multiplicity control part of full success. |
| 6 | `PREREGISTRATION` | Full success requires the actual rarity bound with both local zero-count and twisted-moment producers discharged. A conditional reduction may be meaningful partial progress but cannot close the rarity node. | Publish docs only and await public CI before editing `LeanLab/`. |
| 7 | `PUBLIC_GATE` | Docs-only preregistration commit `58a77f7ca4ee0b04dfe4f4653bdc93d8df080be5` passed Lean Action run `30500943541`, build job `90740248215`, in `2m1s`. | Open production editing at the frozen endpoint; begin with multiplicity-bearing finite counts and the exact shifted-integral change of variables. |
| 8 | `ACTUAL_SOURCE_REDUCTION` | `MaynardPrattTypeIIRarity.lean` compiles the multiplicity-bearing count, the literal critical-line mollifier--zeta value, the exact shifted-integrand norm identity, Type-II charging of the full critical mass, and the local `L1`--`L4` Holder step. | Retain the actual source objects; do not replace the remaining tail, packing, or moment producers by abstract surrogates. |
| 9 | `SOURCE_SIGN_FALSIFICATION` | Direct parametrization of `Re(s)=1/2-beta` gives `Gamma(1/2-beta+i*u)`, whereas the proof of Lemma 24 displays `Gamma(beta-1/2+i*u)`. Lean proves these arguments unequal whenever `beta>1/2`. | Record a literal source sign mismatch and test whether recurrence repairs the intended estimate before classifying the whole lemma. |
| 10 | `RECURRENCE_REPAIR` | Lean proves `(beta-1/2)*norm(Gamma(1/2-beta+i*u)) <= 2` for `1/2<beta<1`. Under the source hypothesis `beta>=sigma>=1/2+1/log T`, this yields the corrected uniform bound `norm(Gamma(1/2-beta+i*u)) <= 2*log T`, including a pointwise bound for the actual Mellin integrand. | Treat the displayed change of variables as falsified but locally repairable; the rarity exponent is not yet proved. |
| 11 | `TAIL_PRODUCER_AUDIT` | Existing compiled inputs give uniform negative-strip Gamma exponential decay, the trivial mollifier bound, and unconditional critical-line zeta growth of exponent `3/8`. No existing theorem combines them into the required uniform integral bound on `|u|>(log T)^2` as `T` and `rho` vary. | Make corrected Gamma-tail truncation the next producer; after it, resume local charge, multiplicity packing, and the fixed twisted fourth moment. |
| 12 | `CORRECTED_TAIL_MAJORANT` | `exists_norm_classicalDetectorMellinContourFactor_typeII_shift_le_pureExp` compiles a uniform corrected-contour majorant of the form `C*M*Y^(1/2-beta)*(1+|gamma|)^(3/8)*exp(-pi*|u|/4)`. `exists_maynardPrattTypeIIContourNormTailMass_le` integrates it with explicit absolute constants. | Discharge the source-scale tail at the literal radius `R=(log T)^2`; do not retain a tail-smallness premise. |
| 13 | `SOURCE_WINDOW_TRUNCATION` | `eventually_maynardPrattTypeIIContourNormTailMass_source_le_one` proves the actual source tail is eventually at most `1` for `M=floor(2*T^(1/100))`, `Y=sqrt T`, `gamma in [T,2T]`, and `R=(log T)^2`. The proof absorbs the polynomial factors into `exp(-pi*log(T)^2/4)`. | Mark full-success criterion 3 closed for the corrected Gamma argument. |
| 14 | `LOCAL_FOURTH_CHARGE_CLOSED` | `eventually_one_sixth_le_source_typeIILocalFourthMoment` combines Type-II largeness, the corrected tail, `|Gamma|<=2*log T` on the compact window, and the compiled `L1`--`L4` Holder inequality. It yields the source local fourth-moment lower charge without an analytic premise. | Mark full-success criterion 4 closed; move to multiplicity-aware packing. |
| 15 | `MULTIPLICITY_PACKING` | `exists_ordinateSeparated_cover` gives a finite greedy separated cover. `exists_maynardPrattTypeIISeparated_card_control` preserves analytic zero multiplicity and proves `R_II(T,sigma) <= L*S.card` from the explicit local occupancy bound `maynardPrattTypeIILocalMultiplicityCount T sigma H center <= L`. | Retain the local occupancy theorem as a named producer instead of hiding it behind distinct-point cardinality. |
| 16 | `LOCAL_ZERO_COUNT_AUDIT` | Repository search found compact zero finiteness and global counts but no compiled Riemann--von Mangoldt or short-interval theorem that bounds the multiplicity-bearing count in a window of radius `(log T)^3` by a power of `log T`. | Select `OBS-H2-TYPE-II-LOCAL-ZERO-COUNT-01` as the next producer; the fixed source-mollifier twisted fourth moment remains independently open. |
| 17 | `LOG_DERIVATIVE_CHARGE` | `MaynardPrattTypeIILocalZeroCount.lean` injects every finite Type-II multiplicity copy into the global xi divisor. Positivity of the paired reciprocal kernel at `2+i*t` gives `localCount/(2*(4+H^2)) <= Re((xi'/xi)(2+i*t))`. | Replace a full Riemann--von Mangoldt reconstruction by this smaller Euler-product-half-plane producer if it yields the required polylogarithmic count. |
| 18 | `RIGHT_HALF_PLANE_BOUND` | The compiled xi logarithmic-derivative decomposition, Stieltjes digamma remainder, and absolute convergence of the von Mangoldt L-series give `Re((xi'/xi)(2+i*t)) <= log(|t|+2)+C`, with `C=3+` one fixed convergent absolute mass. | Specialize this bound to source heights and absorb only the fixed constant, not a hidden zero-count asymptotic. |
| 19 | `SOURCE_LOCAL_ZERO_COUNT` | `eventually_maynardPrattTypeIILocalMultiplicityCount_source_le` proves uniformly for all source Type-II centers that the radius `(log T)^3` count is at most `ceil(30*(log T)^7)`. Analytic multiplicity is preserved throughout. | Mark `OBS-H2-TYPE-II-LOCAL-ZERO-COUNT-01` locally closed. |
| 20 | `PACKING_PRODUCER_CLOSED` | `eventually_exists_maynardPrattTypeIISeparated_source_card_control` composes the explicit local count with greedy separation and proves `R_II(T,sigma) <= ceil(30*(log T)^7)*S.card`. | Mark preregistration criterion 5 closed; make the fixed short-Mobius twisted fourth moment the sole deep analytic producer. |
| 21 | `GLOBAL_WINDOW_CHARGE` | `MaynardPrattTypeIIGlobalCharge.lean` rewrites every centered local fourth moment as an absolute half-open ordinate window. Separation by `(log T)^3` makes the radius-`(log T)^2` windows pairwise disjoint, and `eventually_sum_maynardPrattTypeIILocalFourthMoment_source_le_global` charges their sum to the literal global interval `[T/2,3T]`. | Close the bounded-overlap/global-measure interface without assuming a moment estimate. |
| 22 | `UNIFORM_SIGMA_CHARGE` | `eventually_one_sixth_le_sourceChargeScale_mul_localFourthRoot` retains the monotone factor `Y^(1/2-sigma)` while making the local charge uniform over every selected Type-II multiplicity copy. `fourthMoment_lower_bound_of_charge` removes the fourth root by a checked nonnegative fourth power. | Preserve the horizontal rarity exponent instead of weakening the charge to a sigma-free polylogarithmic bound. |
| 23 | `CONDITIONAL_FULL_COUNT_REDUCTION` | `MaynardPrattTypeIISourceTwistedFourthMomentEstimate A` names exactly the fixed source-mollifier estimate on `[T/2,3T]`. `eventually_exists_typeIISeparated_fullCount_charge_le_of_sourceMomentEstimate` composes it with the compiled local count, packing, local charge, and global charging; no additional analytic premise remains. | Classify the structural reduction as compiled conditional progress, not as a proved Type-II rarity estimate. The moment producer remains open. |
| 24 | `LOCAL_AUDIT` | The new module compiles independently without warnings; its target build completes `8724/8724`, and the full project build completes `8810/8810` with only inherited warnings. Five exact statement witnesses compile in `TargetChecks.lean`; seven registered axiom prints use only `propext`, `Classical.choice`, and `Quot.sound`. The four Type-II modules have empty `sorry/admit/native_decide/axiom/opaque/unsafe` scans, and `git diff --check` passes. | Freeze this loop checkpoint in the ledgers before attacking the fixed twisted fourth moment. Do not register Type-II rarity as proven. |
| 25 | `PUBLIC_CHECKPOINT` | Implementation commit `b44255fdeb49f12a55214888d26c40d761dfe8e5` passed Lean Action run `30505660293`, build job `90754736822`, in `2m49s`. The public checkpoint includes the four production modules, five exact checks, seven axiom audits, and the conditional full-count theorem. | Keep the campaign active. Attack `MaynardPrattTypeIISourceTwistedFourthMomentEstimate A`; do not close the Type-II rarity node. |

## Frozen frontier

- `compiled_left_context`: actual truncated-Mobius mollifier; forward and inverse Mellin
  identities; one-pole contour shift; literal source scales; actual-zero Type-I/Type-II
  disjunction.
- `selected_edge`: multiplicity-bearing Type-II rarity at exponent `2*(1-sigma)`.
- `omission_probe`: replace the cited general twisted fourth-moment asymptotic by a proof of
  only the fixed short-Mobius upper bound needed by the consumer.
- `source_discrepancy`: the arXiv v2 proof displays the opposite real part in its Gamma
  argument after the change of variables. The literal display is kernel-refuted for
  `beta>1/2`; Gamma recurrence recovers its claimed `O(log T)` consequence under the stated
  lower bound on `sigma`.
- `closed_subedges`: corrected Gamma tail at `|u|>(log T)^2`; source-scale compact-window
  local fourth-moment charge; explicit multiplicity-bearing radius-`(log T)^3` zero count;
  finite multiplicity-aware separated packing; disjoint source-window global fourth-moment
  charging; and the conditional full-count composition.
- `local_count_omission`: a full Riemann--von Mangoldt theorem is unnecessary for this
  consumer. Positivity at `2+i*t` and the right-half-plane logarithmic derivative give the
  sufficient `ceil(30*(log T)^7)` occupancy bound.
- `next_producer`: the fixed short-Mobius twisted fourth-moment upper bound.
- `compiled_conditional_endpoint`:
  `eventually_exists_typeIISeparated_fullCount_charge_le_of_sourceMomentEstimate` has only
  `MaynardPrattTypeIISourceTwistedFourthMomentEstimate A` as an undischarged analytic input.
- `remaining_elementary_postprocessing`: normalize the exact compiled charge factors to the
  preregistered `T^(2*(1-sigma))*(log T)^B` display once the moment exponent `A` is fixed.
- `strict_successor`: Type-I rarity, half-isolated clustering without finite-real-part
  rigidity, and actual-zeta bow exclusion.
- `not_claimed`: a full zero-density theorem, H2, a zero-free region, or RH.
- `protected_files`: inherited modified and untracked files remain untouched and unstaged.
- `global_goal`: active.
