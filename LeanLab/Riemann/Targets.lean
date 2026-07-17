import LeanLab.Riemann.LiScaffold
import LeanLab.Riemann.DeBruijnNewman
import LeanLab.Riemann.DeBruijnNewmanHeat
import LeanLab.Riemann.DeBruijnNewmanZeros
import LeanLab.Riemann.DeBruijnNewmanThreshold
import LeanLab.Riemann.DeBruijnNewmanForward
import LeanLab.Riemann.DeBruijnNewmanUpperHalf
import LeanLab.Riemann.DeBruijnNewmanDynamics
import LeanLab.Riemann.DeBruijnNewmanLiMoments
import LeanLab.Riemann.DeBruijnNewmanThirdLi
import LeanLab.Riemann.FinitePowerSumRigidity
import LeanLab.Riemann.H6GapVelocityAudit
import LeanLab.Riemann.H6PositiveCoshLiAudit
import LeanLab.Riemann.H6ReverseHeatLiAudit
import LeanLab.Riemann.LiZeroDivisor
import LeanLab.Riemann.LiHadamard
import LeanLab.Riemann.LiZeroFormula
import LeanLab.Riemann.LiSymmetricZeroFormula
import LeanLab.Riemann.LiReverseCriterion
import LeanLab.Riemann.LiWeilGram
import LeanLab.Riemann.WeilTestAlgebra
import LeanLab.Riemann.WeilConvolution
import LeanLab.Riemann.WeilStripClass
import LeanLab.Riemann.WeilExplicitIntegrand
import LeanLab.Riemann.WeilZeroCutoff
import LeanLab.Riemann.WeilGaussianHeight
import LeanLab.Riemann.WeilGaussianExplicitFormula
import LeanLab.Riemann.WeilSymmetricGaussianFamily
import LeanLab.Riemann.WeilFiniteGaussianTestCore
import LeanLab.Riemann.WeilGaussianQuadraticPositivity
import LeanLab.Riemann.WeilGaussianPositivityCriterion
import LeanLab.Riemann.WeilGaussianFixedWidthCriterion
import LeanLab.Riemann.WeilCompactLaplaceSeparator
import LeanLab.Riemann.WeilCompactLaplaceZeroCutoff
import LeanLab.Riemann.WeilCompactLaplaceArithmeticFormula
import LeanLab.Riemann.WeilCompactPositivityCriterion
import LeanLab.Riemann.WeilGaussianPrimeKernelSignAudit
import LeanLab.Riemann.PolsonGGCContinuationAudit
import LeanLab.Riemann.FreedmanGreenLiftAudit
import LeanLab.Riemann.NymanBeurling
import LeanLab.Riemann.BalazardSaias
import LeanLab.Riemann.ReciprocalZetaSubpower
import LeanLab.Riemann.TruncatedPerron
import LeanLab.Riemann.BalazardSaiasContour
import LeanLab.Riemann.BaezDuarteReverse
import LeanLab.Riemann.BaezDuarteForward
import LeanLab.Riemann.BaezDuarteForwardLimit
import LeanLab.Riemann.BaezDuarteQTwo
import LeanLab.Riemann.BurnolHardy
import LeanLab.Riemann.BurnolFullLowerBound

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Target ledger for RH proof-engineering work

This file is deliberately a compiled ledger, not a source of unproved
mathematical facts. Planned theorem statements live as strings until they are
proved elsewhere and linked back here by name.

The next loops should decrease this ledger or fill a blueprint node, rather
than merely adding convenient rewrite lemmas.
-/

namespace LeanLab.Riemann

/-- Coarse research tier for the target ledger. -/
inductive TargetTier where
  | tier1
  | tier2
  | tier3
  deriving DecidableEq, Repr

/-- Current status of a research target. -/
inductive TargetStatus where
  | planned
  | inProgress
  | proven
  | parked
  deriving DecidableEq, Repr

/--
A compiled bookkeeping entry for the RH project.

`statement` is text only; a target is usable as mathematics only after
`leanName` points at an existing theorem and `status = proven`.
-/
structure ResearchTarget where
  id : String
  tier : TargetTier
  title : String
  statement : String
  leanName : Option Lean.Name := (none : Option Lean.Name)
  status : TargetStatus
  note : String

/-- Current target ledger after the 2026-07-09 architectural review. -/
def rhTargets : List ResearchTarget :=
  [ { id := "T1.r1.baez.duarte.qtwo.criterion"
      tier := .tier1
      title := "Formalize Ehm's twice-weighted Baez-Duarte criterion"
      statement :=
        "Prove Mathlib.RiemannHypothesis iff chi multiplicatively convolved with chi belongs to the complex closed span of chi multiplicatively convolved with the positive-natural Baez-Duarte kernels."
      leanName := some ``riemannHypothesis_iff_baezDuarteQTwoComplexTarget_mem_kernelClosure
      status := .proven
      note := "Campaign CAMPAIGN-20260715-R1-BAEZ-DUARTE-QTWO-01 proves the q=2 criterion. The forward half transports the established q=1 closure through the bounded critical multiplier 1/s. The reverse half independently uses the exact 1/s^2 target Mellin value, the reciprocal kernel tail, local Cauchy-Schwarz, and zero reflection; it does not invert the multiplier. This is an exact RH equivalence, not an unconditional proof of RH." },
    { id := "T1.m1.baez.duarte.criterion"
      tier := .tier1
      title := "Formalize the exact strong Baez-Duarte criterion"
      statement :=
        "Prove Mathlib.RiemannHypothesis iff the aligned complex positive-natural target belongs to the full-half-line natural-kernel closure."
      leanName := some ``riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure
      status := .proven
      note := "Batch M1-18 completes the forward direction through the source weighted Mellin/Fourier formula, compiled Balazard-Saias estimate, fixed-epsilon transformed convergence, epsilon-to-zero dominated convergence, diagonal selection, and weighted-tail removal. Combined with M1-16, this is the exact published strong criterion; it is an RH equivalence, not an unconditional proof of RH." },
    { id := "T1.m1.baez.duarte.fixed.epsilon"
      tier := .tier1
      title := "Compile fixed-epsilon Baez-Duarte convergence"
      statement :=
        "Under Mathlib.RiemannHypothesis and 0<delta<=1/2, prove the source natural Mobius approximations converge in real L2(0,infinity) to an element of the natural-kernel closure."
      leanName := some ``RiemannHypothesis.exists_tendsto_baezDuarteMobiusApproxL2
      status := .proven
      note := "Batch M1-17 proves the exact fixed-delta source convergence through classical/L2 Fourier compatibility, Burnol's compiled transformed-error bound, Plancherel, and closure closedness. Batch M1-18 subsequently completes the source weighted epsilon-to-zero passage and final RH-to-target-closure assembly." },
    { id := "T1.m1.baez.duarte.reverse"
      tier := .tier1
      title := "Formalize the reverse strong Baez-Duarte implication"
      statement :=
        "Prove that membership of the aligned complex positive-natural target in the kernel closure implies Mathlib.RiemannHypothesis."
      leanName := some ``baezDuarteComplexTarget_mem_closure_imp_riemannHypothesis
      status := .proven
      note := "Batch M1-16 proves the exact reverse implication by the Mellin zero obstruction on source-structured full-line errors; no general Nyman-Beurling or Hardy-space premise is assumed. The forward RH-to-closure convergence assembly remains open." },
    { id := "T1.m1.balazard.saias"
      tier := .tier1
      title := "Compile the RH-specialized Balazard-Saias Mobius estimate"
      statement :=
        "Under Mathlib.RiemannHypothesis, prove the uniform N^(-delta/3)(1+|Im(s)|)^eta error bound for Mobius Dirichlet partial sums on 1/2+delta<=Re(s)<=1, using the analytic reciprocal of zeta at s=1."
      leanName := some ``RiemannHypothesis.exists_balazardSaias_specialized_bound_compiled
      status := .proven
      note := "Batch M1-15 compiles the preregistered RH specialization by contour shifting and quantitative error balancing, and discharges the Balazard-Saias premise from the Burnol forward consumer. The stronger general-alpha zero-free-half-plane proposition BalazardSaiasEstimate remains encoded but unproved." },
    { id := "T1.m1.truncated.perron"
      tier := .tier1
      title := "Formalize the source-specialized Mobius truncated Perron estimate"
      statement :=
        "Uniformly approximate the Mobius Dirichlet partial sum by the c=2, x=N+1/2 truncated Perron integral with an absolute C*(N+1)^2/T error."
      leanName := some ``exists_mobiusDirichletPartialSum_sub_truncatedPerronIntegral_le
      status := .proven
      note := "Batch M1-14 proves the exact source target via an explicit 2*pi*i rectangle residue calculation, positive and negative kernel estimates, dominated Mobius-series integration, half-integral logarithmic spacing, and a summable n^(-3/2) majorant." },
    { id := "T1.m1.reciprocal.zeta.subpower"
      tier := .tier1
      title := "Close the RH reciprocal-zeta subpower component of F1"
      statement :=
        "Under RH, uniformly bound reciprocal zeta by C*(1+|Im(s)|)^eta on every closed substrip 1/2+delta<=Re(s)<=1, for arbitrary delta and eta positive."
      leanName := some ``RiemannHypothesis.exists_reciprocalZeta_subpower_bound
      status := .proven
      note := "Batch M1-12 formalizes Titchmarsh 14.2 via an RH zero-free logarithm branch, Borel-Caratheodory, Hadamard three-circles, strict sublinear log growth, asymptotic exponentiation, and a compact low-height patch." },
    { id := "T1.m1.zeta.convexity.three.eighths"
      tier := .tier1
      title := "Close the unconditional zeta-convexity component of F1"
      statement :=
        "Prove an unconditional critical-line Riemann zeta bound with exponent 3/8 for |t| >= 1."
      leanName := some ``exists_norm_riemannZeta_criticalLine_le_rpow
      status := .proven
      note := "Batch M1-09 formalized Fiori's corrected midpoint Phragmen-Lindelof argument. Balazard-Saias remains open, so F1 itself is not closed." },
    { id := "T1.xi.completed.bridge"
      tier := .tier1
      title := "Bridge local xi to the completed zeta variant outside the poles"
      statement :=
        "For s != 0 and s != 1, relate riemannXi s to the completed Riemann zeta expression used by mathlib."
      leanName := some ``riemannXi_eq_mul_completedRiemannZeta
      status := .proven
      note := "Proved from completedRiemannZeta_eq by clearing the two pole-removal terms." },
    { id := "T1.xi.zero.bridge"
      tier := .tier1
      title := "Bridge local xi zeros to project nontrivial zeta zeros"
      statement :=
        "State and prove the precise correspondence between zeros of riemannXi and IsNontrivialZero, with pole and trivial-zero edge cases handled explicitly."
      leanName := some ``isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial
      status := .proven
      note := "Proved with the trivial-zero exclusion explicit on the riemannXi-zero side." },
    { id := "T1.li1.positivity"
      tier := .tier1
      title := "Finish positivity of the second local Li candidate"
      statement :=
        "Prove 0 < (liCoefficientCandidate 1).re, or record a precise library gap after a bounded inventory."
      leanName := some ``liCoefficientCandidate_one_re_pos
      status := .proven
      note := "Proved in Loop 84 by bounding the log-weighted Mellin term by 17/160 and proving that this is below the Li-side threshold." },
    { id := "T1.note.li.scaffold"
      tier := .tier1
      title := "Write a short result note for the xi and Li scaffold"
      statement :=
        "Summarize the local xi bridge, center scaffold, and first two local Li-candidate positivity results, including explicit limits."
      leanName := none
      status := .proven
      note := "Documentation target completed as research/li_scaffold_note_20260709.md; it cites compiled theorem names and separates local results from global RH claims." },
    { id := "T2.inventory.li.hadamard"
      tier := .tier2
      title := "Inventory mathlib support for a Li-criterion statement route"
      statement :=
        "Inspect available Hadamard product, entire function, zero multiset, and log-derivative infrastructure before choosing this route."
      leanName := none
      status := .proven
      note := "Inventory completed as research/tier2_li_hadamard_inventory_20260709.md; recommendation is not to choose this as the immediate Tier 2 route until global product and zero-enumeration bridges exist." },
    { id := "T2.li.xi.zero.divisor"
      tier := .tier2
      title := "Package the exact xi zero divisor with multiplicity"
      statement :=
        "Construct a globally locally finite divisor for riemannXi, prove its finite natural values are the analytic zero multiplicities, identify its support exactly with IsNontrivialZero, and transport multiplicity under s -> 1-s."
      leanName := some ``support_riemannXiZeroDivisor
      status := .proven
      note := "Campaign CAMPAIGN-20260715-XI-DIVISOR-01 excludes negative-even trivial zeta zeros from xi, rules out infinite local order by the identity theorem, and packages the exact locally finite multiplicity carrier. This closes the divisor/local-multiplicity prerequisite only; order-one growth, a Hadamard product, global zero summability, the Li zero-sum identity, all-index positivity, and RH remain open." },
    { id := "T2.li.xi.hadamard.global"
      tier := .tier2
      title := "Align the global genus-one xi Hadamard product"
      statement :=
        "Prove that the project xi is the audited order-one entire xi, align its multiplicity-bearing divisor index exactly with IsNontrivialZero, and transport squared reciprocal summability, the global genus-one product, and the away-from-zeros logarithmic-derivative sum."
      leanName := some ``exists_riemannXi_hadamard_factorization
      status := .proven
      note := "Campaign CAMPAIGN-20260715-XI-HADAMARD-01 snapshots the exact Apache-2.0 dependency closure from PrimeNumberTheoremAnd commit d963a6e694a05cd82e5f9b9ae7f4d94123e85393 and Lean-aligns its global factorization with the prior local xi divisor. This closes the R3 order-growth, canonical-product, and squared-reciprocal zero-summability prerequisites. The derivative-defined Li family, derivative-to-zero identity, all-index positivity, and RH remain open." },
    { id := "T2.li.xi.zero.formula.all-index"
      tier := .tier2
      title := "Justify the all-index compensated Li zero formula"
      statement :=
        "For one fixed genus-one xi Hadamard polynomial, prove every derivative-defined Li candidate equals the exact finite Leibniz combination of the polynomial derivative and multiplicity-indexed compensated zero derivatives, with all infinite-sum differentiations justified locally uniformly."
      leanName := some ``exists_liCoefficientCandidate_eq_hadamard_zero_formula
      status := .proven
      note := "Campaign CAMPAIGN-20260715-LI-ZERO-FORMULA-01 proves a compact-set M-test dominated by the compiled squared reciprocal zero sum, applies iteratedDerivWithin_tsum for every order at s=1, and combines it with the all-index Leibniz identity. The k=0 compensation and the degree-at-most-one exponential polynomial remain explicit. This is known-theorem formalization; the raw classically ordered zero sum, all-index positivity, the Li/RH equivalence, and RH remain open." },
    { id := "T2.li.xi.zero.formula.symmetric-all-index"
      tier := .tier2
      title := "Normalize the all-index Li formula by zero symmetry"
      statement :=
        "Pair every multiplicity-bearing xi zero rho with 1-rho, prove the averaged raw Li zero term is summable and equals liCoefficientCandidate at every index, and under RH identify the summands with half norm squares to obtain real nonnegativity."
      leanName := some ``liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm
      status := .proven
      note := "Campaign CAMPAIGN-20260715-LI-SYMMETRIC-ZERO-01 constructs the exact divisor-index involution, averages the compensated summable formula, and derives cancellation of the degree-at-most-one Hadamard polynomial from xi symmetry. Under RH every paired term is exactly half a complex norm square, so every project Li coefficient is real and nonnegative. This is known-theorem formalization and the forward direction; the reverse implication is closed by the successor reverse-Li campaign, while RH itself remains open." },
    { id := "T2.li.reverse.criterion"
      tier := .tier2
      title := "Formalize the reverse all-index Li criterion"
      statement :=
        "Prove that nonnegative real parts of every derivative-defined project Li coefficient imply Mathlib.RiemannHypothesis, and combine this with the forward direction as an exact equivalence."
      leanName := some ``riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg
      status := .proven
      note := "Campaign CAMPAIGN-20260715-LI-REVERSE-BOMBIERI-LAGARIAS-01 specializes the published large-index power-sum argument to the multiplicity-bearing xi divisor. A finite orbit-radius superlevel set is phase-aligned simultaneously, one off-line orbit supplies the exponentially negative main term, and the complement is dominated by a fixed reciprocal-square tsum times a strictly smaller exponential. This closes the exact Li/RH criterion as known-theorem formalization; it does not prove either equivalent side unconditionally." },
    { id := "T2.li.weil.gram-criterion"
      tier := .tier2
      title := "Formalize the Li-test Weil Gram positivity criterion"
      statement :=
        "Construct the reflection-averaged multiplicity-bearing Gram kernel for Li test functions, prove its exact matrix in terms of the project Li coefficients, identify every finite real quadratic combination with a zero-side norm-square sum under RH, and prove positivity of all such combinations is equivalent to RH."
      leanName := some ``riemannHypothesis_iff_forall_liWeilQuadratic_nonneg
      status := .proven
      note := "Campaign CAMPAIGN-20260715-R3-R5-LI-WEIL-GRAM-01 formalizes Lagarias Theorem 3.1 on the project xi divisor. Reflection averaging cancels the nonsummable reciprocal term before tsum, and the reverse direction uses genuine one-coordinate Finsupp tests. This is an RH-equivalent reformulation with hard_gap_delta=0; it does not prove W1c, W2, or RH." },
    { id := "T2.weil.test-algebra.involution"
      tier := .tier2
      title := "Formalize the Weil test-function involution"
      statement :=
        "Define f_tilde(x)=x^(-1)f(x^(-1)), prove it is involutive on the positive half-line, prove M(f_tilde)(s)=M(f)(1-s), and prove the conjugate-star transform specializes to conjugation on the critical line."
      leanName := some ``mellin_weilStar_criticalLine
      status := .proven
      note := "Campaign CAMPAIGN-20260715-R5-WEIL-TEST-ALGEBRA-01 formalizes Lagarias Appendix A (A.1)-(A.2) using Mathlib's actual Mellin integral, including the endpoint-moment swap and the exact conjugate-star parameter. This is necessary R5 test algebra with hard_gap_delta=0; it is not the explicit formula or a positivity result." },
    { id := "T2.weil.test-algebra.convolution"
      tier := .tier2
      title := "Formalize multiplicative Weil convolution"
      statement :=
        "Define source-faithful dy/y convolution, prove pointwise Mellin convergence is closed under it, prove its Mellin transform is the product, and derive the conjugate-star Hermitian product on the critical line."
      leanName := some ``mellin_weilConvolution_star_criticalLine
      status := .proven
      note := "Campaign CAMPAIGN-20260715-R5-WEIL-CONVOLUTION-01 transports multiplicative convolution to Mathlib's additive Bochner convolution in logarithmic coordinates and justifies Fubini from the two exact MellinConvergent assumptions. This closes W1a only; the analytic-strip test class, complete explicit formula, positivity, and RH remain open." },
    { id := "T2.weil.test-algebra.strip-class"
      tier := .tier2
      title := "Package the physical Weil strip test algebra"
      statement :=
        "Define the positive-width physical Mellin strip class with pointwise closed-strip convergence, open-strip analyticity, closed-strip continuity, and a uniform bound; prove closure under linear operations, Weil involution, conjugate star, multiplicative convolution, and autocorrelation."
      leanName := some ``IsWeilStripAdmissible.weilAutocorrelation
      status := .proven
      note := "Campaign CAMPAIGN-20260715-R5-WEIL-STRIP-CLASS-01 packages the source-facing physical A_delta conditions and proves the W1b algebra core using the compiled W1a transform laws. It deliberately does not claim that the raw-function uniform distance is separated or complete, nor density, a complete explicit formula, positivity, or RH." },
    { id := "T2.weil.explicit-integrand"
      tier := .tier2
      title := "Join the Weil zero, pole, archimedean, and prime integrands"
      statement :=
        "On Re(s)>1, prove the exact xi logarithmic-derivative decomposition into pole terms, the GammaR logarithmic derivative, and the von Mangoldt L-series, then identify it with the multiplicity-bearing Hadamard zero sum."
      leanName := some ``exists_weilExplicitIntegrand_eq_hadamardZeroSum
      status := .proven
      note := "Campaign CAMPAIGN-20260715-R5-WEIL-EXPLICIT-INTEGRAND-01 closes the unconditional W1c0 analytic integrand subedge. It does not assert test-function integration, contour or zero-cutoff limits, local regularization, the complete explicit formula, W2 positivity, or RH." },
    { id := "T2.weil.zero-cutoff.finite-height"
      tier := .tier2
      title := "Formalize the finite-height weighted xi zero cutoff"
      statement :=
        "For every entire weight and rectangle whose boundary contains no xi zero, prove that the boundary integral of the weighted xi logarithmic derivative is 2*pi*i times the finite multiplicity-bearing sum of the weight over strictly interior xi zeros."
      leanName := some ``rectangleBoundaryIntegral_weighted_logDeriv_riemannXi_eq_finsum
      status := .proven
      note := "Campaign CAMPAIGN-20260715-R5-WEIL-ZERO-CUTOFF-01 closes the unconditional finite-height W1c1 zero-side subedge. Genus-one compensation supplies local-uniform convergence on the complete boundary, and the divisor index retains analytic multiplicity. Height limits, prime-side contour decay, endpoint regularization, the complete explicit formula, W2 positivity, and RH remain open." },
    { id := "T2.weil.gaussian-height-limit"
      tier := .tier2
      title := "Pass the symmetric Gaussian xi contour to infinite height"
      statement :=
        "For every a>0 and right line c>1, construct symmetric zero-free heights tending to infinity and prove that the Gaussian-weighted right-vertical xi logarithmic-derivative integrals tend to pi times the absolute multiplicity-bearing Gaussian sum over all xi zeros."
      leanName := some ``exists_gaussianXiZeroFreeHeight_tendsto_rightVerticalIntegral
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-WEIL-GAUSSIAN-HEIGHT-LIMIT-01 proves the fixed-test W1c1 height limit. Reciprocal-square Hadamard summability gives absolute Gaussian zero summability, a polynomial zero-count bound, and quantitatively separated zero-free heights; exp(-a*T^2) then absorbs the fourth-power horizontal log-derivative bound. This is unconditional and multiplicity-bearing, but it is not a generic test-class explicit formula, prime-side identity, positivity criterion, or RH." },
    { id := "T2.weil.gaussian-arithmetic-explicit-formula"
      tier := .tier2
      title := "Evaluate the arithmetic side of the Gaussian xi contour"
      statement :=
        "For every a>0 and c>1, prove the fixed Gaussian explicit formula equating pi times the absolute multiplicity-bearing xi-zero sum to the explicit two-pole contribution plus the integrable GammaR line term minus an absolutely summable Gaussian-smoothed von-Mangoldt prime-power series."
      leanName := some ``gaussianXi_arithmetic_explicit_formula
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-WEIL-GAUSSIAN-EXPLICIT-FORMULA-01 closes the fixed-test arithmetic W1c subedge. It proves the exact Fourier-Gaussian von-Mangoldt prime-power weights and absolute interchange, GammaR full-line integrability from digamma growth, the independent two-pole residue value 2*pi*exp(a/4), and the final multiplicity-bearing Gaussian explicit formula without RH. Generic test classes, singular regularization, Weil positivity, and RH remain open." },
    { id := "T2.weil.symmetric-gaussian-family-explicit-formula"
      tier := .tier2
      title := "Evaluate the symmetric translated Gaussian family"
      statement :=
        "For every a>0, real translation b, and c>1, prove the xi explicit formula for exp(a(s-1/2)^2)cosh(b(s-1/2)), with an absolutely convergent zero sum, exact two-pole term, integrable GammaR term, and the average of the two von-Mangoldt Gaussian kernels centered at log(n)=plus-or-minus b."
      leanName := some ``symmetricGaussianXi_arithmetic_explicit_formula
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-WEIL-SYMMETRIC-GAUSSIAN-FAMILY-01 closes one unconditional two-parameter probe-family subedge. It also factors out a generic selected-height rectangle skeleton for analytic reflection-symmetric summable weights, proves both translated prime branches by exact quadratic-exponential integration, and recovers the centered formula at b=0. Schwartz/Hermite density, tempered-distribution extension, Weil positivity, and RH remain open." },
    { id := "T2.weil.finite-gaussian-test-core"
      tier := .tier2
      title := "Extend the Gaussian formula to its finite test core"
      statement :=
        "For every finite complex superposition of positive-width symmetric Gaussian xi probes, prove the complete explicit formula with the directly synthesized zero tsum, GammaR integral, pole factor, and von-Mangoldt tsum, including absolute convergence and singleton compatibility."
      leanName := some ``symmetricGaussianXiPacket_arithmetic_explicit_formula
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-WEIL-FINITE-GAUSSIAN-TEST-CORE-01 constructs the algebraic test core needed before a density/continuity extension. It proves direct packet summability and finite-sum interchange on the zero, archimedean, and prime sides, and exact singleton and empty-packet reductions. This closes one G6 algebraic-core subedge; Schwartz density, tempered extension, regularization, Weil positivity, and RH remain open." },
    { id := "T2.weil.gaussian-quadratic-positivity"
      tier := .tier2
      title := "Derive Gaussian-Weil quadratic positivity under RH"
      statement :=
        "Assuming RH, prove that every finite real ordered-pair packet of equal-width symmetric Gaussian probes has a summable zero-side square expansion and that the real part of its direct pole-plus-GammaR-minus-von-Mangoldt arithmetic expression is nonnegative."
      leanName := some ``RiemannHypothesis.gaussianXiArithmeticQuadratic_re_nonneg
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-QUADRATIC-POSITIVITY-01 instantiates the finite packet formula at shifts b_i-b_j and coefficients w_i*w_j. Under RH, every multiplicity-bearing zero contribution is exp(-a*gamma^2) times a cosine square plus a sine square. This closes one conditional W2 kernel bridge only; unconditional arithmetic positivity, the converse Weil criterion, Schwartz closure, separated temperedness, and RH remain open." },
    { id := "T2.weil.gaussian-positivity-criterion"
      tier := .tier2
      title := "Characterize RH by finite Gaussian-Weil quadratic positivity"
      statement :=
        "Prove that RH is equivalent to nonnegativity of the real part of every positive-width finite real Gaussian-Weil arithmetic quadratic at contour parameter c=2."
      leanName := some ``riemannHypothesis_iff_gaussianXiArithmeticQuadratic_re_nonneg
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-REVERSE-CRITERION-01 proves the converse by isolating any off-line multiplicity-bearing xi divisor zero with a finite real exponential separator, annihilating its finite low-decay competitors, and controlling the higher-decay tail by dominated convergence. Implementation commit b2d2ce18ff1491f684098b04c7a5be73e0ebdc98 passed public CI run 29453270303; evidence commit 68e96525f3f89562ae47e1da9e074911701a6c2e passed run 29453470463. This formalizes an exact RH-equivalent restricted Gaussian criterion; it does not prove unconditional positivity or RH." },
    { id := "T2.weil.gaussian-fixed-width-positivity-criterion"
      tier := .tier2
      title := "Compress Gaussian-Weil positivity to one fixed width"
      statement :=
        "For every preassigned a0>0, prove that RH is equivalent to nonnegativity of every finite real Gaussian-Weil arithmetic quadratic at exactly width a0 and contour parameter c=2."
      leanName := some ``riemannHypothesis_iff_fixedWidth_gaussianXiArithmeticQuadratic_re_nonneg
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-FIXED-WIDTH-01 realizes every larger Gaussian width as a dominated limit of finite Rademacher exponential packets at the fixed base width, then combines this transfer with the off-line separator criterion. Implementation commit f56b70478ab552802cac719b8e9af0f56fc44b1d passed public Lean Action CI run 29458594435, build job 87497146736; evidence commit f93e73cbdd71785a28cc2b05f8ef2b0390b358cf passed run 29458788171, build job 87497720018. This strictly compresses an RH-equivalent Gaussian criterion; it does not prove unconditional positivity or RH." },
    { id := "T2.weil.compact-laplace-xi-divisor-separator"
      tier := .tier2
      title := "Separate one xi-divisor value by compact Laplace tests"
      statement :=
        "For every selected multiplicity-bearing xi-divisor index and every positive epsilon, construct a smooth compactly supported additive-log test whose bilateral Laplace transform is one at the selected value, is absolutely summable on the complete xi divisor, and has total norm below epsilon over all different zero values."
      leanName := some ``exists_compactSupport_xiDivisor_laplace_tsum_separator
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-COMPACT-LAPLACE-SEPARATOR-01 proves twofold integration-by-parts decay, complete xi-divisor summability, finite superlevel annihilation by a real-shift exponential polynomial, and geometric suppression by compact convolution powers. Equal-value multiplicity copies are protected. Implementation commit 6d12bad98b80c34217757df01943509965a64781 passed public Lean Action CI run 29461298466, build job 87505125618; evidence commit 941756c2e7e0b4da8f765dc7187e4be703af36c8 passed run 29461494669, build job 87505716647. This compiles one unconditional W1 reverse-separation subedge; the generic explicit formula, Weil positivity, G7/W2, and RH remain open." },
    { id := "T2.weil.compact-laplace-zero-cutoff"
      tier := .tier2
      title := "Pass compact-smooth Weil weights through the xi zero cutoff"
      statement :=
        "For every smooth compactly supported additive-log function and c>1, prove that the selected right-edge integral for its reflection-symmetrized bilateral Laplace transform converges to pi times the complete multiplicity-bearing xi-zero tsum."
      leanName := some ``tendsto_symmetrizedCompactLaplaceXiRightVerticalIntegral
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-COMPACT-WEIL-ZERO-CUTOFF-01 proves transform entire-ness by dominated differentiation, reflection symmetry, complete divisor summability, arbitrary iterated integration by parts, and fixed-strip inverse-sixth-power decay. That decay absorbs the compiled fourth-power selected-edge xi logarithmic-derivative bound and closes the compact-smooth zero-side cutoff passage. Implementation commit 0e6451944ee1edb2d76d67f4fe097de2aa19ad17 and evidence commit 6c2f3ab912097e4e5b325e9d0c27d43438a29d99 passed public Lean Action CI runs 29464308480 and 29464469804. The generic compact arithmetic evaluation, W2/G7, and RH remain open." },
    { id := "T2.weil.compact-laplace-arithmetic-formula"
      tier := .tier2
      title := "Evaluate the compact-smooth Weil arithmetic side"
      statement :=
        "For every smooth compactly supported additive-log function and c>1, prove the complete reflection-symmetrized xi explicit formula with the multiplicity-bearing zero tsum, both elementary poles, the GammaR integral, and an explicitly finite von-Mangoldt side."
      leanName := some ``symmetrizedCompactLaplaceXi_arithmetic_explicit_formula
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-COMPACT-WEIL-ARITHMETIC-FORMULA-01 proves exact two-branch Schwartz Fourier inversion with the 2*pi scaling, the reflected 1/n prime factor, finite physical prime support from compact support, full-line pole and GammaR integrability, and the selected-height arithmetic limit. Implementation 55a6406f235a7548bf7f7d53ae5d30014795e9ce and evidence ed5d03f65bd234f95afb55389b2766d611a3eeab passed public Lean Action CI runs 29466850965 and 29467021669. This closes the W1c1 compact arithmetic subedge only; quotient/completeness, distributional regularization, W2/G7 positivity, and RH remain open." },
    { id := "T2.weil.compact-c6-arithmetic-formula"
      tier := .tier2
      title := "Extend the compact Weil formula to six derivatives"
      statement :=
        "For every compactly supported additive-log function with six continuous derivatives and c>1, prove the complete reflection-symmetrized xi explicit formula with the multiplicity-bearing zero tsum, both elementary poles, the GammaR integral, and an explicitly finite von-Mangoldt side."
      leanName := some ``symmetrizedCompactLaplaceXi_arithmetic_explicit_formula_sixContDiff
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-COMPACT-C6-EXPLICIT-FORMULA-01 removes the C-infinity Schwartz wrapper from the compact formula. General Fourier inversion is justified by inverse-square Fourier decay, the first absolute moment follows from inverse-sixth decay, and the selected xi top edge uses exactly six continuous derivatives. Independent module checks, exact target checks, standard-only axiom audits, forbidden scans, and the full 8,681-job build pass locally. Preregistration 540b0ddcbf90a219084f8fdcb80a02ddaad5e277, implementation 3e3c677495c592096d7843aa4845e861bc393937, and evidence 94b6be8fc934b3d4909d066b168491389df9afd8 passed public CI runs 29467845311, 29468797210, and 29468980147. The campaign is publicly closed. This closes only the compact finite-regularity W1 subedge; quotient/completeness, full-class regularization, W2/G7 positivity, and RH remain open." },
    { id := "T2.weil.compact-positivity-criterion"
      tier := .tier2
      title := "Characterize RH by compact arithmetic Weil positivity"
      statement :=
        "For every finite set F containing 0 and 1 and disjoint from the nontrivial zeros, prove that RH is equivalent to nonnegativity of the exact compact arithmetic Weil quadratic for every smooth compactly supported additive-log test whose bilateral Laplace transform vanishes on F."
      leanName := some ``riemannHypothesis_iff_compactWeilArithmeticQuadratic_re_nonneg
      status := .proven
      note := "Campaign CAMPAIGN-20260716-R5-COMPACT-WEIL-CRITERION-01 formalizes the Connes--Consani/Yoshida compact-support criterion. The reverse strengthens the complete-divisor separator with arbitrary finite exact vanishing, pairs rho with 1-conj(rho), and bounds the complete off-target autocorrelation tail without assuming a conjugation permutation. Implementation commit d590ee42e37366388800bafda04020a84eee8452 passed public Lean Action CI run 29487332091, build job 87584836879, in 1m53s; evidence commit 03e1661b077ab8d3e2f8c9b93b19aa63c3c1eebc passed run 29487596817, build job 87585683179, in 2m6s. The campaign is publicly closed as known-theorem formalization. This closes one source-level W1/G6 compact-criterion edge only; unconditional W2/G7 positivity, RH, and the optional distributional extension remain open." },
    { id := "T2.audit.gaussian-prime-kernel-sign"
      tier := .tier2
      title := "Audit the sign of one Gaussian prime-power kernel"
      statement :=
        "For the actual n=2 symmetric Gaussian von-Mangoldt term, construct a positive width and two real shifts whose translation-kernel matrix is neither positive nor negative semidefinite."
      leanName := some ``exists_pos_symmetricGaussianPrimeKernelMatrix_indefinite
      status := .proven
      note := "Audit AUDIT-20260716-R5-GAUSSIAN-PRIME-KERNEL-SIGN-01 uses width (log 2)^2/16 and shifts 0, log 2. The exact arithmetic kernel has a negative (1,-1) quadratic direction and a positive diagonal direction. Implementation commit 01ea63517670a81b8c640de1135dec62d44436b9 passed public Lean Action CI run 29462677629, build job 87509304721; evidence commit af7848aea84287329ce50900d5e425538165baaa passed run 29462828680, build job 87509738532. This eliminates termwise same-sign local-prime Gram assembly only; cancellation in the complete pole, archimedean, and prime form, G6/W1, G7/W2, and RH remain open." },
    { id := "T2.audit.polson-ggc-imaginary-tail"
      tier := .tier2
      title := "Audit the imaginary-axis GGC continuation tail"
      statement :=
        "Prove that a Polson 2018 Levy-Frullani exponential component evaluated at s=i*y is not integrable on (1,infinity) whenever gamma>0 and y^2>2*gamma^2."
      leanName := some ``not_integrableOn_polsonImaginaryFrullaniComponent
      status := .proven
      note := "Audit AUDIT-20260716-R5-POLSON-GGC-CONTINUATION-01 Lean-checks the exact complex-to-real specialization and the positive exponential tail. Implementation commit 0c174e82713c18be16ae9ea3afd5197b77ab4347 passed public Lean Action CI run 29455171888, build job 87486632024; evidence commit d277252fa21de89e228a2d1db6addd727d975d99 passed run 29455360041, build job 87487225276. It eliminates retention of the 2018 defining integral outside its convergence domain, but does not obstruct analytic continuation, reject the revised 2026 RH-equivalent Thorin framework, or imply RH or its negation." },
    { id := "T2.audit.freedman-green-lift-contraction"
      tier := .tier2
      title := "Audit the Green-lift contraction inference"
      statement :=
        "Give an exact finite-dimensional model with a nontrivial trace kernel satisfying the displayed Green-lift factorization, middle-multiplier contraction, and trace-fiber Euler-Lagrange orthogonality, while the compressed map expands and the signed form is negative."
      leanName := some ``freedmanGreenLift_listedPremises_do_not_force_contraction
      status := .proven
      note := "Audit AUDIT-20260716-R4-FREEDMAN-GREEN-LIFT-CONTRACTION-01 checks a two-dimensional real model in which K is contractive, G_-=C K E G_+ and trace-kernel orthogonality hold, but C K E multiplies by two and the unit signed form is -3. Implementation commit b360163ccdad0d0076408c2a65eee99d2d4df7b5 passed public Lean Action CI run 29456581043, build job 87490980870; evidence commit 779a8092992e85b8e8a4b3a57a872456dd7fc1d9 passed run 29456771395, build job 87491571306. This eliminates only the claim that those listed premises force contraction; a concrete Volterra proof with additional norm control, KLM positivity, and RH remain open." },
    { id := "T2.inventory.nyman.beurling"
      tier := .tier2
      title := "Inventory mathlib support for the Nyman-Beurling route"
      statement :=
        "Inspect L2, closure, density, step functions, and fractional-part infrastructure before choosing this route."
      leanName := none
      status := .proven
      note := "Inventory completed as research/tier2_nyman_beurling_inventory_20260709.md; recommendation is to prefer this route for the immediate Tier 2 pivot because the first missing nodes are small L2/measurability lemmas." },
    { id := "T2.pivot"
      tier := .tier2
      title := "Choose one structural Tier 2 route after inventory"
      statement :=
        "Commit the next blueprint to either the Li/Hadamard route or the Nyman-Beurling route."
      leanName := none
      status := .proven
      note := "Loop 88 chooses the Nyman-Beurling foundation route, because the first formal nodes are bounded fractional-part kernels in L2." },
    { id := "T2.nyman.kernel.l2"
      tier := .tier2
      title := "Package the first Nyman-Beurling fractional-part kernel in L2"
      statement :=
        "For every real a, the function x ↦ Int.fract (a / x) belongs to L2 on the unit interval."
      leanName := some ``fractionalPartKernel_memLp_two_unitInterval
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling; the stronger theorem fractionalPartKernel_memLp_unitInterval works for every exponent p, and fractionalPartKernelL2 packages the kernel as an L2 element." },
    { id := "T2.nyman.span.scaffold"
      tier := .tier2
      title := "Define the span generated by Nyman-Beurling kernels"
      statement :=
        "Define the real submodule of L2 on the unit interval generated by fractionalPartKernelL2, and prove each generator belongs to it."
      leanName := some ``fractionalPartKernelL2_mem_nymanBeurlingKernelSpan
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling; nymanBeurlingKernelSpan is the real span of the packaged L2 kernels, with generator membership and the span minimality lemma nymanBeurlingKernelSpan_le." },
    { id := "T2.nyman.closure.scaffold"
      tier := .tier2
      title := "Define the closure of the Nyman-Beurling kernel span"
      statement :=
        "Define the topological closure of nymanBeurlingKernelSpan and prove the span is contained in its closure."
      leanName := some ``nymanBeurlingKernelSpan_le_closure
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling; nymanBeurlingKernelClosure is the topological closure, with span inclusion, closedness, set-closure equality, and generator membership." },
    { id := "T2.nyman.density.predicate"
      tier := .tier2
      title := "Package the Nyman-Beurling density predicate"
      statement :=
        "Define the project-local density predicate for the kernel span and prove its equivalence with nymanBeurlingKernelClosure = top."
      leanName := some ``nymanBeurlingKernelDense_iff_closure_eq_top
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling; nymanBeurlingKernelDense is Dense of the kernel span, equivalent to closure equals top and to pointwise membership in nymanBeurlingKernelClosure." },
    { id := "T2.nyman.orthogonal.reformulation"
      tier := .tier2
      title := "Reformulate kernel-span density by orthogonal complement"
      statement :=
        "Prove that nymanBeurlingKernelDense is equivalent to the orthogonal complement of nymanBeurlingKernelSpan being bottom."
      leanName := some ``nymanBeurlingKernelDense_iff_orthogonal_eq_bot
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling using Submodule.topologicalClosure_eq_top_iff after the local closure-density bridge." },
    { id := "T2.nyman.orthogonal.pointwise"
      tier := .tier2
      title := "Unpack orthogonality against every Nyman-Beurling generator"
      statement :=
        "For f in unitIntervalL2, express f in nymanBeurlingKernelSpan orthogonal complement as vanishing inner product against every fractionalPartKernelL2 a."
      leanName := some ``mem_nymanBeurlingKernelSpan_orthogonal_iff
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling by span induction from the packaged fractional-part generators." },
    { id := "T2.nyman.density.pointwise"
      tier := .tier2
      title := "Reformulate density as absence of generator-orthogonal vectors"
      statement :=
        "Prove that nymanBeurlingKernelDense is equivalent to every f in unitIntervalL2 being zero whenever its inner product with every fractionalPartKernelL2 a vanishes."
      leanName := some ``nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling by combining the orthogonal-bottom density theorem with the pointwise generator-orthogonality theorem." },
    { id := "T2.nyman.inner.integral.inventory"
      tier := .tier2
      title := "Inventory Lp inner-product formulas for packaged kernels"
      statement :=
        "Inspect mathlib support for rewriting inner products with fractionalPartKernelL2 as integrals over the restricted unit interval."
      leanName := some ``inner_fractionalPartKernelL2_eq_integral
      status := .proven
      note := "Inventory recorded in research/tier2_nyman_inner_integral_inventory_20260710.md; mathlib's L2.inner_def plus fractionalPartKernelL2_coeFn gives the first compiled inner-product-to-integral bridge." },
    { id := "T2.nyman.density.integral"
      tier := .tier2
      title := "Reformulate density by integral orthogonality"
      statement :=
        "Prove that nymanBeurlingKernelDense is equivalent to every f in unitIntervalL2 being zero whenever the integral of fractionalPartKernel a times f is zero for every real a."
      leanName := some ``nymanBeurlingKernelDense_iff_forall_integral_eq_zero_imp_eq_zero
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling by combining the density pointwise theorem with inner_fractionalPartKernelL2_eq_integral." },
    { id := "T2.nyman.constant.one.l2"
      tier := .tier2
      title := "Package the constant one function in unitIntervalL2"
      statement :=
        "Define the constant-one function as an element of unitIntervalL2 and prove its almost-everywhere representative theorem."
      leanName := some ``unitIntervalOneL2_coeFn
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling; unitIntervalOne packages the constant-one function, unitIntervalOneL2 is its L2 representative, and unitIntervalOneL2_coeFn identifies the representative almost everywhere." },
    { id := "T2.nyman.density.one.closure"
      tier := .tier2
      title := "Use density to place constant one in the Nyman-Beurling closure"
      statement :=
        "Prove that nymanBeurlingKernelDense implies unitIntervalOneL2 belongs to nymanBeurlingKernelClosure."
      leanName := some ``unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling by applying the pointwise closure form of nymanBeurlingKernelDense to unitIntervalOneL2; this remains conditional on density." },
    { id := "T2.nyman.one.closure.epsilon"
      tier := .tier2
      title := "Reformulate constant-one closure membership by epsilon approximation"
      statement :=
        "Prove an epsilon-distance formulation of unitIntervalOneL2 belonging to nymanBeurlingKernelClosure, with approximants drawn from nymanBeurlingKernelSpan."
      leanName := some ``unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling using Metric.mem_closure_iff; also added exists_nymanBeurlingKernelSpan_dist_unitIntervalOneL2_lt_of_dense as the density-conditioned approximation corollary." },
    { id := "T2.nyman.span.finite.approx"
      tier := .tier2
      title := "Unpack span approximants as finite kernel combinations"
      statement :=
        "Reformulate the epsilon approximant from nymanBeurlingKernelSpan as a finite real linear combination of packaged fractional-part kernels."
      leanName := some ``unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling using Finsupp.mem_span_range_iff_exists_finsupp; also added the density-conditioned finite-combination approximation corollary." },
    { id := "T2.nyman.finite.approx.norm"
      tier := .tier2
      title := "Rewrite finite kernel approximation distance as an L2 norm"
      statement :=
        "Reformulate the finite-kernel epsilon approximation statement using the norm of unitIntervalOneL2 minus the finite kernel combination."
      leanName := some ``unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_norm_sub_lt
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling using dist_eq_norm; also added the density-conditioned norm-approximation corollary." },
    { id := "T2.nyman.finite.approx.integral.inventory"
      tier := .tier2
      title := "Inventory L2 norm-square formulas for finite kernel approximants"
      statement :=
        "Inspect mathlib support for rewriting the L2 norm of unitIntervalOneL2 minus a finite kernel combination as an integral of a squared representative."
      leanName := some ``unitIntervalL2_norm_sq_eq_integral_mul_self
      status := .proven
      note := "Inventory recorded in research/tier2_nyman_finite_approx_integral_inventory_20260710.md; proved the generic L2 norm-square-to-integral bridge and its finite-combination specialization." },
    { id := "T2.nyman.finite.approx.representatives"
      tier := .tier2
      title := "Identify finite kernel combinations with concrete representatives"
      statement :=
        "Prove an almost-everywhere representative theorem for c.sum fun a r => r • fractionalPartKernelL2 a, rewriting it as the corresponding finite sum of fractionalPartKernel functions."
      leanName := some ``finsupp_sum_fractionalPartKernelL2_coeFn
      status := .proven
      note := "Loop 103 proved the finite-combination representative theorem, the constant-one-minus-finite-combination representative theorem, and the concrete norm-square integral formula." },
    { id := "T2.nyman.finite.approx.integral.epsilon"
      tier := .tier2
      title := "Convert concrete finite approximation into an integral-square bound"
      statement :=
        "Assuming nymanBeurlingKernelDense and 0 < eps, derive a finite coefficient family whose concrete squared-error integral is below eps^2."
      leanName := some ``exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense
      status := .proven
      note := "Loop 104 combined the density-conditioned norm approximation, the concrete norm-square integral identity, and sq_lt_sq₀ to derive the concrete squared-error integral bound." },
    { id := "T2.nyman.finite.approx.integral.tolerance"
      tier := .tier2
      title := "Remove the squared tolerance from the concrete integral approximation"
      statement :=
        "Assuming nymanBeurlingKernelDense and 0 < delta, derive a finite coefficient family whose concrete squared-error integral is below delta."
      leanName := some ``exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense_tolerance
      status := .proven
      note := "Loop 105 instantiated the epsilon-square theorem with Real.sqrt delta and simplified by Real.sq_sqrt." },
    { id := "T2.nyman.concrete.approx.predicate"
      tier := .tier2
      title := "Package the concrete Nyman-Beurling approximation predicate"
      statement :=
        "Define a project-local predicate saying every positive tolerance has a finite fractional-part approximation with concrete squared-error integral below that tolerance, and prove nymanBeurlingKernelDense implies it."
      leanName := some ``nymanBeurlingConcreteApprox_of_dense
      status := .proven
      note := "Loop 106 defined nymanBeurlingConcreteApprox and proved nymanBeurlingKernelDense implies it." },
    { id := "T2.nyman.classical.criterion.inventory"
      tier := .tier2
      title := "Inventory the gap to the classical Nyman-Beurling criterion"
      statement :=
        "Compare nymanBeurlingConcreteApprox with the classical Nyman-Beurling/Baez-Duarte criterion and record the exact formal gaps before attempting an RH bridge."
      leanName := none
      status := .proven
      note := "Loop 107 recorded the first inventory. M0 batches 02-05 rejected the bad local predicates and aligned the positive-natural criterion in real and complex L2(0,infinity), including the full tail, endpoint, closure/tolerance form, and coefficient field. Fixed node M0 is complete." },
    { id := "T2.nyman.restricted.concrete.approx.predicate"
      tier := .tier2
      title := "Package a restricted-parameter concrete approximation predicate"
      statement :=
        "Define a concrete approximation predicate requiring finite coefficient support to lie in 0 < a and a <= 1, and prove it implies nymanBeurlingConcreteApprox."
      leanName := some ``nymanBeurlingConcreteApprox_of_restricted
      status := .proven
      note := "Loop 108 defined the project-local restricted predicate. M0 batch 02 proved its exact local closure equivalence but confirmed it is not Beurling's published space because it lacks the zero-moment condition." },
    { id := "T2.nyman.restricted.span.scaffold"
      tier := .tier2
      title := "Scaffold the restricted-parameter kernel span"
      statement :=
        "Define the submodule generated by fractionalPartKernelL2 a for parameters satisfying 0 < a and a <= 1, and prove it is contained in nymanBeurlingKernelSpan."
      leanName := some ``nymanBeurlingRestrictedKernelSpan_le
      status := .proven
      note := "Loop 109 defined the restricted parameter set, restricted kernel set, restricted kernel span, generator membership, and the inclusion into nymanBeurlingKernelSpan." },
    { id := "T2.nyman.restricted.closure.scaffold"
      tier := .tier2
      title := "Scaffold the restricted-parameter kernel closure"
      statement :=
        "Define the topological closure of nymanBeurlingRestrictedKernelSpan, prove the restricted span lies in it, and prove it is contained in nymanBeurlingKernelClosure."
      leanName := some ``nymanBeurlingRestrictedKernelClosure_le
      status := .proven
      note := "Loop 110 defined nymanBeurlingRestrictedKernelClosure, proved span-to-closure, closedness, the closure coercion formula, inclusion into nymanBeurlingKernelClosure, and restricted generator membership in the closure." },
    { id := "T2.nyman.restricted.density.predicate"
      tier := .tier2
      title := "Package the restricted-parameter kernel density predicate"
      statement :=
        "Define density of nymanBeurlingRestrictedKernelSpan and prove its basic closure-top and pointwise-closure forms."
      leanName := some ``nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure
      status := .proven
      note := "Loop 111 defined nymanBeurlingRestrictedKernelDense and proved its closure-top and pointwise restricted-closure equivalences." },
    { id := "T2.nyman.restricted.density.implies.unrestricted"
      tier := .tier2
      title := "Bridge restricted density to unrestricted density"
      statement :=
        "Prove nymanBeurlingRestrictedKernelDense implies nymanBeurlingKernelDense."
      leanName := some ``nymanBeurlingKernelDense_of_restricted
      status := .proven
      note := "Loop 112 used the pointwise closure forms and nymanBeurlingRestrictedKernelClosure_le to prove restricted density implies unrestricted density." },
    { id := "T2.nyman.restricted.density.concrete.approx"
      tier := .tier2
      title := "Derive concrete approximation from restricted density"
      statement :=
        "Prove nymanBeurlingRestrictedKernelDense implies nymanBeurlingConcreteApprox."
      leanName := some ``nymanBeurlingConcreteApprox_of_restrictedKernelDense
      status := .proven
      note := "Loop 113 composed nymanBeurlingKernelDense_of_restricted with nymanBeurlingConcreteApprox_of_dense to derive the existing concrete approximation predicate from restricted density." },
    { id := "T2.nyman.restricted.density.one.closure"
      tier := .tier2
      title := "Place the constant-one target in the restricted closure"
      statement :=
        "Prove nymanBeurlingRestrictedKernelDense implies unitIntervalOneL2 belongs to nymanBeurlingRestrictedKernelClosure."
      leanName := some ``unitIntervalOneL2_mem_restrictedClosure_of_nymanBeurlingRestrictedKernelDense
      status := .proven
      note := "Loop 114 instantiated the pointwise restricted-closure form of nymanBeurlingRestrictedKernelDense at unitIntervalOneL2." },
    { id := "T2.nyman.restricted.one.closure.epsilon"
      tier := .tier2
      title := "Convert restricted closure membership to epsilon approximation"
      statement :=
        "Prove unitIntervalOneL2 belongs to nymanBeurlingRestrictedKernelClosure iff it can be epsilon-approximated by elements of nymanBeurlingRestrictedKernelSpan."
      leanName := some ``unitIntervalOneL2_mem_restrictedClosure_iff_forall_exists_dist_lt
      status := .proven
      note := "Loop 115 proved the restricted closure epsilon-distance equivalence and the restricted-density approximant existence corollary." },
    { id := "T2.nyman.restricted.span.finite.approx"
      tier := .tier2
      title := "Unpack restricted-span approximants into finite sums"
      statement :=
        "Prove membership in nymanBeurlingRestrictedKernelSpan is equivalent to a finite real linear combination of fractionalPartKernelL2 indexed by restricted parameters."
      leanName := some ``mem_nymanBeurlingRestrictedKernelSpan_iff_exists_finsupp_sum
      status := .proven
      note := "Loop 116 defined restrictedFractionalPartKernelL2, proved the restricted kernel set is its range, and unpacked restricted-span membership into subtype-indexed finite sums." },
    { id := "T2.nyman.restricted.finite.approx.dist"
      tier := .tier2
      title := "Get subtype-indexed finite-sum distance approximants"
      statement :=
        "Assuming nymanBeurlingRestrictedKernelDense and 0 < eps, derive a finite coefficient family over restricted parameters whose packaged finite sum is within eps of unitIntervalOneL2."
      leanName := some ``exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense
      status := .proven
      note := "Loop 117 combined the restricted span epsilon approximant theorem with subtype-indexed finite-sum unpacking." },
    { id := "T2.nyman.restricted.finite.approx.norm"
      tier := .tier2
      title := "Rewrite restricted finite-sum approximation in norm form"
      statement :=
        "Assuming nymanBeurlingRestrictedKernelDense and 0 < eps, derive a subtype-indexed finite coefficient family whose packaged finite-sum difference from unitIntervalOneL2 has norm below eps."
      leanName := some ``exists_restricted_finsupp_sum_norm_sub_lt_of_dense
      status := .proven
      note := "Loop 118 rewrote the restricted finite-sum distance approximation as a norm inequality using dist_eq_norm." },
    { id := "T2.nyman.restricted.finite.approx.integral.inventory"
      tier := .tier2
      title := "Inventory norm-square integral bridge for restricted finite sums"
      statement :=
        "Inspect whether the existing L2 norm-square-to-integral bridge applies to subtype-indexed restricted finite kernel combinations."
      leanName := some ``norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self
      status := .proven
      note := "Loop 119 recorded the inventory and proved the restricted finite-sum specialization of the generic L2 norm-square bridge." },
    { id := "T2.nyman.restricted.finite.approx.representatives"
      tier := .tier2
      title := "Identify restricted finite sums with concrete representatives"
      statement :=
        "Prove almost-everywhere representative theorems for subtype-indexed restricted finite kernel sums and their difference from unitIntervalOneL2."
      leanName := some ``restricted_finsupp_sum_fractionalPartKernelL2_coeFn
      status := .proven
      note := "Loop 120 proved the restricted finite-sum representative bridge, the constant-one difference bridge, and the concrete norm-square integral theorem." },
    { id := "T2.nyman.restricted.finite.approx.integral.epsilon"
      tier := .tier2
      title := "Convert restricted finite approximation into an integral-square bound"
      statement :=
        "Assuming nymanBeurlingRestrictedKernelDense and 0 < eps, derive a subtype-indexed restricted finite coefficient family whose concrete squared-error integral is below eps^2."
      leanName := some ``exists_restricted_finsupp_integral_sq_lt_of_dense
      status := .proven
      note := "Loop 121 combined the restricted norm approximation with the concrete norm-square integral theorem." },
    { id := "T2.nyman.restricted.finite.approx.integral.tolerance"
      tier := .tier2
      title := "Remove the squared tolerance from restricted concrete approximation"
      statement :=
        "Assuming nymanBeurlingRestrictedKernelDense and 0 < delta, derive a subtype-indexed restricted finite coefficient family whose concrete squared-error integral is below delta."
      leanName := some ``exists_restricted_finsupp_integral_lt_of_dense_tolerance
      status := .proven
      note := "Loop 122 instantiated the epsilon-square theorem with Real.sqrt delta to obtain an arbitrary positive tolerance." },
    { id := "T2.nyman.restricted.finite.approx.real.support"
      tier := .tier2
      title := "Push restricted subtype coefficients to real-indexed support"
      statement :=
        "Convert subtype-indexed restricted finite coefficients into real-indexed finite coefficients with support contained in 0 < a and a <= 1, preserving the concrete finite sum."
      leanName := some ``exists_real_finsupp_integral_lt_of_restricted
      status := .proven
      note := "Loop 123 used Finsupp.embDomain along the subtype embedding to push restricted coefficients to real-indexed coefficients with explicit support restriction." },
    { id := "T2.nyman.restricted.concrete.approx.of.dense"
      tier := .tier2
      title := "Derive restricted concrete approximation from restricted density"
      statement :=
        "Prove nymanBeurlingRestrictedConcreteApprox from nymanBeurlingRestrictedKernelDense."
      leanName := some ``nymanBeurlingRestrictedConcreteApprox_of_restrictedKernelDense
      status := .proven
      note := "Loop 124 packaged the subtype positive-tolerance approximation and real-support bridge into the restricted concrete approximation predicate." },
    { id := "T2.nyman.restricted.route.summary"
      tier := .tier2
      title := "Summarize the completed restricted concrete approximation branch"
      statement :=
        "Record the compiled chain from nymanBeurlingRestrictedKernelDense to nymanBeurlingRestrictedConcreteApprox and onward to nymanBeurlingConcreteApprox, with remaining classical criterion gaps."
      leanName := none
      status := .proven
      note := "Loop 125 recorded the local restricted chain. M0 batch 02 corrected the summary by isolating the missing zero-moment/full-line-tail condition." },
    { id := "T2.nyman.baez.duarte.natural.index.inventory"
      tier := .tier2
      title := "Inventory Baez-Duarte natural-parameter indexing"
      statement :=
        "Inspect candidate Lean index types and reciprocal maps for representing Baez-Duarte natural-parameter finite approximants, and choose the next small formal bridge."
      leanName := none
      status := .proven
      note := "Loop 126 recorded research/tier2_nyman_baez_duarte_natural_index_inventory_20260710.md and selected the transparent positive-natural subtype plus reciprocal map as the next bridge shape." },
    { id := "T2.nyman.baez.duarte.reciprocal.map"
      tier := .tier2
      title := "Map positive natural indices to restricted real parameters"
      statement :=
        "Define or verify the reciprocal map from positive natural indices into nymanBeurlingRestrictedParameterSet, preparing the natural-indexed finite-sum bridge."
      leanName := some ``baezDuarteReciprocalEmbedding
      status := .proven
      note := "Loop 127 added baezDuartePositiveNatIndex, verified reciprocal membership in the restricted parameter set, and packaged the map as baezDuarteReciprocalEmbedding." },
    { id := "T2.nyman.baez.duarte.natural.finsupp.bridge"
      tier := .tier2
      title := "Push positive-natural coefficients to restricted parameters"
      statement :=
        "Use baezDuarteReciprocalEmbedding to transport positive-natural-indexed finite coefficients into restricted-parameter coefficients while preserving the concrete reciprocal-parameter finite sum."
      leanName := some ``exists_restricted_finsupp_of_baezDuarte_finsupp
      status := .proven
      note := "Loop 128 used Finsupp.embDomain along baezDuarteReciprocalEmbedding to push positive-natural coefficients to restricted-parameter coefficients while preserving the concrete reciprocal finite sum." },
    { id := "T2.nyman.baez.duarte.natural.integral.bridge"
      tier := .tier2
      title := "Push positive-natural integral bounds to restricted parameters"
      statement :=
        "Use the positive-natural finite-sum bridge to transport a concrete squared-error integral bound from reciprocal natural parameters to restricted-parameter coefficients."
      leanName := some ``exists_restricted_finsupp_integral_lt_of_baezDuarte
      status := .proven
      note := "Loop 129 used the positive-natural finite-sum bridge to transport a reciprocal-natural squared-error integral bound to restricted-parameter coefficients." },
    { id := "T2.nyman.baez.duarte.natural.concrete.approx.predicate"
      tier := .tier2
      title := "Package positive-natural concrete approximation"
      statement :=
        "Define the Baez-Duarte positive-natural concrete approximation predicate and prove that it implies nymanBeurlingRestrictedConcreteApprox."
      leanName := some ``nymanBeurlingRestrictedConcreteApprox_of_baezDuarte
      status := .proven
      note := "Loop 130 defined a local positive-natural predicate. M0 batch 02 found its missing full-line tail; Batch 03 added the separate source-faithful predicate nymanBeurlingBaezDuarteFullLineConcreteApprox. This local target remains only a weak consequence." },
    { id := "T2.nyman.baez.duarte.natural.concrete.approx.unrestricted"
      tier := .tier2
      title := "Forget the Baez-Duarte restriction to the concrete predicate"
      statement :=
        "Prove nymanBeurlingBaezDuarteConcreteApprox implies nymanBeurlingConcreteApprox by composing through nymanBeurlingRestrictedConcreteApprox."
      leanName := some ``nymanBeurlingConcreteApprox_unconditional
      status := .parked
      note := "M0 audit AUDIT-20260710-M0-01 proved the conclusion unconditionally using opposite signed parameters. The implication is obsolete as a criterion target, and the unrestricted predicate must not be used for M1." },
    { id := "T2.burnol.distance.lower-bound"
      tier := .tier2
      title := "Formalize Burnol's Nyman-Beurling distance lower bound"
      statement :=
        "Under RH, formalize Burnol's lower bound liminf D(lambda)*sqrt(log(1/lambda)) >= sqrt(sum_rho m_rho^2/|rho|^2), and transfer it to the natural-subspace liminf of d_N*sqrt(log N)."
      leanName := some ``RiemannHypothesis.baezDuarteNaturalDistance_liminf_ge_fullZeroSum
      status := .proven
      note := "Audit G4-01 fixed source dependencies F0-F5, and batches G4-F0 through G4-F5 are publicly complete. The final theorem uses the full extended nonnegative zero sum, needs no summability or countability premise, and proves the exact RH-conditional natural-distance liminf endpoint. Implementation commit 9edf524877c7fcfd2112d50095eb021f3da12b0a passed public CI run 29352792330. This is known mathematics and a quantitative obstruction, not M2/G3 or unconditional RH progress." },
    { id := "H6.debruijn-newman.h0-xi-bridge"
      tier := .tier2
      title := "Identify the source-normalized de Bruijn-Newman H0 with Riemann xi"
      statement :=
        "For the explicit de Bruijn-Newman kernel Phi and transform H, prove H_0(z) = (1/8) * riemannXi((1 + i*z)/2) for every complex z."
      leanName := some ``deBruijnNewmanH_zero_eq_riemannXi
      status := .proven
      note := "Campaign CAMPAIGN-20260717-H6-H0-XI-BRIDGE-01 closed the theta-Mellin/Poisson, change-of-variables, summation, and integration-by-parts chain with no proof placeholders." },
    { id := "H6.debruijn-newman.heat-evolution"
      tier := .tier2
      title := "Formalize the entire de Bruijn-Newman heat evolution"
      statement :=
        "For every real t, prove that z maps to H_t(z) is entire; justify differentiation in t and twice in z under the defining integral; and prove the backward heat equation d_t H_t(z) = -d_z^2 H_t(z) for every complex z."
      leanName := some ``deBruijnNewmanH_backward_heat_equation
      status := .proven
      note := "Campaign CAMPAIGN-20260717-H6-HEAT-EQUATION-01 proves the source-normalized all-real-time analytic evolution using an explicit double-exponential majorant. This closes the heat-evolution subedge only. The all-real-zero framework, Lambda <= 0, and RH remain open." },
    { id := "H6.debruijn-newman.zero-coordinate-framework"
      tier := .tier2
      title := "Align the time-zero de Bruijn-Newman zero coordinate"
      statement :=
        "Prove the exact bijective coordinate between zeros of H_0 and nontrivial zeta zeros, the strict transformed critical strip, and the equivalence between Mathlib.RiemannHypothesis and all zeros of H_0 being real."
      leanName := some ``deBruijnNewman_zeroCoordinate_framework
      status := .proven
      note := "Campaign CAMPAIGN-20260717-H6-ZERO-COORDINATE-FRAMEWORK-01 compiles the full source coordinate z <-> (1+i*z)/2, its inverse, the strict strip -1<Im(z)<1, and the exact RH/all-real-H_0 equivalence. This closes only the definition-alignment part of H6-H2; forward preservation, threshold existence/closedness, H6-E/G8, and RH remain open." },
    { id := "H6.debruijn-newman.threshold-closedness"
      tier := .tier2
      title := "Prove closedness of the all-real-zero time set"
      statement :=
        "For the exact source-normalized family, prove that the set of real times at which every complex zero of H_t is real is closed, without a simple-zero assumption."
      leanName := some ``isClosed_setOf_deBruijnNewmanAllZerosReal
      status := .proven
      note := "Campaign CAMPAIGN-20260717-H6-THRESHOLD-CLOSEDNESS-01 proves joint time-space continuity, strict positivity at spatial zero, arbitrary-multiplicity zero persistence through Jensen's logarithmic circle mean, and exact closedness. That campaign did not prove forward preservation; H6-H2c now proves it separately. Nonempty upper-time existence, H6-E/G8, and RH remain open." },
    { id := "H6.debruijn-newman.forward-preservation"
      tier := .tier2
      title := "Prove forward preservation of real zeros"
      statement :=
        "For arbitrary real t <= tau, prove that all zeros of H_t being real implies all zeros of H_tau are real, with no extra simplicity, spacing, bounded-time, or nonnegative-time hypothesis."
      leanName := some ``deBruijnNewmanAllZerosReal_mono
      status := .proven
      note := "Campaign CAMPAIGN-20260717-H6-FORWARD-PRESERVATION-01 proves the exact source-normalized two-time implication through order-one Hadamard factorization, de Bruijn vertical-shift averages, scaled cosh heat multipliers, dominated compact-uniform convergence, and Jensen zero persistence. This closes forward preservation only; threshold nonemptiness, H6-E/G8, W2/G7, M2/G3, and RH remain open." },
    { id := "H6.debruijn-newman.upper-half"
      tier := .tier2
      title := "Prove de Bruijn's half-time upper bound"
      statement :=
        "For every 0 <= t <= 1/2, prove every zero of the exact source-normalized H_t satisfies Im(z)^2 <= 1-2*t, and deduce unconditionally that every zero of H_(1/2) is real."
      leanName := some ``deBruijnNewmanAllZerosReal_one_half
      status := .proven
      note := "Campaign CAMPAIGN-20260717-H6-UPPER-HALF-01 reconstructs de Bruijn's strip contraction through conjugation-preserving multiplicities, paired genus-one factors, finite vertical-average iteration, and Jensen zero persistence. This proves threshold nonemptiness and Lambda <= 1/2 only; H6-E/G8, W2/G7, M2/G3, and RH remain open." },
    { id := "H6.debruijn-newman.zero-dynamics-force"
      tier := .tier2
      title := "Formalize the divisor-regularized simple-zero force law"
      statement :=
        "Prove absolute summability of the genus-one divisor force, identify it with H_t''/(2*H_t') at every simple zero, and derive x'(t)=2*force along every differentiable simple-zero path."
      leanName := some ``deBruijnNewman_simpleZeroPath_velocity
      status := .proven
      note := "Campaign PROOF-ATTEMPT-20260717-H6-ZERO-DYNAMICS-01 proves the known source force interface through multiplicity-aware Hadamard fiber removal, joint strict Frechet differentiation, and the backward heat equation. This is route infrastructure only: collision exclusion, H6-E/G8, and RH remain open." },
    { id := "H6.debruijn-newman.local-zero-trajectories"
      tier := .tier2
      title := "Construct local real simple-zero trajectories"
      statement :=
        "Prove that every simple real zero extends to a locally unique differentiable real zero path, that two distinct such paths remain locally ordered, and that their real squared gap obeys the exact pair-removed regularized-force evolution law with mutual repulsion constant 8."
      leanName := some ``exists_deBruijnNewman_localRealSimpleZeroPath
      status := .proven
      note := "Campaign PROOF-ATTEMPT-20260717-H6-ZERO-DYNAMICS-01 applies the product-domain real implicit-function theorem to the jointly strict-differentiable source family; conjugation and local uniqueness force real-valuedness. The compiled pair-force decomposition removes both complete simple-zero fibers, proves the remainder absolutely convergent, and isolates the remaining global obstacle as theta-specific control of that remainder over all relevant zero pairs and heights. This is route infrastructure, not collision exclusion or RH progress." },
    { id := "H6.audit.adjacent-gap-eight-sharp"
      tier := .tier2
      title := "Audit sharpness of the adjacent squared-gap velocity bound"
      statement :=
        "Prove that adjacent real simple-zero paths satisfy (gap^2)' <= 8 and its integrated backward lower bound, then construct exact quadratic backward-heat pairs that collide after terminal gap squared divided by eight and within every proposed positive uniform interval."
      leanName := some ``exists_h6GapAuditHeatPolynomial_collision_within
      status := .proven
      note := "Campaign PROOF-ATTEMPT-20260717-H6-ZERO-DYNAMICS-01 proves the adjacent-pair remainder is nonpositive and integrates the resulting sharp velocity bound. The quadratic audit shows this generic mechanism cannot yield a height-uniform backward continuation interval. It eliminates only the generic adjacent-gap branch; theta-specific control, H6-E/G8, and RH remain open." },
    { id := "H6.audit.reverse-heat-li-transfer"
      tier := .tier2
      title := "Falsify generic reverse-heat Li transfer"
      statement :=
        "Construct an entire reflection-symmetric polynomial heat family, nonzero at the Li base point for all nonnegative real times, whose time-one zeros all lie on the critical line but whose time-zero second Li value is negative."
      leanName := some ``h6AuditHeatXiQuadratic_falsifies_reverseLiTransfer
      status := .proven
      note := "Audit AUDIT-20260717-H6-REVERSE-HEAT-LI-01 gives a degree-two exact countermodel. It eliminates only a generic backward-transfer mechanism; the actual de Bruijn-Newman theta family, H6-E/G8, and RH remain open." },
    { id := "H6.debruijn-newman.heat-li-first-two"
      tier := .tier2
      title := "Prove the first two heat-family Li moment inequalities"
      statement :=
        "For every real heat time, identify the first two Li differential expressions of 8*H_t(-i*(2*s-1)) with explicit positive hyperbolic moments, prove the weighted Cauchy-Schwarz bound B(t)^2 <= A(t)*C(t), and deduce that both expressions are positive real numbers."
      leanName := some ``deBruijnNewmanHeat_firstTwoLi_endpoint
      status := .proven
      note := "Campaign PROOF-ATTEMPT-20260717-H6-HEAT-LI-MOMENTS-01 proves the theta-specific all-real-time endpoint. The proof derives exact values F_t(1)=8A, F_t'(1)=16B, F_t''(1)=32C and proves B^2<=AC by integrating the nonnegative square W(A*u*tanh(u)-B)^2. This is a finite-index positive-kernel theorem and is strictly weaker than the all-index Li criterion equivalent to RH. Implementation commit 2bc304e9fe2473519c398269b26b0b06b715e593 passed public Lean Action CI run 29541314279, build job 87763968249; evidence commit 1a7d3d6d8ef08e7726aeb8dff261372822d49b6e passed run 29541519607, job 87764575644." },
    { id := "H6.audit.positive-cosh-li3"
      tier := .tier2
      title := "Falsify generic all-order positive-kernel Li extrapolation"
      statement :=
        "Construct an entire reflection-symmetric positive two-atom cosh transform, normalized at s=1, whose standard first two Li differential expressions are positive real numbers but whose third is a negative real number."
      leanName := some ``h6PositiveCoshAudit_falsifies_allOrder_positiveKernelLi
      status := .proven
      note := "Audit AUDIT-20260717-H6-POSITIVE-COSH-LI3-01 uses atoms at log 2 and 10*log 2 with normalized masses 1/8 and 7/8. Exact hyperbolic values and Mathlib's certified rational interval for log 2 prove the (+,+,-) sign pattern. This eliminates only a generic positive-kernel/Hankel extrapolation from the first-two theta moment theorem; the actual theta kernel, H6-E/G8, W2/G7, M2/G3, and RH remain open. Implementation commit 5fdfc5c7437349735c57552a75838f16b4d63f5e passed public CI run 29543145545, job 87769424525; evidence commit 61ce528793a9fc04e4a6b26ba83463cf0557bafc passed run 29543336971, job 87770059112." },
    { id := "H6.discovery.theta-third-li-covariance"
      tier := .tier2
      title := "Prove the theta-family third Li coefficient by covariance"
      statement :=
        "Extend the exact source-normalized heat family through its fourth hyperbolic moment, prove B(t)*C(t) <= A(t)*D(t), derive the exact third Li differential expression, identify its time-zero value with liCoefficientCandidate 2, and prove that candidate is positive real."
      leanName := some ``deBruijnNewmanHeat_thirdLi_covariance_endpoint
      status := .proven
      note := "Campaign DISCOVERY-20260717-H6-THIRD-LI-COVARIANCE-01 proves the theta-specific ordered covariance using the nonnegative one-integral certificate W(u)*(X(u)-X(r))*(u^2-C/A), then combines it with B^2<=AC and the compiled bound liCoefficientCandidate_zero_re_lt_one. The resulting candidate-two sign is an unconditional finite necessary condition for RH; hard_gap_delta=0 and route_infrastructure_delta=1. Implementation commit 1b521686d4e8561f01ba98a6ceaa4905ced4d92f passed public CI run 29545583372, build job 87777066173; evidence commit abf5ebf19e3636662a45eed7a5eff9e947c3c3b4 passed run 29545784893, job 87777708775." },
    { id := "H10.function-field.finite-spectral-rigidity"
      tier := .tier2
      title := "Formalize finite power-sum spectral rigidity"
      statement :=
        "Prove that an all-power aggregate bound on a finite complex spectrum controls every spectral radius, and that reciprocal functional-equation pairing forces the exact square-root critical circle."
      leanName := some ``norm_eq_sqrt_of_powerSum_bound_and_reciprocal
      status := .proven
      note := "Campaign CAMPAIGN-20260717-H10-FINITE-SPECTRAL-RIGIDITY-01 formalizes the final finite-spectral step in function-field RH using simultaneous phase recurrence. It assumes the aggregate point-count-scale bound and reciprocal pairing; it does not construct them for curves or transfer them to the infinite number-field zero divisor." },
    { id := "T3.rh.goal"
      tier := .tier3
      title := "Riemann Hypothesis"
      statement :=
        "Prove or disprove mathlib's RiemannHypothesis without adding nonstandard axioms."
      leanName := some ``riemannHypothesis_iff_nontrivial_zeros_on_line
      status := .inProgress
      note := "RH is the active project goal under V4.1 and may be attacked directly or through any valuable unresolved dependency." } ]

/-- Targets that still require work before they can be considered discharged. -/
def openRhTargets : List ResearchTarget :=
  rhTargets.filter (fun target => target.status != .proven)

/-- Tier 1 targets that should be preferred before structural route selection. -/
def tierOneRhTargets : List ResearchTarget :=
  rhTargets.filter (fun target => target.tier == .tier1)

end LeanLab.Riemann
