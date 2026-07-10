import LeanLab.Riemann.BaezDuarteConvergence

set_option linter.style.header false

/-!
# Trusted-dependency audit for fixed-gap RH work

The build log for this module must list only Lean's standard extensionality, choice, and quotient
principles for each theorem below.
-/

#print axioms riemannZeta_eq_zetaAbelContinuationFormula
#print axioms LeanLab.Riemann.riemannZeta_eq_zetaAbelContinuationFormula_of_re_pos
#print axioms LeanLab.Riemann.hasMellin_fractionalPartKernel_one
#print axioms LeanLab.Riemann.hasMellin_baezDuarteKernel
#print axioms LeanLab.Riemann.expNeg_quasiMeasurePreserving
#print axioms LeanLab.Riemann.eLpNorm_weightedLogForwardFun
#print axioms LeanLab.Riemann.weightedLogForward_inverse
#print axioms LeanLab.Riemann.weightedLogPullback_coeFn
#print axioms LeanLab.Riemann.weightedLogPullback_symm_coeFn
#print axioms LeanLab.Riemann.norm_baezDuarteFourierMellinL2
#print axioms LeanLab.Riemann.mellin_criticalLine_eq_fourier
#print axioms LeanLab.Riemann.baezDuarteVerticalMajorant_memLp
#print axioms LeanLab.Riemann.baezDuarteCriticalLineZetaZeroOrdinates_countable
#print axioms LeanLab.Riemann.ae_tendsto_baezDuarteZetaRatio_one
