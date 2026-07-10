import LeanLab.Riemann.BaezDuarteZetaRatio

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
#print axioms LeanLab.Riemann.baezDuarteMobiusApprox_two_mul_eq_dirichletTail_of_one_lt
#print axioms LeanLab.Riemann.baezDuarte_weightedTail_norm_sq_le
#print axioms LeanLab.Riemann.tendsto_norm_zero_of_baezDuarte_weightedTail
#print axioms LeanLab.Riemann.baezDuarte_finsupp_norm_sq_le_of_weighted
#print axioms Complex.exists_norm_digamma_le_log
#print axioms LeanLab.Riemann.exists_norm_Gamma_div_le_rpow_of_re_mem_Icc
#print axioms LeanLab.Riemann.exists_norm_baezDuarteZetaRatio_le_rpow
#print axioms LeanLab.Riemann.exists_baezDuarteZetaRatio_bound
#print axioms LeanLab.Riemann.exists_baezDuarteZetaRatioIntegrand_majorant
