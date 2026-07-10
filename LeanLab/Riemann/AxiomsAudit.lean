import LeanLab.Riemann.BaezDuarteMellin

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
