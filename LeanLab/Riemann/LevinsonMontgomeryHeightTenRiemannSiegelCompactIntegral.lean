import LeanLab.Riemann.LevinsonMontgomeryHeightTenRiemannSiegelEndpointMass
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false

/-!
# Exact compact integration for the height-ten Riemann--Siegel endpoint masses

The retained principal argument and quartic denominator correction are replaced by explicit
rational polynomial envelopes on `0 <= v <= 1/2`. Their formal antiderivatives give rational
bounds for the two actual compact endpoint integrals.
-/

open Complex Filter Finset MeasureTheory Real Set

namespace LeanLab.Riemann

noncomputable section

def heightTenPositiveCompactExponent (v : ℝ) : ℝ :=
  (361 / 100 : ℝ) * v - (2063 / 450) * v ^ 2 - (13 / 36) * v ^ 3

theorem heightTenPositiveCompactExponent_range {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    0 ≤ heightTenPositiveCompactExponent v ∧ heightTenPositiveCompactExponent v ≤ 7 / 10 := by
  dsimp [heightTenPositiveCompactExponent]
  constructor
  · have hvSq : v ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [sq_nonneg v]
    have hbracket :
        0 ≤ (361 / 100 : ℝ) - (2063 / 450) * v - (13 / 36) * v ^ 2 := by
      nlinarith
    nlinarith [mul_nonneg hv0 hbracket]
  · let r : ℝ := 3 / 8
    let tangent : ℝ :=
      ((361 / 100 : ℝ) * r - (2063 / 450) * r ^ 2 - (13 / 36) * r ^ 3) +
        ((361 / 100 : ℝ) - 2 * (2063 / 450) * r - 3 * (13 / 36) * r ^ 2) *
          (v - r)
    have hidentity :
        tangent -
            ((361 / 100 : ℝ) * v - (2063 / 450) * v ^ 2 - (13 / 36) * v ^ 3) =
          (v - r) ^ 2 * ((2063 / 450 : ℝ) + (13 / 36) * (v + 2 * r)) := by
      dsimp [tangent, r]
      ring_nf
    have htan :
        (361 / 100 : ℝ) * v - (2063 / 450) * v ^ 2 - (13 / 36) * v ^ 3 ≤
          tangent := by
      have hnonneg :
          0 ≤ tangent -
            ((361 / 100 : ℝ) * v - (2063 / 450) * v ^ 2 - (13 / 36) * v ^ 3) := by
        rw [hidentity]
        positivity
      linarith
    have htanUpper : tangent ≤ 7 / 10 := by
      dsimp [tangent, r]
      nlinarith
    exact htan.trans htanUpper

theorem exp_le_heightTenPositivePolynomial_of_range {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 7 / 10) :
    Real.exp q ≤ (1 + q / 4 + (40 / 73 : ℝ) * (q / 4) ^ 2) ^ 4 := by
  let y := q / 4
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy1 : y ≤ 7 / 40 := by dsimp [y]; linarith
  have hy2 : y < 2 := by linarith
  have hpade := Real.exp_le_two_add_div_two_sub hy0 hy2
  have hden : 0 < 2 - y := by linarith
  have hpoly : (2 + y) / (2 - y) ≤ 1 + y + (40 / 73 : ℝ) * y ^ 2 := by
    rw [div_le_iff₀ hden]
    have hySq : 0 ≤ y ^ 2 := sq_nonneg y
    nlinarith [mul_nonneg hySq (sub_nonneg.mpr hy1)]
  have hone : 0 ≤ Real.exp y := Real.exp_nonneg _
  have htwo : 0 ≤ 1 + y + (40 / 73 : ℝ) * y ^ 2 := by positivity
  have hpow := pow_le_pow_left₀ hone (hpade.trans hpoly) 4
  rw [← Real.exp_nat_mul] at hpow
  have hqy : (4 : ℝ) * y = q := by dsimp [y]; ring
  norm_num at hpow
  rw [hqy] at hpow
  simpa only [y] using hpow

theorem exp_neg_le_heightTenFourthQuadraticPolynomial (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ (1 - t / 4 + (t / 4) ^ 2 / 2) ^ 4 := by
  let y := t / 4
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hquad : Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
    have hlower := Real.quadratic_le_exp_of_nonneg hy
    have hleftPos : 0 < 1 + y + y ^ 2 / 2 := by positivity
    have hright : 0 ≤ 1 - y + y ^ 2 / 2 := by nlinarith [sq_nonneg (y - 1)]
    calc
      Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
      _ = 1 / Real.exp y := by rw [one_div]
      _ ≤ 1 / (1 + y + y ^ 2 / 2) :=
        one_div_le_one_div_of_le hleftPos hlower
      _ ≤ 1 - y + y ^ 2 / 2 := by
        rw [div_le_iff₀ hleftPos]
        nlinarith [sq_nonneg y]
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hquad 4
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow
  have hty : -(4 * y) = -t := by dsimp [y]; ring
  rw [hty] at hpow
  simpa only [y] using hpow

def heightTenPositiveCompactPolynomialEnvelope (v : ℝ) : ℝ :=
  ((1633 / 2000 : ℝ) + (197 / 1000) * v) *
    (1 + heightTenPositiveCompactExponent v / 4 +
      (40 / 73 : ℝ) * (heightTenPositiveCompactExponent v / 4) ^ 2) ^ 4 *
    ((1 / 2 : ℝ) *
      (1 - (29 / 100) * (2 / 3) * (111 / 50 : ℝ) ^ 4 * v ^ 4))

open Polynomial in
def heightTenPositiveCompactEnvelopePolynomial : ℝ[X] :=
  C (1633 / 4000 : ℝ) * X ^ 0 +
  C (628913 / 400000 : ℝ) * X ^ 1 +
  C (253956116563 / 210240000000 : ℝ) * X ^ 2 +
  C (-155011832497999 / 42048000000000 : ℝ) * X ^ 3 +
  C (-9458508442697446238183 / 1105021440000000000000 : ℝ) * X ^ 4 +
  C (-11853913677524176789331 / 2302128000000000000000 : ℝ) * X ^ 5 +
  C (5673659589719367374668052683 / 907498857600000000000000000 : ℝ) * X ^ 6 +
  C (447748747983056896057805222327 / 22687471440000000000000000000 : ℝ) * X ^ 7 +
  C (113849554992258346694371974811814771 /
    5962267494432000000000000000000000 : ℝ) * X ^ 8 +
  C (-7441071839446105789589956369667309 /
    465802148002500000000000000000000 : ℝ) * X ^ 9 +
  C (-128176645088250256600851004087448023357 /
    2683020372494400000000000000000000000 : ℝ) * X ^ 10 +
  C (-10301265128941272638694588931415590537 /
    1490566873608000000000000000000000000 : ℝ) * X ^ 11 +
  C (255699136292655817538428926222158797971041 /
    4829436670489920000000000000000000000000 : ℝ) * X ^ 12 +
  C (57264396662487487665078523803405452789153 /
    2414718335244960000000000000000000000000 : ℝ) * X ^ 13 +
  C (-12656837689890131993683050462276546612589 /
    339569765893822500000000000000000000000 : ℝ) * X ^ 14 +
  C (-22427561947995976672896923860815335299889 /
    1086623250860232000000000000000000000000 : ℝ) * X ^ 15 +
  C (1757181757135220522010439300207434657578027 /
    97796092577420880000000000000000000000000 : ℝ) * X ^ 16 +
  C (77436028244856857948661502695258962302957 /
    8149674381451740000000000000000000000000 : ℝ) * X ^ 17 +
  C (-51126495806343339116656761220473194695873 /
    8149674381451740000000000000000000000000 : ℝ) * X ^ 18 +
  C (-9086115175868017008862753219809736273879 /
    5433116254301160000000000000000000000000 : ℝ) * X ^ 19 +
  C (10270506282195589073292445289493326037989 /
    13039479010322784000000000000000000000000 : ℝ) * X ^ 20 +
  C (7921659138567574353688827106896118030219 /
    32598697525806960000000000000000000000000 : ℝ) * X ^ 21 +
  C (-844449383846673376546343133521694907 /
    40748371907258700000000000000000000000 : ℝ) * X ^ 22 +
  C (-472318706895696983969660765728948621 /
    26078958020645568000000000000000000000 : ℝ) * X ^ 23 +
  C (-7324091108109432291048376248951067 /
    2086316641651645440000000000000000000 : ℝ) * X ^ 24 +
  C (-2289594795412140917387365782259 /
    6258949924954936320000000000000000 : ℝ) * X ^ 25 +
  C (-1430311587807144530660185637 /
    61816789382270976000000000000000 : ℝ) * X ^ 26 +
  C (-138000079906173775206683 /
    154541973455677440000000000000 : ℝ) * X ^ 27 +
  C (-15387692708838936953207 /
    791254904093068492800000000000 : ℝ) * X ^ 28 +
  C (-8734095550809862753 /
    47475294245584109568000000000 : ℝ) * X ^ 29

open Polynomial in
def heightTenPositiveCompactEnvelopePrimitive : ℝ[X] :=
  C (1633 / 4000 : ℝ) * X ^ 1 +
  C (628913 / 800000 : ℝ) * X ^ 2 +
  C (253956116563 / 630720000000 : ℝ) * X ^ 3 +
  C (-155011832497999 / 168192000000000 : ℝ) * X ^ 4 +
  C (-9458508442697446238183 / 5525107200000000000000 : ℝ) * X ^ 5 +
  C (-11853913677524176789331 / 13812768000000000000000 : ℝ) * X ^ 6 +
  C (5673659589719367374668052683 / 6352492003200000000000000000 : ℝ) * X ^ 7 +
  C (447748747983056896057805222327 / 181499771520000000000000000000 : ℝ) * X ^ 8 +
  C (113849554992258346694371974811814771 /
    53660407449888000000000000000000000 : ℝ) * X ^ 9 +
  C (-7441071839446105789589956369667309 /
    4658021480025000000000000000000000 : ℝ) * X ^ 10 +
  C (-128176645088250256600851004087448023357 /
    29513224097438400000000000000000000000 : ℝ) * X ^ 11 +
  C (-10301265128941272638694588931415590537 /
    17886802483296000000000000000000000000 : ℝ) * X ^ 12 +
  C (255699136292655817538428926222158797971041 /
    62782676716368960000000000000000000000000 : ℝ) * X ^ 13 +
  C (57264396662487487665078523803405452789153 /
    33806056693429440000000000000000000000000 : ℝ) * X ^ 14 +
  C (-12656837689890131993683050462276546612589 /
    5093546488407337500000000000000000000000 : ℝ) * X ^ 15 +
  C (-22427561947995976672896923860815335299889 /
    17385972013763712000000000000000000000000 : ℝ) * X ^ 16 +
  C (1757181757135220522010439300207434657578027 /
    1662533573816154960000000000000000000000000 : ℝ) * X ^ 17 +
  C (77436028244856857948661502695258962302957 /
    146694138866131320000000000000000000000000 : ℝ) * X ^ 18 +
  C (-2690868200333859953508250590551220773467 /
    8149674381451740000000000000000000000000 : ℝ) * X ^ 19 +
  C (-9086115175868017008862753219809736273879 /
    108662325086023200000000000000000000000000 : ℝ) * X ^ 20 +
  C (10270506282195589073292445289493326037989 /
    273829059216778464000000000000000000000000 : ℝ) * X ^ 21 +
  C (7921659138567574353688827106896118030219 /
    717171345567753120000000000000000000000000 : ℝ) * X ^ 22 +
  C (-844449383846673376546343133521694907 /
    937212553866950100000000000000000000000 : ℝ) * X ^ 23 +
  C (-472318706895696983969660765728948621 /
    625894992495493632000000000000000000000 : ℝ) * X ^ 24 +
  C (-7324091108109432291048376248951067 /
    52157916041291136000000000000000000000 : ℝ) * X ^ 25 +
  C (-176122676570164685952874290943 /
    12517899849909872640000000000000000 : ℝ) * X ^ 26 +
  C (-1430311587807144530660185637 /
    1669053313321316352000000000000000 : ℝ) * X ^ 27 +
  C (-138000079906173775206683 /
    4327175256758968320000000000000 : ℝ) * X ^ 28 +
  C (-530610093408239205283 /
    791254904093068492800000000000 : ℝ) * X ^ 29 +
  C (-8734095550809862753 /
    1424258827367523287040000000000 : ℝ) * X ^ 30

open Polynomial in
theorem derivative_C_mul_X_pow_succ_heightTen (a : ℝ) (n : ℕ) :
    (C a * X ^ (n + 1)).derivative = C (a * (n + 1 : ℝ)) * X ^ n := by
  rw [Polynomial.derivative_C_mul_X_pow, Nat.add_sub_cancel]
  norm_num [Nat.cast_add]

open Polynomial in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
-- Normalize the thirty exact rational derivative coefficients in one kernel-checked step.
theorem derivative_heightTenPositiveCompactEnvelopePrimitive :
    heightTenPositiveCompactEnvelopePrimitive.derivative =
      heightTenPositiveCompactEnvelopePolynomial := by
  simp only [heightTenPositiveCompactEnvelopePrimitive,
    heightTenPositiveCompactEnvelopePolynomial,
    Polynomial.derivative_add, derivative_C_mul_X_pow_succ_heightTen]
  norm_num

theorem heightTenPositiveCompactEnvelopePolynomial_eval (v : ℝ) :
    heightTenPositiveCompactEnvelopePolynomial.eval v =
      heightTenPositiveCompactPolynomialEnvelope v := by
  simp only [heightTenPositiveCompactEnvelopePolynomial,
    heightTenPositiveCompactPolynomialEnvelope, heightTenPositiveCompactExponent,
    Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring_nf

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Evaluate the degree-thirty rational primitive exactly at both compact endpoints.
theorem integral_heightTenPositiveCompactPolynomialEnvelope_le_sevenTwentieths :
    (∫ v in (0 : ℝ)..(1 / 2), heightTenPositiveCompactPolynomialEnvelope v) ≤ 7 / 20 := by
  simp_rw [← heightTenPositiveCompactEnvelopePolynomial_eval]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => by simpa only [derivative_heightTenPositiveCompactEnvelopePrimitive] using
      heightTenPositiveCompactEnvelopePrimitive.hasDerivAt x)
    (heightTenPositiveCompactEnvelopePolynomial.differentiable.continuous.intervalIntegrable
      (μ := volume) (0 : ℝ) (1 / 2))]
  norm_num [heightTenPositiveCompactEnvelopePrimitive]

def heightTenNegativeCompactDecayExponent (x : ℝ) : ℝ :=
  (39 / 20 : ℝ) * x + (28849 / 6000) * x ^ 2

def heightTenNegativeCompactPolynomialEnvelope (x : ℝ) : ℝ :=
  (1633 / 2000 : ℝ) *
    (1 - heightTenNegativeCompactDecayExponent x / 4 +
      (heightTenNegativeCompactDecayExponent x / 4) ^ 2 / 2) ^ 4 *
    ((1 / 2 : ℝ) *
      (1 - (29 / 100) * (2 / 3) * (111 / 50 : ℝ) ^ 4 * x ^ 4))

open Polynomial in
def heightTenNegativeCompactEnvelopePolynomial : ℝ[X] :=
  C (1633 / 4000 : ℝ) * X ^ 0 +
  C (-63687 / 80000 : ℝ) * X ^ 1 +
  C (-56963939 / 48000000 : ℝ) * X ^ 2 +
  C (17176235297 / 5120000000 : ℝ) * X ^ 3 +
  C (-23078037528926831 / 46080000000000000 : ℝ) * X ^ 4 +
  C (-616818846337343923 / 204800000000000000 : ℝ) * X ^ 5 +
  C (5474201978156036268421 / 1105920000000000000000 : ℝ) * X ^ 6 +
  C (-856078945500047009704483 / 117964800000000000000000 : ℝ) * X ^ 7 +
  C (-23289303106660526795914368719 /
    3397386240000000000000000000 : ℝ) * X ^ 8 +
  C (13831568470779377169934205123 /
    566231040000000000000000000 : ℝ) * X ^ 9 +
  C (3253792853275666929523619773373 /
    1019215872000000000000000000000 : ℝ) * X ^ 10 +
  C (-201377589277204816639615279050691 /
    5662310400000000000000000000000 : ℝ) * X ^ 11 +
  C (65851103423158938640170951882334471 /
    61152952320000000000000000000000000 : ℝ) * X ^ 12 +
  C (132319592473880483773197710324770553 /
    4076863488000000000000000000000000 : ℝ) * X ^ 13 +
  C (-54398796287782948730942527688006852683 /
    36691771392000000000000000000000000000 : ℝ) * X ^ 14 +
  C (-12224429603389907082705452825336368597979 /
    611529523200000000000000000000000000000 : ℝ) * X ^ 15 +
  C (-1930747037841372264063157835170766461923071 /
    4403012567040000000000000000000000000000000 : ℝ) * X ^ 16 +
  C (14941980219456306155663292923195225194283 /
    1887436800000000000000000000000000000000 : ℝ) * X ^ 17 +
  C (3637188821671843827537849007396728353848099 /
    3397386240000000000000000000000000000000000 : ℝ) * X ^ 18 +
  C (-19188886633468050326336915022255079151492249 /
    11324620800000000000000000000000000000000000 : ℝ) * X ^ 19 +
  C (-42583091576070752604961050882848982957030760877 /
    81537269760000000000000000000000000000000000000 : ℝ) * X ^ 20

open Polynomial in
def heightTenNegativeCompactEnvelopePrimitive : ℝ[X] :=
  C (1633 / 4000 : ℝ) * X ^ 1 +
  C (-63687 / 160000 : ℝ) * X ^ 2 +
  C (-56963939 / 144000000 : ℝ) * X ^ 3 +
  C (17176235297 / 20480000000 : ℝ) * X ^ 4 +
  C (-23078037528926831 / 230400000000000000 : ℝ) * X ^ 5 +
  C (-616818846337343923 / 1228800000000000000 : ℝ) * X ^ 6 +
  C (5474201978156036268421 / 7741440000000000000000 : ℝ) * X ^ 7 +
  C (-856078945500047009704483 / 943718400000000000000000 : ℝ) * X ^ 8 +
  C (-23289303106660526795914368719 /
    30576476160000000000000000000 : ℝ) * X ^ 9 +
  C (13831568470779377169934205123 /
    5662310400000000000000000000 : ℝ) * X ^ 10 +
  C (295799350297787902683965433943 /
    1019215872000000000000000000000 : ℝ) * X ^ 11 +
  C (-201377589277204816639615279050691 /
    67947724800000000000000000000000 : ℝ) * X ^ 12 +
  C (65851103423158938640170951882334471 /
    794988380160000000000000000000000000 : ℝ) * X ^ 13 +
  C (132319592473880483773197710324770553 /
    57076088832000000000000000000000000 : ℝ) * X ^ 14 +
  C (-54398796287782948730942527688006852683 /
    550376570880000000000000000000000000000 : ℝ) * X ^ 15 +
  C (-12224429603389907082705452825336368597979 /
    9784472371200000000000000000000000000000 : ℝ) * X ^ 16 +
  C (-113573355167139544944891637362986262466063 /
    4403012567040000000000000000000000000000000 : ℝ) * X ^ 17 +
  C (14941980219456306155663292923195225194283 /
    33973862400000000000000000000000000000000 : ℝ) * X ^ 18 +
  C (3637188821671843827537849007396728353848099 /
    64550338560000000000000000000000000000000000 : ℝ) * X ^ 19 +
  C (-19188886633468050326336915022255079151492249 /
    226492416000000000000000000000000000000000000 : ℝ) * X ^ 20 +
  C (-42583091576070752604961050882848982957030760877 /
    1712282664960000000000000000000000000000000000000 : ℝ) * X ^ 21

open Polynomial in
theorem derivative_heightTenNegativeCompactEnvelopePrimitive :
    heightTenNegativeCompactEnvelopePrimitive.derivative =
      heightTenNegativeCompactEnvelopePolynomial := by
  simp only [heightTenNegativeCompactEnvelopePrimitive,
    heightTenNegativeCompactEnvelopePolynomial,
    Polynomial.derivative_add, derivative_C_mul_X_pow_succ_heightTen]
  norm_num

theorem heightTenNegativeCompactEnvelopePolynomial_eval (x : ℝ) :
    heightTenNegativeCompactEnvelopePolynomial.eval x =
      heightTenNegativeCompactPolynomialEnvelope x := by
  simp only [heightTenNegativeCompactEnvelopePolynomial,
    heightTenNegativeCompactPolynomialEnvelope, heightTenNegativeCompactDecayExponent,
    Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring_nf

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Evaluate the degree-twenty-one rational primitive exactly at both compact endpoints.
theorem integral_heightTenNegativeCompactPolynomialEnvelope_le_oneTenth :
    (∫ x in (0 : ℝ)..(1 / 2), heightTenNegativeCompactPolynomialEnvelope x) ≤ 1 / 10 := by
  simp_rw [← heightTenNegativeCompactEnvelopePolynomial_eval]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => by simpa only [derivative_heightTenNegativeCompactEnvelopePrimitive] using
      heightTenNegativeCompactEnvelopePrimitive.hasDerivAt x)
    (heightTenNegativeCompactEnvelopePolynomial.differentiable.continuous.intervalIntegrable
      (μ := volume) (0 : ℝ) (1 / 2))]
  norm_num [heightTenNegativeCompactEnvelopePrimitive]

theorem heightTen_actualCompactDenominatorFactor_le_rational
    (v : ℝ) :
    (1 / 2 : ℝ) *
        (1 - (29 / 100) * (2 / 3) *
          (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im) ^ 4) ≤
      (1 / 2 : ℝ) *
        (1 - (29 / 100) * (2 / 3) * (111 / 50 : ℝ) ^ 4 * v ^ 4) := by
  have hcoeff := oneHundredEleven_div_fifty_le_pi_mul_sqrtTwoHalf
  have hpow :
      (111 / 50 : ℝ) ^ 4 ≤ (Real.pi * (Real.sqrt 2 / 2)) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hcoeff 4
  have hvpow : 0 ≤ v ^ 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hpow hvpow
  have him :
      (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im) ^ 4 =
        (Real.pi * (Real.sqrt 2 / 2)) ^ 4 * v ^ 4 := by
    rw [deBruijnNewmanRiemannSiegelLine_im]
    ring_nf
  rw [him]
  nlinarith

theorem norm_heightTenRiemannSiegelLineIntegrand_one_positiveCompact_le_polynomial
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖ ≤
      heightTenPositiveCompactPolynomialEnvelope v := by
  let q := heightTenPositiveCompactExponent v
  let A : ℝ :=
    (1 / 2 : ℝ) *
      (1 - (29 / 100) * (2 / 3) *
        (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im) ^ 4)
  let R : ℝ :=
    (1 / 2 : ℝ) *
      (1 - (29 / 100) * (2 / 3) * (111 / 50 : ℝ) ^ 4 * v ^ 4)
  let d : ℝ := (1633 / 2000 : ℝ) + (197 / 1000) * v
  let P : ℝ := (1 + q / 4 + (40 / 73 : ℝ) * (q / 4) ^ 2) ^ 4
  have hpoint :=
    norm_heightTenRiemannSiegelLineIntegrand_one_positiveCompact_le hv0 hv1
  have hq := heightTenPositiveCompactExponent_range hv0 hv1
  have hexp : Real.exp q ≤ P := by
    simpa only [P] using exp_le_heightTenPositivePolynomial_of_range hq.1 hq.2
  have hA : 0 ≤ A := by
    have hden := one_div_norm_deBruijnNewmanRiemannSiegelDenominator_compact_le
      (v := v) (by simpa [abs_of_nonneg hv0] using hv1)
    have hrecip : 0 ≤ 1 /
        ‖deBruijnNewmanRiemannSiegelDenominator
          (deBruijnNewmanRiemannSiegelLine 1 v)‖ := by positivity
    exact hrecip.trans (by simpa only [A] using hden)
  have hAR : A ≤ R := by
    simpa only [A, R] using heightTen_actualCompactDenominatorFactor_le_rational v
  have hR : 0 ≤ R := hA.trans hAR
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hP : 0 ≤ P := (Real.exp_nonneg q).trans hexp
  calc
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖ ≤
        d * Real.exp q * A := by
      simpa only [d, q, A, heightTenPositiveCompactExponent] using hpoint
    _ ≤ d * P * R := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hexp hd) hAR hA
        (mul_nonneg hd hP)
    _ = heightTenPositiveCompactPolynomialEnvelope v := by
      dsimp [d, P, R, q, heightTenPositiveCompactPolynomialEnvelope]

theorem norm_heightTenRiemannSiegelLineIntegrand_one_negativeCompact_le_polynomial
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 10) (-x)‖ ≤
      heightTenNegativeCompactPolynomialEnvelope x := by
  let t := heightTenNegativeCompactDecayExponent x
  let A : ℝ :=
    (1 / 2 : ℝ) *
      (1 - (29 / 100) * (2 / 3) *
        (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 (-x)).im) ^ 4)
  let R : ℝ :=
    (1 / 2 : ℝ) *
      (1 - (29 / 100) * (2 / 3) * (111 / 50 : ℝ) ^ 4 * x ^ 4)
  let P : ℝ := (1 - t / 4 + (t / 4) ^ 2 / 2) ^ 4
  have hpoint :=
    norm_heightTenRiemannSiegelLineIntegrand_one_negativeCompact_le hx0 hx1
  have ht : 0 ≤ t := by dsimp [t, heightTenNegativeCompactDecayExponent]; positivity
  have hexp : Real.exp (-t) ≤ P := by
    simpa only [P] using exp_neg_le_heightTenFourthQuadraticPolynomial t ht
  have hA : 0 ≤ A := by
    have hden := one_div_norm_deBruijnNewmanRiemannSiegelDenominator_compact_le
      (v := -x) (by simpa [abs_of_nonneg hx0] using hx1)
    have hrecip : 0 ≤ 1 /
        ‖deBruijnNewmanRiemannSiegelDenominator
          (deBruijnNewmanRiemannSiegelLine 1 (-x))‖ := by positivity
    exact hrecip.trans (by simpa only [A] using hden)
  have hAR : A ≤ R := by
    have h := heightTen_actualCompactDenominatorFactor_le_rational (-x)
    simpa only [A, R, neg_pow, Even.neg_pow (by decide : Even 4)] using h
  have hR : 0 ≤ R := hA.trans hAR
  have hP : 0 ≤ P := (Real.exp_nonneg (-t)).trans hexp
  calc
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 10) (-x)‖ ≤
        (1633 / 2000 : ℝ) * Real.exp (-t) * A := by
      convert hpoint using 1
      dsimp [t, A, heightTenNegativeCompactDecayExponent]
      ring_nf
    _ ≤ (1633 / 2000 : ℝ) * P * R := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hexp (by norm_num)) hAR hA
        (mul_nonneg (by norm_num) hP)
    _ = heightTenNegativeCompactPolynomialEnvelope x := by
      dsimp [P, R, t, heightTenNegativeCompactPolynomialEnvelope]

theorem integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveCompact_le :
    (∫ v in Set.Ioc (0 : ℝ) (1 / 2),
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) ≤ 7 / 20 := by
  have hactual : IntegrableOn (fun v : ℝ =>
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) (Set.Ioc 0 (1 / 2)) :=
    (integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint (13 / 2))).norm.integrableOn
  have hpoly : IntegrableOn heightTenPositiveCompactPolynomialEnvelope (Set.Ioc 0 (1 / 2)) := by
    have hc : Continuous heightTenPositiveCompactPolynomialEnvelope := by
      unfold heightTenPositiveCompactPolynomialEnvelope heightTenPositiveCompactExponent
      fun_prop
    exact hc.integrableOn_Ioc
  calc
    (∫ v in Set.Ioc (0 : ℝ) (1 / 2),
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) ≤
        ∫ v in Set.Ioc (0 : ℝ) (1 / 2), heightTenPositiveCompactPolynomialEnvelope v := by
      apply setIntegral_mono_on hactual hpoly measurableSet_Ioc
      intro v hv
      exact norm_heightTenRiemannSiegelLineIntegrand_one_positiveCompact_le_polynomial hv.1.le hv.2
    _ = ∫ v in (0 : ℝ)..(1 / 2), heightTenPositiveCompactPolynomialEnvelope v := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
    _ ≤ 7 / 20 :=
      integral_heightTenPositiveCompactPolynomialEnvelope_le_sevenTwentieths

theorem integral_norm_heightTenRiemannSiegelLineIntegrand_one_negativeCompact_le :
    (∫ x in Set.Ioc (0 : ℝ) (1 / 2),
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 10) (-x)‖) ≤ 1 / 10 := by
  have hactual : IntegrableOn (fun x : ℝ =>
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 10) (-x)‖) (Set.Ioc 0 (1 / 2)) := by
    exact ((integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint 10)).norm.comp_neg).integrableOn
  have hpoly : IntegrableOn heightTenNegativeCompactPolynomialEnvelope (Set.Ioc 0 (1 / 2)) := by
    have hc : Continuous heightTenNegativeCompactPolynomialEnvelope := by
      unfold heightTenNegativeCompactPolynomialEnvelope heightTenNegativeCompactDecayExponent
      fun_prop
    exact hc.integrableOn_Ioc
  calc
    (∫ x in Set.Ioc (0 : ℝ) (1 / 2),
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint 10) (-x)‖) ≤
        ∫ x in Set.Ioc (0 : ℝ) (1 / 2), heightTenNegativeCompactPolynomialEnvelope x := by
      apply setIntegral_mono_on hactual hpoly measurableSet_Ioc
      intro x hx
      exact norm_heightTenRiemannSiegelLineIntegrand_one_negativeCompact_le_polynomial hx.1.le hx.2
    _ = ∫ x in (0 : ℝ)..(1 / 2), heightTenNegativeCompactPolynomialEnvelope x := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
    _ ≤ 1 / 10 :=
      integral_heightTenNegativeCompactPolynomialEnvelope_le_oneTenth

theorem sum_integral_norm_heightTenRiemannSiegelLineIntegrand_one_compact_le_nineTwentieths :
    (∫ x in Set.Ioc (0 : ℝ) (1 / 2),
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint 10) (-x)‖) +
      (∫ v in Set.Ioc (0 : ℝ) (1 / 2),
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) ≤
      9 / 20 := by
  nlinarith [integral_norm_heightTenRiemannSiegelLineIntegrand_one_negativeCompact_le,
    integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveCompact_le]

end

end LeanLab.Riemann
