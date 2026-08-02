import LeanLab.Riemann.LevinsonMontgomeryHeightTenRiemannSiegelCompactIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option linter.style.header false

/-!
# Tail integration at the height-ten Riemann--Siegel endpoints

Phase-sensitive polynomial envelopes retain enough principal-argument decay to bound the
negative tail and the first positive-tail interval. Convex exponential envelopes are integrated
by exact rational trapezoid certificates.
-/

open Complex Filter Finset MeasureTheory Real Set
open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

private theorem antitone_tailArctanTerm (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n + 1) / (2 * n + 1)) := by
  intro a b hab
  have hpow : x ^ (2 * b + 1) ≤ x ^ (2 * a + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hden : (2 : ℝ) * a + 1 ≤ (2 : ℝ) * b + 1 := by
    exact_mod_cast (show 2 * a + 1 ≤ 2 * b + 1 by omega)
  exact div_le_div₀ (pow_nonneg hx0 _) hpow (by positivity) hden

theorem tailArctan_le_firstThreeTerms {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  have hsum :
      Tendsto (fun n => ∑ i ∈ range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * i + 1))) atTop
        (nhds (Real.arctan x)) := by
    simpa only [div_eq_mul_inv, mul_assoc, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using
      (Real.hasSum_arctan (x := x)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hx0])).tendsto_sum_nat
  have hanti := antitone_tailArctanTerm x hx0 hx1.le
  have hupper := hanti.tendsto_le_alternating_series hsum 1
  norm_num [Finset.sum_range_succ] at hupper
  simpa only [sub_eq_add_neg] using hupper

theorem tailFirstFourTerms_le_arctan {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7 ≤ Real.arctan x := by
  have hsum :
      Tendsto (fun n => ∑ i ∈ range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * i + 1))) atTop
        (nhds (Real.arctan x)) := by
    simpa only [div_eq_mul_inv, mul_assoc, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using
      (Real.hasSum_arctan (x := x)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hx0])).tendsto_sum_nat
  have hanti := antitone_tailArctanTerm x hx0 hx1.le
  have hlower := hanti.alternating_series_le_tendsto hsum 2
  norm_num [Finset.sum_range_succ] at hlower
  linarith

theorem tail_self_le_arctan_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    x ≤ Real.arctan x := by
  have h := arctan_le_self_of_nonneg (show 0 ≤ -x by linarith)
  rw [Real.arctan_neg] at h
  linarith

def heightTenTailCenteredRatio (v : ℝ) : ℝ :=
  (2 * Real.sqrt 2 * v - 3) / 3

theorem heightTenTail_arctan_recenter {v : ℝ} (_hv0 : 0 ≤ v) (hv1 : v ≤ 2) :
    Real.arctan ((Real.sqrt 2 * v) / (3 - Real.sqrt 2 * v)) =
      Real.pi / 4 + Real.arctan (heightTenTailCenteredRatio v) := by
  let z := heightTenTailCenteredRatio v
  have hsqrt : Real.sqrt 2 < 3 / 2 := Real.sqrt_two_lt_three_halves
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have htailNonneg : 0 ≤ (2 - v) * Real.sqrt 2 :=
    mul_nonneg (sub_nonneg.mpr hv1) hsqrtNonneg
  have hdenPos : 0 < 3 - Real.sqrt 2 * v := by
    nlinarith
  have hz1 : z < 1 := by
    dsimp [z, heightTenTailCenteredRatio]
    nlinarith
  have hadd := Real.arctan_add (x := (1 : ℝ)) (y := z) (by simpa using hz1)
  rw [Real.arctan_one] at hadd
  have hden : 3 - Real.sqrt 2 * v ≠ 0 := hdenPos.ne'
  have hzone : 1 - z ≠ 0 := by linarith
  have hratio : (1 + z) / (1 - z) =
      (Real.sqrt 2 * v) / (3 - Real.sqrt 2 * v) := by
    field_simp [hden, hzone]
    dsimp [z, heightTenTailCenteredRatio]
    ring
  simp only [one_mul] at hadd
  rw [hratio] at hadd
  exact hadd.symm

def heightTenPositiveNearTailAnglePolynomial (v : ℝ) : ℝ :=
  (87 / 200 : ℝ) * v + (69 / 200) * v ^ 2 - (11 / 200) * v ^ 3

private theorem heightTen_positiveNearTailBernstein
    {v : ℝ} (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ (31415 / 40000 : ℝ) +
        (heightTenTailCenteredRatio v - heightTenTailCenteredRatio v ^ 3 / 3 +
          heightTenTailCenteredRatio v ^ 5 / 5) -
        heightTenPositiveNearTailAnglePolynomial v := by
  let u := 2 * v - 1
  let w := 2 - 2 * v
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hsqrtLower : (7071 / 5000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hB : 0 ≤ (2 / 3 : ℝ) * v + (80 / 81) * v ^ 3 + (128 / 1215) * v ^ 5 := by
    positivity
  have hsplit :
      (31415 / 40000 : ℝ) +
          (heightTenTailCenteredRatio v - heightTenTailCenteredRatio v ^ 3 / 3 +
            heightTenTailCenteredRatio v ^ 5 / 5) -
          heightTenPositiveNearTailAnglePolynomial v =
        (-1951 / 24000 : ℝ) - (87 / 200) * v - (2221 / 1800) * v ^ 2 +
          (11 / 200) * v ^ 3 - (64 / 81) * v ^ 4 +
          Real.sqrt 2 *
            ((2 / 3) * v + (80 / 81) * v ^ 3 + (128 / 1215) * v ^ 5) := by
    dsimp [heightTenTailCenteredRatio, heightTenPositiveNearTailAnglePolynomial]
    rw [show
      (31415 / 40000 : ℝ) +
            ((2 * Real.sqrt 2 * v - 3) / 3 -
              ((2 * Real.sqrt 2 * v - 3) / 3) ^ 3 / 3 +
              ((2 * Real.sqrt 2 * v - 3) / 3) ^ 5 / 5) -
            (87 / 200 * v + 69 / 200 * v ^ 2 - 11 / 200 * v ^ 3) =
          (-1951 / 24000 : ℝ) - 87 / 200 * v - 2221 / 1800 * v ^ 2 +
              11 / 200 * v ^ 3 - 64 / 81 * v ^ 4 +
              Real.sqrt 2 *
                (2 / 3 * v + 80 / 81 * v ^ 3 + 128 / 1215 * v ^ 5) +
            (Real.sqrt 2 ^ 2 - 2) *
              (-4 / 9 * v ^ 2 + 40 / 81 * Real.sqrt 2 * v ^ 3 -
                16 / 81 * (Real.sqrt 2 ^ 2 + 2) * v ^ 4 +
                32 / 1215 * Real.sqrt 2 * (Real.sqrt 2 ^ 2 + 2) * v ^ 5) by
        ring]
    rw [hsqrtSq]
    ring
  have hrational :
      0 ≤ (-1951 / 24000 : ℝ) + (2539 / 5000) * v - (2221 / 1800) * v ^ 2 +
          (39197 / 27000) * v ^ 3 - (64 / 81) * v ^ 4 +
          (37712 / 253125) * v ^ 5 := by
    have hid :
        (-1951 / 24000 : ℝ) + (2539 / 5000) * v - (2221 / 1800) * v ^ 2 +
            (39197 / 27000) * v ^ 3 - (64 / 81) * v ^ 4 +
            (37712 / 253125) * v ^ 5 =
          (3551 / 4050000 : ℝ) * w ^ 5 +
          (37229 / 16200000 : ℝ) * 5 * u * w ^ 4 +
          (8419 / 3600000 : ℝ) * 10 * u ^ 2 * w ^ 3 +
          (2623 / 648000 : ℝ) * 10 * u ^ 3 * w ^ 2 +
          (85123 / 16200000 : ℝ) * 5 * u ^ 4 * w +
          (17401 / 5400000 : ℝ) * u ^ 5 := by
      dsimp [u, w]
      ring
    rw [hid]
    positivity
  rw [hsplit]
  have hdelta := mul_nonneg (sub_nonneg.mpr hsqrtLower) hB
  nlinarith

theorem heightTen_positiveNearTailAnglePolynomial_le
    {v : ℝ} (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 1) :
    heightTenPositiveNearTailAnglePolynomial v ≤
      -Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) := by
  have hvPos : 0 ≤ v := by linarith
  have harg := arg_deBruijnNewmanRiemannSiegelLine_one_eq_neg_arctan hvPos (by linarith)
  have hrecenter := heightTenTail_arctan_recenter hvPos (by linarith)
  have hden : 3 - Real.sqrt 2 * v ≠ 0 := by
    have hsqrt := Real.sqrt_two_lt_three_halves
    have hsqrtNonneg := Real.sqrt_nonneg 2
    have htailNonneg : 0 ≤ (2 - v) * Real.sqrt 2 :=
      mul_nonneg (by linarith) hsqrtNonneg
    nlinarith
  have hratio :
      (Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v) =
        (Real.sqrt 2 * v) / (3 - Real.sqrt 2 * v) := by
    field_simp [hden]
  let z := heightTenTailCenteredRatio v
  have hsqrt : Real.sqrt 2 < 3 / 2 := Real.sqrt_two_lt_three_halves
  have hz0 : z < 0 := by dsimp [z, heightTenTailCenteredRatio]; nlinarith
  have hzLower : -1 < z := by
    have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    dsimp [z, heightTenTailCenteredRatio]
    nlinarith
  have hu0 : 0 ≤ -z := by linarith
  have hu1 : -z < 1 := by linarith
  have harctan := tailArctan_le_firstThreeTerms hu0 hu1
  rw [Real.arctan_neg] at harctan
  have hzLowerBound : z - z ^ 3 / 3 + z ^ 5 / 5 ≤ Real.arctan z := by
    nlinarith
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hbern := heightTen_positiveNearTailBernstein hv0 hv1
  have hpoly : heightTenPositiveNearTailAnglePolynomial v ≤
      Real.pi / 4 + (z - z ^ 3 / 3 + z ^ 5 / 5) := by
    dsimp [z] at hbern ⊢
    nlinarith
  rw [harg, neg_neg, hratio, hrecenter]
  exact hpoly.trans (by
    simpa [z] using add_le_add_left hzLowerBound (Real.pi / 4))

theorem arg_deBruijnNewmanRiemannSiegelLine_one_tail_eq_neg_arctan
    {v : ℝ} (_hv0 : 0 ≤ v) (hv2 : v ≤ 2) :
    Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) =
      -Real.arctan
        ((Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v)) := by
  let z := deBruijnNewmanRiemannSiegelLine 1 v
  have hsqrt : Real.sqrt 2 < 3 / 2 := Real.sqrt_two_lt_three_halves
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have htailNonneg : 0 ≤ (2 - v) * Real.sqrt 2 :=
    mul_nonneg (sub_nonneg.mpr hv2) hsqrtNonneg
  have hzRe : z.re = 3 / 2 - Real.sqrt 2 / 2 * v := by
    simp [z]
    norm_num
  have hzRePos : 0 < z.re := by
    rw [hzRe]
    nlinarith
  have htan :
      Real.tan (Complex.arg z) =
        -((Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v)) := by
    rw [Complex.tan_arg]
    rw [hzRe]
    simp only [z, deBruijnNewmanRiemannSiegelLine_im]
    ring
  have hprincipal := Real.arctan_eq_of_tan_eq htan ⟨
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hzRePos),
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hzRePos)⟩
  simpa only [Real.arctan_neg] using hprincipal.symm

def heightTenPositiveMiddleTailAnglePolynomial (v : ℝ) : ℝ :=
  (18 / 25 : ℝ) * v + (v - 1) * (2 - v) / 5

private theorem heightTen_positiveMiddleTailAnglePolynomial_le_of_centered_nonpos
    {v : ℝ} (hv1 : 1 ≤ v) (_hv2 : v ≤ 2)
    (hz : heightTenTailCenteredRatio v ≤ 0) :
    heightTenPositiveMiddleTailAnglePolynomial v ≤
      Real.pi / 4 + Real.arctan (heightTenTailCenteredRatio v) := by
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hsqrtLower : (7071 / 5000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hfactor : 0 ≤ (2 / 3 : ℝ) * v := by positivity
  have hsqrtDelta := mul_nonneg (sub_nonneg.mpr hsqrtLower) hfactor
  have hrational :
      0 ≤ (1483 / 8000 : ℝ) - (943 / 2500) * v + (1 / 5) * v ^ 2 := by
    have hsecond : 0 ≤ (1 / 5 : ℝ) * v - 443 / 2500 := by nlinarith
    have hproduct := mul_nonneg (sub_nonneg.mpr hv1) hsecond
    nlinarith
  have hlinear :
      heightTenPositiveMiddleTailAnglePolynomial v ≤
        Real.pi / 4 + heightTenTailCenteredRatio v := by
    dsimp [heightTenPositiveMiddleTailAnglePolynomial, heightTenTailCenteredRatio]
    nlinarith
  exact hlinear.trans (by
    simpa using add_le_add_left (tail_self_le_arctan_of_nonpos hz) (Real.pi / 4))

private theorem heightTen_positiveMiddleTailBernstein
    {v : ℝ} (hv1 : 1 ≤ v) (hv2 : v ≤ 2) :
    0 ≤ Real.pi / 4 +
        (heightTenTailCenteredRatio v - heightTenTailCenteredRatio v ^ 3 / 3 +
          heightTenTailCenteredRatio v ^ 5 / 5 -
          heightTenTailCenteredRatio v ^ 7 / 7) -
        heightTenPositiveMiddleTailAnglePolynomial v := by
  let u := v - 1
  let w := 2 - v
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hsqrtUpper : Real.sqrt 2 ≤ (14143 / 10000 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2]
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  let C : ℝ :=
    (160 / 81) * v ^ 3 + (1792 / 1215) * v ^ 5 + (1024 / 15309) * v ^ 7
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hsplit :
      (31415 / 40000 : ℝ) +
          (heightTenTailCenteredRatio v - heightTenTailCenteredRatio v ^ 3 / 3 +
            heightTenTailCenteredRatio v ^ 5 / 5 -
            heightTenTailCenteredRatio v ^ 7 / 7) -
          heightTenPositiveMiddleTailAnglePolynomial v =
        (31415 / 40000 : ℝ) - 76 / 105 + 2 / 5 - 33 / 25 * v +
          89 / 45 * v ^ 2 + 256 / 81 * v ^ 4 + 512 / 729 * v ^ 6 -
          Real.sqrt 2 * C := by
    dsimp [heightTenTailCenteredRatio, heightTenPositiveMiddleTailAnglePolynomial, C]
    rw [show
      (31415 / 40000 : ℝ) +
            ((2 * Real.sqrt 2 * v - 3) / 3 -
              ((2 * Real.sqrt 2 * v - 3) / 3) ^ 3 / 3 +
              ((2 * Real.sqrt 2 * v - 3) / 3) ^ 5 / 5 -
              ((2 * Real.sqrt 2 * v - 3) / 3) ^ 7 / 7) -
            (18 / 25 * v + (v - 1) * (2 - v) / 5) =
          (31415 / 40000 : ℝ) - 76 / 105 + 2 / 5 - 33 / 25 * v +
              89 / 45 * v ^ 2 + 256 / 81 * v ^ 4 + 512 / 729 * v ^ 6 -
              Real.sqrt 2 *
                (160 / 81 * v ^ 3 + 1792 / 1215 * v ^ 5 +
                  1024 / 15309 * v ^ 7) +
            (Real.sqrt 2 ^ 2 - 2) *
              (8 / 9 * v ^ 2 - 80 / 81 * Real.sqrt 2 * v ^ 3 +
                64 / 81 * (Real.sqrt 2 ^ 2 + 2) * v ^ 4 -
                448 / 1215 * Real.sqrt 2 * (Real.sqrt 2 ^ 2 + 2) * v ^ 5 +
                64 / 729 * (Real.sqrt 2 ^ 4 + 2 * Real.sqrt 2 ^ 2 + 4) * v ^ 6 -
                128 / 15309 * Real.sqrt 2 *
                  (Real.sqrt 2 ^ 4 + 2 * Real.sqrt 2 ^ 2 + 4) * v ^ 7) by
        ring]
    rw [hsqrtSq]
    norm_num
  have hrational :
      0 ≤ (31415 / 40000 : ℝ) - 76 / 105 + 2 / 5 - 33 / 25 * v +
          89 / 45 * v ^ 2 + 256 / 81 * v ^ 4 + 512 / 729 * v ^ 6 -
          (14143 / 10000) * C := by
    have hid :
        (31415 / 40000 : ℝ) - 76 / 105 + 2 / 5 - 33 / 25 * v +
            89 / 45 * v ^ 2 + 256 / 81 * v ^ 4 + 512 / 729 * v ^ 6 -
            (14143 / 10000) * C =
          (24317623 / 3061800000 : ℝ) * w ^ 7 +
          (32429303 / 3061800000 : ℝ) * 7 * u * w ^ 6 +
          (10969489 / 437400000 : ℝ) * 21 * u ^ 2 * w ^ 5 +
          (133282871 / 3061800000 : ℝ) * 35 * u ^ 3 * w ^ 4 +
          (173850679 / 3061800000 : ℝ) * 35 * u ^ 4 * w ^ 3 +
          (187080311 / 3061800000 : ℝ) * 21 * u ^ 5 * w ^ 2 +
          (216392311 / 3061800000 : ℝ) * 7 * u ^ 6 * w +
          (18015953 / 437400000 : ℝ) * u ^ 7 := by
      dsimp [u, w, C]
      ring
    rw [hid]
    positivity
  have hsqrtDelta := mul_nonneg (sub_nonneg.mpr hsqrtUpper) hC
  have hpiDelta : 0 ≤ (Real.pi - 31415 / 10000) / 4 := by positivity
  have hbase :
      0 ≤ (31415 / 40000 : ℝ) +
          (heightTenTailCenteredRatio v - heightTenTailCenteredRatio v ^ 3 / 3 +
            heightTenTailCenteredRatio v ^ 5 / 5 -
            heightTenTailCenteredRatio v ^ 7 / 7) -
          heightTenPositiveMiddleTailAnglePolynomial v := by
    rw [hsplit]
    nlinarith
  have hdecomp :
      Real.pi / 4 +
            (heightTenTailCenteredRatio v - heightTenTailCenteredRatio v ^ 3 / 3 +
              heightTenTailCenteredRatio v ^ 5 / 5 -
              heightTenTailCenteredRatio v ^ 7 / 7) -
            heightTenPositiveMiddleTailAnglePolynomial v =
        ((31415 / 40000 : ℝ) +
            (heightTenTailCenteredRatio v - heightTenTailCenteredRatio v ^ 3 / 3 +
              heightTenTailCenteredRatio v ^ 5 / 5 -
              heightTenTailCenteredRatio v ^ 7 / 7) -
            heightTenPositiveMiddleTailAnglePolynomial v) +
          (Real.pi - 31415 / 10000) / 4 := by
    ring
  rw [hdecomp]
  positivity

theorem heightTen_positiveMiddleTailAnglePolynomial_le
    {v : ℝ} (hv1 : 1 ≤ v) (hv2 : v ≤ 2) :
    heightTenPositiveMiddleTailAnglePolynomial v ≤
      -Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) := by
  have hv0 : 0 ≤ v := by linarith
  have harg := arg_deBruijnNewmanRiemannSiegelLine_one_tail_eq_neg_arctan hv0 hv2
  have hrecenter := heightTenTail_arctan_recenter hv0 hv2
  have hden : 3 - Real.sqrt 2 * v ≠ 0 := by
    have hsqrt := Real.sqrt_two_lt_three_halves
    have hsqrtNonneg := Real.sqrt_nonneg 2
    have htailNonneg : 0 ≤ (2 - v) * Real.sqrt 2 :=
      mul_nonneg (sub_nonneg.mpr hv2) hsqrtNonneg
    nlinarith
  have hratio :
      (Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v) =
        (Real.sqrt 2 * v) / (3 - Real.sqrt 2 * v) := by
    field_simp [hden]
  rw [harg, neg_neg, hratio, hrecenter]
  by_cases hz : heightTenTailCenteredRatio v ≤ 0
  · exact heightTen_positiveMiddleTailAnglePolynomial_le_of_centered_nonpos hv1 hv2 hz
  · have hz0 : 0 ≤ heightTenTailCenteredRatio v := le_of_not_ge hz
    have hz1 : heightTenTailCenteredRatio v < 1 := by
      have hsqrt := Real.sqrt_two_lt_three_halves
      have hsqrtNonneg := Real.sqrt_nonneg 2
      have htailNonneg : 0 ≤ (2 - v) * Real.sqrt 2 :=
        mul_nonneg (sub_nonneg.mpr hv2) hsqrtNonneg
      dsimp [heightTenTailCenteredRatio]
      nlinarith
    have harctan := tailFirstFourTerms_le_arctan hz0 hz1
    have hbern := heightTen_positiveMiddleTailBernstein hv1 hv2
    have hpoly : heightTenPositiveMiddleTailAnglePolynomial v ≤
        Real.pi / 4 +
          (heightTenTailCenteredRatio v - heightTenTailCenteredRatio v ^ 3 / 3 +
            heightTenTailCenteredRatio v ^ 5 / 5 -
            heightTenTailCenteredRatio v ^ 7 / 7) := by
      linarith
    exact hpoly.trans (by
      simpa using add_le_add_left harctan (Real.pi / 4))

theorem heightTen_negativeTailAngleLinear_le {x : ℝ} (hx : 0 ≤ x) :
    Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) ≤
      (Real.sqrt 2 / 3) * x := by
  have harg := arg_deBruijnNewmanRiemannSiegelLine_one_neg_le_ratio hx
  have hden : 0 < 3 + Real.sqrt 2 * x := by positivity
  have hratio :
      (Real.sqrt 2 / 2 * x) / (3 / 2 + Real.sqrt 2 / 2 * x) =
        Real.sqrt 2 * x / (3 + Real.sqrt 2 * x) := by
    field_simp [hden.ne']
  rw [hratio] at harg
  have hlinear : Real.sqrt 2 * x / (3 + Real.sqrt 2 * x) ≤
      (Real.sqrt 2 / 3) * x := by
    rw [div_le_iff₀ hden]
    have htx : 0 ≤ Real.sqrt 2 * x := mul_nonneg (Real.sqrt_nonneg 2) hx
    nlinarith [sq_nonneg (Real.sqrt 2 * x)]
  exact harg.trans hlinear

theorem heightTen_negativeTailTotalExponent_le
    {x : ℝ} (hx : 1 / 2 ≤ x) :
    10 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
          (-Real.pi * x ^ 2 - Real.sqrt 2 * Real.pi * (1 + 1 / 2) * x) -
        Real.pi * (Real.sqrt 2 / 2) * x ≤
      -(57 / 10 : ℝ) * x := by
  have hx0 : 0 ≤ x := by linarith
  have harg := heightTen_negativeTailAngleLinear_le hx0
  have hphase := mul_le_mul_of_nonneg_left harg (by norm_num : (0 : ℝ) ≤ 10)
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hsqrtLower : (7071 / 5000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hpiLower : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hgapLower :
      (39 / 20 : ℝ) ≤ Real.sqrt 2 * ((3 / 2) * Real.pi - 10 / 3) := by
    have hgap : (16547 / 12000 : ℝ) ≤ (3 / 2) * Real.pi - 10 / 3 := by
      nlinarith
    calc
      (39 / 20 : ℝ) ≤ (7071 / 5000 : ℝ) * (16547 / 12000) := by norm_num
      _ ≤ Real.sqrt 2 * ((3 / 2) * Real.pi - 10 / 3) :=
        mul_le_mul hsqrtLower hgap (by norm_num) (by positivity)
  have hdenDecay : (111 / 50 : ℝ) ≤ Real.pi * (Real.sqrt 2 / 2) :=
    oneHundredEleven_div_fifty_le_pi_mul_sqrtTwoHalf
  have hquadDecay : (157 / 100 : ℝ) * x ≤ Real.pi * x ^ 2 := by
    have hhalf : (157 / 100 : ℝ) ≤ Real.pi / 2 := by nlinarith
    have hsquare : x / 2 ≤ x ^ 2 := by
      nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx)]
    nlinarith [mul_le_mul_of_nonneg_left hhalf hx0]
  have hgapMul := mul_le_mul_of_nonneg_right hgapLower hx0
  have hdenMul := mul_le_mul_of_nonneg_right hdenDecay hx0
  nlinarith

theorem norm_heightTenRiemannSiegelLineIntegrand_one_negativeTail_le
    {x : ℝ} (hx : 1 / 2 ≤ x) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 10) (-x)‖ ≤
      (1633 / 2000 : ℝ) * (9 / 8) * Real.exp (-(57 / 10 : ℝ) * x) := by
  have hx0 : 0 ≤ x := by linarith
  rw [norm_heightTenRiemannSiegelLineIntegrand_one_eq_factorization]
  have hrpow := rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_neg_le hx0
  have hden := one_div_norm_deBruijnNewmanRiemannSiegelDenominator_tail_le
    (v := -x) (by simpa [abs_of_nonneg hx0] using hx)
  have hexponent := heightTen_negativeTailTotalExponent_le hx
  let A := 10 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
    (-Real.pi * x ^ 2 - Real.sqrt 2 * Real.pi * (1 + 1 / 2) * x)
  let B := -(Real.pi * (Real.sqrt 2 / 2) * x)
  have hdenB :
      1 / ‖deBruijnNewmanRiemannSiegelDenominator
          (deBruijnNewmanRiemannSiegelLine 1 (-x))‖ ≤
        (9 / 8 : ℝ) * Real.exp B := by
    simpa [B, abs_of_nonneg hx0] using hden
  rw [show
    10 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
        (-Real.pi * (-x) ^ 2 + Real.sqrt 2 * Real.pi * (1 + 1 / 2) * (-x)) = A by
      dsimp [A]
      ring]
  calc
    ‖deBruijnNewmanRiemannSiegelLine 1 (-x)‖ ^ (-(1 / 2 : ℝ)) *
          Real.exp A *
          (1 / ‖deBruijnNewmanRiemannSiegelDenominator
            (deBruijnNewmanRiemannSiegelLine 1 (-x))‖) ≤
        (1633 / 2000 : ℝ) * Real.exp A * ((9 / 8) * Real.exp B) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hrpow (Real.exp_nonneg _)) hdenB
        (one_div_nonneg.mpr (norm_nonneg _))
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    _ = (1633 / 2000 : ℝ) * (9 / 8) * (Real.exp A * Real.exp B) := by
      ring
    _ = (1633 / 2000 : ℝ) * (9 / 8) * Real.exp (A + B) := by
      have hab := Real.exp_add A B
      rw [hab]
    _ ≤ (1633 / 2000 : ℝ) * (9 / 8) * Real.exp (-(57 / 10 : ℝ) * x) := by
      gcongr
      dsimp [A, B]
      nlinarith

theorem seventeen_le_exp_fiftySeven_div_twenty :
    (17 : ℝ) ≤ Real.exp (57 / 20) := by
  have hseries := Real.sum_le_exp_of_nonneg
    (x := (57 / 20 : ℝ)) (by norm_num) 8
  have hpartial :
      (17 : ℝ) ≤ ∑ i ∈ range 8,
        (57 / 20 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact hpartial.trans hseries

theorem integral_norm_heightTenRiemannSiegelLineIntegrand_one_negativeTail_le :
    (∫ x in Set.Ioi (1 / 2 : ℝ),
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 10) (-x)‖) ≤ 19 / 2000 := by
  let g : ℝ → ℝ := fun x =>
    (1633 / 2000 : ℝ) * (9 / 8) * Real.exp (-(57 / 10 : ℝ) * x)
  have hactual : IntegrableOn (fun x : ℝ =>
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 10) (-x)‖) (Set.Ioi (1 / 2)) := by
    exact ((integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint 10)).norm.comp_neg).integrableOn
  have hg : IntegrableOn g (Set.Ioi (1 / 2)) := by
    exact (integrableOn_exp_mul_Ioi (a := -(57 / 10 : ℝ)) (by norm_num) (1 / 2)).const_mul _
  have hexpInv : Real.exp (-(57 / 20 : ℝ)) ≤ 1 / 17 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num) seventeen_le_exp_fiftySeven_div_twenty
  calc
    (∫ x in Set.Ioi (1 / 2 : ℝ),
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint 10) (-x)‖) ≤
        ∫ x in Set.Ioi (1 / 2 : ℝ), g x := by
      apply setIntegral_mono_on hactual hg measurableSet_Ioi
      intro x hx
      exact norm_heightTenRiemannSiegelLineIntegrand_one_negativeTail_le hx.le
    _ = (1633 / 2000 : ℝ) * (9 / 8) *
        (-(Real.exp (-(57 / 10 : ℝ) * (1 / 2))) / (-(57 / 10 : ℝ))) := by
      dsimp [g]
      rw [MeasureTheory.integral_const_mul]
      rw [integral_exp_mul_Ioi (a := -(57 / 10 : ℝ)) (by norm_num)]
    _ ≤ 19 / 2000 := by
      norm_num at hexpInv ⊢
      nlinarith

theorem intervalIntegral_le_trapezoid_of_convexOn
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hcont : Continuous f) :
    (∫ x in a..b, f x) ≤ (b - a) / 2 * (f a + f b) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let g : ℝ → ℝ := fun x =>
    ((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b
  have hfi : IntervalIntegrable f volume a b := hcont.intervalIntegrable _ _
  have hgi : IntervalIntegrable g volume a b := by
    have hgcont : Continuous g := by
      dsimp [g]
      fun_prop
    exact hgcont.intervalIntegrable _ _
  have hpoint : ∀ x ∈ Set.Icc a b, f x ≤ g x := by
    intro x hx
    let s := (b - x) / (b - a)
    let t := (x - a) / (b - a)
    have hs0 : 0 ≤ s := by
      dsimp [s]
      exact div_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hab.le)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab.le)
    have hst : s + t = 1 := by
      dsimp [s, t]
      field_simp
      ring
    have hcombo : s * a + t * b = x := by
      dsimp [s, t]
      field_simp
      ring
    have h := hf.2 (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab.le⟩)
      (show b ∈ Set.Icc a b by exact ⟨hab.le, le_rfl⟩) hs0 ht0 hst
    simpa [g, s, t, smul_eq_mul, hcombo] using h
  calc
    (∫ x in a..b, f x) ≤ ∫ x in a..b, g x :=
      intervalIntegral.integral_mono_on hab.le hfi hgi hpoint
    _ = (b - a) / 2 * (f a + f b) := by
      have hgform : ∀ x : ℝ,
          g x = ((f b - f a) / (b - a)) * x +
            (b * f a - a * f b) / (b - a) := by
        intro x
        dsimp [g]
        field_simp
        ring
      simp_rw [hgform]
      let c := (f b - f a) / (b - a)
      let d := (b * f a - a * f b) / (b - a)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => by
          convert (((hasDerivAt_id x).pow 2).const_mul c).div_const 2 |>.add
            ((hasDerivAt_id x).const_mul d) using 1;
              (dsimp [c, d, id]; ring))
        (by
          have hc : Continuous (fun x : ℝ => c * x + d) := by fun_prop
          exact hc.intervalIntegrable _ _)]
      dsimp [c, d]
      field_simp
      ring

def heightTenPositiveNearTailExponent (v : ℝ) : ℝ :=
  (3233 / 2000 : ℝ) * v - (673 / 125) * v ^ 2 + (143 / 400) * v ^ 3

def heightTenPositiveNearTailExponentDeriv (v : ℝ) : ℝ :=
  (3233 / 2000 : ℝ) - (1346 / 125) * v + (429 / 400) * v ^ 2

def heightTenPositiveNearTailExponentDeriv2 (v : ℝ) : ℝ :=
  -(1346 / 125 : ℝ) + (429 / 200) * v

theorem hasDerivAt_heightTenPositiveNearTailExponent (v : ℝ) :
    HasDerivAt heightTenPositiveNearTailExponent
      (heightTenPositiveNearTailExponentDeriv v) v := by
  have h := (((hasDerivAt_id v).const_mul (3233 / 2000 : ℝ)).sub
    (((hasDerivAt_id v).pow 2).const_mul (673 / 125 : ℝ))).add
      (((hasDerivAt_id v).pow 3).const_mul (143 / 400 : ℝ))
  have hfun : heightTenPositiveNearTailExponent =
      ((fun y : ℝ => (3233 / 2000 : ℝ) * id y) -
        fun y : ℝ => (673 / 125 : ℝ) * (id ^ 2) y) +
        fun y : ℝ => (143 / 400 : ℝ) * (id ^ 3) y := by
    funext y
    simp only [heightTenPositiveNearTailExponent, Pi.add_apply, Pi.sub_apply,
      Pi.pow_apply, id_eq]
  rw [hfun]
  exact h.congr_deriv (by
    dsimp [heightTenPositiveNearTailExponentDeriv]
    ring)

theorem hasDerivAt_heightTenPositiveNearTailExponentDeriv (v : ℝ) :
    HasDerivAt heightTenPositiveNearTailExponentDeriv
      (heightTenPositiveNearTailExponentDeriv2 v) v := by
  have h := ((hasDerivAt_const v (3233 / 2000 : ℝ)).sub
    ((hasDerivAt_id v).const_mul (1346 / 125 : ℝ))).add
      (((hasDerivAt_id v).pow 2).const_mul (429 / 400 : ℝ))
  have hfun : heightTenPositiveNearTailExponentDeriv =
      ((fun _ : ℝ => (3233 / 2000 : ℝ)) -
        fun y : ℝ => (1346 / 125 : ℝ) * id y) +
        fun y : ℝ => (429 / 400 : ℝ) * (id ^ 2) y := by
    funext y
    simp only [heightTenPositiveNearTailExponentDeriv, Pi.add_apply, Pi.sub_apply,
      Pi.pow_apply, id_eq]
  rw [hfun]
  exact h.congr_deriv (by
    dsimp [heightTenPositiveNearTailExponentDeriv2]
    ring)

private theorem heightTen_positiveNearTailSecondFactor_nonneg
    {v : ℝ} (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ heightTenPositiveNearTailExponentDeriv v ^ 2 +
      heightTenPositiveNearTailExponentDeriv2 v := by
  let u := 2 * v - 1
  let w := 2 - 2 * v
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hid :
      heightTenPositiveNearTailExponentDeriv v ^ 2 +
          heightTenPositiveNearTailExponentDeriv2 v =
        (6528321 / 2560000 : ℝ) * w ^ 4 +
        (72321907 / 6400000 : ℝ) * 4 * u * w ^ 3 +
        (283853927 / 12000000 : ℝ) * 6 * u ^ 2 * w ^ 2 +
        (155851247 / 4000000 : ℝ) * 4 * u ^ 3 * w +
        (56647241 / 1000000 : ℝ) * u ^ 4 := by
    dsimp [heightTenPositiveNearTailExponentDeriv,
      heightTenPositiveNearTailExponentDeriv2, u, w]
    ring
  rw [hid]
  positivity

theorem convexOn_exp_heightTenPositiveNearTailExponent :
    ConvexOn ℝ (Set.Icc (1 / 2 : ℝ) 1)
      (fun v => Real.exp (heightTenPositiveNearTailExponent v)) := by
  let f : ℝ → ℝ := fun v => Real.exp (heightTenPositiveNearTailExponent v)
  let f' : ℝ → ℝ := fun v =>
    Real.exp (heightTenPositiveNearTailExponent v) *
      heightTenPositiveNearTailExponentDeriv v
  let f'' : ℝ → ℝ := fun v =>
    Real.exp (heightTenPositiveNearTailExponent v) *
      (heightTenPositiveNearTailExponentDeriv v ^ 2 +
        heightTenPositiveNearTailExponentDeriv2 v)
  change ConvexOn ℝ (Set.Icc (1 / 2 : ℝ) 1) f
  have hfcont : Continuous f := by
    dsimp [f]
    unfold heightTenPositiveNearTailExponent
    fun_prop
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'')
    (convex_Icc (1 / 2 : ℝ) 1) hfcont.continuousOn ?_ ?_ ?_
  · intro v hv
    exact (hasDerivAt_heightTenPositiveNearTailExponent v).exp.hasDerivWithinAt
  · intro v hv
    have hq := hasDerivAt_heightTenPositiveNearTailExponent v
    have hqp := hasDerivAt_heightTenPositiveNearTailExponentDeriv v
    have h := hq.exp.mul hqp
    have hfun : f' =
        (fun x => Real.exp (heightTenPositiveNearTailExponent x)) *
          heightTenPositiveNearTailExponentDeriv := by
      funext x
      rfl
    rw [hfun]
    exact (h.congr_deriv (by dsimp [f'']; ring)).hasDerivWithinAt
  · intro v hv
    have hvIoo : v ∈ Set.Ioo (1 / 2 : ℝ) 1 := by simpa using hv
    exact mul_nonneg (Real.exp_nonneg _)
      (heightTen_positiveNearTailSecondFactor_nonneg hvIoo.1.le hvIoo.2.le)

theorem heightTen_positiveNearTailTotalExponent_le
    {v : ℝ} (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 1) :
    (13 / 2 : ℝ) * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) +
          (-Real.pi * v ^ 2 +
            Real.sqrt 2 * Real.pi * (1 + 1 / 2) * v) -
        Real.pi * (Real.sqrt 2 / 2) * v ≤
      heightTenPositiveNearTailExponent v := by
  have harg := heightTen_positiveNearTailAnglePolynomial_le hv0 hv1
  have hphase := mul_le_mul_of_nonneg_left harg (by norm_num : (0 : ℝ) ≤ 13 / 2)
  have hpiSqrtUpper : Real.pi * Real.sqrt 2 ≤ (1111 / 250 : ℝ) := by
    calc
      Real.pi * Real.sqrt 2 = 2 * (Real.pi * (Real.sqrt 2 / 2)) := by ring
      _ ≤ 2 * (1111 / 500 : ℝ) := by
        gcongr
        exact pi_mul_sqrtTwoHalf_le_oneThousandOneHundredEleven_div_fiveHundred
      _ = (1111 / 250 : ℝ) := by norm_num
  have hpiLower : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hvNonneg : 0 ≤ v := by linarith
  have hlinear := mul_le_mul_of_nonneg_right hpiSqrtUpper hvNonneg
  have hquadratic := mul_le_mul_of_nonneg_right hpiLower (sq_nonneg v)
  dsimp [heightTenPositiveNearTailAnglePolynomial,
    heightTenPositiveNearTailExponent] at hphase ⊢
  nlinarith

theorem norm_heightTenRiemannSiegelLineIntegrand_one_positiveNearTail_le
    {v : ℝ} (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 1) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖ ≤
      (9 / 8 : ℝ) * Real.exp (heightTenPositiveNearTailExponent v) := by
  have hvNonneg : 0 ≤ v := by linarith
  rw [norm_heightTenRiemannSiegelLineIntegrand_one_eq_factorization]
  have hrpow := rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_le_one v
  have hden := one_div_norm_deBruijnNewmanRiemannSiegelDenominator_tail_le
    (v := v) (by simpa [abs_of_nonneg hvNonneg] using hv0)
  have hexponent := heightTen_positiveNearTailTotalExponent_le hv0 hv1
  let A := (13 / 2 : ℝ) * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) +
    (-Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (1 + 1 / 2) * v)
  let B := -(Real.pi * (Real.sqrt 2 / 2) * v)
  have hdenB :
      1 / ‖deBruijnNewmanRiemannSiegelDenominator
          (deBruijnNewmanRiemannSiegelLine 1 v)‖ ≤
        (9 / 8 : ℝ) * Real.exp B := by
    simpa [B, abs_of_nonneg hvNonneg] using hden
  calc
    ‖deBruijnNewmanRiemannSiegelLine 1 v‖ ^ (-(1 / 2 : ℝ)) *
          Real.exp A *
          (1 / ‖deBruijnNewmanRiemannSiegelDenominator
            (deBruijnNewmanRiemannSiegelLine 1 v)‖) ≤
        1 * Real.exp A * ((9 / 8 : ℝ) * Real.exp B) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hrpow (Real.exp_nonneg _)) hdenB
        (one_div_nonneg.mpr (norm_nonneg _))
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    _ = (9 / 8 : ℝ) * Real.exp (A + B) := by
      have hab := Real.exp_add A B
      rw [hab]
      ring
    _ ≤ (9 / 8 : ℝ) * Real.exp (heightTenPositiveNearTailExponent v) := by
      gcongr
      dsimp [A, B]
      nlinarith

theorem exp_neg_le_heightTenEighthQuadraticPolynomial (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ (1 - t / 8 + (t / 8) ^ 2 / 2) ^ 8 := by
  let y := t / 8
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
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hquad 8
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow
  have hty : -(8 * y) = -t := by dsimp [y]; ring
  rw [hty] at hpow
  simpa only [y] using hpow

def heightTenPositiveNearTailExpEnvelope (v : ℝ) : ℝ :=
  let t := -heightTenPositiveNearTailExponent v
  (1 - t / 8 + (t / 8) ^ 2 / 2) ^ 8

theorem heightTenPositiveNearTailExponent_nonpos
    {v : ℝ} (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 1) :
    heightTenPositiveNearTailExponent v ≤ 0 := by
  have hvNonneg : 0 ≤ v := by linarith
  have hvSq : v ^ 2 ≤ 1 := by nlinarith [sq_nonneg v]
  have hbracket :
      (3233 / 2000 : ℝ) - (673 / 125) * v + (143 / 400) * v ^ 2 ≤ 0 := by
    nlinarith
  dsimp [heightTenPositiveNearTailExponent]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hvNonneg hbracket]

theorem exp_heightTenPositiveNearTailExponent_le_envelope
    {v : ℝ} (hv0 : 1 / 2 ≤ v) (hv1 : v ≤ 1) :
    Real.exp (heightTenPositiveNearTailExponent v) ≤
      heightTenPositiveNearTailExpEnvelope v := by
  have hq := heightTenPositiveNearTailExponent_nonpos hv0 hv1
  have h := exp_neg_le_heightTenEighthQuadraticPolynomial
    (-heightTenPositiveNearTailExponent v) (by linarith)
  simpa [heightTenPositiveNearTailExpEnvelope] using h

private def heightTenNearTailNode (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) + n / 16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Normalize the nine exact rational node envelopes in one kernel-checked step.
theorem integral_exp_heightTenPositiveNearTailExponent_le_threeTwentyFifths :
    (∫ v in (1 / 2 : ℝ)..1, Real.exp (heightTenPositiveNearTailExponent v)) ≤
      3 / 25 := by
  let f : ℝ → ℝ := fun v => Real.exp (heightTenPositiveNearTailExponent v)
  have hfcont : Continuous f := by
    dsimp [f]
    unfold heightTenPositiveNearTailExponent
    fun_prop
  have hsplit :
      ∑ k ∈ range 8,
          ∫ v in heightTenNearTailNode k..heightTenNearTailNode (k + 1), f v =
        ∫ v in (1 / 2 : ℝ)..1, f v := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := f) (a := heightTenNearTailNode) (n := 8)
      (fun k hk => hfcont.intervalIntegrable (μ := volume) _ _)
    norm_num [heightTenNearTailNode] at h ⊢
    exact h
  have hsegments :
      ∑ k ∈ range 8,
          ∫ v in heightTenNearTailNode k..heightTenNearTailNode (k + 1), f v ≤
        ∑ k ∈ range 8, (1 / 32 : ℝ) *
          (f (heightTenNearTailNode k) + f (heightTenNearTailNode (k + 1))) := by
    apply sum_le_sum
    intro k hk
    have hk8 : k < 8 := mem_range.mp hk
    have hkReal : (k : ℝ) ≤ 7 := by
      exact_mod_cast (Nat.le_pred_of_lt hk8)
    have hleft : 1 / 2 ≤ heightTenNearTailNode k := by
      dsimp [heightTenNearTailNode]
      have hkNonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have hright : heightTenNearTailNode (k + 1) ≤ 1 := by
      dsimp [heightTenNearTailNode]
      push_cast
      norm_num
      linarith
    have hsub := Set.Icc_subset_Icc hleft hright
    have hconv : ConvexOn ℝ
        (Set.Icc (heightTenNearTailNode k) (heightTenNearTailNode (k + 1))) f := by
      refine ⟨convex_Icc _ _, ?_⟩
      intro x hx y hy a b ha hb hab
      exact convexOn_exp_heightTenPositiveNearTailExponent.2
        (hsub hx) (hsub hy) ha hb hab
    have htrap := intervalIntegral_le_trapezoid_of_convexOn
      (show heightTenNearTailNode k ≤ heightTenNearTailNode (k + 1) by
        dsimp [heightTenNearTailNode]
        push_cast
        norm_num
        linarith)
      hconv hfcont
    have hwidth :
        (heightTenNearTailNode (k + 1) - heightTenNearTailNode k) / 2 =
          (1 / 32 : ℝ) := by
      dsimp [heightTenNearTailNode]
      push_cast
      ring
    rw [hwidth] at htrap
    exact htrap
  rw [hsplit] at hsegments
  calc
    (∫ v in (1 / 2 : ℝ)..1, Real.exp (heightTenPositiveNearTailExponent v)) =
        ∫ v in (1 / 2 : ℝ)..1, f v := by rfl
    _ ≤ ∑ k ∈ range 8, (1 / 32 : ℝ) *
          (f (heightTenNearTailNode k) + f (heightTenNearTailNode (k + 1))) := hsegments
    _ ≤ ∑ k ∈ range 8, (1 / 32 : ℝ) *
          (heightTenPositiveNearTailExpEnvelope (heightTenNearTailNode k) +
            heightTenPositiveNearTailExpEnvelope (heightTenNearTailNode (k + 1))) := by
      apply sum_le_sum
      intro k hk
      have hk8 : k < 8 := mem_range.mp hk
      have hk9 : k + 1 ≤ 8 := by omega
      have hkReal : (k : ℝ) ≤ 7 := by
        exact_mod_cast (Nat.le_pred_of_lt hk8)
      have hk9Real : (k : ℝ) + 1 ≤ 8 := by
        exact_mod_cast hk9
      dsimp [f]
      gcongr
      · apply exp_heightTenPositiveNearTailExponent_le_envelope
        · dsimp [heightTenNearTailNode]
          have hkNonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith
        · dsimp [heightTenNearTailNode]
          norm_num
          linarith
      · apply exp_heightTenPositiveNearTailExponent_le_envelope
        · dsimp [heightTenNearTailNode]
          have hkNonneg : (0 : ℝ) ≤ (k + 1 : ℕ) := Nat.cast_nonneg (k + 1)
          nlinarith
        · dsimp [heightTenNearTailNode]
          push_cast
          norm_num
          linarith
    _ ≤ 3 / 25 := by
      norm_num [Finset.sum_range_succ, heightTenNearTailNode,
        heightTenPositiveNearTailExpEnvelope, heightTenPositiveNearTailExponent]

theorem integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveNearTail_le :
    (∫ v in Set.Ioc (1 / 2 : ℝ) 1,
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) ≤ 27 / 200 := by
  let g : ℝ → ℝ := fun v =>
    (9 / 8 : ℝ) * Real.exp (heightTenPositiveNearTailExponent v)
  have hactual : IntegrableOn (fun v : ℝ =>
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) (Set.Ioc (1 / 2) 1) :=
    (integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint (13 / 2))).norm.integrableOn
  have hg : IntegrableOn g (Set.Ioc (1 / 2) 1) := by
    have hcont : Continuous g := by
      dsimp [g]
      unfold heightTenPositiveNearTailExponent
      fun_prop
    exact hcont.integrableOn_Ioc
  calc
    (∫ v in Set.Ioc (1 / 2 : ℝ) 1,
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) ≤
        ∫ v in Set.Ioc (1 / 2 : ℝ) 1, g v := by
      apply setIntegral_mono_on hactual hg measurableSet_Ioc
      intro v hv
      exact norm_heightTenRiemannSiegelLineIntegrand_one_positiveNearTail_le hv.1.le hv.2
    _ = ∫ v in (1 / 2 : ℝ)..1, g v := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
    _ = (9 / 8 : ℝ) *
        ∫ v in (1 / 2 : ℝ)..1, Real.exp (heightTenPositiveNearTailExponent v) := by
      dsimp [g]
      rw [intervalIntegral.integral_const_mul]
    _ ≤ 27 / 200 := by
      nlinarith [integral_exp_heightTenPositiveNearTailExponent_le_threeTwentyFifths]

theorem rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_le_fortyNineFiftieths
    (v : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLine 1 v‖ ^ (-(1 / 2 : ℝ)) ≤ 49 / 50 := by
  let d := ‖deBruijnNewmanRiemannSiegelLine 1 v‖
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hdSq := norm_deBruijnNewmanRiemannSiegelLine_one_sq v
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdPos : 0 < d := by
    have hone := one_le_norm_deBruijnNewmanRiemannSiegelLine_one v
    dsimp [d]
    linarith
  have hdLowerSq : (9 / 8 : ℝ) ≤ d ^ 2 := by
    dsimp [d] at hdSq ⊢
    nlinarith [sq_nonneg (v - 3 * Real.sqrt 2 / 4)]
  have hdLower : (2500 / 2401 : ℝ) ≤ d := by
    have hrat : (2500 / 2401 : ℝ) ^ 2 < 9 / 8 := by norm_num
    nlinarith [sq_nonneg d]
  have hsqrtLower : (50 / 49 : ℝ) ≤ Real.sqrt d := by
    rw [Real.le_sqrt (by norm_num) hd0]
    norm_num
    exact hdLower
  have hrecip : 1 / Real.sqrt d ≤ 1 / (50 / 49 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hsqrtLower
  have hrpow : d ^ (-(1 / 2 : ℝ)) = (Real.sqrt d)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hdPos.le]
  rw [show ‖deBruijnNewmanRiemannSiegelLine 1 v‖ = d by rfl, hrpow]
  norm_num at hrecip ⊢
  exact hrecip

def heightTenPositiveMiddleTailExponent (v : ℝ) : ℝ :=
  -(3683 / 2000 : ℝ) * v ^ 2 - (517 / 125) * v + 13 / 5

def heightTenPositiveMiddleTailExponentDeriv (v : ℝ) : ℝ :=
  -(3683 / 1000 : ℝ) * v - 517 / 125

def heightTenPositiveMiddleTailExponentDeriv2 (_v : ℝ) : ℝ :=
  -(3683 / 1000 : ℝ)

theorem hasDerivAt_heightTenPositiveMiddleTailExponent (v : ℝ) :
    HasDerivAt heightTenPositiveMiddleTailExponent
      (heightTenPositiveMiddleTailExponentDeriv v) v := by
  have h := ((((hasDerivAt_id v).pow 2).const_mul (3683 / 2000 : ℝ)).neg.sub
    ((hasDerivAt_id v).const_mul (517 / 125 : ℝ))).add_const (13 / 5 : ℝ)
  have hfun : heightTenPositiveMiddleTailExponent =
      ((fun y : ℝ => -((3683 / 2000 : ℝ) * (id ^ 2) y)) -
        fun y : ℝ => (517 / 125 : ℝ) * id y) +
        fun _ : ℝ => (13 / 5 : ℝ) := by
    funext y
    dsimp [heightTenPositiveMiddleTailExponent]
    ring
  rw [hfun]
  exact h.congr_deriv (by
    dsimp [heightTenPositiveMiddleTailExponentDeriv]
    ring)

theorem hasDerivAt_heightTenPositiveMiddleTailExponentDeriv (v : ℝ) :
    HasDerivAt heightTenPositiveMiddleTailExponentDeriv
      (heightTenPositiveMiddleTailExponentDeriv2 v) v := by
  have h := ((hasDerivAt_id v).const_mul (3683 / 1000 : ℝ)).neg.sub_const
    (517 / 125 : ℝ)
  have hfun : heightTenPositiveMiddleTailExponentDeriv =
      (fun y : ℝ => -((3683 / 1000 : ℝ) * id y)) -
        fun _ : ℝ => (517 / 125 : ℝ) := by
    funext y
    dsimp [heightTenPositiveMiddleTailExponentDeriv]
    ring
  rw [hfun]
  exact h.congr_deriv (by
    dsimp [heightTenPositiveMiddleTailExponentDeriv2]
    ring)

private theorem heightTen_positiveMiddleTailSecondFactor_nonneg
    {v : ℝ} (hv1 : 1 ≤ v) :
    0 ≤ heightTenPositiveMiddleTailExponentDeriv v ^ 2 +
      heightTenPositiveMiddleTailExponentDeriv2 v := by
  let x := (3683 / 1000 : ℝ) * v + 517 / 125
  have hx7 : 7 ≤ x := by dsimp [x]; nlinarith
  have hxm : 0 ≤ x - 7 := by linarith
  have hxp : 0 ≤ x + 7 := by linarith
  have hprod := mul_nonneg hxm hxp
  dsimp [heightTenPositiveMiddleTailExponentDeriv,
    heightTenPositiveMiddleTailExponentDeriv2, x] at hprod ⊢
  nlinarith

theorem convexOn_exp_heightTenPositiveMiddleTailExponent :
    ConvexOn ℝ (Set.Icc (1 : ℝ) 2)
      (fun v => Real.exp (heightTenPositiveMiddleTailExponent v)) := by
  let f : ℝ → ℝ := fun v => Real.exp (heightTenPositiveMiddleTailExponent v)
  let f' : ℝ → ℝ := fun v =>
    Real.exp (heightTenPositiveMiddleTailExponent v) *
      heightTenPositiveMiddleTailExponentDeriv v
  let f'' : ℝ → ℝ := fun v =>
    Real.exp (heightTenPositiveMiddleTailExponent v) *
      (heightTenPositiveMiddleTailExponentDeriv v ^ 2 +
        heightTenPositiveMiddleTailExponentDeriv2 v)
  change ConvexOn ℝ (Set.Icc (1 : ℝ) 2) f
  have hfcont : Continuous f := by
    dsimp [f]
    unfold heightTenPositiveMiddleTailExponent
    fun_prop
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'')
    (convex_Icc (1 : ℝ) 2) hfcont.continuousOn ?_ ?_ ?_
  · intro v hv
    exact (hasDerivAt_heightTenPositiveMiddleTailExponent v).exp.hasDerivWithinAt
  · intro v hv
    have hq := hasDerivAt_heightTenPositiveMiddleTailExponent v
    have hqp := hasDerivAt_heightTenPositiveMiddleTailExponentDeriv v
    have h := hq.exp.mul hqp
    have hfun : f' =
        (fun x => Real.exp (heightTenPositiveMiddleTailExponent x)) *
          heightTenPositiveMiddleTailExponentDeriv := by
      funext x
      rfl
    rw [hfun]
    exact (h.congr_deriv (by dsimp [f'']; ring)).hasDerivWithinAt
  · intro v hv
    have hvIoo : v ∈ Set.Ioo (1 : ℝ) 2 := by simpa using hv
    exact mul_nonneg (Real.exp_nonneg _)
      (heightTen_positiveMiddleTailSecondFactor_nonneg hvIoo.1.le)

theorem heightTen_positiveMiddleTailTotalExponent_le
    {v : ℝ} (hv1 : 1 ≤ v) (hv2 : v ≤ 2) :
    (13 / 2 : ℝ) * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) +
          (-Real.pi * v ^ 2 +
            Real.sqrt 2 * Real.pi * (1 + 1 / 2) * v) -
        Real.pi * (Real.sqrt 2 / 2) * v ≤
      heightTenPositiveMiddleTailExponent v := by
  have harg := heightTen_positiveMiddleTailAnglePolynomial_le hv1 hv2
  have hphase := mul_le_mul_of_nonneg_left harg (by norm_num : (0 : ℝ) ≤ 13 / 2)
  have hpiSqrtUpper : Real.pi * Real.sqrt 2 ≤ (1111 / 250 : ℝ) := by
    calc
      Real.pi * Real.sqrt 2 = 2 * (Real.pi * (Real.sqrt 2 / 2)) := by ring
      _ ≤ 2 * (1111 / 500 : ℝ) := by
        gcongr
        exact pi_mul_sqrtTwoHalf_le_oneThousandOneHundredEleven_div_fiveHundred
      _ = (1111 / 250 : ℝ) := by norm_num
  have hpiLower : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hvNonneg : 0 ≤ v := by linarith
  have hlinear := mul_le_mul_of_nonneg_right hpiSqrtUpper hvNonneg
  have hquadratic := mul_le_mul_of_nonneg_right hpiLower (sq_nonneg v)
  dsimp [heightTenPositiveMiddleTailAnglePolynomial,
    heightTenPositiveMiddleTailExponent] at hphase ⊢
  nlinarith

theorem norm_heightTenRiemannSiegelLineIntegrand_one_positiveMiddleTail_le
    {v : ℝ} (hv1 : 1 ≤ v) (hv2 : v ≤ 2) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖ ≤
      (49 / 50 : ℝ) * (9 / 8) *
        Real.exp (heightTenPositiveMiddleTailExponent v) := by
  have hvNonneg : 0 ≤ v := by linarith
  rw [norm_heightTenRiemannSiegelLineIntegrand_one_eq_factorization]
  have hrpow :=
    rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_le_fortyNineFiftieths v
  have hden := one_div_norm_deBruijnNewmanRiemannSiegelDenominator_tail_le
    (v := v) (by
      have hvHalf : (1 / 2 : ℝ) ≤ v := by linarith
      simpa [abs_of_nonneg hvNonneg] using hvHalf)
  have hexponent := heightTen_positiveMiddleTailTotalExponent_le hv1 hv2
  let A := (13 / 2 : ℝ) * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) +
    (-Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (1 + 1 / 2) * v)
  let B := -(Real.pi * (Real.sqrt 2 / 2) * v)
  have hdenB :
      1 / ‖deBruijnNewmanRiemannSiegelDenominator
          (deBruijnNewmanRiemannSiegelLine 1 v)‖ ≤
        (9 / 8 : ℝ) * Real.exp B := by
    simpa [B, abs_of_nonneg hvNonneg] using hden
  calc
    ‖deBruijnNewmanRiemannSiegelLine 1 v‖ ^ (-(1 / 2 : ℝ)) *
          Real.exp A *
          (1 / ‖deBruijnNewmanRiemannSiegelDenominator
            (deBruijnNewmanRiemannSiegelLine 1 v)‖) ≤
        (49 / 50 : ℝ) * Real.exp A * ((9 / 8) * Real.exp B) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hrpow (Real.exp_nonneg _)) hdenB
        (one_div_nonneg.mpr (norm_nonneg _))
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    _ = (49 / 50 : ℝ) * (9 / 8) * Real.exp (A + B) := by
      have hab := Real.exp_add A B
      rw [hab]
      ring
    _ ≤ (49 / 50 : ℝ) * (9 / 8) *
        Real.exp (heightTenPositiveMiddleTailExponent v) := by
      gcongr
      dsimp [A, B]
      nlinarith

theorem exp_neg_le_heightTenThirtySecondQuadraticPolynomial
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ (1 - t / 32 + (t / 32) ^ 2 / 2) ^ 32 := by
  let y := t / 32
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
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hquad 32
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow
  have hty : -(32 * y) = -t := by dsimp [y]; ring
  rw [hty] at hpow
  simpa only [y] using hpow

def heightTenPositiveMiddleTailExpEnvelope (v : ℝ) : ℝ :=
  let t := -heightTenPositiveMiddleTailExponent v
  (1 - t / 32 + (t / 32) ^ 2 / 2) ^ 32

theorem heightTenPositiveMiddleTailExponent_nonpos
    {v : ℝ} (hv1 : 1 ≤ v) :
    heightTenPositiveMiddleTailExponent v ≤ 0 := by
  have hvSq : 1 ≤ v ^ 2 := by nlinarith [sq_nonneg v]
  dsimp [heightTenPositiveMiddleTailExponent]
  nlinarith

theorem exp_heightTenPositiveMiddleTailExponent_le_envelope
    {v : ℝ} (hv1 : 1 ≤ v) :
    Real.exp (heightTenPositiveMiddleTailExponent v) ≤
      heightTenPositiveMiddleTailExpEnvelope v := by
  have hq := heightTenPositiveMiddleTailExponent_nonpos hv1
  have h := exp_neg_le_heightTenThirtySecondQuadraticPolynomial
    (-heightTenPositiveMiddleTailExponent v) (by linarith)
  simpa [heightTenPositiveMiddleTailExpEnvelope] using h

private def heightTenMiddleTailNode (n : ℕ) : ℝ :=
  1 + n / 8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Normalize the nine exact rational node envelopes in one kernel-checked step.
theorem integral_exp_heightTenPositiveMiddleTailExponent_le_oneTwoHundredTen :
    (∫ v in (1 : ℝ)..2, Real.exp (heightTenPositiveMiddleTailExponent v)) ≤
      1 / 210 := by
  let f : ℝ → ℝ := fun v => Real.exp (heightTenPositiveMiddleTailExponent v)
  have hfcont : Continuous f := by
    dsimp [f]
    unfold heightTenPositiveMiddleTailExponent
    fun_prop
  have hsplit :
      ∑ k ∈ range 8,
          ∫ v in heightTenMiddleTailNode k..heightTenMiddleTailNode (k + 1), f v =
        ∫ v in (1 : ℝ)..2, f v := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := f) (a := heightTenMiddleTailNode) (n := 8)
      (fun k hk => hfcont.intervalIntegrable (μ := volume) _ _)
    norm_num [heightTenMiddleTailNode] at h ⊢
    exact h
  have hsegments :
      ∑ k ∈ range 8,
          ∫ v in heightTenMiddleTailNode k..heightTenMiddleTailNode (k + 1), f v ≤
        ∑ k ∈ range 8, (1 / 16 : ℝ) *
          (f (heightTenMiddleTailNode k) + f (heightTenMiddleTailNode (k + 1))) := by
    apply sum_le_sum
    intro k hk
    have hk8 : k < 8 := mem_range.mp hk
    have hkReal : (k : ℝ) ≤ 7 := by
      exact_mod_cast (Nat.le_pred_of_lt hk8)
    have hleft : 1 ≤ heightTenMiddleTailNode k := by
      dsimp [heightTenMiddleTailNode]
      have hkNonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have hright : heightTenMiddleTailNode (k + 1) ≤ 2 := by
      dsimp [heightTenMiddleTailNode]
      push_cast
      linarith
    have hsub := Set.Icc_subset_Icc hleft hright
    have hconv : ConvexOn ℝ
        (Set.Icc (heightTenMiddleTailNode k) (heightTenMiddleTailNode (k + 1))) f := by
      refine ⟨convex_Icc _ _, ?_⟩
      intro x hx y hy a b ha hb hab
      exact convexOn_exp_heightTenPositiveMiddleTailExponent.2
        (hsub hx) (hsub hy) ha hb hab
    have htrap := intervalIntegral_le_trapezoid_of_convexOn
      (show heightTenMiddleTailNode k ≤ heightTenMiddleTailNode (k + 1) by
        dsimp [heightTenMiddleTailNode]
        push_cast
        norm_num
        linarith)
      hconv hfcont
    have hwidth :
        (heightTenMiddleTailNode (k + 1) - heightTenMiddleTailNode k) / 2 =
          (1 / 16 : ℝ) := by
      dsimp [heightTenMiddleTailNode]
      push_cast
      ring
    rw [hwidth] at htrap
    exact htrap
  rw [hsplit] at hsegments
  calc
    (∫ v in (1 : ℝ)..2, Real.exp (heightTenPositiveMiddleTailExponent v)) =
        ∫ v in (1 : ℝ)..2, f v := by rfl
    _ ≤ ∑ k ∈ range 8, (1 / 16 : ℝ) *
          (f (heightTenMiddleTailNode k) + f (heightTenMiddleTailNode (k + 1))) := hsegments
    _ ≤ ∑ k ∈ range 8, (1 / 16 : ℝ) *
          (heightTenPositiveMiddleTailExpEnvelope (heightTenMiddleTailNode k) +
            heightTenPositiveMiddleTailExpEnvelope (heightTenMiddleTailNode (k + 1))) := by
      apply sum_le_sum
      intro k hk
      have hk8 : k < 8 := mem_range.mp hk
      have hk9 : k + 1 ≤ 8 := by omega
      have hkReal : (k : ℝ) ≤ 7 := by
        exact_mod_cast (Nat.le_pred_of_lt hk8)
      dsimp [f]
      gcongr
      · apply exp_heightTenPositiveMiddleTailExponent_le_envelope
        dsimp [heightTenMiddleTailNode]
        have hkNonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      · apply exp_heightTenPositiveMiddleTailExponent_le_envelope
        dsimp [heightTenMiddleTailNode]
        have hkNonneg : (0 : ℝ) ≤ (k + 1 : ℕ) := Nat.cast_nonneg (k + 1)
        nlinarith
    _ ≤ 1 / 210 := by
      norm_num [Finset.sum_range_succ, heightTenMiddleTailNode,
        heightTenPositiveMiddleTailExpEnvelope, heightTenPositiveMiddleTailExponent]

theorem integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveMiddleTail_le :
    (∫ v in Set.Ioc (1 : ℝ) 2,
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) ≤ 21 / 4000 := by
  let g : ℝ → ℝ := fun v =>
    (49 / 50 : ℝ) * (9 / 8) * Real.exp (heightTenPositiveMiddleTailExponent v)
  have hactual : IntegrableOn (fun v : ℝ =>
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) (Set.Ioc (1 : ℝ) 2) :=
    (integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint (13 / 2))).norm.integrableOn
  have hg : IntegrableOn g (Set.Ioc (1 : ℝ) 2) := by
    have hcont : Continuous g := by
      dsimp [g]
      unfold heightTenPositiveMiddleTailExponent
      fun_prop
    exact hcont.integrableOn_Ioc
  calc
    (∫ v in Set.Ioc (1 : ℝ) 2,
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) ≤
        ∫ v in Set.Ioc (1 : ℝ) 2, g v := by
      apply setIntegral_mono_on hactual hg measurableSet_Ioc
      intro v hv
      exact norm_heightTenRiemannSiegelLineIntegrand_one_positiveMiddleTail_le hv.1.le hv.2
    _ = ∫ v in (1 : ℝ)..2, g v := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
    _ = (49 / 50 : ℝ) * (9 / 8) *
        ∫ v in (1 : ℝ)..2, Real.exp (heightTenPositiveMiddleTailExponent v) := by
      dsimp [g]
      rw [intervalIntegral.integral_const_mul]
    _ ≤ 21 / 4000 := by
      nlinarith [integral_exp_heightTenPositiveMiddleTailExponent_le_oneTwoHundredTen]

private theorem arg_deBruijnNewmanRiemannSiegelLine_one_eq_neg_arctan_of_re_pos
    {v : ℝ} (hre : 0 < (deBruijnNewmanRiemannSiegelLine 1 v).re) :
    Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) =
      -Real.arctan
        ((Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v)) := by
  let z := deBruijnNewmanRiemannSiegelLine 1 v
  have hzRe : z.re = 3 / 2 - Real.sqrt 2 / 2 * v := by
    simp [z]
    norm_num
  have hzRePos : 0 < z.re := by simpa only [z] using hre
  have htan :
      Real.tan (Complex.arg z) =
        -((Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v)) := by
    rw [Complex.tan_arg]
    rw [hzRe]
    simp only [z, deBruijnNewmanRiemannSiegelLine_im]
    ring
  have hprincipal := Real.arctan_eq_of_tan_eq htan ⟨
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hzRePos),
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hzRePos)⟩
  simpa only [Real.arctan_neg] using hprincipal.symm

theorem heightTen_positiveFarTailAngle_le
    {v : ℝ} (hv : 2 ≤ v) :
    (6 / 5 : ℝ) ≤ -Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) := by
  let z := deBruijnNewmanRiemannSiegelLine 1 v
  have hv0 : 0 ≤ v := by linarith
  have him : z.im < 0 := by
    have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    dsimp [z]
    simp only [deBruijnNewmanRiemannSiegelLine_im]
    nlinarith
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  by_cases hrePos : 0 < z.re
  · have harg := arg_deBruijnNewmanRiemannSiegelLine_one_eq_neg_arctan_of_re_pos
      (v := v) (by simpa only [z] using hrePos)
    have hzRe : z.re = 3 / 2 - Real.sqrt 2 / 2 * v := by
      simp [z]
      norm_num
    have hden : 0 < 3 / 2 - Real.sqrt 2 / 2 * v := by
      rw [← hzRe]
      exact hrePos
    let r := (Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v)
    have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
    have hsqrtLower : (7071 / 5000 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2]
    have hsqrtMul := mul_le_mul_of_nonneg_right hsqrtLower hv0
    have hr3 : (3 : ℝ) ≤ r := by
      dsimp [r]
      rw [le_div_iff₀ hden]
      nlinarith
    have hrPos : 0 < r := by
      dsimp [r]
      positivity
    have hinvPos : 0 < r⁻¹ := inv_pos.mpr hrPos
    have hinvLe : r⁻¹ ≤ (1 / 3 : ℝ) := by
      rw [inv_le_comm₀ hrPos (by norm_num : (0 : ℝ) < 1 / 3)]
      norm_num
      exact hr3
    have harctanInvLe : Real.arctan r⁻¹ ≤ (1 / 3 : ℝ) :=
      (arctan_le_self_of_nonneg hinvPos.le).trans hinvLe
    have hinvEq := Real.arctan_inv_of_pos hrPos
    have harctanLower : (6 / 5 : ℝ) ≤ Real.arctan r := by
      nlinarith
    rw [harg, neg_neg]
    simpa only [r] using harctanLower
  · have hre : z.re ≤ 0 := le_of_not_gt hrePos
    have hratio : z.re / ‖z‖ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hre (norm_nonneg z)
    have harccos : Real.pi / 2 ≤ Real.arccos (z.re / ‖z‖) := by
      simpa using (Real.arccos_le_arccos hratio)
    have hsix : (6 / 5 : ℝ) ≤ Real.pi / 2 := by nlinarith
    rw [Complex.arg_of_im_neg him, neg_neg]
    exact hsix.trans harccos

theorem heightTen_positiveFarTailTotalExponent_le
    {v : ℝ} (hv : 2 ≤ v) :
    (13 / 2 : ℝ) * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) +
          (-Real.pi * v ^ 2 +
            Real.sqrt 2 * Real.pi * (1 + 1 / 2) * v) -
        Real.pi * (Real.sqrt 2 / 2) * v ≤
      -(9 / 2 : ℝ) * v := by
  have harg := heightTen_positiveFarTailAngle_le hv
  have hphase := mul_le_mul_of_nonneg_left (show
      Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) ≤ -(6 / 5 : ℝ) by
        linarith) (by norm_num : (0 : ℝ) ≤ 13 / 2)
  have hpiSqrtUpper : Real.pi * Real.sqrt 2 ≤ (1111 / 250 : ℝ) := by
    calc
      Real.pi * Real.sqrt 2 = 2 * (Real.pi * (Real.sqrt 2 / 2)) := by ring
      _ ≤ 2 * (1111 / 500 : ℝ) := by
        gcongr
        exact pi_mul_sqrtTwoHalf_le_oneThousandOneHundredEleven_div_fiveHundred
      _ = (1111 / 250 : ℝ) := by norm_num
  have hpiLower : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hv0 : 0 ≤ v := by linarith
  have hlinear := mul_le_mul_of_nonneg_right hpiSqrtUpper hv0
  have hquadratic := mul_le_mul_of_nonneg_right hpiLower (sq_nonneg v)
  have hvSq : 2 * v ≤ v ^ 2 := by
    nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hv)]
  nlinarith

theorem norm_heightTenRiemannSiegelLineIntegrand_one_positiveFarTail_le
    {v : ℝ} (hv : 2 ≤ v) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖ ≤
      (49 / 50 : ℝ) * (9 / 8) * Real.exp (-(9 / 2 : ℝ) * v) := by
  have hv0 : 0 ≤ v := by linarith
  rw [norm_heightTenRiemannSiegelLineIntegrand_one_eq_factorization]
  have hrpow :=
    rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_le_fortyNineFiftieths v
  have hden := one_div_norm_deBruijnNewmanRiemannSiegelDenominator_tail_le
    (v := v) (by
      have hvHalf : (1 / 2 : ℝ) ≤ v := by linarith
      simpa [abs_of_nonneg hv0] using hvHalf)
  have hexponent := heightTen_positiveFarTailTotalExponent_le hv
  let A := (13 / 2 : ℝ) * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) +
    (-Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (1 + 1 / 2) * v)
  let B := -(Real.pi * (Real.sqrt 2 / 2) * v)
  have hdenB :
      1 / ‖deBruijnNewmanRiemannSiegelDenominator
          (deBruijnNewmanRiemannSiegelLine 1 v)‖ ≤
        (9 / 8 : ℝ) * Real.exp B := by
    simpa [B, abs_of_nonneg hv0] using hden
  calc
    ‖deBruijnNewmanRiemannSiegelLine 1 v‖ ^ (-(1 / 2 : ℝ)) *
          Real.exp A *
          (1 / ‖deBruijnNewmanRiemannSiegelDenominator
            (deBruijnNewmanRiemannSiegelLine 1 v)‖) ≤
        (49 / 50 : ℝ) * Real.exp A * ((9 / 8) * Real.exp B) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hrpow (Real.exp_nonneg _)) hdenB
        (one_div_nonneg.mpr (norm_nonneg _))
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    _ = (49 / 50 : ℝ) * (9 / 8) * Real.exp (A + B) := by
      have hab := Real.exp_add A B
      rw [hab]
      ring
    _ ≤ (49 / 50 : ℝ) * (9 / 8) * Real.exp (-(9 / 2 : ℝ) * v) := by
      gcongr
      dsimp [A, B]
      nlinarith

theorem oneThousand_le_exp_nine :
    (1000 : ℝ) ≤ Real.exp 9 := by
  have hseries := Real.sum_le_exp_of_nonneg (x := (9 : ℝ)) (by norm_num) 7
  have hpartial :
      (1000 : ℝ) ≤ ∑ i ∈ range 7, (9 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact hpartial.trans hseries

theorem integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveFarFarTail_le :
    (∫ v in Set.Ioi (2 : ℝ),
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) ≤ 1 / 4000 := by
  let g : ℝ → ℝ := fun v =>
    (49 / 50 : ℝ) * (9 / 8) * Real.exp (-(9 / 2 : ℝ) * v)
  have hactual : IntegrableOn (fun v : ℝ =>
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) (Set.Ioi (2 : ℝ)) :=
    (integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint (13 / 2))).norm.integrableOn
  have hg : IntegrableOn g (Set.Ioi (2 : ℝ)) := by
    exact (integrableOn_exp_mul_Ioi (a := -(9 / 2 : ℝ)) (by norm_num) 2).const_mul _
  have hexpInv : Real.exp (-(9 : ℝ)) ≤ 1 / 1000 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num) oneThousand_le_exp_nine
  calc
    (∫ v in Set.Ioi (2 : ℝ),
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) ≤
        ∫ v in Set.Ioi (2 : ℝ), g v := by
      apply setIntegral_mono_on hactual hg measurableSet_Ioi
      intro v hv
      exact norm_heightTenRiemannSiegelLineIntegrand_one_positiveFarTail_le hv.le
    _ = (49 / 50 : ℝ) * (9 / 8) *
        (-(Real.exp (-(9 / 2 : ℝ) * 2)) / (-(9 / 2 : ℝ))) := by
      dsimp [g]
      rw [MeasureTheory.integral_const_mul]
      rw [integral_exp_mul_Ioi (a := -(9 / 2 : ℝ)) (by norm_num)]
    _ ≤ 1 / 4000 := by
      norm_num at hexpInv ⊢
      nlinarith

theorem integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveFarTail_le :
    (∫ v in Set.Ioi (1 : ℝ),
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) ≤ 11 / 2000 := by
  let f : ℝ → ℝ := fun v =>
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖
  have hfull : IntegrableOn f (Set.Ioi (1 : ℝ)) :=
    (integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint (13 / 2))).norm.integrableOn
  have htail : IntegrableOn f (Set.Ioi (2 : ℝ)) := hfull.mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hfull htail
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hsplit
  calc
    (∫ v in Set.Ioi (1 : ℝ),
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) =
        (∫ v in Set.Ioc (1 : ℝ) 2, f v) + ∫ v in Set.Ioi (2 : ℝ), f v := by
      simpa only [f] using hsplit.symm
    _ ≤ 21 / 4000 + 1 / 4000 := by
      exact add_le_add
        integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveMiddleTail_le
        integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveFarFarTail_le
    _ = 11 / 2000 := by norm_num

theorem sum_integral_norm_heightTenRiemannSiegelLineIntegrand_one_tails_le_threeTwentieths :
    (∫ x in Set.Ioi (1 / 2 : ℝ),
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint 10) (-x)‖) +
      (∫ v in Set.Ioc (1 / 2 : ℝ) 1,
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) +
      (∫ v in Set.Ioi (1 : ℝ),
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖) ≤
      3 / 20 := by
  nlinarith [integral_norm_heightTenRiemannSiegelLineIntegrand_one_negativeTail_le,
    integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveNearTail_le,
    integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveFarTail_le]

theorem heightTenRiemannSiegelNegativeEndpointMass_one_le_twoHundredNineteenTwoThousandths :
    heightTenRiemannSiegelNegativeEndpointMass 1 ≤ 219 / 2000 := by
  let f : ℝ → ℝ := fun x =>
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint 10) (-x)‖
  have hfull : IntegrableOn f (Set.Ioi (0 : ℝ)) := by
    exact ((integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint 10)).norm.comp_neg).integrableOn
  have htail : IntegrableOn f (Set.Ioi (1 / 2 : ℝ)) :=
    hfull.mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hfull htail
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hsplit
  have hchange := integral_comp_neg_Ioi (0 : ℝ) (fun v : ℝ =>
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint 10) v‖)
  calc
    heightTenRiemannSiegelNegativeEndpointMass 1 =
        ∫ x in Set.Ioi (0 : ℝ), f x := by
      simpa only [heightTenRiemannSiegelNegativeEndpointMass, neg_zero, f] using hchange.symm
    _ = (∫ x in Set.Ioc (0 : ℝ) (1 / 2), f x) +
        ∫ x in Set.Ioi (1 / 2 : ℝ), f x := hsplit.symm
    _ ≤ 1 / 10 + 19 / 2000 := by
      exact add_le_add
        integral_norm_heightTenRiemannSiegelLineIntegrand_one_negativeCompact_le
        integral_norm_heightTenRiemannSiegelLineIntegrand_one_negativeTail_le
    _ = 219 / 2000 := by norm_num

theorem heightTenRiemannSiegelPositiveEndpointMass_one_le_nineHundredEightyOneTwoThousandths :
    heightTenRiemannSiegelPositiveEndpointMass 1 ≤ 981 / 2000 := by
  let f : ℝ → ℝ := fun v =>
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖
  have hfull : IntegrableOn f (Set.Ioi (0 : ℝ)) :=
    (integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint (13 / 2))).norm.integrableOn
  have hhalf : IntegrableOn f (Set.Ioi (1 / 2 : ℝ)) :=
    hfull.mono_set (Ioi_subset_Ioi (by norm_num))
  have hone : IntegrableOn f (Set.Ioi (1 : ℝ)) :=
    hhalf.mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit0 := intervalIntegral.integral_interval_add_Ioi hfull hhalf
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hsplit0
  have hsplitHalf := intervalIntegral.integral_interval_add_Ioi hhalf hone
  rw [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hsplitHalf
  calc
    heightTenRiemannSiegelPositiveEndpointMass 1 =
        (∫ v in Set.Ioc (0 : ℝ) (1 / 2), f v) +
          ((∫ v in Set.Ioc (1 / 2 : ℝ) 1, f v) +
            ∫ v in Set.Ioi (1 : ℝ), f v) := by
      change (∫ v in Set.Ioi (0 : ℝ), f v) = _
      rw [← hsplit0, ← hsplitHalf]
    _ ≤ 7 / 20 + (27 / 200 + 11 / 2000) := by
      gcongr
      · exact integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveCompact_le
      · exact integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveNearTail_le
      · exact integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveFarTail_le
    _ = 981 / 2000 := by norm_num

theorem heightTenRiemannSiegelOneEndpointMassBound :
    HeightTenRiemannSiegelOneEndpointMassBound := by
  dsimp [HeightTenRiemannSiegelOneEndpointMassBound]
  nlinarith [
    heightTenRiemannSiegelNegativeEndpointMass_one_le_twoHundredNineteenTwoThousandths,
    heightTenRiemannSiegelPositiveEndpointMass_one_le_nineHundredEightyOneTwoThousandths]

theorem heightTenRiemannSiegelOneRemainderMargin :
    HeightTenRiemannSiegelOneRemainderMargin :=
  heightTenRiemannSiegelOneRemainderMargin_of_phaseNormBounds
    heightTenRiemannSiegelOneEndpointMassBound
    heightTenRiemannSiegelOnePrefactorPhaseMargin

theorem riemannZeta_criticalLine_ne_zero_thirteenHalves_ten
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 10) :
    riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * I) ≠ 0 :=
  riemannZeta_criticalLine_ne_zero_thirteenHalves_ten_of_riemannSiegel
    heightTenRiemannSiegelOneRemainderMargin hy0 hy1

theorem speiserZetaDerivRatio_rightVertical_re_neg_thirteenHalves_ten
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 10) :
    (speiserZetaDerivRatio
      ((1 / 2 : ℂ) + (y : ℂ) * I)).re < 0 :=
  speiserZetaDerivRatio_rightVertical_re_neg_thirteenHalves_ten_of_riemannSiegel
    heightTenRiemannSiegelOneRemainderMargin hy0 hy1

end

end LeanLab.Riemann
