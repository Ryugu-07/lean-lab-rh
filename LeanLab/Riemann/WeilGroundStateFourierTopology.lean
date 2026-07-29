import LeanLab.Riemann.WeilGroundStateAlignment

set_option linter.style.header false

/-!
# Fourier topology at the Connes ground-state approximation edge

Compact-uniform convergence of the centered Fourier transform on a closed strip is controlled by
an exponentially weighted `L¹` error.  This file proves that transfer and records a smooth
escaping-support packet showing why unweighted `L¹` or `L²` convergence alone is insufficient.
-/

noncomputable section

open Complex Filter Function MeasureTheory Set
open scoped ContDiff Topology

namespace LeanLab.Riemann

/-- The Fourier transform in the source coordinate used by the Connes ground-state route. -/
def weilGroundStateFourierTransform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  compactLaplaceTransform f (I * z)

/-- The exponentially weighted `L¹` error that controls a closed Fourier strip. -/
def weilGroundStateFourierStripError
    (A : ℝ) (f g : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, Real.exp (A * |x|) * ‖f x - g x‖

theorem continuous_weilGroundStateFourierStripMajorant
    {A : ℝ} {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x : ℝ ↦ Real.exp (A * |x|) * ‖f x - g x‖) := by
  fun_prop

theorem hasCompactSupport_weilGroundStateFourierStripMajorant
    {A : ℝ} {f g : ℝ → ℂ}
    (hfsupp : HasCompactSupport f) (hgsupp : HasCompactSupport g) :
    HasCompactSupport (fun x : ℝ ↦ Real.exp (A * |x|) * ‖f x - g x‖) := by
  exact (hfsupp.sub hgsupp).norm.mul_left

theorem integrable_weilGroundStateFourierStripMajorant
    {A : ℝ} {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (hfsupp : HasCompactSupport f) (hgsupp : HasCompactSupport g) :
    Integrable (fun x : ℝ ↦ Real.exp (A * |x|) * ‖f x - g x‖) := by
  exact (continuous_weilGroundStateFourierStripMajorant hf hg).integrable_of_hasCompactSupport
    (hasCompactSupport_weilGroundStateFourierStripMajorant hfsupp hgsupp)

theorem weilGroundStateFourierStripError_nonneg
    (A : ℝ) (f g : ℝ → ℂ) :
    0 ≤ weilGroundStateFourierStripError A f g := by
  apply integral_nonneg
  intro x
  positivity

theorem norm_exp_I_mul_mul_real (z : ℂ) (x : ℝ) :
    ‖Complex.exp (I * z * (x : ℂ))‖ = Real.exp (-z.im * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem neg_im_mul_le_stripWeight
    {A : ℝ} (_hA : 0 ≤ A) {z : ℂ} (hz : |z.im| ≤ A) (x : ℝ) :
    -z.im * x ≤ A * |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    have hzim : -A ≤ z.im := (abs_le.mp hz).1
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge hx)]
    have hzim : z.im ≤ A := (abs_le.mp hz).2
    nlinarith

theorem norm_exp_I_mul_mul_real_le_stripWeight
    {A : ℝ} (hA : 0 ≤ A) {z : ℂ} (hz : |z.im| ≤ A) (x : ℝ) :
    ‖Complex.exp (I * z * (x : ℂ))‖ ≤ Real.exp (A * |x|) := by
  rw [norm_exp_I_mul_mul_real]
  exact Real.exp_le_exp.mpr (neg_im_mul_le_stripWeight hA hz x)

theorem norm_weilGroundStateFourierTransform_sub_le_stripError
    {A : ℝ} (hA : 0 ≤ A) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (hfsupp : HasCompactSupport f) (hgsupp : HasCompactSupport g)
    {z : ℂ} (hz : |z.im| ≤ A) :
    ‖weilGroundStateFourierTransform f z -
        weilGroundStateFourierTransform g z‖ ≤
      weilGroundStateFourierStripError A f g := by
  have hfInt :
      Integrable (fun x : ℝ ↦ Complex.exp (I * z * (x : ℂ)) * f x) := by
    simpa [mul_assoc] using integrable_compactLaplaceKernel hf hfsupp (I * z)
  have hgInt :
      Integrable (fun x : ℝ ↦ Complex.exp (I * z * (x : ℂ)) * g x) := by
    simpa [mul_assoc] using integrable_compactLaplaceKernel hg hgsupp (I * z)
  have hmajor :=
    integrable_weilGroundStateFourierStripMajorant
      (A := A) hf hg hfsupp hgsupp
  have hdiff :
      weilGroundStateFourierTransform f z -
          weilGroundStateFourierTransform g z =
        ∫ x : ℝ, Complex.exp (I * z * (x : ℂ)) * (f x - g x) := by
    unfold weilGroundStateFourierTransform compactLaplaceTransform
    rw [← integral_sub hfInt hgInt]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hdiff]
  apply norm_integral_le_of_norm_le hmajor
  filter_upwards with x
  rw [norm_mul]
  gcongr
  exact norm_exp_I_mul_mul_real_le_stripWeight hA hz x

/-- Uniform convergence on the whole closed horizontal strip `|Im z| ≤ A`. -/
def WeilGroundStateUniformOnClosedStrip
    (A : ℝ) (F : ℕ → ℂ → ℂ) (target : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      ∀ z : ℂ, |z.im| ≤ A → ‖F n z - target z‖ < ε

theorem weilGroundStateFourier_uniform_zero_of_stripError
    {A : ℝ} (hA : 0 ≤ A) {f g : ℕ → ℝ → ℂ}
    (hf : ∀ n, Continuous (f n)) (hg : ∀ n, Continuous (g n))
    (hfsupp : ∀ n, HasCompactSupport (f n))
    (hgsupp : ∀ n, HasCompactSupport (g n))
    (herror :
      Tendsto (fun n ↦ weilGroundStateFourierStripError A (f n) (g n))
        atTop (nhds 0)) :
    WeilGroundStateUniformOnClosedStrip A
      (fun n z ↦
        weilGroundStateFourierTransform (f n) z -
          weilGroundStateFourierTransform (g n) z)
      (fun _ ↦ 0) := by
  intro ε hε
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        weilGroundStateFourierStripError A (f n) (g n) < ε :=
    (tendsto_order.1 herror).2 ε hε
  filter_upwards [hevent] with n hn
  intro z hz
  simpa only [sub_zero] using
    lt_of_le_of_lt
      (norm_weilGroundStateFourierTransform_sub_le_stripError hA
        (hf n) (hg n) (hfsupp n) (hgsupp n) hz)
      hn

theorem weilGroundStateFourier_uniform_transfer
    {A : ℝ} (hA : 0 ≤ A) {f g : ℕ → ℝ → ℂ} {target : ℂ → ℂ}
    (hf : ∀ n, Continuous (f n)) (hg : ∀ n, Continuous (g n))
    (hfsupp : ∀ n, HasCompactSupport (f n))
    (hgsupp : ∀ n, HasCompactSupport (g n))
    (hgTarget :
      WeilGroundStateUniformOnClosedStrip A
        (fun n ↦ weilGroundStateFourierTransform (g n)) target)
    (herror :
      Tendsto (fun n ↦ weilGroundStateFourierStripError A (f n) (g n))
        atTop (nhds 0)) :
    WeilGroundStateUniformOnClosedStrip A
      (fun n ↦ weilGroundStateFourierTransform (f n)) target := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hfg :
      ∀ᶠ n : ℕ in atTop,
        ∀ z : ℂ, |z.im| ≤ A →
          ‖weilGroundStateFourierTransform (f n) z -
              weilGroundStateFourierTransform (g n) z‖ < ε / 2 := by
    have hzero := weilGroundStateFourier_uniform_zero_of_stripError
      hA hf hg hfsupp hgsupp herror (ε / 2) hhalf
    simpa only [sub_zero] using hzero
  have hgt := hgTarget (ε / 2) hhalf
  filter_upwards [hfg, hgt] with n hfgN hgtN
  intro z hz
  calc
    ‖weilGroundStateFourierTransform (f n) z - target z‖ =
        ‖(weilGroundStateFourierTransform (f n) z -
            weilGroundStateFourierTransform (g n) z) +
          (weilGroundStateFourierTransform (g n) z - target z)‖ := by
      congr 1
      ring
    _ ≤
        ‖weilGroundStateFourierTransform (f n) z -
            weilGroundStateFourierTransform (g n) z‖ +
          ‖weilGroundStateFourierTransform (g n) z - target z‖ := by
      exact norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hfgN z hz) (hgtN z hz)
    _ = ε := by ring

theorem weilGroundStateCenteredFourier_eq_transform
    (L : ℝ) (f : ℝ → ℂ) (z : ℂ) :
    weilGroundStateCenteredFourier L f z =
      weilGroundStateFourierTransform (fun x ↦ f (x + L / 2)) z := by
  rfl

theorem norm_weilGroundStateCenteredFourier_sub_le_stripError
    {A : ℝ} (hA : 0 ≤ A) {L : ℝ} {f g : ℝ → ℂ}
    (hf : Continuous (fun x ↦ f (x + L / 2)))
    (hg : Continuous (fun x ↦ g (x + L / 2)))
    (hfsupp : HasCompactSupport (fun x ↦ f (x + L / 2)))
    (hgsupp : HasCompactSupport (fun x ↦ g (x + L / 2)))
    {z : ℂ} (hz : |z.im| ≤ A) :
    ‖weilGroundStateCenteredFourier L f z -
        weilGroundStateCenteredFourier L g z‖ ≤
      weilGroundStateFourierStripError A
        (fun x ↦ f (x + L / 2)) (fun x ↦ g (x + L / 2)) := by
  simpa only [weilGroundStateCenteredFourier_eq_transform] using
    norm_weilGroundStateFourierTransform_sub_le_stripError
      hA hf hg hfsupp hgsupp hz

theorem weilGroundStateCenteredFourier_uniform_transfer
    {A : ℝ} (hA : 0 ≤ A) {L : ℕ → ℝ}
    {f g : ℕ → ℝ → ℂ} {target : ℂ → ℂ}
    (hf : ∀ n, Continuous (fun x ↦ f n (x + L n / 2)))
    (hg : ∀ n, Continuous (fun x ↦ g n (x + L n / 2)))
    (hfsupp : ∀ n, HasCompactSupport (fun x ↦ f n (x + L n / 2)))
    (hgsupp : ∀ n, HasCompactSupport (fun x ↦ g n (x + L n / 2)))
    (hgTarget :
      WeilGroundStateUniformOnClosedStrip A
        (fun n z ↦ weilGroundStateCenteredFourier (L n) (g n) z) target)
    (herror :
      Tendsto
        (fun n ↦ weilGroundStateFourierStripError A
          (fun x ↦ f n (x + L n / 2))
          (fun x ↦ g n (x + L n / 2)))
        atTop (nhds 0)) :
    WeilGroundStateUniformOnClosedStrip A
      (fun n z ↦ weilGroundStateCenteredFourier (L n) (f n) z) target := by
  simpa only [weilGroundStateCenteredFourier_eq_transform] using
    weilGroundStateFourier_uniform_transfer
      hA hf hg hfsupp hgsupp hgTarget herror

/-- The fixed interior point at which the escaping packet remains visible. -/
def weilGroundStateEscapingPoint : ℂ :=
  -I / 4

/-- The real Laplace coordinate corresponding to `weilGroundStateEscapingPoint`. -/
def weilGroundStateEscapingRate : ℂ :=
  1 / 4

/-- A smooth compact packet translated to `n` and scaled by `exp (-n/4)`. -/
def weilGroundStateEscapingPacket (n : ℕ) (x : ℝ) : ℂ :=
  (Real.exp (-((n : ℝ) / 4)) : ℂ) *
    compactLaplaceModulatedBump weilGroundStateEscapingRate (x - n)

theorem contDiff_weilGroundStateEscapingPacket (n : ℕ) :
    ContDiff ℝ ∞ (weilGroundStateEscapingPacket n) := by
  exact contDiff_const.mul
    ((contDiff_compactLaplaceModulatedBump weilGroundStateEscapingRate).comp
      (contDiff_id.sub contDiff_const))

theorem continuous_weilGroundStateEscapingPacket (n : ℕ) :
    Continuous (weilGroundStateEscapingPacket n) :=
  (contDiff_weilGroundStateEscapingPacket n).continuous

theorem hasCompactSupport_weilGroundStateEscapingPacket (n : ℕ) :
    HasCompactSupport (weilGroundStateEscapingPacket n) := by
  exact
    ((hasCompactSupport_compactLaplaceModulatedBump weilGroundStateEscapingRate).comp_homeomorph
      (Homeomorph.addRight (-(n : ℝ)))).mul_left

theorem I_mul_weilGroundStateEscapingPoint :
    I * weilGroundStateEscapingPoint = weilGroundStateEscapingRate := by
  unfold weilGroundStateEscapingPoint weilGroundStateEscapingRate
  calc
    I * (-I / 4) = -(I * I) / 4 := by ring
    _ = 1 / 4 := by rw [Complex.I_mul_I]; norm_num

theorem weilGroundStateEscapingPoint_mem_open_halfStrip :
    |weilGroundStateEscapingPoint.im| < 1 / 2 := by
  norm_num [weilGroundStateEscapingPoint]

@[simp] theorem weilGroundStateFourierTransform_escapingPacket
    (n : ℕ) :
    weilGroundStateFourierTransform
      (weilGroundStateEscapingPacket n) weilGroundStateEscapingPoint = 1 := by
  unfold weilGroundStateFourierTransform weilGroundStateEscapingPacket
  rw [I_mul_weilGroundStateEscapingPoint,
    compactLaplaceTransform_const_mul,
    compactLaplaceTransform_translate,
    compactLaplaceTransform_modulatedBump_self]
  simp only [weilGroundStateEscapingRate, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, mul_one]
  rw [← Complex.exp_add]
  rw [show -((n : ℂ) / 4) +
      (1 / 4 : ℂ) * (n : ℂ) = 0 by
    ring]
  exact Complex.exp_zero

@[simp] theorem weilGroundStateCenteredFourier_zero_escapingPacket
    (n : ℕ) :
    weilGroundStateCenteredFourier 0
      (weilGroundStateEscapingPacket n) weilGroundStateEscapingPoint = 1 := by
  rw [weilGroundStateCenteredFourier_eq_transform]
  simp

/-- The ordinary, unweighted `L¹` mass. -/
def weilGroundStateUnweightedMass (f : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, ‖f x‖

theorem weilGroundStateUnweightedMass_escapingPacket
    (n : ℕ) :
    weilGroundStateUnweightedMass (weilGroundStateEscapingPacket n) =
      Real.exp (-((n : ℝ) / 4)) *
        weilGroundStateUnweightedMass
          (compactLaplaceModulatedBump weilGroundStateEscapingRate) := by
  unfold weilGroundStateUnweightedMass weilGroundStateEscapingPacket
  have htrans :
      (∫ x : ℝ, ‖compactLaplaceModulatedBump
          weilGroundStateEscapingRate (x - n)‖) =
        ∫ x : ℝ, ‖compactLaplaceModulatedBump
          weilGroundStateEscapingRate x‖ := by
    rw [← integral_add_right_eq_self
      (fun x : ℝ ↦ ‖compactLaplaceModulatedBump
        weilGroundStateEscapingRate (x - n)‖) n]
    apply integral_congr_ae
    filter_upwards with x
    norm_num
  calc
    (∫ x : ℝ,
        ‖(Real.exp (-((n : ℝ) / 4)) : ℂ) *
          compactLaplaceModulatedBump
            weilGroundStateEscapingRate (x - n)‖) =
      ∫ x : ℝ,
        Real.exp (-((n : ℝ) / 4)) *
          ‖compactLaplaceModulatedBump
            weilGroundStateEscapingRate (x - n)‖ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
    _ = Real.exp (-((n : ℝ) / 4)) *
        ∫ x : ℝ, ‖compactLaplaceModulatedBump
          weilGroundStateEscapingRate (x - n)‖ := by
      rw [integral_const_mul]
    _ = Real.exp (-((n : ℝ) / 4)) *
        ∫ x : ℝ, ‖compactLaplaceModulatedBump
          weilGroundStateEscapingRate x‖ := by rw [htrans]

theorem tendsto_weilGroundStateUnweightedMass_escapingPacket :
    Tendsto
      (fun n : ℕ ↦
        weilGroundStateUnweightedMass (weilGroundStateEscapingPacket n))
      atTop (nhds 0) := by
  have hn :
      Tendsto (fun n : ℕ ↦ (n : ℝ) / 4) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num) tendsto_natCast_atTop_atTop
  have hexp :
      Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) / 4))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hn
  rw [show (fun n : ℕ ↦
      weilGroundStateUnweightedMass (weilGroundStateEscapingPacket n)) =
      fun n : ℕ ↦
        Real.exp (-((n : ℝ) / 4)) *
          weilGroundStateUnweightedMass
            (compactLaplaceModulatedBump weilGroundStateEscapingRate) by
    funext n
    exact weilGroundStateUnweightedMass_escapingPacket n]
  simpa using hexp.mul_const
    (weilGroundStateUnweightedMass
      (compactLaplaceModulatedBump weilGroundStateEscapingRate))

/-- The unweighted squared mass, included as a negative control for `L²` convergence. -/
def weilGroundStateUnweightedSqMass (f : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, ‖f x‖ ^ 2

theorem weilGroundStateUnweightedSqMass_escapingPacket
    (n : ℕ) :
    weilGroundStateUnweightedSqMass (weilGroundStateEscapingPacket n) =
      Real.exp (-((n : ℝ) / 2)) *
        weilGroundStateUnweightedSqMass
          (compactLaplaceModulatedBump weilGroundStateEscapingRate) := by
  unfold weilGroundStateUnweightedSqMass weilGroundStateEscapingPacket
  have hexpSq : Real.exp (-((n : ℝ) / 4)) ^ 2 =
      Real.exp (-((n : ℝ) / 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have htrans :
      (∫ x : ℝ,
          ‖compactLaplaceModulatedBump
            weilGroundStateEscapingRate (x - n)‖ ^ 2) =
        ∫ x : ℝ,
          ‖compactLaplaceModulatedBump
            weilGroundStateEscapingRate x‖ ^ 2 := by
    rw [← integral_add_right_eq_self
      (fun x : ℝ ↦
        ‖compactLaplaceModulatedBump
          weilGroundStateEscapingRate (x - n)‖ ^ 2) n]
    apply integral_congr_ae
    filter_upwards with x
    norm_num
  calc
    (∫ x : ℝ,
        ‖(Real.exp (-((n : ℝ) / 4)) : ℂ) *
          compactLaplaceModulatedBump
            weilGroundStateEscapingRate (x - n)‖ ^ 2) =
      ∫ x : ℝ,
        Real.exp (-((n : ℝ) / 2)) *
          ‖compactLaplaceModulatedBump
            weilGroundStateEscapingRate (x - n)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        rw [norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), mul_pow, hexpSq]
    _ = Real.exp (-((n : ℝ) / 2)) *
        ∫ x : ℝ,
          ‖compactLaplaceModulatedBump
            weilGroundStateEscapingRate (x - n)‖ ^ 2 := by
      rw [integral_const_mul]
    _ = Real.exp (-((n : ℝ) / 2)) *
        ∫ x : ℝ,
          ‖compactLaplaceModulatedBump
            weilGroundStateEscapingRate x‖ ^ 2 := by rw [htrans]

theorem tendsto_weilGroundStateUnweightedSqMass_escapingPacket :
    Tendsto
      (fun n : ℕ ↦
        weilGroundStateUnweightedSqMass (weilGroundStateEscapingPacket n))
      atTop (nhds 0) := by
  have hn :
      Tendsto (fun n : ℕ ↦ (n : ℝ) / 2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num) tendsto_natCast_atTop_atTop
  have hexp :
      Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) / 2))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hn
  rw [show (fun n : ℕ ↦
      weilGroundStateUnweightedSqMass (weilGroundStateEscapingPacket n)) =
      fun n : ℕ ↦
        Real.exp (-((n : ℝ) / 2)) *
          weilGroundStateUnweightedSqMass
            (compactLaplaceModulatedBump weilGroundStateEscapingRate) by
    funext n
    exact weilGroundStateUnweightedSqMass_escapingPacket n]
  simpa using hexp.mul_const
    (weilGroundStateUnweightedSqMass
      (compactLaplaceModulatedBump weilGroundStateEscapingRate))

theorem not_weilGroundStateEscapingPacket_uniform_zero :
    ¬ WeilGroundStateUniformOnClosedStrip (1 / 4)
      (fun n ↦ weilGroundStateFourierTransform
        (weilGroundStateEscapingPacket n))
      (fun _ ↦ 0) := by
  intro huniform
  have hevent := huniform (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  have hz : |weilGroundStateEscapingPoint.im| ≤ 1 / 4 := by
    norm_num [weilGroundStateEscapingPoint]
  have hsmall := hN N le_rfl weilGroundStateEscapingPoint hz
  norm_num at hsmall

/-- The complete positive transfer and escaping-mass negative-control certificate. -/
structure WeilGroundStateFourierTopologyCertificate : Prop where
  stripKernel :
    ∀ {A : ℝ}, 0 ≤ A → ∀ {z : ℂ}, |z.im| ≤ A → ∀ x : ℝ,
      ‖Complex.exp (I * z * (x : ℂ))‖ ≤ Real.exp (A * |x|)
  stripTransfer :
    ∀ {A : ℝ}, 0 ≤ A → ∀ {f g : ℕ → ℝ → ℂ} {target : ℂ → ℂ},
      (∀ n, Continuous (f n)) →
      (∀ n, Continuous (g n)) →
      (∀ n, HasCompactSupport (f n)) →
      (∀ n, HasCompactSupport (g n)) →
      WeilGroundStateUniformOnClosedStrip A
        (fun n ↦ weilGroundStateFourierTransform (g n)) target →
      Tendsto (fun n ↦ weilGroundStateFourierStripError A (f n) (g n))
        atTop (nhds 0) →
      WeilGroundStateUniformOnClosedStrip A
        (fun n ↦ weilGroundStateFourierTransform (f n)) target
  sourceStripTransfer :
    ∀ {A : ℝ}, 0 ≤ A → ∀ {L : ℕ → ℝ}
      {f g : ℕ → ℝ → ℂ} {target : ℂ → ℂ},
      (∀ n, Continuous (fun x ↦ f n (x + L n / 2))) →
      (∀ n, Continuous (fun x ↦ g n (x + L n / 2))) →
      (∀ n, HasCompactSupport (fun x ↦ f n (x + L n / 2))) →
      (∀ n, HasCompactSupport (fun x ↦ g n (x + L n / 2))) →
      WeilGroundStateUniformOnClosedStrip A
        (fun n z ↦ weilGroundStateCenteredFourier (L n) (g n) z) target →
      Tendsto
        (fun n ↦ weilGroundStateFourierStripError A
          (fun x ↦ f n (x + L n / 2))
          (fun x ↦ g n (x + L n / 2)))
        atTop (nhds 0) →
      WeilGroundStateUniformOnClosedStrip A
        (fun n z ↦ weilGroundStateCenteredFourier (L n) (f n) z) target
  escapingSmooth :
    ∀ n, ContDiff ℝ ∞ (weilGroundStateEscapingPacket n)
  escapingCompact :
    ∀ n, HasCompactSupport (weilGroundStateEscapingPacket n)
  escapingInterior :
    |weilGroundStateEscapingPoint.im| < 1 / 2
  escapingValue :
    ∀ n,
      weilGroundStateFourierTransform
        (weilGroundStateEscapingPacket n) weilGroundStateEscapingPoint = 1
  escapingL1 :
    Tendsto
      (fun n : ℕ ↦
        weilGroundStateUnweightedMass (weilGroundStateEscapingPacket n))
      atTop (nhds 0)
  escapingL2Sq :
    Tendsto
      (fun n : ℕ ↦
        weilGroundStateUnweightedSqMass (weilGroundStateEscapingPacket n))
      atTop (nhds 0)
  escapingNotUniform :
    ¬ WeilGroundStateUniformOnClosedStrip (1 / 4)
      (fun n ↦ weilGroundStateFourierTransform
        (weilGroundStateEscapingPacket n))
      (fun _ ↦ 0)

theorem weilGroundStateFourierTopology_endpoint :
    WeilGroundStateFourierTopologyCertificate where
  stripKernel := fun {_A} hA {_z} hz x ↦
    norm_exp_I_mul_mul_real_le_stripWeight hA hz x
  stripTransfer := fun {_A} hA {_f _g} {_target}
      hf hg hfsupp hgsupp htarget herror ↦
    weilGroundStateFourier_uniform_transfer
      hA hf hg hfsupp hgsupp htarget herror
  sourceStripTransfer := fun {_A} hA {_L} {_f _g} {_target}
      hf hg hfsupp hgsupp htarget herror ↦
    weilGroundStateCenteredFourier_uniform_transfer
      hA hf hg hfsupp hgsupp htarget herror
  escapingSmooth := contDiff_weilGroundStateEscapingPacket
  escapingCompact := hasCompactSupport_weilGroundStateEscapingPacket
  escapingInterior := weilGroundStateEscapingPoint_mem_open_halfStrip
  escapingValue := weilGroundStateFourierTransform_escapingPacket
  escapingL1 := tendsto_weilGroundStateUnweightedMass_escapingPacket
  escapingL2Sq := tendsto_weilGroundStateUnweightedSqMass_escapingPacket
  escapingNotUniform := not_weilGroundStateEscapingPacket_uniform_zero

end LeanLab.Riemann
