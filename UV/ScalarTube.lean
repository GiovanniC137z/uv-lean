import UV.DepthAsymptotics
import UV.Holomorphy
import UV.PrincipalSqrt
import UV.EvenDescent
import UV.ScalarRotation
import UV.RealBoxIdentity
import UV.ContourExchange
import Mathlib.Analysis.Complex.TaylorSeries

/-! The literal complex symmetric routing and its uniform scalar tube bounds.
Source: prop:OQED-bubble-tube. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace UV

abbrev TubeMomentum := Fin 4 → ℂ

def tubeReal (P : TubeMomentum) : ScalarMomentum := WithLp.toLp 2 (fun i => (P i).re)
def tubeImag (P : TubeMomentum) : ScalarMomentum := WithLp.toLp 2 (fun i => (P i).im)
def complexifyMomentum (q : ScalarMomentum) : TubeMomentum := fun i => (q i : ℂ)
def complexMomentumSquare (P : TubeMomentum) : ℂ := ∑ i, P i ^ 2
def tubeShift (k : ScalarMomentum) (P : TubeMomentum) : TubeMomentum :=
  fun i => (k i : ℂ) + ((1 / 2 : ℝ) : ℂ) * P i

theorem tubeReal_continuous : Continuous tubeReal := by unfold tubeReal; fun_prop
theorem tubeImag_continuous : Continuous tubeImag := by unfold tubeImag; fun_prop

theorem tubeReal_neg (P : TubeMomentum) : tubeReal (-P) = -tubeReal P := by
  ext i
  simp [tubeReal]

theorem tubeImag_neg (P : TubeMomentum) : tubeImag (-P) = -tubeImag P := by
  ext i
  simp [tubeImag]

theorem tubeReal_complexify (q : ScalarMomentum) : tubeReal (complexifyMomentum q) = q := by
  ext i
  simp [tubeReal, complexifyMomentum]

theorem tubeImag_complexify (q : ScalarMomentum) : tubeImag (complexifyMomentum q) = 0 := by
  ext i
  simp [tubeImag, complexifyMomentum]

theorem complexMomentumSquare_re (P : TubeMomentum) :
    (complexMomentumSquare P).re = ‖tubeReal P‖ ^ 2 - ‖tubeImag P‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [tubeReal, tubeImag, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  unfold complexMomentumSquare
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_two, Complex.mul_re]

theorem complexMomentumSquare_complexify (q : ScalarMomentum) :
    complexMomentumSquare (complexifyMomentum q) = (((‖q‖ ^ 2) : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [complexMomentumSquare, complexifyMomentum, Real.norm_eq_abs, sq_abs]

theorem tubeReal_shift (k : ScalarMomentum) (P : TubeMomentum) :
    tubeReal (tubeShift k P) = k + (1 / 2 : ℝ) • tubeReal P := by
  ext i
  simp [tubeReal, tubeShift, Complex.mul_re]

theorem tubeImag_shift (k : ScalarMomentum) (P : TubeMomentum) :
    tubeImag (tubeShift k P) = (1 / 2 : ℝ) • tubeImag P := by
  ext i
  simp [tubeImag, tubeShift, Complex.mul_im]

theorem complexMomentumSquare_shift_re (k : ScalarMomentum) (P : TubeMomentum) (Λ : ℝ) :
    (complexMomentumSquare (tubeShift k P) + (Λ ^ 2 : ℝ)).re =
      ‖k + (1 / 2 : ℝ) • tubeReal P‖ ^ 2 + Λ ^ 2 - ‖tubeImag P‖ ^ 2 / 4 := by
  simp only [Complex.add_re, Complex.ofReal_re]
  rw [complexMomentumSquare_re, tubeReal_shift, tubeImag_shift, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  ring

theorem complexMomentumSquare_shift_re_lower (k : ScalarMomentum) (P : TubeMomentum) (Λ : ℝ)
    {d : ℝ} (hd : 0 ≤ d) (hP : ‖tubeImag P‖ ≤ d) :
    ‖k + (1 / 2 : ℝ) • tubeReal P‖ ^ 2 + Λ ^ 2 - d ^ 2 / 4 ≤
      (complexMomentumSquare (tubeShift k P) + (Λ ^ 2 : ℝ)).re := by
  rw [complexMomentumSquare_shift_re]
  have hh := mul_nonneg (sub_nonneg.mpr hP) (add_nonneg hd (norm_nonneg (tubeImag P)))
  nlinarith

theorem tube_strip_mass_gap {m M d : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hd : 0 ≤ d) (hdlt : d < 2 * min m M) :
    0 < m ^ 2 - d ^ 2 / 4 ∧ 0 < M ^ 2 - d ^ 2 / 4 := by
  have hdm : d < 2 * m := lt_of_lt_of_le hdlt (by nlinarith [min_le_left m M])
  have hdM : d < 2 * M := lt_of_lt_of_le hdlt (by nlinarith [min_le_right m M])
  constructor <;> nlinarith

def scalarMomentumTube (m M : ℝ) : Set TubeMomentum :=
  {P | ‖tubeImag P‖ < 2 * min m M}

theorem scalarMomentumTube_isOpen (m M : ℝ) : IsOpen (scalarMomentumTube m M) :=
  isOpen_lt (continuous_norm.comp tubeImag_continuous) continuous_const

theorem tubeShift_square_differentiable (k : ScalarMomentum) :
    Differentiable ℂ (fun P : TubeMomentum => complexMomentumSquare (tubeShift k P)) := by
  unfold complexMomentumSquare tubeShift
  fun_prop

theorem tubeShift_square_continuous (P : TubeMomentum) :
    Continuous (fun k : ScalarMomentum => complexMomentumSquare (tubeShift k P)) := by
  unfold complexMomentumSquare tubeShift
  fun_prop

theorem symmetric_shift_norm_sum (k x : ScalarMomentum) :
    2 * ‖k‖ ≤ ‖k - (1 / 2 : ℝ) • x‖ + ‖k + (1 / 2 : ℝ) • x‖ := by
  have ht := norm_add_le (k - (1 / 2 : ℝ) • x) (k + (1 / 2 : ℝ) • x)
  have he : (k - (1 / 2 : ℝ) • x) + (k + (1 / 2 : ℝ) • x) = (2 : ℝ) • k := by module
  rw [he, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ht
  exact ht

def scalarTubeEnvelope (a M m d : ℝ) (k : ScalarMomentum) : ℝ :=
  Real.exp (2 * a * M) * Real.exp (-2 * a * ‖k‖) / (m ^ 2 - d ^ 2 / 4) ^ 2

theorem scalarTubeEnvelope_integrable {a : ℝ} (ha : 0 < a) (M m d : ℝ) :
    Integrable (scalarTubeEnvelope a M m d) := by
  have h := (integrable_norm_pow_exp (E := ScalarMomentum) (μ := volume) (by linarith : 0 < 2 * a) 0).const_mul
    (Real.exp (2 * a * M) / (m ^ 2 - d ^ 2 / 4) ^ 2)
  convert h using 1
  funext k
  simp only [scalarTubeEnvelope, pow_zero, one_mul]
  rw [show -2 * a * ‖k‖ = -(2 * a * ‖k‖) by ring]
  ring

def scalarTubeIntegrand (a M m : ℝ) (P : TubeMomentum) (k : ScalarMomentum) : ℂ :=
  principalScalarCovariance a M m (complexMomentumSquare (tubeShift k (-P))) *
    principalScalarCovariance a M m (complexMomentumSquare (tubeShift k P))

def scalarTubeBubble (a M m : ℝ) (P : TubeMomentum) : ℂ :=
  (((2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) * ∫ k, scalarTubeIntegrand a M m P k

theorem tubeShift_denominator_norm_lower {m d : ℝ} (hd : 0 ≤ d)
    {P : TubeMomentum} (hP : ‖tubeImag P‖ ≤ d) (k : ScalarMomentum) :
    m ^ 2 - d ^ 2 / 4 ≤ ‖complexMomentumSquare (tubeShift k P) + ((m ^ 2 : ℝ) : ℂ)‖ := by
  have hl := complexMomentumSquare_shift_re_lower k P m hd hP
  have hr := Complex.re_le_norm (complexMomentumSquare (tubeShift k P) + ((m ^ 2 : ℝ) : ℂ))
  nlinarith [sq_nonneg ‖k + (1 / 2 : ℝ) • tubeReal P‖]

theorem tubeShift_covariance_norm_bound {a M m d : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hM : 0 < M) (hd : 0 ≤ d) (hdlt : d < 2 * min m M)
    {P : TubeMomentum} (hP : ‖tubeImag P‖ ≤ d) (k : ScalarMomentum) :
    ‖principalScalarCovariance a M m (complexMomentumSquare (tubeShift k P))‖ ≤
      Real.exp (a * M) * Real.exp (-a * ‖k + (1 / 2 : ℝ) • tubeReal P‖) /
        (m ^ 2 - d ^ 2 / 4) := by
  have hgap := tube_strip_mass_gap hm hM hd hdlt
  have hl := complexMomentumSquare_shift_re_lower k P M hd hP
  have hs : ‖k + (1 / 2 : ℝ) • tubeReal P‖ ≤
      Real.sqrt (complexMomentumSquare (tubeShift k P) + ((M ^ 2 : ℝ) : ℂ)).re := by
    have hsq : ‖k + (1 / 2 : ℝ) • tubeReal P‖ ^ 2 ≤
        (complexMomentumSquare (tubeShift k P) + ((M ^ 2 : ℝ) : ℂ)).re := by linarith [hgap.2]
    simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt hsq
  calc
    _ ≤ Real.exp (a * M) *
        Real.exp (-a * Real.sqrt (complexMomentumSquare (tubeShift k P) + ((M ^ 2 : ℝ) : ℂ)).re) /
          (m ^ 2 - d ^ 2 / 4) := principalScalarCovariance_norm_bound ha hgap.1
            (tubeShift_denominator_norm_lower hd hP k)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hgap.1.le
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hs (neg_nonpos.mpr ha)

/-- The source majorant is uniform in every real part of external momentum. -/
theorem scalarTubeIntegrand_norm_bound {a M m d : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) (hd : 0 ≤ d) (hdlt : d < 2 * min m M)
    {P : TubeMomentum} (hP : ‖tubeImag P‖ ≤ d) (k : ScalarMomentum) :
    ‖scalarTubeIntegrand a M m P k‖ ≤ scalarTubeEnvelope a M m d k := by
  have hPn : ‖tubeImag (-P)‖ ≤ d := by simpa only [tubeImag_neg, norm_neg] using hP
  have hp := tubeShift_covariance_norm_bound ha.le hm hM hd hdlt hP k
  have hn := tubeShift_covariance_norm_bound ha.le hm hM hd hdlt hPn k
  rw [tubeReal_neg, smul_neg, ← sub_eq_add_neg] at hn
  let u := ‖k - (1 / 2 : ℝ) • tubeReal P‖
  let v := ‖k + (1 / 2 : ℝ) • tubeReal P‖
  let L := m ^ 2 - d ^ 2 / 4
  have hL : 0 < L := (tube_strip_mass_gap hm hM hd hdlt).1
  have he1 : Real.exp (a * M) * Real.exp (a * M) = Real.exp (2 * a * M) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (-a * u) * Real.exp (-a * v) = Real.exp (-a * (u + v)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have ht : 2 * ‖k‖ ≤ u + v := symmetric_shift_norm_sum k (tubeReal P)
  have he : Real.exp (-a * (u + v)) ≤ Real.exp (-2 * a * ‖k‖) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left ht ha.le
    nlinarith
  unfold scalarTubeIntegrand
  rw [norm_mul]
  calc
    _ ≤ (Real.exp (a * M) * Real.exp (-a * u) / L) *
        (Real.exp (a * M) * Real.exp (-a * v) / L) := mul_le_mul hn hp (norm_nonneg _) (by positivity)
    _ = (Real.exp (a * M) * Real.exp (a * M)) *
        (Real.exp (-a * u) * Real.exp (-a * v)) / L ^ 2 := by
      simp only [div_eq_mul_inv, ← inv_pow]
      ring
    _ = Real.exp (2 * a * M) * Real.exp (-a * (u + v)) / L ^ 2 := by rw [he1, he2]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le) (sq_nonneg L)

theorem scalarTubeIntegrand_measurable (a M m : ℝ) (P : TubeMomentum) :
    Measurable (scalarTubeIntegrand a M m P) :=
  ((principalScalarCovariance_measurable a M m).comp (tubeShift_square_continuous (-P)).measurable).mul
    ((principalScalarCovariance_measurable a M m).comp (tubeShift_square_continuous P).measurable)

theorem scalarTubeIntegrand_integrable {a M m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) {P : TubeMomentum} (hP : P ∈ scalarMomentumTube m M) :
    Integrable (scalarTubeIntegrand a M m P) := by
  apply (scalarTubeEnvelope_integrable ha M m ‖tubeImag P‖).mono'
  · exact (scalarTubeIntegrand_measurable a M m P).aestronglyMeasurable
  · exact Eventually.of_forall (scalarTubeIntegrand_norm_bound ha hm hM (norm_nonneg _) hP le_rfl)

theorem tubeShift_covariance_differentiableAt {a M m : ℝ}
    (hm : 0 < m) (hM : 0 < M) {P : TubeMomentum} (hP : P ∈ scalarMomentumTube m M) (k : ScalarMomentum) :
    DifferentiableAt ℂ (fun Q => principalScalarCovariance a M m (complexMomentumSquare (tubeShift k Q))) P := by
  have hgap := tube_strip_mass_gap hm hM (norm_nonneg (tubeImag P)) hP
  have hroot : 0 < (complexMomentumSquare (tubeShift k P) + ((M ^ 2 : ℝ) : ℂ)).re := by
    have hl := complexMomentumSquare_shift_re_lower k P M (norm_nonneg _) le_rfl
    nlinarith [sq_nonneg ‖k + (1 / 2 : ℝ) • tubeReal P‖, hgap.2]
  have hden : complexMomentumSquare (tubeShift k P) + ((m ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have hn := tubeShift_denominator_norm_lower (m := m) (norm_nonneg _) (P := P) le_rfl k
    intro he
    rw [he, norm_zero] at hn
    linarith [hgap.1]
  exact (principalScalarCovariance_differentiableAt a M m hroot hden).comp P
    (tubeShift_square_differentiable k P)

theorem scalarTubeIntegrand_differentiableOn {a M m : ℝ} (hm : 0 < m) (hM : 0 < M) (k : ScalarMomentum) :
    DifferentiableOn ℂ (fun P => scalarTubeIntegrand a M m P k) (scalarMomentumTube m M) := by
  intro P hP
  have hPn : -P ∈ scalarMomentumTube m M := by
    simpa only [scalarMomentumTube, mem_setOf_eq, tubeImag_neg, norm_neg] using hP
  exact (((tubeShift_covariance_differentiableAt hm hM hPn k).comp P differentiableAt_id.neg).mul
    (tubeShift_covariance_differentiableAt hm hM hP k)).differentiableWithinAt

/-- Joint complex Fréchet holomorphy of the literal symmetric four-momentum
integral, obtained from the explicit common L1 majorant. -/
theorem scalarTubeBubble_differentiableOn {a M m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) :
    DifferentiableOn ℂ (scalarTubeBubble a M m) (scalarMomentumTube m M) := by
  have hi : DifferentiableOn ℂ (fun P => ∫ k, scalarTubeIntegrand a M m P k) (scalarMomentumTube m M) := by
    apply holomorphy_from_local_graph_majorants (scalarMomentumTube_isOpen m M)
      (fun P _ => (scalarTubeIntegrand_measurable a M m P).aestronglyMeasurable)
      (Eventually.of_forall (scalarTubeIntegrand_differentiableOn hm hM))
    intro c hc
    let d := (‖tubeImag c‖ + 2 * min m M) / 2
    have hcd : ‖tubeImag c‖ < d := by
      dsimp [d]
      linarith [show ‖tubeImag c‖ < 2 * min m M from hc]
    have hdlt : d < 2 * min m M := by dsimp [d]; linarith [show ‖tubeImag c‖ < 2 * min m M from hc]
    have hd : 0 ≤ d := (norm_nonneg _).trans hcd.le
    have hopen : IsOpen {P : TubeMomentum | ‖tubeImag P‖ < d} :=
      isOpen_lt (continuous_norm.comp tubeImag_continuous) continuous_const
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hopen c hcd
    refine ⟨R, hR, (fun P hP => (hball hP).trans hdlt), scalarTubeEnvelope a M m d,
      scalarTubeEnvelope_integrable ha M m d, ?_⟩
    exact Eventually.of_forall (fun k P hP => scalarTubeIntegrand_norm_bound ha hm hM hd hdlt (hball hP).le k)
  intro P hP
  exact (hi P hP).const_mul (((2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ)

theorem tubeShift_complexify (k x : ScalarMomentum) :
    tubeShift k (complexifyMomentum x) = complexifyMomentum (k + (1 / 2 : ℝ) • x) := by
  ext i
  simp [tubeShift, complexifyMomentum]

theorem complexifyMomentum_neg (x : ScalarMomentum) :
    complexifyMomentum (-x) = -complexifyMomentum x := by ext i; simp [complexifyMomentum]

theorem scalarTubeIntegrand_ofReal (a M m : ℝ) (x k : ScalarMomentum) :
    scalarTubeIntegrand a M m (complexifyMomentum x) k =
      ((scalarCovariance a M m (k - (1 / 2 : ℝ) • x) *
        scalarCovariance a M m (k + (1 / 2 : ℝ) • x) : ℝ) : ℂ) := by
  unfold scalarTubeIntegrand
  rw [← complexifyMomentum_neg, tubeShift_complexify, tubeShift_complexify,
    complexMomentumSquare_complexify, complexMomentumSquare_complexify]
  rw [principalScalarCovariance_ofReal a M m (sq_nonneg _),
    principalScalarCovariance_ofReal a M m (sq_nonneg _)]
  simp only [scalarCovariance, smul_neg, ← sub_eq_add_neg, Complex.ofReal_mul]

/-- The holomorphic symmetric integral agrees with the original real bubble
by an actual real translation of the integration variable. -/
theorem scalarTubeBubble_ofReal (a M m : ℝ) (x : ScalarMomentum) :
    scalarTubeBubble a M m (complexifyMomentum x) = (scalarBubble a M m x : ℂ) := by
  have he : (∫ k, scalarCovariance a M m (k - (1 / 2 : ℝ) • x) *
      scalarCovariance a M m (k + (1 / 2 : ℝ) • x)) =
        ∫ q, scalarBubbleIntegrand a M m x q := by
    calc
      _ = ∫ k, scalarBubbleIntegrand a M m x (k + (-(1 / 2 : ℝ)) • x) := by
        apply integral_congr_ae
        filter_upwards with k
        unfold scalarBubbleIntegrand
        congr 2 <;> module
      _ = _ := integral_add_right_eq_self _ _
  unfold scalarTubeBubble scalarBubble
  simp_rw [scalarTubeIntegrand_ofReal]
  rw [integral_complex_ofReal, he]
  push_cast
  rfl

theorem fourier_exp_norm_integral {a : ℝ} (ha : 0 < a) :
    (2 * Real.pi) ^ (-4 : ℤ) * (∫ k : ScalarMomentum, Real.exp (-2 * a * ‖k‖)) =
      3 / (64 * Real.pi ^ 2 * a ^ 4) := by
  rw [fourier_radial_integral (fun r => Real.exp (-2 * a * r))]
  have hr := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 3) (b := 2 * a)
    (by norm_num) (by norm_num) (by positivity)
  norm_num only [Real.rpow_one, Real.rpow_ofNat, div_one, one_div_one,
    Real.Gamma_nat_eq_factorial, Nat.factorial, Nat.cast_ofNat, mul_one] at hr
  rw [Real.rpow_neg (by positivity), Real.rpow_ofNat] at hr
  norm_num [Real.Gamma_nat_eq_factorial] at hr
  simp only [← neg_mul] at hr
  rw [hr]
  field_simp
  ring

theorem scalarTubeEnvelope_fourier_integral {a : ℝ} (ha : 0 < a) (M m d : ℝ) :
    (2 * Real.pi) ^ (-4 : ℤ) * (∫ k, scalarTubeEnvelope a M m d k) =
      3 * Real.exp (2 * a * M) / (64 * Real.pi ^ 2 * a ^ 4 * (m ^ 2 - d ^ 2 / 4) ^ 2) := by
  have he : scalarTubeEnvelope a M m d =
      (fun k => (Real.exp (2 * a * M) / (m ^ 2 - d ^ 2 / 4) ^ 2) * Real.exp (-2 * a * ‖k‖)) := by
    funext k
    unfold scalarTubeEnvelope
    ring
  rw [he, integral_const_mul]
  calc
    _ = (Real.exp (2 * a * M) / (m ^ 2 - d ^ 2 / 4) ^ 2) *
        ((2 * Real.pi) ^ (-4 : ℤ) * ∫ k : ScalarMomentum, Real.exp (-2 * a * ‖k‖)) := by ring
    _ = _ := by
      rw [fourier_exp_norm_integral ha]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem scalarTubeBubble_norm_bound {a M m d : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) (hd : 0 ≤ d) (hdlt : d < 2 * min m M)
    {P : TubeMomentum} (hP : ‖tubeImag P‖ ≤ d) :
    ‖scalarTubeBubble a M m P‖ ≤
      3 * Real.exp (2 * a * M) / (64 * Real.pi ^ 2 * a ^ 4 * (m ^ 2 - d ^ 2 / 4) ^ 2) := by
  have hi := scalarTubeIntegrand_integrable ha hm hM (lt_of_le_of_lt hP hdlt)
  unfold scalarTubeBubble
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-4 : ℤ))]
  calc
    _ ≤ (2 * Real.pi) ^ (-4 : ℤ) * ∫ k, ‖scalarTubeIntegrand a M m P k‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ (2 * Real.pi) ^ (-4 : ℤ) * ∫ k, scalarTubeEnvelope a M m d k :=
      mul_le_mul_of_nonneg_left (integral_mono hi.norm (scalarTubeEnvelope_integrable ha M m d)
        (scalarTubeIntegrand_norm_bound ha hm hM hd hdlt hP)) (by positivity)
    _ = _ := scalarTubeEnvelope_fourier_integral ha M m d

def tubeAxis (t : ℂ) : TubeMomentum := Pi.single 0 t

theorem tubeImag_axis_norm (t : ℂ) : ‖tubeImag (tubeAxis t)‖ = |t.im| := by
  rw [EuclideanSpace.norm_eq]
  simp [tubeImag, tubeAxis, Fin.sum_univ_succ, Real.sqrt_sq_eq_abs]

theorem tubeAxis_differentiable : Differentiable ℂ tubeAxis := by
  unfold tubeAxis
  apply differentiable_pi.mpr
  intro i
  by_cases hi : i = 0
  · subst i
    simpa only [Pi.single_eq_same] using (differentiable_id : Differentiable ℂ (fun t : ℂ => t))
  · simpa only [Pi.single_eq_of_ne hi] using (differentiable_const (c := (0 : ℂ)))

theorem tubeAxis_neg (t : ℂ) : tubeAxis (-t) = -tubeAxis t := by
  ext i
  by_cases hi : i = 0
  · subst i; simp [tubeAxis]
  · simp [tubeAxis, hi]

theorem tubeAxis_complexify (r : ℝ) : complexifyMomentum (scalarAxis r) = tubeAxis (r : ℂ) := by
  ext i
  by_cases hi : i = 0
  · subst i; simp [scalarAxis, tubeAxis, complexifyMomentum]
  · simp [scalarAxis, tubeAxis, complexifyMomentum, hi]

theorem scalarTubeBubble_even (a M m : ℝ) (P : TubeMomentum) :
    scalarTubeBubble a M m (-P) = scalarTubeBubble a M m P := by
  unfold scalarTubeBubble
  congr 1
  apply integral_congr_ae
  filter_upwards with k
  simp only [scalarTubeIntegrand, neg_neg]
  ring

def scalarTubeAxisFunction (a M m : ℝ) (t : ℂ) : ℂ := scalarTubeBubble a M m (tubeAxis t)

theorem scalarTubeAxisFunction_even (a M m : ℝ) (t : ℂ) :
    scalarTubeAxisFunction a M m (-t) = scalarTubeAxisFunction a M m t := by
  rw [scalarTubeAxisFunction, tubeAxis_neg, scalarTubeBubble_even]
  rfl

theorem scalarTubeAxisFunction_analyticOnNhd {a M m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) :
    AnalyticOnNhd ℂ (scalarTubeAxisFunction a M m) (Metric.ball 0 (2 * min m M)) := by
  apply DifferentiableOn.analyticOnNhd
  · intro t ht
    have hnorm : ‖t‖ < 2 * min m M := by simpa only [Metric.mem_ball, dist_zero_right] using ht
    have hdom : tubeAxis t ∈ scalarMomentumTube m M := by
      change ‖tubeImag (tubeAxis t)‖ < 2 * min m M
      rw [tubeImag_axis_norm]
      exact (Complex.abs_im_le_norm t).trans_lt hnorm
    exact (((scalarTubeBubble_differentiableOn ha hm hM).differentiableAt
      ((scalarMomentumTube_isOpen m M).mem_nhds hdom)).comp t (tubeAxis_differentiable t)).differentiableWithinAt
  · exact Metric.isOpen_ball

def scalarInvariantBubble (a M m : ℝ) : ℂ → ℂ := evenSquareDescent (scalarTubeAxisFunction a M m)

theorem scalarInvariantBubble_analyticOnNhd {a M m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) :
    AnalyticOnNhd ℂ (scalarInvariantBubble a M m) (Metric.ball 0 (4 * (min m M) ^ 2)) := by
  have hrad : 0 < 2 * min m M := by positivity
  have he : (2 * min m M) ^ 2 = 4 * (min m M) ^ 2 := by ring
  simpa only [scalarInvariantBubble, he] using evenSquareDescent_analyticOnNhd hrad
    (scalarTubeAxisFunction_analyticOnNhd ha hm hM) (scalarTubeAxisFunction_even a M m)

theorem scalarInvariantBubble_square (a M m : ℝ) (t : ℂ) :
    scalarInvariantBubble a M m (t ^ 2) = scalarTubeAxisFunction a M m t :=
  evenSquareDescent_sq (scalarTubeAxisFunction_even a M m) t

theorem scalarInvariantBubble_ofReal_momentum (a M m : ℝ) (P : ScalarMomentum) :
    scalarInvariantBubble a M m (((‖P‖ ^ 2) : ℝ) : ℂ) = (scalarBubble a M m P : ℂ) := by
  rw [Complex.ofReal_pow, scalarInvariantBubble_square, scalarTubeAxisFunction,
    ← tubeAxis_complexify, scalarTubeBubble_ofReal, ← scalarBubble_axis_reduction a M m P]

def scalarTubeTaylorBudget (a M m R : ℝ) : ℝ :=
  3 * Real.exp (2 * a * M) / (64 * Real.pi ^ 2 * a ^ 4 * (m ^ 2 - R / 4) ^ 2)

theorem scalarInvariantBubble_norm_bound {a M m R : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) (hR : 0 ≤ R) (hRlt : R < 4 * (min m M) ^ 2)
    {w : ℂ} (hw : ‖w‖ ≤ R) : ‖scalarInvariantBubble a M m w‖ ≤ scalarTubeTaylorBudget a M m R := by
  have hd : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  have hdlt : Real.sqrt R < 2 * min m M := by
    apply (Real.sqrt_lt hR (by positivity)).mpr
    nlinarith
  have hnorm : ‖principalSqrt w‖ ≤ Real.sqrt R := by
    rw [principalSqrt_norm]
    exact Real.sqrt_le_sqrt hw
  have hdom : ‖tubeImag (tubeAxis (principalSqrt w))‖ ≤ Real.sqrt R := by
    rw [tubeImag_axis_norm]
    exact (Complex.abs_im_le_norm _).trans hnorm
  have hb := scalarTubeBubble_norm_bound ha hm hM hd hdlt hdom
  simpa only [scalarInvariantBubble, evenSquareDescent, scalarTubeAxisFunction,
    scalarTubeTaylorBudget, Real.sq_sqrt hR] using hb

theorem complexMomentumSquare_differentiable : Differentiable ℂ complexMomentumSquare := by
  unfold complexMomentumSquare
  fun_prop

theorem complexMomentumSquare_norm_bound (P : TubeMomentum) :
    ‖complexMomentumSquare P‖ ≤ 4 * ‖P‖ ^ 2 := by
  calc
    _ ≤ ∑ i : Fin 4, ‖P i ^ 2‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖P‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm P i) 2
    _ = _ := by simp

theorem tubeImag_norm_bound (P : TubeMomentum) : ‖tubeImag P‖ ≤ 2 * ‖P‖ := by
  have hs : ‖tubeImag P‖ ^ 2 ≤ 4 * ‖P‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 4, ‖P‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simp only [tubeImag, PiLp.toLp_apply, Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) ((Complex.abs_im_le_norm _).trans (norm_le_pi_norm P i)) 2
      _ = _ := by simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * ‖P‖)).mp
  nlinarith

/-- Rotational equality on real momenta extends to a genuine complex
neighborhood, by the identity theorem in each complex coordinate. -/
theorem scalarTubeBubble_invariant {a M m : ℝ} (ha : 0 < a) (hm : 0 < m) (hM : 0 < M)
    {P : TubeMomentum} (hP : ‖P‖ < min m M / 2) :
    scalarTubeBubble a M m P = scalarInvariantBubble a M m (complexMomentumSquare P) := by
  let r := min m M / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hsmall : ∀ Q ∈ Metric.ball (0 : TubeMomentum) r, Q ∈ scalarMomentumTube m M ∧
      complexMomentumSquare Q ∈ Metric.ball 0 (4 * (min m M) ^ 2) := by
    intro Q hQ
    have hn : ‖Q‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hQ
    have hs : ‖Q‖ ^ 2 < r ^ 2 := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hn
    have hmin : 0 < min m M := lt_min hm hM
    constructor
    · change ‖tubeImag Q‖ < 2 * min m M
      have hb := tubeImag_norm_bound Q
      dsimp [r] at *
      nlinarith
    · simp only [Metric.mem_ball, dist_zero_right]
      have hb := complexMomentumSquare_norm_bound Q
      dsimp [r] at *
      nlinarith
  have hF : DifferentiableOn ℂ (scalarTubeBubble a M m) (Metric.ball 0 r) :=
    (scalarTubeBubble_differentiableOn ha hm hM).mono (fun Q hQ => (hsmall Q hQ).1)
  have hG : DifferentiableOn ℂ (fun Q => scalarInvariantBubble a M m (complexMomentumSquare Q))
      (Metric.ball (0 : TubeMomentum) r) := by
    intro Q hQ
    exact (((scalarInvariantBubble_analyticOnNhd ha hm hM) _ (hsmall Q hQ).2).differentiableAt.comp Q
      (complexMomentumSquare_differentiable Q)).differentiableWithinAt
  have hreal : ∀ x : Fin 4 → ℝ, ‖x‖ < r →
      scalarTubeBubble a M m (complexifyRealBox x) =
        scalarInvariantBubble a M m (complexMomentumSquare (complexifyRealBox x)) := by
    intro x _
    change scalarTubeBubble a M m (complexifyMomentum (WithLp.toLp 2 x)) =
      scalarInvariantBubble a M m (complexMomentumSquare (complexifyMomentum (WithLp.toLp 2 x)))
    rw [complexMomentumSquare_complexify, scalarTubeBubble_ofReal]
    exact (scalarInvariantBubble_ofReal_momentum a M m (WithLp.toLp 2 x)).symm
  have he := eqOn_complex_ball_of_real_ball hr hF hG hreal
  apply he
  simpa only [Metric.mem_ball, dist_zero_right, r] using hP

def scalarInvariantCoefficient (a M m : ℝ) (n : ℕ) : ℂ :=
  poleTaylorCoeff (scalarInvariantBubble a M m) n

theorem scalarInvariantCoefficient_norm_bound {a M m R : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hRlt : R < 4 * (min m M) ^ 2) (n : ℕ) :
    ‖scalarInvariantCoefficient a M m n‖ ≤ scalarTubeTaylorBudget a M m R * R⁻¹ ^ n := by
  apply pole_cauchy_coefficient_bound hR
    ((scalarInvariantBubble_analyticOnNhd ha hm hM).differentiableOn.mono (Metric.closedBall_subset_ball hRlt))
  intro w hw
  exact scalarInvariantBubble_norm_bound ha hm hM hR.le hRlt
    (by simpa only [Metric.mem_sphere, dist_zero_right] using (le_of_eq hw))

theorem scalarInvariantBubble_taylor_remainder {a M m r R : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) (hr : 0 < r) (hrR : r < R)
    (hRlt : R < 4 * (min m M) ^ 2) (N : ℕ) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖scalarInvariantBubble a M m w -
      ∑ n ∈ Finset.range (N + 1), scalarInvariantCoefficient a M m n * w ^ n‖ ≤
        scalarTubeTaylorBudget a M m R * (r / R) ^ (N + 1) / (1 - r / R) := by
  have hR : 0 < R := hr.trans hrR
  have hq : r / R < 1 := (div_lt_one hR).mpr hrR
  have hC : 0 ≤ scalarTubeTaylorBudget a M m R := by unfold scalarTubeTaylorBudget; positivity
  have hbound : ∀ n : ℕ, ‖scalarInvariantCoefficient a M m n * w ^ n‖ ≤
      scalarTubeTaylorBudget a M m R * (r / R) ^ n := by
    intro n
    rw [norm_mul, norm_pow]
    calc
      _ ≤ (scalarTubeTaylorBudget a M m R * R⁻¹ ^ n) * r ^ n :=
        mul_le_mul (scalarInvariantCoefficient_norm_bound ha hm hM hR hRlt n)
          (pow_le_pow_left₀ (norm_nonneg _) hw n) (pow_nonneg (norm_nonneg _) _) (by positivity)
      _ = _ := by rw [div_pow]; ring
  have hwball : w ∈ Metric.ball 0 (4 * (min m M) ^ 2) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hw.trans_lt (hrR.trans hRlt)
  have hs := Complex.hasSum_taylorSeries_on_ball
    (scalarInvariantBubble_analyticOnNhd ha hm hM).differentiableOn hwball
  have hs' : HasSum (fun n : ℕ => scalarInvariantCoefficient a M m n * w ^ n)
      (scalarInvariantBubble a M m w) := by
    convert hs using 1
    funext n
    simp only [scalarInvariantCoefficient, poleTaylorCoeff, sub_zero, smul_eq_mul]
    ring
  rw [norm_sub_rev]
  exact norm_sub_le_of_geometric_bound_of_hasSum hq hbound hs' (N + 1)

theorem scalarInvariantBubble_taylor_remainder_sup {a M m r R : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) (hr : 0 < r) (hrR : r < R)
    (hRlt : R < 4 * (min m M) ^ 2) (N : ℕ) :
    sSup ((fun w : ℂ => ‖scalarInvariantBubble a M m w -
      ∑ n ∈ Finset.range (N + 1), scalarInvariantCoefficient a M m n * w ^ n‖) '' Metric.closedBall 0 r) ≤
        scalarTubeTaylorBudget a M m R * (r / R) ^ (N + 1) / (1 - r / R) := by
  apply csSup_le
  · refine ⟨‖scalarInvariantBubble a M m 0 -
      ∑ n ∈ Finset.range (N + 1), scalarInvariantCoefficient a M m n * (0 : ℂ) ^ n‖, 0, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_self] using hr.le
  · rintro v ⟨w, hw, rfl⟩
    exact scalarInvariantBubble_taylor_remainder ha hm hM hr hrR hRlt N
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)

/-- All assertions of `prop:OQED-bubble-tube`, for the literal principal-branch
covariance and the actual symmetric four-dimensional integral. -/
theorem oqed_bubble_tube {a M m : ℝ} (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) :
    DifferentiableOn ℂ (scalarTubeBubble a M m) (scalarMomentumTube m M) ∧
    (∀ P ∈ scalarMomentumTube m M, Integrable (scalarTubeIntegrand a M m P)) ∧
    (∀ P : ScalarMomentum, scalarTubeBubble a M m (complexifyMomentum P) = (scalarBubble a M m P : ℂ)) ∧
    (∀ d, 0 ≤ d → d < 2 * min m M → Integrable (scalarTubeEnvelope a M m d) ∧
      ∀ P : TubeMomentum, ‖tubeImag P‖ ≤ d → ∀ k, ‖scalarTubeIntegrand a M m P k‖ ≤ scalarTubeEnvelope a M m d k) ∧
    AnalyticOnNhd ℂ (scalarInvariantBubble a M m) (Metric.ball 0 (4 * (min m M) ^ 2)) ∧
    (∀ P : TubeMomentum, ‖P‖ < min m M / 2 →
      scalarTubeBubble a M m P = scalarInvariantBubble a M m (complexMomentumSquare P)) ∧
    (∀ r R, 0 < r → r < R → R < 4 * (min m M) ^ 2 →
      (∀ n, ‖scalarInvariantCoefficient a M m n‖ ≤ scalarTubeTaylorBudget a M m R * R⁻¹ ^ n) ∧
      ∀ N, sSup ((fun w : ℂ => ‖scalarInvariantBubble a M m w -
        ∑ n ∈ Finset.range (N + 1), scalarInvariantCoefficient a M m n * w ^ n‖) '' Metric.closedBall 0 r) ≤
          scalarTubeTaylorBudget a M m R * (r / R) ^ (N + 1) / (1 - r / R)) := by
  refine ⟨scalarTubeBubble_differentiableOn ha hm hM, (fun _ hP => scalarTubeIntegrand_integrable ha hm hM hP),
    scalarTubeBubble_ofReal a M m, ?_, scalarInvariantBubble_analyticOnNhd ha hm hM,
    (fun _ hP => scalarTubeBubble_invariant ha hm hM hP), ?_⟩
  · intro d hd hdlt
    exact ⟨scalarTubeEnvelope_integrable ha M m d, fun _ hP k => scalarTubeIntegrand_norm_bound ha hm hM hd hdlt hP k⟩
  · intro r R hr hrR hRlt
    exact ⟨scalarInvariantCoefficient_norm_bound ha hm hM (hr.trans hrR) hRlt,
      scalarInvariantBubble_taylor_remainder_sup ha hm hM hr hrR hRlt⟩

end UV
