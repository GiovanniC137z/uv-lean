import UV.AnalyticScalar
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Sharp uniform depth bounds, strict auxiliary-mass monotonicity and complex
depth holomorphy for the literal scalar comparison bubble.
Source: prop:OQED-bubble-depth-monotone. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV

theorem depthProfile_eq_div {M u : ℝ} (hM : 0 ≤ M) (hu : 0 < u) :
    depthProfile M u = u / (Real.sqrt (u + M ^ 2) + M) := by
  have hs := Real.sq_sqrt (show 0 ≤ u + M ^ 2 by positivity)
  have hd : 0 < Real.sqrt (u + M ^ 2) + M := by positivity
  unfold depthProfile
  apply (eq_div_iff hd.ne').mpr
  nlinarith

theorem depthProfile_strict_antitone_mass {M N u : ℝ}
    (hM : 0 ≤ M) (hMN : M < N) (hu : 0 < u) : depthProfile N u < depthProfile M u := by
  have hN := hM.trans hMN.le
  rw [depthProfile_eq_div hN hu, depthProfile_eq_div hM hu]
  apply div_lt_div_of_pos_left hu (by positivity)
  have hs := Real.sqrt_le_sqrt (show u + M ^ 2 ≤ u + N ^ 2 by nlinarith)
  linarith

theorem depthProfile_antitone_mass {M N u : ℝ}
    (hM : 0 ≤ M) (hMN : M ≤ N) (hu : 0 ≤ u) : depthProfile N u ≤ depthProfile M u := by
  rcases eq_or_lt_of_le hu with rfl | hu'
  · simp [depthProfile, Real.sqrt_sq hM, Real.sqrt_sq (hM.trans hMN)]
  rcases eq_or_lt_of_le hMN with rfl | hMN'
  · rfl
  exact (depthProfile_strict_antitone_mass hM hMN' hu').le

theorem kernel_monotone_mass {a M N u : ℝ} (ha : 0 ≤ a)
    (hM : 0 ≤ M) (hMN : M ≤ N) (hu : 0 ≤ u) : kernel a M u ≤ kernel a N u := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (depthProfile_antitone_mass hM hMN hu) (by linarith)

theorem kernel_strict_monotone_mass {a M N u : ℝ} (ha : 0 < a)
    (hM : 0 ≤ M) (hMN : M < N) (hu : 0 < u) : kernel a M u < kernel a N u := by
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_neg_left (depthProfile_strict_antitone_mass hM hMN hu) (by linarith)

theorem scalarBubble_monotone_mass {a M N m : ℝ} (ha : 0 < a)
    (hM : 0 ≤ M) (hMN : M ≤ N) (hm : 0 < m) (P : ScalarMomentum) :
    scalarBubble a M m P ≤ scalarBubble a N m P := by
  unfold scalarBubble
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (scalarBubbleIntegrand_integrable ha hM hm P)
    (scalarBubbleIntegrand_integrable ha (hM.trans hMN) hm P)
  intro q
  unfold scalarBubbleIntegrand scalarCovariance
  apply mul_le_mul
  · exact div_le_div_of_nonneg_right (kernel_monotone_mass ha.le hM hMN (sq_nonneg _)) (by positivity)
  · exact div_le_div_of_nonneg_right (kernel_monotone_mass ha.le hM hMN (sq_nonneg _)) (by positivity)
  · exact div_nonneg (kernel_pos _ _ _).le (by positivity)
  · exact div_nonneg (kernel_pos _ _ _).le (by positivity)

theorem scalarBubble_strict_monotone_mass {a M N m : ℝ} (ha : 0 < a)
    (hM : 0 ≤ M) (hMN : M < N) (hm : 0 < m) (P : ScalarMomentum) :
    scalarBubble a M m P < scalarBubble a N m P := by
  let f := scalarBubbleIntegrand a M m P
  let g := scalarBubbleIntegrand a N m P
  have hN := hM.trans hMN.le
  have hle : ∀ q, f q ≤ g q := by
    intro q
    unfold f g scalarBubbleIntegrand scalarCovariance
    apply mul_le_mul
    · exact div_le_div_of_nonneg_right (kernel_monotone_mass ha.le hM hMN.le (sq_nonneg _)) (by positivity)
    · exact div_le_div_of_nonneg_right (kernel_monotone_mass ha.le hM hMN.le (sq_nonneg _)) (by positivity)
    · exact div_nonneg (kernel_pos _ _ _).le (by positivity)
    · exact div_nonneg (kernel_pos _ _ _).le (by positivity)
  obtain ⟨q, hq⟩ := exists_ne (0 : ScalarMomentum)
  have hstrict : f q < g q := by
    have hk := kernel_strict_monotone_mass ha hM hMN (sq_pos_of_pos (norm_pos_iff.mpr hq))
    have hk' := kernel_monotone_mass ha.le hM hMN.le (sq_nonneg ‖q + P‖)
    unfold f g scalarBubbleIntegrand scalarCovariance
    apply mul_lt_mul
    · exact (div_lt_div_iff_of_pos_right (by positivity)).mpr hk
    · exact div_le_div_of_nonneg_right hk' (by positivity)
    · exact div_pos (kernel_pos _ _ _) (by positivity)
    · exact div_nonneg (kernel_pos _ _ _).le (by positivity)
  have hf := scalarBubbleIntegrand_integrable ha hM hm P
  have hg := scalarBubbleIntegrand_integrable ha hN hm P
  have hcont : Continuous (fun q => g q - f q) := by
    unfold f g scalarBubbleIntegrand
    exact ((scalarCovariance_continuous hm).mul
      ((scalarCovariance_continuous hm).comp (continuous_id.add continuous_const))).sub
      ((scalarCovariance_continuous hm).mul
        ((scalarCovariance_continuous hm).comp (continuous_id.add continuous_const)))
  have hi : 0 < ∫ q, g q - f q := integral_pos_of_integrable_nonneg_nonzero hcont
    (hg.sub hf) (fun q => sub_nonneg.mpr (hle q)) (sub_pos.mpr hstrict).ne'
  rw [integral_sub hg hf] at hi
  unfold scalarBubble
  exact mul_lt_mul_of_pos_left (sub_pos.mp hi) (by positivity)

def sharpDepthConstant (n : ℕ) (amin : ℝ) : ℝ :=
  if n = 0 then 1 else (2 * (n : ℝ) / (Real.exp 1 * amin)) ^ n

theorem sharpDepthConstant_nonneg {amin : ℝ} (hmin : 0 < amin) (n : ℕ) :
    0 ≤ sharpDepthConstant n amin := by
  unfold sharpDepthConstant
  split_ifs <;> positivity

theorem mul_exp_neg_le_exp_neg_one (x : ℝ) :
    x * Real.exp (-x) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (x - 1)
  have he : Real.exp (x - 1) * Real.exp (-x) = Real.exp (-1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (x - 1) * Real.exp (-x) := by gcongr; linarith
    _ = _ := he

theorem pow_mul_exp_neg_sharp {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.exp (-(c * x)) ≤
      if n = 0 then 1 else ((n : ℝ) / (Real.exp 1 * c)) ^ n := by
  by_cases hn : n = 0
  · subst n
    simp only [pow_zero, one_mul, ite_true]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hc.le hx))
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs := mul_exp_neg_le_exp_neg_one (c * x / (n : ℝ))
  have ht : x * Real.exp (-(c * x / (n : ℝ))) ≤ (n : ℝ) / c * Real.exp (-1) := by
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (n : ℝ) / c by positivity)
    convert hm using 1
    field_simp
  have hp := pow_le_pow_left₀ (mul_nonneg hx (Real.exp_pos _).le) ht n
  have he : (Real.exp (-(c * x / (n : ℝ)))) ^ n = Real.exp (-(c * x)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [mul_pow, he] at hp
  rw [if_neg hn]
  convert hp using 1
  congr 1
  rw [Real.exp_neg]
  field_simp

theorem pow_mul_exp_neg_sharp_depth {amin x : ℝ} (hmin : 0 < amin) (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.exp (-((amin / 2) * x)) ≤ sharpDepthConstant n amin := by
  have hs := pow_mul_exp_neg_sharp (c := amin / 2) (by linarith) hx n
  convert hs using 1
  unfold sharpDepthConstant
  split_ifs
  · rfl
  · congr 1
    field_simp

theorem scalarDepthWeighted_sharp_uniform_bound {a amin M : ℝ}
    (hmin : 0 < amin) (ha : amin ≤ a) (hM : 0 ≤ M)
    (n : ℕ) (m : ℝ) (P q : ScalarMomentum) :
    scalarDepthWeighted n a M m P q ≤
      sharpDepthConstant n amin * scalarBubbleIntegrand (amin / 2) M m P q := by
  rw [scalarDepthWeighted_split n a (amin / 2)]
  have hH := scalarDepthSum_nonneg hM P q
  have he : Real.exp (-((a - amin / 2) * scalarDepthSum M P q)) ≤
      Real.exp (-((amin / 2) * scalarDepthSum M P q)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (scalarCovariance_nonneg _) (scalarCovariance_nonneg _))
  calc
    _ ≤ scalarDepthSum M P q ^ n *
        Real.exp (-((amin / 2) * scalarDepthSum M P q)) := by gcongr
    _ ≤ _ := pow_mul_exp_neg_sharp_depth hmin hH n

theorem scalarBubbleMoment_sharp_uniform_bound {a amin M m : ℝ}
    (hmin : 0 < amin) (ha : amin ≤ a) (hM : 0 ≤ M) (hm : 0 < m)
    (n : ℕ) (P : ScalarMomentum) :
    scalarBubbleMoment n a M m P ≤
      sharpDepthConstant n amin * scalarBubble (amin / 2) M m P := by
  have hi : (∫ q, scalarDepthWeighted n a M m P q) ≤
      sharpDepthConstant n amin * ∫ q, scalarBubbleIntegrand (amin / 2) M m P q := by
    rw [← integral_const_mul]
    apply integral_mono (scalarDepthWeighted_integrable (hmin.trans_le ha) hM hm n P)
      ((scalarBubbleIntegrand_integrable (by linarith : 0 < amin / 2) hM hm P).const_mul _)
    intro q
    exact scalarDepthWeighted_sharp_uniform_bound hmin ha hM n m P q
  unfold scalarBubbleMoment scalarBubble
  calc
    _ ≤ (2 * Real.pi) ^ (-4 : ℤ) *
        (sharpDepthConstant n amin * ∫ q, scalarBubbleIntegrand (amin / 2) M m P q) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

/-- The sharp derivative bound is uniform in the full real momentum domain and
in every auxiliary mass interval `[0,Mmax]`, including order zero. -/
theorem scalarBubble_derivative_sharp_uniform_bound {a amin M Mmax m : ℝ}
    (hmin : 0 < amin) (ha : amin ≤ a) (hM : 0 ≤ M) (hMM : M ≤ Mmax) (hm : 0 < m)
    (n : ℕ) (P : ScalarMomentum) :
    |iteratedDeriv n (fun b => scalarBubble b M m P) a| ≤
      sharpDepthConstant n amin * scalarBubble (amin / 2) Mmax m 0 := by
  have ha0 : 0 < a := hmin.trans_le ha
  have hc := sharpDepthConstant_nonneg hmin n
  rw [scalarBubble_iteratedDeriv ha0 hM hm n P, abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul, abs_of_pos (scalarBubbleMoment_pos ha0 hM hm n P)]
  calc
    _ ≤ sharpDepthConstant n amin * scalarBubble (amin / 2) M m P :=
      scalarBubbleMoment_sharp_uniform_bound hmin ha hM hm n P
    _ ≤ sharpDepthConstant n amin * scalarBubble (amin / 2) M m 0 :=
      mul_le_mul_of_nonneg_left (scalarBubble_le_zero_transfer (by linarith) hM hm P) hc
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (scalarBubble_monotone_mass (by linarith) hM hMM hm 0) hc

def complexScalarBubbleIntegrand (z : ℂ) (M m : ℝ) (P q : ScalarMomentum) : ℂ :=
  Complex.exp (-(z * (scalarDepthSum M P q : ℂ))) /
    (((‖q‖ ^ 2 + m ^ 2) * (‖q + P‖ ^ 2 + m ^ 2) : ℝ) : ℂ)

def complexScalarBubble (z : ℂ) (M m : ℝ) (P : ScalarMomentum) : ℂ :=
  (((2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) * ∫ q, complexScalarBubbleIntegrand z M m P q

def complexScalarBubbleDerivativeIntegrand (z : ℂ) (M m : ℝ) (P q : ScalarMomentum) : ℂ :=
  -(scalarDepthSum M P q : ℂ) * complexScalarBubbleIntegrand z M m P q

theorem complexScalarBubbleIntegrand_continuous (z : ℂ) (M : ℝ) {m : ℝ}
    (hm : 0 < m) (P : ScalarMomentum) : Continuous (complexScalarBubbleIntegrand z M m P) := by
  unfold complexScalarBubbleIntegrand
  apply Continuous.div
  · unfold scalarDepthSum depthProfile
    fun_prop
  · fun_prop
  · intro q
    exact_mod_cast (show (‖q‖ ^ 2 + m ^ 2) * (‖q + P‖ ^ 2 + m ^ 2) ≠ 0 by positivity)

theorem complexScalarBubbleDerivativeIntegrand_continuous (z : ℂ) (M : ℝ) {m : ℝ}
    (hm : 0 < m) (P : ScalarMomentum) :
    Continuous (complexScalarBubbleDerivativeIntegrand z M m P) :=
  ((Complex.continuous_ofReal.comp (scalarDepthSum_continuous M P)).neg).mul
    (complexScalarBubbleIntegrand_continuous z M hm P)

theorem complexScalarBubbleIntegrand_norm (z : ℂ) (M : ℝ) {m : ℝ}
    (hm : 0 < m) (P q : ScalarMomentum) :
    ‖complexScalarBubbleIntegrand z M m P q‖ = scalarBubbleIntegrand z.re M m P q := by
  rw [scalarBubbleIntegrand_exponential]
  simp only [complexScalarBubbleIntegrand, norm_div, Complex.norm_exp, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (show 0 < (‖q‖ ^ 2 + m ^ 2) * (‖q + P‖ ^ 2 + m ^ 2) by positivity)]

theorem complexScalarBubbleDerivativeIntegrand_norm (z : ℂ) {M m : ℝ}
    (hM : 0 ≤ M) (hm : 0 < m) (P q : ScalarMomentum) :
    ‖complexScalarBubbleDerivativeIntegrand z M m P q‖ = scalarDepthWeighted 1 z.re M m P q := by
  unfold complexScalarBubbleDerivativeIntegrand scalarDepthWeighted
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (scalarDepthSum_nonneg hM P q),
    complexScalarBubbleIntegrand_norm z M hm P q]
  simp only [pow_one]

theorem complexScalarBubbleIntegrand_integrable {z : ℂ} {M m : ℝ}
    (hz : 0 < z.re) (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    Integrable (complexScalarBubbleIntegrand z M m P) := by
  apply (scalarBubbleIntegrand_integrable hz hM hm P).mono'
  · exact (complexScalarBubbleIntegrand_continuous z M hm P).aestronglyMeasurable
  · exact Eventually.of_forall (fun q => (complexScalarBubbleIntegrand_norm z M hm P q).le)

theorem complexScalarBubbleIntegrand_hasDerivAt (z : ℂ) (M m : ℝ) (P q : ScalarMomentum) :
    HasDerivAt (fun w => complexScalarBubbleIntegrand w M m P q)
      (complexScalarBubbleDerivativeIntegrand z M m P q) z := by
  convert ((((hasDerivAt_id z).mul_const (scalarDepthSum M P q : ℂ)).neg.cexp).div_const
    (((‖q‖ ^ 2 + m ^ 2) * (‖q + P‖ ^ 2 + m ^ 2) : ℝ) : ℂ)) using 1
  simp only [complexScalarBubbleDerivativeIntegrand, complexScalarBubbleIntegrand, id_eq, Pi.neg_apply]
  ring

theorem complexScalarBubble_hasDerivAt {z : ℂ} {M m : ℝ}
    (hz : 0 < z.re) (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    HasDerivAt (fun w => complexScalarBubble w M m P)
      ((((2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) *
        ∫ q, complexScalarBubbleDerivativeIntegrand z M m P q) z := by
  have hbound : Integrable (fun q =>
      (((1 : ℕ).factorial : ℝ) / ((z.re / 2) / 2) ^ 1) *
        scalarBubbleIntegrand ((z.re / 2) / 2) M m P q) :=
    (scalarBubbleIntegrand_integrable (by linarith : 0 < (z.re / 2) / 2) hM hm P).const_mul _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w q => complexScalarBubbleIntegrand w M m P q)
    (F' := fun w q => complexScalarBubbleDerivativeIntegrand w M m P q)
    (x₀ := z) (ε := z.re / 2) (μ := volume)
    (bound := fun q => (((1 : ℕ).factorial : ℝ) / ((z.re / 2) / 2) ^ 1) *
      scalarBubbleIntegrand ((z.re / 2) / 2) M m P q)
    (by linarith)
    (Eventually.of_forall (fun w =>
      (complexScalarBubbleIntegrand_continuous w M hm P).aestronglyMeasurable))
    (complexScalarBubbleIntegrand_integrable hz hM hm P)
    ((complexScalarBubbleDerivativeIntegrand_continuous z M hm P).aestronglyMeasurable)
    (Eventually.of_forall (fun q w hw => by
      rw [complexScalarBubbleDerivativeIntegrand_norm w hM hm P q]
      apply scalarDepthWeighted_uniform_bound (by linarith : 0 < z.re / 2) _ hM
      have hdist : ‖w - z‖ < z.re / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
      have hre : |w.re - z.re| ≤ ‖w - z‖ := by
        simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
      have hlow := (abs_le.mp (hre.trans hdist.le)).1
      linarith)) hbound
    (Eventually.of_forall (fun q w _ => complexScalarBubbleIntegrand_hasDerivAt w M m P q))
  exact hd.2.const_mul (((2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ)

/-- Holomorphy in complex depth on the open right half-plane, including M=0. -/
theorem complexScalarBubble_analyticOnNhd_rightHalfPlane {M m : ℝ}
    (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    AnalyticOnNhd ℂ (fun z => complexScalarBubble z M m P) {z : ℂ | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (complexScalarBubble_hasDerivAt hz hM hm P).differentiableAt.differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

theorem complexScalarBubble_ofReal (a M m : ℝ) (P : ScalarMomentum) :
    complexScalarBubble (a : ℂ) M m P = (scalarBubble a M m P : ℂ) := by
  have he : complexScalarBubbleIntegrand (a : ℂ) M m P =
      (fun q => (scalarBubbleIntegrand a M m P q : ℂ)) := by
    funext q
    rw [scalarBubbleIntegrand_exponential]
    simp only [complexScalarBubbleIntegrand, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
      ← Complex.ofReal_exp, ← Complex.ofReal_div]
  unfold complexScalarBubble scalarBubble
  rw [he, integral_complex_ofReal]
  norm_cast

@[simp] theorem sharpDepthConstant_zero (amin : ℝ) : sharpDepthConstant 0 amin = 1 := by
  simp [sharpDepthConstant]

theorem sharpDepthConstant_of_pos {n : ℕ} (hn : 0 < n) (amin : ℝ) :
    sharpDepthConstant n amin = (2 * (n : ℝ) / (Real.exp 1 * amin)) ^ n := by
  simp only [sharpDepthConstant, if_neg (Nat.ne_of_gt hn)]

theorem scalarBubble_signed_iteratedDeriv {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (n : ℕ) (P : ScalarMomentum) :
    (-1 : ℝ) ^ n * iteratedDeriv n (fun b => scalarBubble b M m P) a =
      scalarBubbleMoment n a M m P := by
  rw [scalarBubble_iteratedDeriv ha hM hm n P, ← mul_assoc, ← mul_pow]
  norm_num

theorem scalarBubble_strictMonoOn_mass {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (P : ScalarMomentum) :
    StrictMonoOn (fun M => scalarBubble a M m P) (Ici 0) := by
  intro M hM N _ hMN
  exact scalarBubble_strict_monotone_mass ha hM hMN hm P

/-- All assertions of `prop:OQED-bubble-depth-monotone` for the actual
four-dimensional Lebesgue integral: strict complete monotonicity, the sharp
uniform constant, a holomorphic depth extension agreeing on the real axis,
and strict auxiliary-mass monotonicity on the stated real domain. -/
theorem oqed_bubble_depth_monotone {M m : ℝ} (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    (∀ a, 0 < a → ∀ n : ℕ,
      (-1 : ℝ) ^ n * iteratedDeriv n (fun b => scalarBubble b M m P) a =
        scalarBubbleMoment n a M m P ∧ 0 < scalarBubbleMoment n a M m P) ∧
    (∀ amin, 0 < amin → ∀ Mmax, M ≤ Mmax → ∀ a, amin ≤ a → ∀ n : ℕ,
      |iteratedDeriv n (fun b => scalarBubble b M m P) a| ≤
        sharpDepthConstant n amin * scalarBubble (amin / 2) Mmax m 0) ∧
    AnalyticOnNhd ℂ (fun z => complexScalarBubble z M m P) {z : ℂ | 0 < z.re} ∧
    (∀ a : ℝ, complexScalarBubble (a : ℂ) M m P = (scalarBubble a M m P : ℂ)) ∧
    (∀ a, 0 < a → StrictMonoOn (fun N => scalarBubble a N m P) (Ici 0)) := by
  refine ⟨?_, ?_, complexScalarBubble_analyticOnNhd_rightHalfPlane hM hm P,
    (fun a => complexScalarBubble_ofReal a M m P), ?_⟩
  · intro a ha n
    exact ⟨scalarBubble_signed_iteratedDeriv ha hM hm n P, scalarBubbleMoment_pos ha hM hm n P⟩
  · intro amin hmin Mmax hMM a ha n
    exact scalarBubble_derivative_sharp_uniform_bound hmin ha hM hMM hm n P
  · intro a ha
    exact scalarBubble_strictMonoOn_mass ha hm P

end UV
