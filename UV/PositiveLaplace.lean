import UV.Convergence
import UV.AlternatingExp
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Actual Laplace transforms of a finite positive measure with positive
support and an open interval of exponential moments. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

namespace UV

def positiveComplexLaplace (ν : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ l, Complex.exp (-(l : ℂ) * z) ∂ν

def positiveRealLaplace (ν : Measure ℝ) (w : ℝ) : ℝ :=
  ∫ l, Real.exp (-l * w) ∂ν

def positiveComplexMoment (ν : Measure ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ l, (l : ℂ) ^ n * Complex.exp (-(l : ℂ) * z) ∂ν

def positiveRealMoment (ν : Measure ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  ∫ l, l ^ n * Real.exp (-l * w) ∂ν

def positiveLaplaceCoeff (ν : Measure ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * positiveRealMoment ν n 0 / (n.factorial : ℝ)

theorem positive_laplace_exponential_margin {R w : ℝ} (hR : 0 < R) (hw : -R < w) :
    ∃ s : ℝ, 0 < s ∧ s < R ∧ 0 < s + w := by
  refine ⟨(max 0 (-w) + R) / 2, ?_, ?_, ?_⟩
  · have hh := le_max_left (0 : ℝ) (-w)
    linarith
  · have hh : max 0 (-w) < R := max_lt hR (by linarith)
    linarith
  · have hh := le_max_right (0 : ℝ) (-w)
    have hh' : max 0 (-w) < R := max_lt hR (by linarith)
    linarith

theorem positive_laplace_weighted_bound {s w l : ℝ} (hgap : 0 < s + w)
    (hl : 0 ≤ l) (n : ℕ) :
    l ^ n * Real.exp (-l * w) ≤
      ((n.factorial : ℝ) / (s + w) ^ n) * Real.exp (s * l) := by
  have he : Real.exp (-l * w) = Real.exp (-((s + w) * l)) * Real.exp (s * l) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_mul_exp_neg_le hgap hl n) (Real.exp_nonneg _)

theorem positive_real_moment_integrable {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (n : ℕ) {w : ℝ} (hw : -R < w) :
    Integrable (fun (l : ℝ) => l ^ n * Real.exp (-l * w)) ν := by
  obtain ⟨s, hs, hsR, hgap⟩ := positive_laplace_exponential_margin hR hw
  apply ((hexp s hs hsR).const_mul ((n.factorial : ℝ) / (s + w) ^ n)).mono'
  · exact (by fun_prop : Continuous (fun l : ℝ => l ^ n * Real.exp (-l * w))).aestronglyMeasurable
  · filter_upwards [hp] with l hl
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hl.le _) (Real.exp_nonneg _))]
    exact positive_laplace_weighted_bound hgap hl.le n

theorem positive_complex_integrand_norm (n : ℕ) (z : ℂ) {l : ℝ} (hl : 0 ≤ l) :
    ‖(l : ℂ) ^ n * Complex.exp (-(l : ℂ) * z)‖ =
      l ^ n * Real.exp (-l * z.re) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hl, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]

theorem positive_complex_moment_integrable {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (n : ℕ) {z : ℂ} (hz : -R < z.re) :
    Integrable (fun (l : ℝ) => (l : ℂ) ^ n * Complex.exp (-(l : ℂ) * z)) ν := by
  apply (positive_real_moment_integrable hR hp hexp n hz).mono'
  · exact (by fun_prop : Continuous (fun l : ℝ =>
      (l : ℂ) ^ n * Complex.exp (-(l : ℂ) * z))).aestronglyMeasurable
  · filter_upwards [hp] with l hl
    exact (positive_complex_integrand_norm n z hl.le).le

theorem positive_complex_moment_hasDerivAt {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (n : ℕ) {z : ℂ} (hz : -R < z.re) :
    HasDerivAt (positiveComplexMoment ν n) (-positiveComplexMoment ν (n + 1) z) z := by
  obtain ⟨s, hs, hsR, hgap⟩ := positive_laplace_exponential_margin hR hz
  let ε := (s + z.re) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let C : ℝ := ((n + 1).factorial : ℝ) / ε ^ (n + 1)
  have hbound : Integrable (fun (l : ℝ) => C * Real.exp (s * l)) ν := (hexp s hs hsR).const_mul C
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u (l : ℝ) => (l : ℂ) ^ n * Complex.exp (-(l : ℂ) * u))
    (F' := fun u (l : ℝ) => -((l : ℂ) ^ (n + 1) * Complex.exp (-(l : ℂ) * u)))
    (x₀ := z) (ε := ε) (μ := ν) (bound := fun (l : ℝ) => C * Real.exp (s * l)) hε
    (Eventually.of_forall (fun u => (by fun_prop : Continuous (fun l : ℝ =>
      (l : ℂ) ^ n * Complex.exp (-(l : ℂ) * u))).aestronglyMeasurable))
    (positive_complex_moment_integrable hR hp hexp n hz)
    (by exact (by fun_prop : Continuous (fun l : ℝ =>
      -((l : ℂ) ^ (n + 1) * Complex.exp (-(l : ℂ) * z)))).aestronglyMeasurable)
    (by
      filter_upwards [hp] with l hl
      intro u hu
      rw [norm_neg, positive_complex_integrand_norm (n + 1) u hl.le]
      have hure : z.re - u.re < ε := by
        have hh := (Complex.abs_re_le_norm (u - z)).trans_lt (mem_ball_iff_norm.mp hu)
        rw [Complex.sub_re] at hh
        linarith [(abs_lt.mp hh).1]
      have he : Real.exp (-l * u.re) ≤ Real.exp (-l * (z.re - ε)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        _ ≤ l ^ (n + 1) * Real.exp (-l * (z.re - ε)) :=
          mul_le_mul_of_nonneg_left he (pow_nonneg hl.le _)
        _ ≤ _ := by
          have hg : 0 < s + (z.re - ε) := by dsimp [ε]; linarith
          have heq : s + (z.re - ε) = ε := by dsimp [ε]; ring
          simpa only [heq, C] using positive_laplace_weighted_bound hg hl.le (n + 1))
    hbound
    (Eventually.of_forall (fun l u _ => by
      have hh := (((hasDerivAt_id u).const_mul (-(l : ℂ))).cexp).const_mul ((l : ℂ) ^ n)
      convert hh using 1
      simp only [pow_succ, id_eq]
      ring))
  simpa only [positiveComplexMoment, integral_neg] using hd.2

theorem positive_complex_moment_ofReal (ν : Measure ℝ) (n : ℕ) (w : ℝ) :
    positiveComplexMoment ν n (w : ℂ) = (positiveRealMoment ν n w : ℂ) := by
  unfold positiveComplexMoment positiveRealMoment
  rw [← integral_complex_ofReal]
  congr 1
  funext l
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp, Complex.ofReal_neg]

theorem positive_complex_laplace_ofReal (ν : Measure ℝ) (w : ℝ) :
    positiveComplexLaplace ν (w : ℂ) = (positiveRealLaplace ν w : ℂ) := by
  simpa only [positiveComplexMoment, positiveRealMoment, pow_zero, one_mul,
    positiveComplexLaplace, positiveRealLaplace] using positive_complex_moment_ofReal ν 0 w

theorem positive_real_moment_hasDerivAt {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (n : ℕ) {w : ℝ} (hw : -R < w) :
    HasDerivAt (positiveRealMoment ν n) (-positiveRealMoment ν (n + 1) w) w := by
  have hd := (positive_complex_moment_hasDerivAt hR hp hexp n
    (z := (w : ℂ)) hw).real_of_complex
  simpa only [positive_complex_moment_ofReal, Complex.ofReal_re, Complex.neg_re] using hd

theorem positive_complex_laplace_differentiableOn {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν) :
    DifferentiableOn ℂ (positiveComplexLaplace ν) {z : ℂ | -R < z.re} := by
  intro z hz
  have heq : positiveComplexMoment ν 0 = positiveComplexLaplace ν := by
    funext u
    simp only [positiveComplexMoment, pow_zero, one_mul, positiveComplexLaplace]
  rw [← heq]
  exact (positive_complex_moment_hasDerivAt hR hp hexp 0 hz).differentiableAt.differentiableWithinAt

theorem positive_real_laplace_iteratedDeriv {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (n : ℕ) {w : ℝ} (hw : -R < w) :
    iteratedDeriv n (positiveRealLaplace ν) w = (-1 : ℝ) ^ n * positiveRealMoment ν n w := by
  induction n generalizing w with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul, positiveRealLaplace,
      positiveRealMoment]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (positiveRealLaplace ν) =ᶠ[𝓝 w]
        (fun u => (-1 : ℝ) ^ n * positiveRealMoment ν n u) := by
      filter_upwards [eventually_gt_nhds hw] with u hu
      exact ih hu
    rw [heq.deriv_eq, ((positive_real_moment_hasDerivAt hR hp hexp n hw).const_mul
      ((-1 : ℝ) ^ n)).deriv]
    ring

theorem positive_complex_laplace_iteratedDeriv {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (n : ℕ) {z : ℂ} (hz : -R < z.re) :
    iteratedDeriv n (positiveComplexLaplace ν) z = (-1 : ℂ) ^ n * positiveComplexMoment ν n z := by
  induction n generalizing z with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul, positiveComplexLaplace,
      positiveComplexMoment]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hopen : IsOpen {z : ℂ | -R < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have heq : iteratedDeriv n (positiveComplexLaplace ν) =ᶠ[𝓝 z]
        (fun u => (-1 : ℂ) ^ n * positiveComplexMoment ν n u) := by
      filter_upwards [hopen.mem_nhds hz] with u hu
      exact ih hu
    rw [heq.deriv_eq, ((positive_complex_moment_hasDerivAt hR hp hexp n hz).const_mul
      ((-1 : ℂ) ^ n)).deriv]
    ring

theorem positive_complex_laplace_coefficient {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (n : ℕ) :
    iteratedDeriv n (positiveComplexLaplace ν) 0 / (n.factorial : ℂ) =
      (positiveLaplaceCoeff ν n : ℂ) := by
  rw [positive_complex_laplace_iteratedDeriv hR hp hexp n (by simpa using neg_neg_of_pos hR)]
  have he := positive_complex_moment_ofReal ν n 0
  simp only [Complex.ofReal_zero] at he
  rw [he]
  simp only [positiveLaplaceCoeff, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_natCast]

theorem positive_real_moment_pos {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l) (hν : ν ≠ 0)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (n : ℕ) {w : ℝ} (hw : -R < w) : 0 < positiveRealMoment ν n w := by
  letI : NeZero ν := ⟨hν⟩
  have hi := positive_real_moment_integrable hR hp hexp n hw
  have hn : 0 ≤ᵐ[ν] (fun l => l ^ n * Real.exp (-l * w)) := by
    filter_upwards [hp] with l hl
    exact (mul_pos (pow_pos hl n) (Real.exp_pos _)).le
  by_contra! hbad
  have hz : (∫ l, l ^ n * Real.exp (-l * w) ∂ν) = 0 :=
    le_antisymm hbad (integral_nonneg_of_ae hn)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
  obtain ⟨l, hl, hlzero⟩ := (hp.and hzero).exists
  exact (mul_pos (pow_pos hl n) (Real.exp_pos _)).ne' hlzero

theorem positive_real_laplace_strictCM {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l) (hν : ν ≠ 0)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (n : ℕ) {w : ℝ} (hw : -R < w) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n (positiveRealLaplace ν) w := by
  rw [positive_real_laplace_iteratedDeriv hR hp hexp n hw, ← mul_assoc, ← mul_pow]
  norm_num only [neg_one_mul, neg_neg, one_pow, one_mul]
  exact positive_real_moment_pos hR hp hν hexp n hw

theorem positive_laplace_coefficient_alternates {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l) (hν : ν ≠ 0)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (n : ℕ) : 0 < (-1 : ℝ) ^ n * positiveLaplaceCoeff ν n := by
  have hm := positive_real_moment_pos hR hp hν hexp n (w := 0) (by linarith)
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  unfold positiveLaplaceCoeff
  rw [← mul_div_assoc, ← mul_assoc, hsign, one_mul]
  exact div_pos hm (by positivity)

theorem positive_laplace_coefficient_abs {ν : Measure ℝ} (hp : ∀ᵐ l ∂ν, 0 < l)
    (n : ℕ) : |positiveLaplaceCoeff ν n| = positiveRealMoment ν n 0 / (n.factorial : ℝ) := by
  have hn : 0 ≤ positiveRealMoment ν n 0 := by
    unfold positiveRealMoment
    apply integral_nonneg_of_ae
    filter_upwards [hp] with l hl
    exact mul_nonneg (pow_nonneg hl.le _) (Real.exp_nonneg _)
  simp only [positiveLaplaceCoeff, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_nonneg hn, abs_of_nonneg (show (0 : ℝ) ≤ n.factorial by positivity)]

theorem positive_laplace_finite_polynomial_integral {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (N : ℕ) (w : ℝ) :
    Integrable (fun l => ∑ n ∈ Finset.range (N + 1), (-l * w) ^ n / (n.factorial : ℝ)) ν ∧
      (∫ l, ∑ n ∈ Finset.range (N + 1), (-l * w) ^ n / (n.factorial : ℝ) ∂ν) =
        ∑ n ∈ Finset.range (N + 1), positiveLaplaceCoeff ν n * w ^ n := by
  have hi : ∀ n : ℕ, Integrable (fun l => (-l * w) ^ n / (n.factorial : ℝ)) ν := by
    intro n
    have hn := (positive_real_moment_integrable hR hp hexp n (w := 0) (by linarith)).mul_const
      ((-1 : ℝ) ^ n * w ^ n / (n.factorial : ℝ))
    convert hn using 1
    funext l
    simp only [mul_zero, Real.exp_zero, mul_one]
    rw [mul_pow, neg_pow]
    ring
  refine ⟨integrable_finset_sum _ (fun n _ => hi n), ?_⟩
  rw [integral_finset_sum _ (fun n _ => hi n)]
  apply Finset.sum_congr rfl
  intro n _
  have heq : (fun l : ℝ => (-l * w) ^ n / (n.factorial : ℝ)) =
      (fun l => (l ^ n * Real.exp (-l * 0)) *
        ((-1 : ℝ) ^ n * w ^ n / (n.factorial : ℝ))) := by
    funext l
    simp only [mul_zero, Real.exp_zero, mul_one]
    rw [mul_pow, neg_pow]
    ring
  rw [heq, integral_mul_const]
  unfold positiveLaplaceCoeff positiveRealMoment
  ring

theorem positive_laplace_signed_taylor {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (N : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ (-1 : ℝ) ^ (N + 1) * (positiveRealLaplace ν w -
      ∑ n ∈ Finset.range (N + 1), positiveLaplaceCoeff ν n * w ^ n) ∧
    (-1 : ℝ) ^ (N + 1) * (positiveRealLaplace ν w -
      ∑ n ∈ Finset.range (N + 1), positiveLaplaceCoeff ν n * w ^ n) ≤
        |positiveLaplaceCoeff ν (N + 1)| * w ^ (N + 1) := by
  let T : ℝ → ℝ := fun l => ∑ n ∈ Finset.range (N + 1), (-l * w) ^ n / (n.factorial : ℝ)
  let E : ℝ → ℝ := fun l => (-1 : ℝ) ^ (N + 1) * (Real.exp (-l * w) - T l)
  obtain ⟨hTi, hT⟩ := positive_laplace_finite_polynomial_integral hR hp hexp N w
  have hExp : Integrable (fun l => Real.exp (-l * w)) ν := by
    simpa only [pow_zero, one_mul] using
      positive_real_moment_integrable hR hp hexp 0 (w := w) (by linarith)
  have hEi : Integrable E ν := (hExp.sub hTi).const_mul _
  have hU : Integrable (fun l => (l * w) ^ (N + 1) / ((N + 1).factorial : ℝ)) ν := by
    have hi := (positive_real_moment_integrable hR hp hexp (N + 1) (w := 0)
      (by linarith)).mul_const (w ^ (N + 1) / ((N + 1).factorial : ℝ))
    convert hi using 1
    funext l
    simp only [mul_zero, Real.exp_zero, mul_one, mul_pow]
    ring
  have hpoint : ∀ᵐ l ∂ν, 0 ≤ E l ∧ E l ≤ (l * w) ^ (N + 1) / ((N + 1).factorial : ℝ) := by
    filter_upwards [hp] with l hl
    simpa only [E, T, neg_mul] using exp_neg_signed_taylor_remainder (mul_nonneg hl.le hw) N
  have hEeq : (∫ l, E l ∂ν) = (-1 : ℝ) ^ (N + 1) *
      (positiveRealLaplace ν w - ∑ n ∈ Finset.range (N + 1), positiveLaplaceCoeff ν n * w ^ n) := by
    rw [show E = (fun l => (-1 : ℝ) ^ (N + 1) * (Real.exp (-l * w) - T l)) from rfl,
      integral_const_mul, integral_sub]
    · rw [show (∫ l, T l ∂ν) = _ from hT]
      rfl
    · simpa only [pow_zero, one_mul] using
        positive_real_moment_integrable hR hp hexp 0 (w := w) (by linarith)
    · exact hTi
  have hUeq : (∫ l, (l * w) ^ (N + 1) / ((N + 1).factorial : ℝ) ∂ν) =
      |positiveLaplaceCoeff ν (N + 1)| * w ^ (N + 1) := by
    rw [positive_laplace_coefficient_abs hp]
    have heq : (fun l : ℝ => (l * w) ^ (N + 1) / ((N + 1).factorial : ℝ)) =
        (fun l => (l ^ (N + 1) * Real.exp (-l * 0)) *
          (w ^ (N + 1) / ((N + 1).factorial : ℝ))) := by
      funext l
      simp only [mul_zero, Real.exp_zero, mul_one, mul_pow]
      ring
    rw [heq, integral_mul_const]
    unfold positiveRealMoment
    ring
  exact ⟨hEeq ▸ integral_nonneg_of_ae (hpoint.mono (fun _ h => h.1)),
    hEeq ▸ hUeq ▸ integral_mono_ae hEi hU (hpoint.mono (fun _ h => h.2))⟩

theorem positive_real_laplace_coefficient {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    (n : ℕ) : iteratedDeriv n (positiveRealLaplace ν) 0 / (n.factorial : ℝ) =
      positiveLaplaceCoeff ν n := by
  rw [positive_real_laplace_iteratedDeriv hR hp hexp n (by linarith)]
  rfl

theorem positive_laplace_odd_truncation_lower {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    {N : ℕ} (hN : Odd N) {w : ℝ} (hw : 0 ≤ w) :
    (∑ n ∈ Finset.range (N + 1), positiveLaplaceCoeff ν n * w ^ n) ≤ positiveRealLaplace ν w := by
  have h := (positive_laplace_signed_taylor hR hp hexp N hw).1
  rw [pow_succ, hN.neg_one_pow] at h
  linarith

theorem positive_laplace_even_truncation_upper {ν : Measure ℝ} {R : ℝ}
    (hR : 0 < R) (hp : ∀ᵐ l ∂ν, 0 < l)
    (hexp : ∀ s : ℝ, 0 < s → s < R → Integrable (fun (l : ℝ) => Real.exp (s * l)) ν)
    {N : ℕ} (hN : Even N) {w : ℝ} (hw : 0 ≤ w) :
    positiveRealLaplace ν w ≤ ∑ n ∈ Finset.range (N + 1), positiveLaplaceCoeff ν n * w ^ n := by
  have h := (positive_laplace_signed_taylor hR hp hexp N hw).1
  rw [pow_succ, hN.neg_one_pow] at h
  linarith

end UV
