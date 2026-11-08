import UV.ReflectionPositivity
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! Smooth positive-time probes for the literal heat covariance. The product
approximate identity below has integral one and shrinking support; convergence
of the actual two-time reflection pairings follows from the convolution theorem. -/

noncomputable section
open MeasureTheory Filter Set Function Metric
open scoped Topology Convolution ContDiff Matrix

namespace UV

def timeProbeRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem timeProbeRadius_pos (n : ℕ) : 0 < timeProbeRadius n := by
  unfold timeProbeRadius
  positivity

theorem timeProbeRadius_tendsto : Tendsto timeProbeRadius atTop (𝓝 0) := by
  exact (tendsto_atTop_add_const_right atTop 1
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_div_atTop 1

def timeProbeBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := timeProbeRadius n / 2
  rOut := timeProbeRadius n
  rIn_pos := div_pos (timeProbeRadius_pos n) (by norm_num)
  rIn_lt_rOut := by have := timeProbeRadius_pos n; linarith

def timeProbeKernel (n : ℕ) : ℝ → ℝ := (timeProbeBump n).normed volume

def smoothTimeProbe (n : ℕ) (c : ℝ) (s : ℝ) : ℝ := timeProbeKernel n (c - s)

def productTimeProbeKernel (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  timeProbeKernel n z.1 * timeProbeKernel n z.2

theorem productTimeProbeKernel_nonneg (n : ℕ) (z : ℝ × ℝ) :
    0 ≤ productTimeProbeKernel n z := by
  exact mul_nonneg ((timeProbeBump n).nonneg_normed _)
    ((timeProbeBump n).nonneg_normed _)

theorem productTimeProbeKernel_integral (n : ℕ) :
    (∫ z : ℝ × ℝ, productTimeProbeKernel n z) = 1 := by
  change (∫ z : ℝ × ℝ, timeProbeKernel n z.1 * timeProbeKernel n z.2
    ∂volume.prod volume) = 1
  rw [integral_prod_mul]
  simp only [timeProbeKernel, ContDiffBump.integral_normed, mul_one]

theorem productTimeProbeKernel_support_small :
    Tendsto (fun n => support (productTimeProbeKernel n)) atTop
      (𝓝 (0 : ℝ × ℝ)).smallSets := by
  rw [nhds_basis_ball.smallSets.tendsto_right_iff]
  intro ε hε
  filter_upwards [timeProbeRadius_tendsto.eventually (gt_mem_nhds hε)] with n hn
  intro z hz
  have hh : timeProbeKernel n z.1 ≠ 0 ∧ timeProbeKernel n z.2 ≠ 0 :=
    mul_ne_zero_iff.mp hz
  have h₁ : ‖z.1‖ < timeProbeRadius n := by
    have hs : z.1 ∈ support ((timeProbeBump n).normed volume) := hh.1
    rw [(timeProbeBump n).support_normed_eq] at hs
    simpa only [mem_ball, dist_zero_right, timeProbeBump] using hs
  have h₂ : ‖z.2‖ < timeProbeRadius n := by
    have hs : z.2 ∈ support ((timeProbeBump n).normed volume) := hh.2
    rw [(timeProbeBump n).support_normed_eq] at hs
    simpa only [mem_ball, dist_zero_right, timeProbeBump] using hs
  simp only [mem_ball, dist_zero_right, Prod.norm_def]
  exact max_lt (h₁.trans hn) (h₂.trans hn)

/-- The genuine joint two-time reflection pairing of two smooth probes. -/
def reflectionPair (K f g : ℝ → ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, f z.1 * g z.2 * K (z.1 + z.2)

theorem reflectionPair_comm (K f g : ℝ → ℝ) :
    reflectionPair K f g = reflectionPair K g f := by
  unfold reflectionPair
  change (∫ z : ℝ × ℝ, f z.1 * g z.2 * K (z.1 + z.2) ∂volume.prod volume) = _
  rw [← integral_prod_swap]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [add_comm z.2 z.1, mul_comm (f z.2) (g z.1)]

theorem reflectionPairMatrix_isHermitian {ι : Type*} (K : ℝ → ℝ) (f : ι → ℝ → ℝ) :
    (Matrix.of fun i j => reflectionPair K (f i) (f j)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [Matrix.of_apply, star_trivial]
  exact reflectionPair_comm K (f j) (f i)

theorem smoothTimeProbe_contDiff (n : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (smoothTimeProbe n c) :=
  (timeProbeBump n).contDiff_normed.comp (contDiff_const.sub contDiff_id)

theorem smoothTimeProbe_support_subset (n : ℕ) (c : ℝ) :
    support (smoothTimeProbe n c) ⊆ closedBall c (timeProbeRadius n) := by
  intro s hs
  have hh : c - s ∈ support ((timeProbeBump n).normed volume) := hs
  rw [(timeProbeBump n).support_normed_eq] at hh
  have hn : ‖c - s‖ < timeProbeRadius n := by
    simpa only [mem_ball, dist_zero_right, timeProbeBump] using hh
  apply mem_closedBall.mpr
  rw [dist_eq_norm_sub, norm_sub_rev]
  exact hn.le

theorem smoothTimeProbe_hasCompactSupport (n : ℕ) (c : ℝ) :
    HasCompactSupport (smoothTimeProbe n c) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c _)
    (smoothTimeProbe_support_subset n c)

theorem smoothTimeProbe_positive_support (n : ℕ) {c : ℝ}
    (hc : timeProbeRadius n < c) : tsupport (smoothTimeProbe n c) ⊆ Ioi 0 := by
  have ht : tsupport (smoothTimeProbe n c) ⊆ closedBall c (timeProbeRadius n) :=
    closure_minimal (smoothTimeProbe_support_subset n c) isClosed_closedBall
  intro s hs
  have hd := mem_closedBall.mp (ht hs)
  rw [Real.dist_eq] at hd
  have hl := (abs_le.mp hd).1
  change 0 < s
  linarith

/-- The reflection integrals of compact smooth probes are genuine integrals;
    their values do not depend on the totalized integral's divergence convention. -/
theorem reflectionPair_integrable {K f g : ℝ → ℝ} (hK : Continuous K)
    (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (fun z : ℝ × ℝ => f z.1 * g z.2 * K (z.1 + z.2)) := by
  have hcont : Continuous (fun z : ℝ × ℝ => f z.1 * g z.2 * K (z.1 + z.2)) :=
    ((hf.comp continuous_fst).mul (hg.comp continuous_snd)).mul
      (hK.comp (continuous_fst.add continuous_snd))
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    ((show IsCompact (tsupport f) from hfc).prod (show IsCompact (tsupport g) from hgc))
  intro z hz
  have hh : f z.1 ≠ 0 ∧ g z.2 ≠ 0 := by
    have hm := (mul_ne_zero_iff.mp hz).1
    exact mul_ne_zero_iff.mp hm
  exact ⟨subset_closure hh.1, subset_closure hh.2⟩

theorem smoothTimeProbe_pair_tendsto {K : ℝ → ℝ} (hK : Continuous K) (c d : ℝ) :
    Tendsto (fun n => reflectionPair K (smoothTimeProbe n c) (smoothTimeProbe n d))
      atTop (𝓝 (K (c + d))) := by
  have hg : Continuous (fun z : ℝ × ℝ => K (z.1 + z.2)) :=
    hK.comp (continuous_fst.add continuous_snd)
  have h := convolution_tendsto_right
    (μ := (volume : Measure (ℝ × ℝ)))
    (φ := productTimeProbeKernel)
    (g := fun _ : ℕ => fun z : ℝ × ℝ => K (z.1 + z.2))
    (k := fun _ : ℕ => (c, d))
    (Eventually.of_forall productTimeProbeKernel_nonneg)
    (Eventually.of_forall productTimeProbeKernel_integral)
    productTimeProbeKernel_support_small
    (Eventually.of_forall (fun _ => hg.aestronglyMeasurable))
    ((hg.tendsto (c, d)).comp tendsto_snd) tendsto_const_nhds
  convert h using 1
  ext n
  unfold reflectionPair
  rw [← integral_sub_left_eq_self _ volume (c, d)]
  simp only [smoothTimeProbe, productTimeProbeKernel, convolution,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
    sub_sub_cancel]

def IsSmoothPositiveTimeProbe (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioi 0

def smoothReflectionMatrix (K : ℝ → ℝ) (n : ℕ) (c d : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => reflectionPair K (smoothTimeProbe n (![c, d] i))
    (smoothTimeProbe n (![c, d] j))

theorem smoothReflectionMatrix_det_tendsto {K : ℝ → ℝ} (hK : Continuous K) (c d : ℝ) :
    Tendsto (fun n => (smoothReflectionMatrix K n c d).det) atTop
      (𝓝 (K (c + c) * K (d + d) - K (c + d) * K (d + c))) := by
  convert ((smoothTimeProbe_pair_tendsto hK c c).mul
    (smoothTimeProbe_pair_tendsto hK d d)).sub
    ((smoothTimeProbe_pair_tendsto hK c d).mul
      (smoothTimeProbe_pair_tendsto hK d c)) using 1
  ext n
  simp only [smoothReflectionMatrix, Matrix.det_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- A negative point-probe determinant for a continuous kernel produces an
    actual counterexample consisting of compactly supported C-infinity probes
    whose entire closed supports lie at strictly positive times. -/
theorem smooth_counterexample_of_negative_point_determinant {K : ℝ → ℝ}
    (hK : Continuous K) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hdet : K (c + c) * K (d + d) - K (c + d) * K (d + c) < 0) :
    ∃ f : Fin 2 → ℝ → ℝ, (∀ i, IsSmoothPositiveTimeProbe (f i)) ∧
      (∀ i j, Integrable (fun z : ℝ × ℝ =>
        f i z.1 * f j z.2 * K (z.1 + z.2))) ∧
      (Matrix.of fun i j => reflectionPair K (f i) (f j)).det < 0 ∧
      ¬ (Matrix.of fun i j => reflectionPair K (f i) (f j)).PosSemidef := by
  have hm := (smoothReflectionMatrix_det_tendsto hK c d).eventually
    (eventually_lt_nhds hdet)
  have hr := timeProbeRadius_tendsto.eventually (gt_mem_nhds (lt_min hc hd))
  obtain ⟨n, hn, hneg⟩ := (hr.and hm).exists
  let f : Fin 2 → ℝ → ℝ := fun i => smoothTimeProbe n (![c, d] i)
  have hf : ∀ i, IsSmoothPositiveTimeProbe (f i) := by
    intro i
    refine ⟨smoothTimeProbe_contDiff n _, smoothTimeProbe_hasCompactSupport n _, ?_⟩
    apply smoothTimeProbe_positive_support n
    fin_cases i
    · exact hn.trans_le (min_le_left c d)
    · exact hn.trans_le (min_le_right c d)
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · intro i j
    exact reflectionPair_integrable hK (hf i).1.continuous (hf j).1.continuous
      (hf i).2.1 (hf j).2.1
  · exact hneg
  · intro hp
    have hnonneg := hp.det_nonneg
    change 0 ≤ (smoothReflectionMatrix K n c d).det at hnonneg
    exact (not_lt_of_ge hnonneg) hneg

/-- The heat covariance violates reflection positivity on actual smooth,
    compactly supported positive-time test probes. This closes the approximation
    step in prop:OS-counterexample. -/
theorem heatTimeCovariance_smooth_counterexample {t w : ℝ}
    (ht : 0 < t) (hw : 0 < w) :
    ∃ f : Fin 2 → ℝ → ℝ, (∀ i, IsSmoothPositiveTimeProbe (f i)) ∧
      (∀ i j, Integrable (fun z : ℝ × ℝ =>
        f i z.1 * f j z.2 * heatTimeCovariance t w (z.1 + z.2))) ∧
      (Matrix.of fun i j => reflectionPair (heatTimeCovariance t w) (f i) (f j)).det < 0 ∧
      ¬ (Matrix.of fun i j => reflectionPair (heatTimeCovariance t w) (f i) (f j)).PosSemidef := by
  obtain ⟨δ, hδ, hneg⟩ := heatTimeCovariance_negative_hankel ht hw
  let ε := δ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; linarith
  have hp := hneg ε hε hεδ
  apply smooth_counterexample_of_negative_point_determinant
    (continuous_iff_continuousAt.mpr (fun u => (heatTimeCovariance_hasDerivAt ht hw u).continuousAt))
    hε (show 0 < 2 * ε by positivity)
  simpa only [show ε + ε = 2 * ε by ring, show 2 * ε + 2 * ε = 4 * ε by ring,
    show ε + 2 * ε = 3 * ε by ring, show 2 * ε + ε = 3 * ε by ring, pow_two] using hp

def fourierReflectionPair (t w : ℝ) (f g : ℝ → ℝ) : ℂ :=
  ∫ z : ℝ × ℝ, (f z.1 : ℂ) * (g z.2 : ℂ) *
    heatTimeFourierCovariance t w (z.1 + z.2)

theorem fourierReflectionPair_eq_real {t w : ℝ} (ht : 0 < t) (hw : 0 < w)
    (f g : ℝ → ℝ) :
    fourierReflectionPair t w f g = (reflectionPair (heatTimeCovariance t w) f g : ℂ) := by
  unfold fourierReflectionPair reflectionPair
  simp_rw [heatTimeFourierCovariance_eq_real ht hw, ← Complex.ofReal_mul]
  exact integral_complex_ofReal

open scoped ComplexOrder in
/-- Fully smooth positive-time failure for the literal complex Fourier
    covariance in eq:heat-time-covariance. The probes and all pairing
    integrability claims are constructed, rather than assumed. -/
theorem heatTimeFourierCovariance_smooth_counterexample {t w : ℝ}
    (ht : 0 < t) (hw : 0 < w) :
    ∃ f : Fin 2 → ℝ → ℝ, (∀ i, IsSmoothPositiveTimeProbe (f i)) ∧
      (∀ i j, Integrable (fun z : ℝ × ℝ =>
        (f i z.1 : ℂ) * (f j z.2 : ℂ) * heatTimeFourierCovariance t w (z.1 + z.2))) ∧
      ¬ (Matrix.of fun i j => fourierReflectionPair t w (f i) (f j)).PosSemidef := by
  obtain ⟨f, hf, hint, hdet, _⟩ := heatTimeCovariance_smooth_counterexample ht hw
  refine ⟨f, hf, ?_, ?_⟩
  · intro i j
    simp_rw [heatTimeFourierCovariance_eq_real ht hw, ← Complex.ofReal_mul]
    exact (hint i j).ofReal
  · intro hp
    have hn := (Complex.nonneg_iff.mp hp.det_nonneg).1
    simp only [Matrix.det_fin_two, Matrix.of_apply, fourierReflectionPair_eq_real ht hw,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re] at hn
    simp only [Matrix.det_fin_two, Matrix.of_apply] at hdet
    exact (not_lt_of_ge hn) hdet

/-- A negative real quadratic form in two genuine smooth test probes. This
    expresses the failed OS inequality directly, beyond matrix terminology. -/
theorem heatTimeCovariance_smooth_negative_quadratic {t w : ℝ}
    (ht : 0 < t) (hw : 0 < w) :
    ∃ (f : Fin 2 → ℝ → ℝ) (c : Fin 2 → ℝ),
      (∀ i, IsSmoothPositiveTimeProbe (f i)) ∧
      (∀ i j, Integrable (fun z : ℝ × ℝ =>
        f i z.1 * f j z.2 * heatTimeCovariance t w (z.1 + z.2))) ∧
      (∑ i, ∑ j, c i * c j * reflectionPair (heatTimeCovariance t w) (f i) (f j)) < 0 := by
  classical
  obtain ⟨f, hf, hint, _, hnot⟩ := heatTimeCovariance_smooth_counterexample ht hw
  have hn : ¬ ∀ c : Fin 2 → ℝ, 0 ≤ star c ⬝ᵥ
      ((Matrix.of fun i j => reflectionPair (heatTimeCovariance t w) (f i) (f j)) *ᵥ c) := by
    intro h
    exact hnot ⟨reflectionPairMatrix_isHermitian _ f, h⟩
  obtain ⟨c, hc⟩ := not_forall.mp hn
  refine ⟨f, c, hf, hint, ?_⟩
  have hc' := lt_of_not_ge hc
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_add, add_mul,
    mul_assoc, mul_comm, mul_left_comm] using hc'

/-- Direct failure of the source's finite-family reflection-positivity
    inequality, using the literal Fourier covariance and real coefficients
    (which are in particular admissible complex coefficients). -/
theorem heatTimeFourierCovariance_smooth_OS_violation {t w : ℝ}
    (ht : 0 < t) (hw : 0 < w) :
    ∃ (f : Fin 2 → ℝ → ℝ) (c : Fin 2 → ℝ),
      (∀ i, IsSmoothPositiveTimeProbe (f i)) ∧
      (∀ i j, Integrable (fun z : ℝ × ℝ =>
        (f i z.1 : ℂ) * (f j z.2 : ℂ) * heatTimeFourierCovariance t w (z.1 + z.2))) ∧
      (∑ i, ∑ j, (c i : ℂ) * (c j : ℂ) * fourierReflectionPair t w (f i) (f j)).re < 0 := by
  obtain ⟨f, c, hf, hint, hneg⟩ := heatTimeCovariance_smooth_negative_quadratic ht hw
  refine ⟨f, c, hf, ?_, ?_⟩
  · intro i j
    simp_rw [heatTimeFourierCovariance_eq_real ht hw, ← Complex.ofReal_mul]
    exact (hint i j).ofReal
  · simpa only [fourierReflectionPair_eq_real ht hw, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum, Complex.ofReal_re] using hneg

end UV
