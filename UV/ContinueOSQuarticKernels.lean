import UV.ContinueOSJointWitness
import UV.RevisionOSInteraction
import UV.DepthAsymptotics

/-! Coincidence and spatial contraction estimates for the two fixed-depth
boundary quartic reflection tests. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

namespace UV

/-- Position-space coincidence of the transferred massive field. Each of the
two source insertions supplies one Poisson factor. -/
def osCoincidence (m r : ℝ) : ℝ := stableCoordinateCovariance (2 * r) m 0

theorem osGreenPoisson_pos {m a : ℝ} (hm : 0 < m) (ha : 0 < a) (x : OSFourSpace) :
    0 < stableCoordinateCovariance a m x := by
  letI := stableGreenMeasure_finite hm
  have hi := stableCoordinateConvolution_integrable ha (stableGreenMeasure m) x
  apply (integral_pos_iff_support_of_nonneg (fun y => (stablePoissonKernel_pos ha (x-y)).le) hi).mpr
  have hs : Function.support (fun y => stablePoissonKernel a (x-y)) = univ := by
    ext y
    exact iff_true_intro (stablePoissonKernel_pos ha _).ne'
  rw [hs]
  exact Measure.measure_univ_pos.mpr (stableGreenMeasure_ne_zero hm)

theorem osCoincidence_pos {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    0 < osCoincidence m r := osGreenPoisson_pos hm (by positivity) _

theorem osCoincidence_radial {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    osCoincidence m r = (8 * Real.pi ^ 2)⁻¹ * ∫ k in Ioi 0,
      k ^ 3 * (Real.exp (-(2*r) * k) / (k ^ 2 + m ^ 2)) := by
  have h := stableCoordinateCovariance_inverseFourier (by positivity : 0 < 2*r) hm 0
  simp only [stableFourierPhase, inner_zero_right, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, integral_complex_ofReal, ← Complex.ofReal_mul,
    Complex.ofReal_inj] at h
  unfold osCoincidence
  rw [← h]
  simp_rw [scalarCovariance_stable]
  exact fourier_radial_integral (fun k => Real.exp (-(2*r) * k) / (k ^ 2 + m ^ 2))

/-- Uniform bound with the manuscript's four-dimensional Fourier normalization. -/
theorem osCoincidence_bound {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    osCoincidence m r ≤ 1 / (32 * Real.pi ^ 2 * r ^ 2) := by
  rw [osCoincidence_radial hm hr]
  have hr2 : 0 < 2*r := by positivity
  have hi : IntegrableOn (fun k : ℝ => k * Real.exp (-(2*r) * k)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 2*r)
      (by norm_num) le_rfl hr2)
  have ht : (∫ k in Ioi 0, k * Real.exp (-(2*r) * k)) = (2*r)⁻¹ ^ 2 := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1) (b := 2*r)
      (by norm_num) (by norm_num) hr2
    norm_num [Real.Gamma_nat_eq_factorial, Real.rpow_neg hr2.le] at h
    simpa only [neg_mul, inv_pow] using h
  have hb (k : ℝ) (hk : 0 < k) : k ^ 3 * (Real.exp (-(2*r) * k) / (k ^ 2 + m ^ 2)) ≤
      k * Real.exp (-(2*r) * k) := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hk.le (Real.exp_pos (-(2*r)*k)).le) (sq_nonneg m)]
  have hlow : IntegrableOn (fun k : ℝ => k^3 * (Real.exp (-(2*r)*k) / (k^2+m^2))) (Ioi 0) := by
    apply hi.mono' (by fun_prop (disch := intro x; positivity))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with k hk
    change 0 < k at hk
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ k^3 * (Real.exp (-(2*r)*k) / (k^2+m^2)))]
    exact hb k hk
  have hcmp := integral_mono_ae hlow hi ((ae_restrict_mem measurableSet_Ioi).mono hb)
  rw [ht] at hcmp
  calc
    _ ≤ (8 * Real.pi ^ 2)⁻¹ * (2*r)⁻¹ ^ 2 := mul_le_mul_of_nonneg_left hcmp (by positivity)
    _ = _ := by field_simp; ring

/-- Smearing the position-space mixed massive covariance against an actual
probe. Its Fourier kernel is the one-depth massive propagator. -/
def osGreenPoissonTransfer (m r : ℝ) (g : OSFourSpace → ℝ) (x : OSFourSpace) : ℝ :=
  ∫ y, stableCoordinateCovariance r m (x-y) * g y

theorem osGreenPoissonTransfer_continuous {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    {g : OSFourSpace → ℝ} (hc : Continuous g) (hi : Integrable g) :
    Continuous (osGreenPoissonTransfer m r g) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_integral_filter_of_dominated_convergence
    (fun y => (stablePoissonKernel r 0 / m^2) * ‖g y‖)
  · exact Eventually.of_forall fun z => (((stableCoordinateCovariance_continuous hr hm).comp
        (continuous_const.sub continuous_id)).mul hc).aestronglyMeasurable
  · exact Eventually.of_forall fun z => Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_of_nonneg (stableCoordinateCovariance_nonneg hr _ _)]
      exact mul_le_mul_of_nonneg_right (stableCoordinateCovariance_le hr hm _) (norm_nonneg _)
  · exact hi.norm.const_mul _
  · exact Eventually.of_forall fun y => (((stableCoordinateCovariance_continuous hr hm).comp
      (continuous_id.sub continuous_const)).mul continuous_const).continuousAt

theorem osGreenPoissonTransfer_pos {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    {g : OSFourSpace → ℝ} (hc : Continuous g) (hk : HasCompactSupport g) (hn : 0 ≤ g)
    (hg : ∃ x, 0 < g x) (x : OSFourSpace) : 0 < osGreenPoissonTransfer m r g x := by
  obtain ⟨y,hy⟩ := hg
  have hcont := ((stableCoordinateCovariance_continuous hr hm).comp
    (continuous_const.sub continuous_id) |>.mul hc : Continuous (fun y => stableCoordinateCovariance r m (x-y)*g y))
  exact integral_pos_of_integrable_nonneg_nonzero hcont
    (hcont.integrable_of_hasCompactSupport hk.mul_left)
    (fun y => mul_nonneg (osGreenPoisson_pos hm hr _).le (hn y)) (mul_pos (osGreenPoisson_pos hm hr _) hy).ne'

/-- The spatial factor in either insertion is integrable and strictly
positive for every nonzero continuous nonnegative compact switch. -/
private theorem osSwitched_positive {ζ H : OSFourSpace → ℝ}
    (hc : Continuous ζ) (hk : HasCompactSupport ζ) (hn : 0 ≤ ζ) (hz : ∃ x, 0 < ζ x)
    (hH : Continuous H) (hpos : ∀ x, 0 < H x) : 0 < ∫ x, ζ x * H x := by
  obtain ⟨x,hx⟩ := hz
  exact integral_pos_of_integrable_nonneg_nonzero (hc.mul hH)
    ((hc.mul hH).integrable_of_hasCompactSupport hk.mul_right)
    (fun y => mul_nonneg (hn y) (hpos y).le) (mul_pos hx (hpos x)).ne'

def osReflectedBump (x : OSFourSpace) : ℝ := osPositiveBump (osTimeReflect x)

private theorem osReflectedBump_cont : Continuous osReflectedBump := osPositiveBump.continuous.comp osTimeReflect_continuous
private theorem osReflectedBump_compact : HasCompactSupport osReflectedBump :=
  osPositiveBump.hasCompactSupport.comp_homeomorph osTimeReflectionHomeomorph
private theorem osReflectedBump_nonzero : ∃ x, 0 < osReflectedBump x := by
  obtain ⟨x,hx⟩ := osPositiveBump_nonzero
  exact ⟨osTimeReflect x, by simpa only [osReflectedBump, osTimeReflect_involutive x] using hx⟩

def osRawQuarticSlope (m r : ℝ) (ζ : OSFourSpace → ℝ) : ℝ :=
  -(osCoincidence m r / 2) * ∫ x, ζ x *
    (osPoissonTransfer r osReflectedBump x * osPoissonTransfer r osPositiveBump x)

theorem osRawQuarticSlope_neg {m r : ℝ} (hm : 0 < m) (hr : 0 < r) {ζ : OSFourSpace → ℝ}
    (hc : Continuous ζ) (hk : HasCompactSupport ζ) (hn : 0 ≤ ζ) (hz : ∃ x, 0 < ζ x) :
    osRawQuarticSlope m r ζ < 0 := by
  have hi (x : OSFourSpace) := osPoissonTransfer_pos hr osReflectedBump_cont osReflectedBump_compact
    (fun z => osPositiveBump.nonneg' _) osReflectedBump_nonzero x
  have hj (x : OSFourSpace) := osPoissonTransfer_pos hr osPositiveBump.continuous osPositiveBump.hasCompactSupport
    osPositiveBump.nonneg' osPositiveBump_nonzero x
  apply mul_neg_of_neg_of_pos (neg_lt_zero.mpr (half_pos (osCoincidence_pos hm hr)))
  exact osSwitched_positive hc hk hn hz
    ((osPoissonTransfer_continuous hr osReflectedBump_cont
      (osReflectedBump_cont.integrable_of_hasCompactSupport osReflectedBump_compact)).mul
      (osPoissonTransfer_continuous hr osPositiveBump.continuous
        (osPositiveBump.continuous.integrable_of_hasCompactSupport osPositiveBump.hasCompactSupport)))
    (fun x => mul_pos (hi x) (hj x))

def osWickQuarticSlope (m r : ℝ) (ζ : OSFourSpace → ℝ) : ℝ :=
  -(∫ x, ζ x * (osPoissonTransfer r osReflectedBump x * osPoissonTransfer r osPositiveBump x *
    osGreenPoissonTransfer m r osReflectedBump x * osGreenPoissonTransfer m r osPositiveBump x))

theorem osWickQuarticSlope_neg {m r : ℝ} (hm : 0 < m) (hr : 0 < r) {ζ : OSFourSpace → ℝ}
    (hc : Continuous ζ) (hk : HasCompactSupport ζ) (hn : 0 ≤ ζ) (hz : ∃ x, 0 < ζ x) :
    osWickQuarticSlope m r ζ < 0 := by
  have hθ := osReflectedBump_cont
  have hb := osPositiveBump.continuous
  have hpθ := osPoissonTransfer_pos hr hθ osReflectedBump_compact
    (fun _ => osPositiveBump.nonneg' _) osReflectedBump_nonzero
  have hpb := osPoissonTransfer_pos hr hb osPositiveBump.hasCompactSupport osPositiveBump.nonneg' osPositiveBump_nonzero
  have hgθ := osGreenPoissonTransfer_pos hm hr hθ osReflectedBump_compact
    (fun _ => osPositiveBump.nonneg' _) osReflectedBump_nonzero
  have hgb := osGreenPoissonTransfer_pos hm hr hb osPositiveBump.hasCompactSupport osPositiveBump.nonneg' osPositiveBump_nonzero
  have hiθ : Integrable osReflectedBump := hθ.integrable_of_hasCompactSupport osReflectedBump_compact
  have hib : Integrable (osPositiveBump : OSFourSpace → ℝ) := hb.integrable_of_hasCompactSupport osPositiveBump.hasCompactSupport
  exact neg_lt_zero.mpr (osSwitched_positive hc hk hn hz
    ((((osPoissonTransfer_continuous hr hθ hiθ).mul (osPoissonTransfer_continuous hr hb hib)).mul
      (osGreenPoissonTransfer_continuous hm hr hθ hiθ)).mul (osGreenPoissonTransfer_continuous hm hr hb hib))
      (fun x => mul_pos (mul_pos (mul_pos (hpθ x) (hpb x)) (hgθ x)) (hgb x)))

end UV
