import UV.ContinueOSQuarticKernels

/-! Point evaluations of the transferred covariance on compact boundary
smearings, with both members of the reflected quadratic witness. -/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap FourierTransform Topology

namespace UV

def osPointSource (m r : ℝ) (f : OSProbe) : OSFourSpace → ℂ :=
  𝓕⁻ (fun k => (osCovWeight m r k : ℂ) * 𝓕 f k)

theorem osCovWeight_fourier {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (k : OSFourSpace) :
    𝓕 (fun x => (stableCoordinateCovariance r m x : ℂ)) k = (osCovWeight m r k : ℂ) := by
  rw [osFourier_phase, stableCoordinateCovariance_characteristic hr hm, scalarCovariance_stable]
  congr 1
  simp [osCovWeight, osTransferSymbol, osMassiveSymbol, norm_smul, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_pow, add_comm]

theorem osGreenPoissonTransfer_fourier {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    {g : OSFourSpace → ℝ} (hg : Integrable g) (k : OSFourSpace) :
    𝓕 (fun x => (osGreenPoissonTransfer m r g x : ℂ)) k =
      (osCovWeight m r k : ℂ) * 𝓕 (fun x => (g x : ℂ)) k := by
  unfold osGreenPoissonTransfer
  rw [osKernel_convolution_fourier (stableCoordinateCovariance_continuous hr hm)
    (stableCoordinateCovariance_integrable hr hm) hg, osCovWeight_fourier hm hr]

theorem osPointSource_spatial {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (f : OSProbe)
    {h : OSFourSpace → ℝ} (hh : Continuous h) (hi : Integrable h)
    (hf : (f : OSFourSpace → ℂ) = fun x => (h x : ℂ)) :
    osPointSource m r f = fun x => (osGreenPoissonTransfer m r h x : ℂ) := by
  have hT : Integrable (osGreenPoissonTransfer m r h) :=
    (osKernel_weighted_joint (stableCoordinateCovariance_continuous hr hm)
      (stableCoordinateCovariance_integrable hr hm) hi).swap.integral_prod_left
  have htrans : Integrable (fun x => (osGreenPoissonTransfer m r h x : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hT
  have hF : 𝓕 (fun x => (osGreenPoissonTransfer m r h x : ℂ)) =
      fun k => (osCovWeight m r k : ℂ) * 𝓕 f k := by
    funext k
    rw [osGreenPoissonTransfer_fourier hm hr hi, hf]
  have hci := (Complex.continuous_ofReal.comp (osGreenPoissonTransfer_continuous hm hr hh hi))
  unfold osPointSource
  rw [← hF]
  apply hci.fourier_inversion htrans
  change Integrable (𝓕 (fun x => (osGreenPoissonTransfer m r h x : ℂ)))
  rw [hF]
  refine ((SchwartzMap.fourierTransformCLM ℂ f).integrable.norm.const_mul ((m^2)⁻¹)).mono' ?_ ?_
  · have hc : Continuous (osCovWeight m r) := by
      unfold osCovWeight osTransferSymbol osMassiveSymbol
      fun_prop (disch := intro k; positivity)
    exact ((Complex.continuous_ofReal.comp hc).mul
      (SchwartzMap.fourierTransformCLM ℂ f).continuous).aestronglyMeasurable
  · filter_upwards with k
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (osCovWeight_bound hm hr.le _).1]
    exact mul_le_mul_of_nonneg_right (osCovWeight_bound hm hr.le _).2 (norm_nonneg _)

theorem osPointSource_local_spatial {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (f : OSProbe)
    {h : OSFourSpace → ℝ} (hh : Continuous h) (hi : Integrable h)
    (hf : (f : OSFourSpace → ℂ) = fun x => (h x : ℂ)) :
    osPointSource m r (osMassiveLocal m f) = fun x => (osPoissonTransfer r h x : ℂ) := by
  have hF : 𝓕 (fun x => (osPoissonTransfer r h x : ℂ)) =
      fun k => (osCovWeight m r k : ℂ) * 𝓕 (osMassiveLocal m f) k := by
    funext k
    rw [osPoissonTransfer_fourier hr hi, osMassiveLocal_fourier, ← hf,
      osCovWeight, Complex.ofReal_div]
    have hne : (osMassiveSymbol m k : ℂ) ≠ 0 := by exact_mod_cast (osMassiveSymbol_pos hm _).ne'
    field_simp
  unfold osPointSource
  rw [← hF]
  apply (Complex.continuous_ofReal.comp (osPoissonTransfer_continuous hr hh hi)).fourier_inversion
    (Complex.ofRealCLM.integrable_comp (osPoissonTransfer_integrable hr hi))
  change Integrable (𝓕 (fun x => (osPoissonTransfer r h x : ℂ)))
  have hF' : 𝓕 (fun x => (osPoissonTransfer r h x : ℂ)) =
      fun k => (osTransferSymbol r k : ℂ) * 𝓕 f k := by
    funext k
    rw [osPoissonTransfer_fourier hr hi, hf]
  rw [hF']
  refine (SchwartzMap.fourierTransformCLM ℂ f).integrable.norm.mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp (show Continuous (osTransferSymbol r) by
      unfold osTransferSymbol; fun_prop)).mul (SchwartzMap.fourierTransformCLM ℂ f).continuous).aestronglyMeasurable
  · filter_upwards with k
    rw [norm_mul, Complex.norm_real, osTransferSymbol, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) (by positivity)))

/-- Both unreflected and reflected point contractions for f and h with h=u
the explicit positive-GT probe. -/
theorem osPointSource_four_pairings {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (x : OSFourSpace) :
    osPointSource m r (osMassiveLocal m osBumpProbe) x = (osPoissonTransfer r osPositiveBump x : ℂ) ∧
    osPointSource m r (osReflectProbe (osMassiveLocal m osBumpProbe)) x =
      (osPoissonTransfer r osReflectedBump x : ℂ) ∧
    osPointSource m r osBumpProbe x = (osGreenPoissonTransfer m r osPositiveBump x : ℂ) ∧
    osPointSource m r (osReflectProbe osBumpProbe) x = (osGreenPoissonTransfer m r osReflectedBump x : ℂ) := by
  have hc : Continuous osReflectedBump := osPositiveBump.continuous.comp osTimeReflect_continuous
  have hi : Integrable osReflectedBump := hc.integrable_of_hasCompactSupport
    (osPositiveBump.hasCompactSupport.comp_homeomorph osTimeReflectionHomeomorph)
  have hb : Integrable (osPositiveBump : OSFourSpace → ℝ) :=
    osPositiveBump.continuous.integrable_of_hasCompactSupport osPositiveBump.hasCompactSupport
  rw [← osMassiveLocal_reflect]
  exact ⟨congrFun (osPointSource_local_spatial hm hr _ osPositiveBump.continuous hb rfl) x,
    congrFun (osPointSource_local_spatial hm hr _ hc hi rfl) x,
    congrFun (osPointSource_spatial hm hr _ osPositiveBump.continuous hb rfl) x,
    congrFun (osPointSource_spatial hm hr _ hc hi rfl) x⟩

end UV
