import UV.ContinueOSOrientedProbe
import UV.ContinueOSPoissonPairing

/-! The actual three massive Fourier covariance blocks in the joint
Osterwalder--Schrader test at positive depth. -/

noncomputable section

open MeasureTheory Set Filter
open scoped SchwartzMap FourierTransform Topology ComplexConjugate

namespace UV

def osCovWeight (m a : ℝ) (k : OSFourSpace) : ℝ :=
  osTransferSymbol a k / osMassiveSymbol m k

@[simp] theorem osTransferSymbol_zero (k : OSFourSpace) : osTransferSymbol 0 k = 1 := by
  simp [osTransferSymbol]

theorem osTransferSymbol_add (a b : ℝ) (k : OSFourSpace) :
    osTransferSymbol (a + b) k = osTransferSymbol a k * osTransferSymbol b k := by
  unfold osTransferSymbol
  rw [← Real.exp_add]
  congr 1
  ring

theorem osCovWeight_bound {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (k : OSFourSpace) :
    0 ≤ osCovWeight m a k ∧ osCovWeight m a k ≤ (m ^ 2)⁻¹ := by
  have hS : m ^ 2 ≤ osMassiveSymbol m k := by
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hP : osTransferSymbol a k ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ a * (2 * Real.pi * ‖k‖) := by positivity
    linarith)
  refine ⟨div_nonneg (Real.exp_pos _).le (osMassiveSymbol_pos hm _).le, ?_⟩
  exact (div_le_div_of_nonneg_right hP (osMassiveSymbol_pos hm _).le).trans
    (by simpa only [one_div] using (one_div_le_one_div_of_le (sq_pos_of_pos hm) hS))

/-- The oriented reflection acts on the first test of the covariance with a
total Poisson depth a. The depths of the source matrix are 0, r, r, and 2r. -/
def osReflectedBlock (m a : ℝ) (f g : OSProbe) : ℂ :=
  ∫ k, conj (𝓕 f (osTimeReflect k)) * (osCovWeight m a k : ℂ) * 𝓕 g k

theorem osReflectedBlock_integrable {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (f g : OSProbe) :
    Integrable (fun k => conj (𝓕 f (osTimeReflect k)) * (osCovWeight m a k : ℂ) * 𝓕 g k) := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let G := SchwartzMap.fourierTransformCLM ℂ g
  have hc : Continuous (osCovWeight m a) := by
    unfold osCovWeight osTransferSymbol osMassiveSymbol
    fun_prop (disch := intro k; positivity)
  apply (G.integrable.norm.const_mul (‖F.toBoundedContinuousFunction‖ * (m ^ 2)⁻¹)).mono'
  · exact (((Complex.continuous_conj.comp (F.continuous.comp osTimeReflect_continuous)).mul
      (Complex.continuous_ofReal.comp hc)).mul G.continuous).aestronglyMeasurable
  · filter_upwards with k
    rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg
      (osCovWeight_bound hm ha k).1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (F.toBoundedContinuousFunction.norm_coe_le_norm _) (osCovWeight_bound hm ha k).2
      (osCovWeight_bound hm ha k).1 (norm_nonneg _)) (norm_nonneg _)

theorem osReflectedBlock_hermitian (m a : ℝ) (f g : OSProbe) :
    conj (osReflectedBlock m a f g) = osReflectedBlock m a g f := by
  unfold osReflectedBlock
  rw [← integral_conj]
  calc
    _ = ∫ k, (fun x => conj (𝓕 g (osTimeReflect x)) * (osCovWeight m a x : ℂ) * 𝓕 f x)
        (osTimeReflect k) := by
      congr 1
      funext k
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, osTimeReflect_involutive k,
        osCovWeight, osTransferSymbol, osMassiveSymbol, osTimeReflect_norm]
      ring
    _ = _ := osTimeReflectionIsometry.measurePreserving.integral_comp
      osTimeReflectionIsometry.toHomeomorph.measurableEmbedding
        (fun k => conj (𝓕 g (osTimeReflect k)) * (osCovWeight m a k : ℂ) * 𝓕 f k)

theorem osReflectedBlock_local {m : ℝ} (hm : 0 < m) (a : ℝ) (u g : OSProbe) :
    osReflectedBlock m a (osMassiveLocal m u) g =
      ∫ k, conj (𝓕 u (osTimeReflect k)) * ((osTransferSymbol a k : ℂ) * 𝓕 g k) := by
  unfold osReflectedBlock
  congr 1
  funext k
  have hS : osMassiveSymbol m (osTimeReflect k) = osMassiveSymbol m k := by
    simp [osMassiveSymbol, osTimeReflect_norm]
  have hn : (osMassiveSymbol m k : ℂ) ≠ 0 := by exact_mod_cast (osMassiveSymbol_pos hm _).ne'
  rw [osMassiveLocal_fourier, map_mul, hS, Complex.conj_ofReal, osCovWeight, Complex.ofReal_div]
  field_simp

private theorem osBump_fourier_reflection (k : OSFourSpace) :
    conj (𝓕 osBumpProbe (osTimeReflect k)) = 𝓕⁻ (osReflectProbe osBumpProbe) k := by
  rw [← osReflectProbe_fourier]
  exact (osFourier_inverse_real (fun x => osPositiveBump (osTimeReflect x)) k).symm

/-- Exact null reflected covariance for the local massive probe. -/
theorem osReflectedBlock_local_zero {m : ℝ} (hm : 0 < m) (g : OSProbe)
    (hg : tsupport g ⊆ {x | 1 ≤ x 0}) :
    osReflectedBlock m 0 (osMassiveLocal m osBumpProbe) g = 0 := by
  rw [osReflectedBlock_local hm]
  simp only [osTransferSymbol_zero, Complex.ofReal_one, one_mul, osBump_fourier_reflection]
  rw [osFourier_duality _ g.integrable]
  have h (x : OSFourSpace) :
      osReflectProbe osBumpProbe x * g x = 0 := by
    by_cases hx : 1 ≤ x 0
    · apply mul_eq_zero_of_left
      change osBumpProbe (osTimeReflect x) = 0
      apply image_eq_zero_of_notMem_tsupport
      intro hy
      have h' := osBumpProbe_support hy
      change 1 ≤ osTimeReflect x 0 at h'
      rw [osTimeReflect_time] at h'
      linarith
    · exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport (fun hy =>
        hx (hg hy)))
  simp only [h, integral_zero]

theorem osReflectedBlock_null {m : ℝ} (hm : 0 < m) :
    osReflectedBlock m 0 (osMassiveLocal m osBumpProbe) (osMassiveLocal m osBumpProbe) = 0 :=
  osReflectedBlock_local_zero hm _ (osBumpLocal_support m)

/-- Exact undeformed Euclidean mixed pairing of the same two source slots. -/
theorem osReflectedBlock_mixed {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    osReflectedBlock m r (osMassiveLocal m osBumpProbe) osBumpProbe =
      ((∫ x, osPositiveBump (osTimeReflect x) * osPoissonTransfer r osPositiveBump x : ℝ) : ℂ) := by
  have hg : Integrable (osPositiveBump : OSFourSpace → ℝ) :=
    osPositiveBump.continuous.integrable_of_hasCompactSupport osPositiveBump.hasCompactSupport
  rw [osReflectedBlock_local hm]
  simp_rw [osBump_fourier_reflection]
  change (∫ k, 𝓕⁻ (osReflectProbe osBumpProbe) k * ((osTransferSymbol r k : ℂ) *
    𝓕 (fun x => (osPositiveBump x : ℂ)) k)) = _
  simp_rw [← osPoissonTransfer_fourier hr hg]
  have ht : Integrable (fun x => (osPoissonTransfer r osPositiveBump x : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (osPoissonTransfer_integrable hr hg)
  rw [osFourier_duality (osReflectProbe osBumpProbe) ht]
  simp only [osReflectProbe_apply, osBumpProbe_apply, ← Complex.ofReal_mul, integral_complex_ofReal]

theorem osReflectedBlock_mixed_pos {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    0 < (osReflectedBlock m r (osMassiveLocal m osBumpProbe) osBumpProbe).re := by
  rw [osReflectedBlock_mixed hm hr]
  exact os_poisson_mixed_reflected_pos hr osPositiveBump.continuous
    osPositiveBump.hasCompactSupport osPositiveBump.nonneg' osPositiveBump_nonzero
    osPositiveBump.nonneg' osPositiveBump.continuous osPositiveBump.hasCompactSupport osPositiveBump_nonzero

/-- The quadratic test on the joint algebra with two independently smeared
source slots. The two off-diagonal blocks are retained separately. -/
def osJointReflectedQuadratic (m r t : ℝ) (f g : OSProbe) : ℝ :=
  t ^ 2 * (osReflectedBlock m 0 f f).re + t * (osReflectedBlock m r f g).re +
    t * (osReflectedBlock m r g f).re + (osReflectedBlock m (r + r) g g).re

theorem os_joint_massive_obstruction {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    ∃ f g : OSProbe, tsupport f ⊆ {x | 1 ≤ x 0} ∧ tsupport g ⊆ {x | 1 ≤ x 0} ∧
      HasCompactSupport f ∧ HasCompactSupport g ∧
      ∃ t : ℝ, osJointReflectedQuadratic m r t f g < 0 := by
  let f := osMassiveLocal m osBumpProbe
  let g := osBumpProbe
  have hg : HasCompactSupport g := osPositiveBump.hasCompactSupport.comp_left
    (g := Complex.ofReal) Complex.ofReal_zero
  have hf : HasCompactSupport f := hg.of_isClosed_subset isClosed_closure (osMassiveLocal_tsupport m g)
  refine ⟨f, g, osBumpLocal_support m, osBumpProbe_support, hf, hg, ?_⟩
  obtain ⟨t, ht⟩ := os_negative_of_zero_diagonal_nonzero_mixed (osReflectedBlock_mixed_pos hm hr).ne'
    (osReflectedBlock m (r + r) g g).re
  refine ⟨t, ?_⟩
  have h0 : osReflectedBlock m 0 f f = 0 := osReflectedBlock_null hm
  have hcross := congrArg Complex.re (osReflectedBlock_hermitian m r f g)
  simp only [Complex.conj_re] at hcross
  unfold osJointReflectedQuadratic
  rw [h0, ← hcross, Complex.zero_re, mul_zero, zero_add]
  change 2 * (osReflectedBlock m r f g).re * t + (osReflectedBlock m (r + r) g g).re < 0 at ht
  linarith

end UV
