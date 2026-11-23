import UV.ContinueThinCurrentPerimeter
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The Fourier kernel of a smooth window has the uniform integrable
line majorant needed by the actual arclength perimeter calculation. -/

noncomputable section

open MeasureTheory Filter Set Bornology
open scoped BigOperators InnerProductSpace RealInnerProductSpace FourierTransform SchwartzMap Topology ENNReal

namespace UV

def thinFourierScale : ℝ := (2 * Real.pi)⁻¹

theorem thinFourierScale_pos : 0 < thinFourierScale := by unfold thinFourierScale; positivity

/-- The manuscript's inverse transform and mathlib's inverse transform
differ by the stated four-dimensional normalization and argument scale. -/
theorem thinWindowInverse_eq_fourier (f : ThinCurrentPlane → ℝ) (x : ThinCurrentPlane) :
    thinWindowInverse f x =
      (((2 * Real.pi) ^ 4)⁻¹ : ℝ) •
        𝓕⁻ (fun p => (f p : ℂ)) (thinFourierScale • x) := by
  rw [thinWindowInverse, Real.fourierIntegralInv_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  unfold thinPlaneWave thinFourierScale
  rw [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0),
    one_mul, smul_eq_mul, mul_comm Complex.I, mul_comm]

/-- The normalized Fourier kernel is a genuine Schwartz function
when the window is smooth with compact support. -/
theorem thinWindowInverse_isSchwartz {φ : ThinCurrentPlane → ℝ}
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ K : 𝓢(ThinCurrentPlane, ℂ), thinWindowInverse φ = K := by
  let f : ThinCurrentPlane → ℂ := fun p => (φ p : ℂ)
  have hcf : HasCompactSupport f := by
    have he : Function.support f = Function.support φ := by
      ext p
      simp [Function.mem_support, f]
    simpa only [HasCompactSupport, tsupport, he] using hc
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f := Complex.ofRealCLM.contDiff.comp hsm
  let S := hcf.toSchwartzMap hf
  let U := (SchwartzMap.fourierTransformCLE ℂ).symm S
  let a : ℝˣ := Units.mk0 thinFourierScale thinFourierScale_pos.ne'
  let T : ThinCurrentPlane ≃L[ℝ] ThinCurrentPlane := ContinuousLinearEquiv.smulLeft a
  let K : 𝓢(ThinCurrentPlane, ℂ) :=
    (((2 * Real.pi) ^ 4)⁻¹ : ℝ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ T U
  refine ⟨K, ?_⟩
  funext x
  rw [thinWindowInverse_eq_fourier]
  change _ = (((2 * Real.pi) ^ 4)⁻¹ : ℝ) •
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ T U) x)
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  change _ = (((2 * Real.pi) ^ 4)⁻¹ : ℝ) • U (thinFourierScale • x)
  dsimp only [U]
  rw [SchwartzMap.fourierTransformCLE_symm_apply]
  rfl

/-- A single inverse-square majorant controls every actual unit line of
a Schwartz kernel, and also proves its vanishing at spatial infinity. -/
theorem thinSchwartz_kernel_controls (K : 𝓢(ThinCurrentPlane, ℂ)) :
    Tendsto K (cobounded ThinCurrentPlane) (𝓝 0) ∧
      ∃ dom : ℝ → ℝ, Integrable dom ∧ ∀ x z, |z| ≤ ‖x‖ → ‖K x‖ ≤ dom z := by
  obtain ⟨A, ha, hA⟩ := K.decay 0 0
  obtain ⟨B, hb, hB⟩ := K.decay 2 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hA
  simp only [norm_iteratedFDeriv_zero] at hB
  let dom : ℝ → ℝ := fun z => (A + B) * (1 + z ^ 2)⁻¹
  have hdom (x : ThinCurrentPlane) (z : ℝ) (hz : |z| ≤ ‖x‖) : ‖K x‖ ≤ dom z := by
    unfold dom
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + z ^ 2)]
    have hsq : z ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [← sq_abs z]
      exact pow_le_pow_left₀ (abs_nonneg _) hz 2
    have h := mul_le_mul_of_nonneg_right hsq (norm_nonneg (K x))
    nlinarith [hA x, hB x]
  have hbound : Tendsto (fun x : ThinCurrentPlane => 1 + ‖x‖ ^ 2)
      (cobounded ThinCurrentPlane) atTop := by
    have hN : Tendsto (fun x : ThinCurrentPlane => ‖x‖) (cobounded ThinCurrentPlane) atTop :=
      tendsto_norm_cobounded_atTop
    apply tendsto_atTop.mpr
    intro t
    filter_upwards [hN.eventually_ge_atTop (max 1 t)] with x hx
    have h1 := (le_max_left (1 : ℝ) t).trans hx
    have h2 := (le_max_right (1 : ℝ) t).trans hx
    nlinarith
  refine ⟨?_, dom, integrable_inv_one_add_sq.const_mul _, hdom⟩
  apply squeeze_zero_norm
    (fun x => hdom x ‖x‖ (by rw [abs_of_nonneg (norm_nonneg x)]))
  have h := (tendsto_inv_atTop_zero.comp hbound).const_mul (A + B)
  simpa only [mul_zero] using h

end UV
