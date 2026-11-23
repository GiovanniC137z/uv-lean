import UV.RevisionOSJoint
import UV.ContinuationSectorPlane
import Mathlib.Analysis.Distribution.FourierSchwartz

/-! The local massive Euclidean operator and its inverse on smooth probes
in oriented GT coordinates on one sector-plane. Mathlib's Fourier variable
is measured in cycles, so the physical momentum is 2πk. -/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap FourierTransform RealInnerProductSpace Topology BigOperators

namespace UV

abbrev OSProbe := 𝓢(OSFourSpace, ℂ)

/-- Coordinate axes of the intrinsic Euclidean chart are unit vectors. -/
def osAxis (i : Fin 4) : SectorPlane.UnitVector OSFourSpace :=
  ⟨EuclideanSpace.single i 1, by simp⟩

def osD (i : Fin 4) : OSProbe →L[ℂ] OSProbe :=
  SchwartzMap.pderivCLM ℂ (osAxis i).val

/-- The local differential operator on its Schwartz core. -/
def osMassiveLocal (m : ℝ) (u : OSProbe) : OSProbe :=
  (m ^ 2 : ℂ) • u - ∑ i : Fin 4, osD i (osD i u)

def osMassiveSymbol (m : ℝ) (k : OSFourSpace) : ℝ :=
  m ^ 2 + (2 * Real.pi) ^ 2 * ‖k‖ ^ 2

theorem osMassiveSymbol_pos {m : ℝ} (hm : 0 < m) (k : OSFourSpace) :
    0 < osMassiveSymbol m k := by unfold osMassiveSymbol; positivity

theorem osD_fourier (i : Fin 4) (u : OSProbe) (k : OSFourSpace) :
    𝓕 (osD i u) k = (2 * Real.pi * Complex.I * (k i : ℂ)) * 𝓕 u k := by
  have hF : Integrable (fderiv ℝ u) := (SchwartzMap.fderivCLM ℂ u).integrable
  change 𝓕 (fun x => (fderiv ℝ u x) (osAxis i).val) k = _
  rw [← Real.fourierIntegral_continuousLinearMap_apply hF,
    Real.fourierIntegral_fderiv u.integrable u.differentiable hF]
  simp [VectorFourier.fourierSMulRight_apply, osAxis, EuclideanSpace.inner_single_right,
    smul_eq_mul]
  ring

private theorem osProbe_sum_apply (v : Fin 4 → OSProbe) (x : OSFourSpace) :
    (∑ i, v i) x = ∑ i, v i x := by
  simpa only [SchwartzMap.delta_apply] using map_sum (SchwartzMap.delta ℂ ℂ x) v Finset.univ

theorem osMassiveLocal_fourier (m : ℝ) (u : OSProbe) (k : OSFourSpace) :
    𝓕 (osMassiveLocal m u) k = (osMassiveSymbol m k : ℂ) * 𝓕 u k := by
  change (SchwartzMap.fourierTransformCLM ℂ (osMassiveLocal m u)) k = _
  simp only [osMassiveLocal, map_sub, map_smul, map_sum]
  change (m ^ 2 : ℂ) * 𝓕 u k - (∑ i : Fin 4, SchwartzMap.fourierTransformCLM ℂ
    (osD i (osD i u))) k = _
  have hev : (∑ i : Fin 4, SchwartzMap.fourierTransformCLM ℂ (osD i (osD i u))) k =
      ∑ i : Fin 4, 𝓕 (osD i (osD i u)) k := by
    exact osProbe_sum_apply _ _
  rw [hev]
  simp_rw [osD_fourier]
  have hnorm : ‖k‖ ^ 2 = ∑ i, (k i) ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, sq_abs]
  simp only [osMassiveSymbol, hnorm, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_sum]
  simp only [Fin.sum_univ_four]
  linear_combination (norm := ring_nf) -(2 * Real.pi : ℂ)^2 *
    ((k 0 : ℂ)^2 + (k 1 : ℂ)^2 + (k 2 : ℂ)^2 + (k 3 : ℂ)^2) * 𝓕 u k *
      Complex.I_sq

/-- The massive resolvent acting on Schwartz data using its inverse Fourier multiplier. -/
def osMassiveResolvent (m : ℝ) (f : OSProbe) : OSFourSpace → ℂ :=
  𝓕⁻ (fun k => (osMassiveSymbol m k : ℂ)⁻¹ * 𝓕 f k)

theorem osMassiveResolvent_local {m : ℝ} (hm : 0 < m) (u : OSProbe) :
    osMassiveResolvent m (osMassiveLocal m u) = u := by
  have h : (fun k => (osMassiveSymbol m k : ℂ)⁻¹ * 𝓕 (osMassiveLocal m u) k) = 𝓕 u := by
    funext k
    rw [osMassiveLocal_fourier, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact_mod_cast (osMassiveSymbol_pos hm k).ne'
  rw [osMassiveResolvent, h]
  exact u.continuous.fourier_inversion u.integrable (SchwartzMap.fourierTransformCLM ℂ u).integrable

theorem osD_tsupport (i : Fin 4) (u : OSProbe) :
    tsupport (osD i u) ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  contrapose! hx
  rw [Function.notMem_support]
  change (fderiv ℝ u x) (osAxis i).val = 0
  rw [fderiv_of_notMem_tsupport ℝ hx, ContinuousLinearMap.zero_apply]

theorem osMassiveLocal_tsupport (m : ℝ) (u : OSProbe) :
    tsupport (osMassiveLocal m u) ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  contrapose! hx
  have hu := image_eq_zero_of_notMem_tsupport hx
  have hd (i : Fin 4) : (osD i (osD i u)) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (osD_tsupport i u (osD_tsupport i _ h)))
  rw [Function.notMem_support]
  change (m ^ 2 : ℂ) * u x - (∑ i : Fin 4, osD i (osD i u)) x = 0
  rw [show (∑ i : Fin 4, osD i (osD i u)) x = ∑ i : Fin 4, osD i (osD i u) x
    from osProbe_sum_apply _ _]
  simp [hu, hd]

/-- Differentiating an actual real probe in a unit spatial or GT direction
preserves reality. -/
theorem osD_real (i : Fin 4) (u : OSProbe) (hu : ∀ x, (u x).im = 0) (x : OSFourSpace) :
    (osD i u x).im = 0 := by
  have he : Complex.imCLM ∘ (u : OSFourSpace → ℂ) = 0 := funext hu
  have hd := (Complex.imCLM.hasFDerivAt.comp x (u.hasFDerivAt x)).fderiv
  rw [he, fderiv_zero] at hd
  exact (congrArg (fun T : OSFourSpace →L[ℝ] ℝ => T (osAxis i).val) hd).symm

theorem osMassiveLocal_real (m : ℝ) (u : OSProbe) (hu : ∀ x, (u x).im = 0) (x : OSFourSpace) :
    (osMassiveLocal m u x).im = 0 := by
  change ((m^2 : ℂ)*u x - (∑ i : Fin 4, osD i (osD i u)) x).im = 0
  rw [osProbe_sum_apply]
  have hD (i : Fin 4) := osD_real i (osD i u) (osD_real i u hu) x
  rw [Complex.sub_im, Complex.mul_im, Complex.im_sum, hu, mul_zero]
  simp [← Complex.ofReal_pow, hD]

end UV
