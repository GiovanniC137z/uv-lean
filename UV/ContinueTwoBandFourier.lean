import UV.ContinueTwoBandGaussianMarks
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! The physical-frequency Fourier transform of a normalized three-dimensional
heat hop and of every polarized displacement moment. The positive phase
agrees with the straight-link orientation. -/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace FourierTransform ContDiff

namespace UV.SectorPlane

/-- Heat density for a spatial displacement of a single hop. -/
def twoBandDisplacementDensity (σ : ℝ) (z : Spatial) : ℝ :=
  ((4 * Real.pi * σ^2) ^ (3/2 : ℝ))⁻¹ * Real.exp (-((4*σ^2)⁻¹ * ‖z‖^2))

def twoBandDisplacementWave (k z : Spatial) : ℂ :=
  Complex.exp ((⟪z,k⟫ : ℝ) * Complex.I)

theorem twoBand_displacement_wave_norm (k z : Spatial) : ‖twoBandDisplacementWave k z‖ = 1 := by
  simp [twoBandDisplacementWave,Complex.norm_exp]

theorem twoBand_displacement_density_moment (g : ℝ) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Integrable (fun z : Spatial => ‖z‖^n * ‖(g * twoBandDisplacementDensity σ z : ℂ)‖) := by
  let a := (4*σ^2)⁻¹
  let c := ((4*Real.pi*σ^2)^(3/2:ℝ))⁻¹
  have ha : 0 < a := by unfold a; positivity
  have hc : 0 ≤ c := by unfold c; positivity
  have h := (integrable_real_degree_gaussian (μ := (volume : Measure Spatial))
    (a := a) (D := (n:ℝ)) ha (by positivity)).const_mul (|g| * c)
  simp only [Real.rpow_natCast] at h
  refine h.mono' (by unfold twoBandDisplacementDensity; fun_prop) ?_
  filter_upwards with z
  have hnonneg : 0 ≤ c * Real.exp (-(a * ‖z‖^2)) := by positivity
  change ‖‖z‖^n * ‖(g:ℂ) * ((c * Real.exp (-(a * ‖z‖^2)) : ℝ) : ℂ)‖‖ ≤ _
  rw [Real.norm_of_nonneg (by positivity),norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_of_nonneg hnonneg]
  nlinarith [mul_nonneg (mul_nonneg (abs_nonneg g) hc) (Real.exp_nonneg (-(a*‖z‖^2)))]

theorem twoBand_displacement_fourier (g : ℝ) {σ : ℝ} (hσ : 0 < σ) (k : Spatial) :
    (∫ z, twoBandDisplacementWave k z * (g * twoBandDisplacementDensity σ z : ℂ)) =
      (twoBandSpatialHop g σ k : ℂ) := by
  let a := (4*σ^2)⁻¹
  let c := (4*Real.pi*σ^2)^(3/2:ℝ)
  have ha : 0 < a := by unfold a; positivity
  have hc : 0 < c := by unfold c; positivity
  have hmass : (Real.pi / (a : ℂ)) ^ ((Module.finrank ℝ Spatial : ℂ)/2) = (c:ℂ) := by
    have hr : Real.pi / a = 4*Real.pi*σ^2 := by unfold a; rw [div_inv_eq_mul]; ring
    unfold c
    rw [Complex.ofReal_cpow (by positivity),←hr,Complex.ofReal_div]
    norm_num [Spatial,finrank_euclideanSpace]
  have hexp : Complex.I^2 * (‖k‖:ℂ)^2 / (4*(a:ℂ)) = (-(σ^2 * ‖k‖^2) : ℝ) := by
    dsimp [a]
    push_cast
    rw [Complex.I_sq]
    field_simp
  calc
    _ = (g:ℂ) * (c:ℂ)⁻¹ * ∫ z : Spatial, Complex.exp (-(a:ℂ)*(‖z‖:ℂ)^2 + Complex.I*⟪k,z⟫) := by
      rw [← integral_const_mul]
      congr 1
      funext z
      rw [twoBandDisplacementWave,twoBandDisplacementDensity,real_inner_comm z k,Complex.exp_add]
      push_cast
      simp only [c,a]
      push_cast
      ring_nf
    _ = _ := by
      rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (show 0 < (a:ℂ).re from ha),
        hmass,hexp,twoBandSpatialHop,Complex.ofReal_mul,Complex.ofReal_exp]
      have hn : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      field_simp

theorem twoBand_displacement_density_mass {σ : ℝ} (hσ : 0 < σ) :
    (∫ z : Spatial, twoBandDisplacementDensity σ z) = 1 := by
  have h := twoBand_displacement_fourier 1 hσ 0
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal (f := twoBandDisplacementDensity σ)]
  simpa [twoBandDisplacementWave,twoBandSpatialHop] using h

private def twoBandAngularPairing : Spatial →L[ℝ] Spatial →L[ℝ] ℝ :=
  (-(2 * Real.pi)⁻¹) • innerSL ℝ

private theorem twoBand_angular_pairing_apply (z k : Spatial) :
    twoBandAngularPairing z k = -(2*Real.pi)⁻¹ * ⟪z,k⟫ := rfl

private theorem twoBand_angular_transform (f : Spatial → ℂ) (k : Spatial) :
    VectorFourier.fourierIntegral Real.fourierChar volume twoBandAngularPairing.toLinearMap₁₂ f k =
      ∫ z, twoBandDisplacementWave k z * f z := by
  rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
  congr 1
  funext z
  change Complex.exp (↑(-2*Real.pi * twoBandAngularPairing z k) * Complex.I) * f z = _
  rw [twoBand_angular_pairing_apply]
  have hs : -2*Real.pi * (-(2*Real.pi)⁻¹ * ⟪z,k⟫) = ⟪z,k⟫ := by
    field_simp
  rw [hs]
  rfl

theorem twoBand_displacement_fourier_derivative (g : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {n : ℕ} (u : Fin n → UnitVector Spatial) (k : Spatial) :
    (∫ z, twoBandDisplacementWave k z * ((∏ j, Complex.I * (⟪z,(u j).val⟫ : ℝ)) *
        (g * twoBandDisplacementDensity σ z : ℂ))) =
      (iteratedFDeriv ℝ n (twoBandSpatialHop g σ) k (fun j => (u j).val) : ℂ) := by
  let f : Spatial → ℂ := fun z => g * twoBandDisplacementDensity σ z
  let L := twoBandAngularPairing
  have hφ : VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂ f =
      Complex.ofRealCLM ∘ twoBandSpatialHop g σ := by
    funext k
    exact (twoBand_angular_transform f k).trans (twoBand_displacement_fourier g hσ k)
  have hf : AEStronglyMeasurable f := by unfold f twoBandDisplacementDensity; fun_prop
  have hMoment (r : ℕ) : Integrable (fun z => ‖z‖^r * ‖f z‖) := twoBand_displacement_density_moment g hσ r
  have hD := VectorFourier.iteratedFDeriv_fourierIntegral (N := (n:ℕ∞)) L (fun r _ => hMoment r) hf (le_refl (n:ℕ∞))
  have hv := congrArg (fun F : Spatial → ContinuousMultilinearMap ℝ (fun _ : Fin n => Spatial) ℂ =>
      F k (fun j => (u j).val)) hD
  rw [hφ] at hv
  change iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ twoBandSpatialHop g σ) k _ = _ at hv
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_left (twoBand_gaussian_hop_smooth g σ).contDiffAt
    (show (n : WithTop ℕ∞) ≤ ∞ by exact_mod_cast le_top)] at hv
  change ((iteratedFDeriv ℝ n (twoBandSpatialHop g σ) k (fun j => (u j).val) : ℝ) : ℂ) = _ at hv
  rw [hv]
  change _ = VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂
    (fun z => VectorFourier.fourierPowSMulRight L f z n) k (fun j => (u j).val)
  rw [Real.fourierIntegral_continuousMultilinearMap_apply'
    (VectorFourier.integrable_fourierPowSMulRight L (hMoment n) hf),twoBand_angular_transform]
  congr 1
  funext z
  rw [VectorFourier.fourierPowSMulRight_apply]
  change _ = _ * ((-(2 * (Real.pi:ℂ) * Complex.I))^n *
    ((↑(∏ j, twoBandAngularPairing z (u j).val) : ℂ) * f z))
  simp_rw [twoBand_angular_pairing_apply]
  rw [Complex.ofReal_prod]
  simp_rw [Complex.ofReal_mul]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← mul_assoc ((-(2 * (Real.pi:ℂ) * Complex.I))^n),
    ← mul_assoc ((-(2 * (Real.pi:ℂ) * Complex.I))^n),←mul_pow]
  have hp : -(2 * (Real.pi:ℂ) * Complex.I) * ((-(2*Real.pi)⁻¹:ℝ):ℂ) = Complex.I := by
    push_cast
    field_simp
  rw [hp]

end UV.SectorPlane
