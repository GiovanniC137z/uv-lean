import UV.ContinueFiveBallMagneticSpeed
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

/-! Spatial normalizations and the uniform bound on the vacuum-projected
magnetic row. All Fourier phases use the fixed spatial readout. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane
open scoped Topology RealInnerProductSpace NNReal

namespace UV

/-- The essential soft-momentum filter on the locked spatial chart. -/
def magneticSoftMomenta : Filter Spatial := 𝓝 0 ⊓ ae volume

instance magnetic_soft_momenta_nontrivial : NeBot magneticSoftMomenta := by
  apply inf_neBot_iff.mpr
  intro s hs t ht
  obtain ⟨x,hx,hxt⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_pos_of_mem_nhds (volume : Measure Spatial) hs).ne' (ae_restrict_of_ae ht)
  exact ⟨x,hx,hxt⟩

theorem magnetic_spatial_norm_soft : Tendsto (fun P:Spatial => ‖P‖) magneticSoftMomenta (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun P:Spatial => ‖P‖) (𝓝 0) (𝓝 0) := by simpa only [norm_zero] using (continuous_norm.tendsto (0:Spatial))
    exact h.mono_left inf_le_left
  · apply (show magneticSoftMomenta ≤ ae volume from inf_le_right)
    change ∀ᵐ P:Spatial, 0 < ‖P‖
    rw [ae_iff]
    simp

/-- Expected inverse-fourth-moment control at the origin and the
pointwise inverse-fourth-power tail combine to give an integrable
majorant everywhere in three space dimensions. -/
theorem magnetic_poisson_envelope {D W r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hnear : W ≤ D) (hfar : 0 < r → W ≤ (r^4)⁻¹) :
    W ≤ 16*(1+D)*((1+r)^4)⁻¹ := by
  rw [←div_eq_mul_inv,le_div_iff₀ (by positivity)]
  by_cases h : r ≤ 1
  · have hpow : (1+r)^4 ≤ 16 := by
      calc (1+r)^4 ≤ (2:ℝ)^4 := pow_le_pow_left₀ (by positivity) (by linarith) _
           _ = _ := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hnear (show 0 ≤ (1+r)^4 by positivity),mul_le_mul_of_nonneg_left hpow hD]
  · have hr' : 0 < r := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+r) (show 1+r ≤ 2*r by linarith) 4
    have hdiv : ((r^4)⁻¹)*(1+r)^4 ≤ 16 := by
      rw [inv_mul_eq_div,div_le_iff₀ (by positivity)]
      simpa only [mul_pow,show (2:ℝ)^4=16 by norm_num] using hpow
    linarith [mul_le_mul_of_nonneg_right (hfar hr') (show 0 ≤ (1+r)^4 by positivity)]

theorem magnetic_covariance_integrable {F : Type*} [NormedAddCommGroup F] {c A D : ℝ} (hc : 0 < c)
    (G : Spatial → F) (hG : AEStronglyMeasurable G volume)
    (hbound : ∀ x, ‖G x‖ ≤ A*Real.exp (-c*‖x‖^2)+D*normalPhotonWeight 4 x) :
    Integrable G volume := by
  have hg : Integrable (fun x:Spatial => Real.exp (-c*‖x‖^2)) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b := (c:ℂ)) (by simpa using hc) 0 (0:Spatial)).norm
    simpa [Complex.norm_exp,Complex.mul_re,←Complex.ofReal_pow] using h
  exact ((hg.const_mul A).add ((normal_photon_weight_integrable volume
    (by rw [finrank_euclideanSpace_fin]; decide : Module.finrank ℝ Spatial < 4)).const_mul D)).mono' hG (Eventually.of_forall hbound)

/-- The Fourier transform of the spatial Gram kernel supplies a single
operator-norm constant for all momenta, including every transverse
orientation. The Fourier integrand is a complex scalar times an operator. -/
theorem magnetic_gram_row_bound {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (B : Spatial → H →L[ℂ] F) (G : Spatial → F →L[ℂ] F) (P : Spatial)
    (hGram : (B P).comp (B P).adjoint = ∫ x, Complex.exp (-Complex.I*(⟪P,x⟫:ℝ)) • G x) :
    ‖B P‖ ≤ Real.sqrt (∫ x, ‖G x‖) := by
  have hsq := ContinuousLinearMap.norm_adjoint_comp_self (B P).adjoint
  rw [ContinuousLinearMap.adjoint_adjoint,LinearIsometryEquiv.norm_map] at hsq
  have h := norm_integral_le_integral_norm (μ := volume) (fun x:Spatial => Complex.exp (-Complex.I*(⟪P,x⟫:ℝ)) • G x)
  simp only [←hGram,hsq,norm_smul,Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.I_re,Complex.neg_im,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,neg_zero,zero_mul,mul_zero,sub_zero,Real.exp_zero,one_mul] at h
  exact (Real.le_sqrt (norm_nonneg _) (integral_nonneg fun x => norm_nonneg (G x))).mpr ((pow_two _).trans_le h)

/-- The transverse magnetic curl has the same singular value on both
real polarizations. Its unit direction is the carrier spatial momentum,
distinct from the oriented geo-momentum pole unit. -/
theorem magnetic_curl_singular (μ : Measure ℝ≥0) {L : ℝ} (hL : 0 < L)
    (P : Spatial) (hP : P ≠ 0) (u : UnitVector Spatial) (hu : ⟪P,u.val⟫=0) :
    ‖(magneticWidthLaplace μ ‖P‖ / (Real.sqrt (2*‖P‖)*L)) •
        (WithLp.toLp 2 (crossProduct (WithLp.ofLp P) (WithLp.ofLp u.val)) : Spatial)‖ =
      magneticSingularValue μ L ‖P‖ := by
  have hp := norm_pos_iff.mpr hP
  have hπ : 0 < Real.sqrt ‖P‖ := Real.sqrt_pos_of_pos hp
  have hμ : 0 ≤ magneticWidthLaplace μ ‖P‖ := integral_nonneg fun _ => (Real.exp_pos _).le
  rw [norm_smul,Real.norm_of_nonneg (div_nonneg hμ (by positivity)),InnerProductGeometry.norm_ofLp_crossProduct,
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two P u.val).mp hu,Real.sin_pi_div_two,u.property,mul_one,mul_one,
    magneticSingularValue,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  field_simp [hL.ne',hπ.ne',(Real.sqrt_pos_of_pos (by norm_num : (0:ℝ)<2)).ne']
  nlinarith [congrArg (magneticWidthLaplace μ ‖P‖*·) (Real.sq_sqrt hp.le)]

/-- Essential spatial liminf of either normalized branch. The uniform
constant is calculated from the Fourier Gram kernel of its projected
row, rather than provided as a pointwise operator-norm bound. -/
theorem magnetic_pole_essential_speed {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {κ d L : ℝ} (hκ : 0 < κ) (hd : 0 < d) (hL : 0 < L)
    (G : Spatial → F →L[ℂ] F) (B : Spatial → H →L[ℂ] F) (E : Spatial → ℝ) (u w : Spatial → H)
    (hGram : ∀ᶠ P in magneticSoftMomenta, (B P).comp (B P).adjoint = ∫ x, Complex.exp (-Complex.I*(⟪P,x⟫:ℝ)) • G x)
    (hbare : ∀ᶠ P in magneticSoftMomenta, ‖B P (u P)‖ = magneticSingularValue μ L ‖P‖*‖u P‖)
    (hunit : ∀ᶠ P in magneticSoftMomenta, ‖u P‖^2+‖w P‖^2=1)
    (hform : ∀ᶠ P in magneticSoftMomenta, ‖P‖*‖u P‖^2+d*‖w P‖^2+κ*‖B P (u P+w P)‖^2 ≤ E P)
    (htrial : ∀ᶠ P in magneticSoftMomenta, E P ≤ (1+κ/(2*L^2))*‖P‖) :
    let K := Real.sqrt (∫ x, ‖G x‖)
    0 < κ*d/(2*L^2*(d+κ*K^2)) ∧ κ*d/(2*L^2*(d+κ*K^2)) ≤ liminf (fun P => E P/‖P‖-1) magneticSoftMomenta := by
  apply magnetic_low_pole_speed magneticSoftMomenta μ hκ hd hL _ E B u w magnetic_spatial_norm_soft _ hunit hform htrial
  filter_upwards [hGram,hbare] with P hg hb using ⟨magnetic_gram_row_bound B G P hg,hb⟩

end UV
