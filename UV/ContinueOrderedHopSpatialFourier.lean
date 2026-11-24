import UV.ContinueOrderedHopFourierClosure

/-! Spatial closure for the actual normalized Gaussian hopping and complete
straight-link marks, at fixed plane polarizations. A zero-frequency spatial
mode on an extra slot differentiates the same heat hop. -/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology

namespace UV.SectorPlane

theorem orderedHop_zero_spatial_mark (u : UnitVector Spatial) (z : Spatial) :
    twoBandLineMode u 0 z = Complex.I*(⟪z,u.val⟫:ℝ) := by
  simp [twoBandLineMode,twoBandDisplacementWave,Real.volume_real_Icc_of_le zero_le_one]

private theorem line_continuous (u : UnitVector Spatial) (q : Spatial) : Continuous (twoBandLineMode u q) := by
  have he : twoBandLineMode u q = fun z => ∫ s in (0:ℝ)..1,
      Complex.I*(⟪z,u.val⟫:ℝ)*twoBandDisplacementWave q (s • z) := by
    funext z
    rw [twoBandLineMode,intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]
  rw [he]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry twoBandDisplacementWave
  fun_prop

private theorem line_norm (u : UnitVector Spatial) (q z : Spatial) : ‖twoBandLineMode u q z‖ ≤ ‖z‖ := by
  apply (norm_integral_le_integral_norm _).trans
  have he (s : ℝ) : ‖Complex.I*(⟪z,u.val⟫:ℝ)*twoBandDisplacementWave q (s • z)‖ = |⟪z,u.val⟫| := by
    rw [norm_mul,twoBand_displacement_wave_norm,mul_one,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  simp_rw [he]
  rw [setIntegral_const,Real.volume_real_Icc_of_le zero_le_one,sub_zero,one_smul]
  simpa only [u.property,mul_one] using abs_real_inner_le_norm z u.val

private theorem spatial_position_continuous (g σ : ℝ) {r : ℕ} (u : Fin r → UnitVector Spatial)
    (b : Spatial) (q : Fin r → Spatial) : Continuous (twoBandFourierLinkKernel g σ u b q 0) := by
  unfold twoBandFourierLinkKernel
  simp only [twoBand_link_variations_eval,Complex.exp_zero,mul_one,List.prod_ofFn]
  refine Continuous.mul ?_ (continuous_finset_prod _ fun j _ => line_continuous _ _)
  unfold twoBandDisplacementWave twoBandDisplacementDensity
  fun_prop

private theorem spatial_position_bound (g : ℝ) {σ : ℝ} (hσ : 0 < σ) {r : ℕ}
    (u : Fin r → UnitVector Spatial) (b : Spatial) (q : Fin r → Spatial) :
    ∃ C : ℝ, ∀ z, ‖twoBandFourierLinkKernel g σ u b q 0 z‖ ≤ C := by
  let η := min 1 (orderedHopPrecision σ)
  have hη : 0 < η := lt_min zero_lt_one (orderedHop_precision_pos hσ)
  refine ⟨|g| * (orderedHopMomentConstant η r * orderedHopTiltPeak σ η),?_⟩
  intro z
  have hd : 0 ≤ twoBandDisplacementDensity σ z := by unfold twoBandDisplacementDensity; positivity
  have hp := (orderedHop_tilt_le_majorant hσ hη.le 1 (0,z)).trans
    (orderedHop_tilt_majorant_le_peak hσ (min_le_left _ _) (min_le_right _ _) _)
  simp only [orderedHopDensity,orderedHopLength,abs_zero,mul_zero,Real.exp_zero,one_mul,zero_add] at hp
  have hr := (pow_le_pow_left₀ (norm_nonneg z) (show ‖z‖ ≤ 1+‖z‖ by linarith) r).trans
    (orderedHop_nonneg_power_bound hη (norm_nonneg z) r)
  have hC : 0 ≤ orderedHopMomentConstant η r := by unfold orderedHopMomentConstant; positivity
  unfold twoBandFourierLinkKernel
  simp only [twoBand_link_variations_eval,Complex.exp_zero,mul_one,List.prod_ofFn,norm_mul,twoBand_displacement_wave_norm,
    one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd,norm_prod]
  have hP : (∏ j, ‖twoBandLineMode (u j) (q j) z‖) ≤ ‖z‖^r := by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      Finset.prod_le_prod (s := Finset.univ) (fun _ _ => norm_nonneg _) (fun j _ => line_norm (u j) (q j) z)
  calc
    _ ≤ |g| * twoBandDisplacementDensity σ z * (orderedHopMomentConstant η r * Real.exp (η*‖z‖)) :=
      mul_le_mul_of_nonneg_left (hP.trans hr) (mul_nonneg (abs_nonneg _) hd)
    _ = |g| * (orderedHopMomentConstant η r * (twoBandDisplacementDensity σ z * Real.exp (η*‖z‖))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hC) (abs_nonneg _)

theorem orderedHop_spatial_symbol (g : ℝ) {σ : ℝ} (hσ : 0 < σ) {r : ℕ} (u : Fin r → UnitVector Spatial)
    (b : Spatial) (q : Fin r → Spatial) (k : Spatial) :
    orderedHopFourier (twoBandFourierLinkKernel g σ u b q 0) k = (twoBandGaussianWilsonMark g σ u b q k : ℂ) := by
  rw [←twoBand_fourier_link_eq_gaussian_wilson_mark g hσ]
  apply integral_congr_ae (ae_of_all _ (fun z => ?_))
  have hw : orderedHopWave k z * twoBandDisplacementWave b z = twoBandDisplacementWave (k+b) z := by
    unfold orderedHopWave twoBandDisplacementWave
    rw [inner_add_right,Complex.ofReal_add,add_mul,Complex.exp_add]
  unfold twoBandFourierLinkKernel
  rw [zero_add,← hw]; ring

/-- Keep the independent three-momentum inside the Fourier representation
of the spatial closure, with the same direction and momentum for every
straight-link placement. Arbitrarily many marks can share one hop. -/
theorem orderedHop_spatial_closure {n : ℕ} (g : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (r : Fin (n+1) → ℕ) (u : ∀ i, Fin (r i) → UnitVector Spatial)
    (b : Fin (n+1) → Spatial) (q : ∀ i, Fin (r i) → Spatial) :
    ((2*Real.pi)^3)⁻¹ • (∫ k : Spatial, ∏ i, (twoBandGaussianWilsonMark g σ (u i) (b i) (q i) k : ℂ)) =
      ∫ z : Fin n → Spatial, ∏ i, twoBandFourierLinkKernel g σ (u i) (b i) (q i) 0 (orderedHopSpatialIncrements 0 z i) := by
  let f := fun i => twoBandFourierLinkKernel g σ (u i) (b i) (q i) 0
  have hI (i) := twoBand_fourier_link_kernel_integrable g hσ (u i) (b i) (q i) 0
  obtain ⟨C,hC⟩ := spatial_position_bound g hσ (u 0) (b 0) (q 0)
  have hsym (i) := orderedHop_spatial_symbol g hσ (u i) (b i) (q i)
  have hAbs : Integrable (fun k => ∏ i, (twoBandGaussianWilsonMark g σ (u i) (b i) (q i) k : ℂ)) := by
    simp_rw [←Complex.ofReal_prod]
    exact (twoBand_wilson_multipliers_integrable g hσ r u b q).ofReal
  have hCont (i) := spatial_position_continuous g σ (u i) (b i) (q i)
  have h := orderedHop_fourier_return (f := f 0) (h := fun i : Fin n => f i.succ)
    (hCont 0).measurable (fun i => (hCont i.succ).measurable) (hI 0) (fun i => hI i.succ) hC
    (ae_of_all _ fun _ => (hCont 0).continuousAt) (by
      simpa only [Fin.prod_univ_succ,f,hsym] using hAbs)
  simpa only [orderedHopClosure,finrank_euclideanSpace,Fintype.card_fin,f,hsym,Fin.prod_univ_succ,
    orderedHopSpatialIncrements,Fin.cons_zero,Fin.cons_succ] using h

end UV.SectorPlane
