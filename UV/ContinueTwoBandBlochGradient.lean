import UV.ContinueTwoBandPositiveCoulomb
import UV.ContinueTwoBandGaussianMarks
import UV.ContinueRelativeSpectralMark
import Mathlib.Probability.Moments.Variance

/-! The Hilbert--Schmidt gradient of the actual unit Pauli vector. Its
translation estimate gives the manuscript's spatial soft factor with 1/4. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace

namespace UV.SectorPlane

def spatialGradientSquare (f : Spatial → Spatial) (k : Spatial) : ℝ :=
  ∑ i : Fin 3, ‖fderiv ℝ f k (spectralMarkSpatialUnit i).val‖^2

private theorem spatial_gradient_nonneg (f : Spatial → Spatial) (x : Spatial) : 0 ≤ spatialGradientSquare f x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem continuous_spatial_gradient_square {f : Spatial → Spatial} (hf : ContDiff ℝ 1 f) :
    Continuous (spatialGradientSquare f) := by
  apply continuous_finset_sum
  intro i _
  exact ((hf.continuous_fderiv le_rfl).clm_apply continuous_const).norm.pow 2

private theorem spatial_direction_gradient_square (f : Spatial → Spatial) (k p : Spatial) :
    ‖fderiv ℝ f k p‖^2 ≤ ‖p‖^2 * spatialGradientSquare f k := by
  let L := fderiv ℝ f k
  have hp : ∑ i : Fin 3, (p i) • (spectralMarkSpatialUnit i).val = p := by
    ext i
    change (EuclideanSpace.proj i : Spatial →L[ℝ] ℝ) (∑ j : Fin 3, (p j) • (spectralMarkSpatialUnit j).val) = _
    rw [map_sum]
    simp [spectralMarkSpatialUnit,EuclideanSpace.single_apply]
  have hN : ‖L p‖ ≤ ∑ i : Fin 3, |p i| * ‖L (spectralMarkSpatialUnit i).val‖ := by
    conv_lhs => rw [← hp,map_sum]
    simpa only [map_smul,norm_smul,Real.norm_eq_abs] using
      (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun i => L ((p i) • (spectralMarkSpatialUnit i).val)))
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) (fun i => |p i|)
    (fun i => ‖L (spectralMarkSpatialUnit i).val‖)
  apply (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans
  simpa only [EuclideanSpace.norm_sq_eq p,Real.norm_eq_abs,spatialGradientSquare,L] using h

private def unitSegmentMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

private instance : IsProbabilityMeasure unitSegmentMeasure := ⟨by
  norm_num [unitSegmentMeasure,Measure.restrict_apply_univ,Real.volume_Ioc]⟩

private theorem continuous_segment_integrable {F : Type*} [NormedAddCommGroup F] {f : ℝ → F}
    (hf : Continuous f) : Integrable f unitSegmentMeasure :=
  hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem spatial_segment_bound {f : Spatial → Spatial} (hf : ContDiff ℝ 1 f) (k p : Spatial) :
    ‖f (k+p) - f k‖^2 ≤ ‖p‖^2 * ∫ t, spatialGradientSquare f (k+t • p) ∂unitSegmentMeasure := by
  let u := fun t : ℝ => fderiv ℝ f (k+t • p) p
  have hT : Continuous (fun t : ℝ => k+t • p) := by fun_prop
  have hu : Continuous u := ((hf.continuous_fderiv le_rfl).comp hT).clm_apply continuous_const
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => f (k+s • p)) (u t) t := by
    have hA : HasDerivAt (fun s : ℝ => k+s • p) p t := by
      simpa only [one_smul] using (hasDerivAt_id t).smul_const p |>.const_add k
    exact ((hf.differentiable le_rfl).differentiableAt.hasFDerivAt).comp_hasDerivAt t hA
  have hU : (∫ t, u t ∂unitSegmentMeasure) = f (k+p)-f k := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
      (fun t _ => hd t) (hu.intervalIntegrable _ _)
    simpa only [unitSegmentMeasure,intervalIntegral.integral_of_le zero_le_one,zero_smul,
      one_smul,add_zero] using h
  have hs := continuous_segment_integrable (hu.norm.pow 2)
  have hL := (memLp_two_iff_integrable_sq (μ := unitSegmentMeasure) hu.norm.aestronglyMeasurable).2 hs
  have hV := variance_nonneg (fun t => ‖u t‖) unitSegmentMeasure
  rw [variance_eq_sub hL] at hV
  rw [← hU, ← integral_const_mul]
  calc
    _ ≤ (∫ t, ‖u t‖ ∂unitSegmentMeasure)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2
    _ ≤ ∫ t, ‖u t‖^2 ∂unitSegmentMeasure := sub_nonneg.mp hV
    _ ≤ _ := integral_mono hs
      ((continuous_segment_integrable ((continuous_spatial_gradient_square hf).comp hT)).const_mul _)
      (fun t => spatial_direction_gradient_square f _ _)

private theorem spatial_translation_energy {f : Spatial → Spatial} (hf : ContDiff ℝ 1 f)
    (hG : Integrable (spatialGradientSquare f)) (p : Spatial) :
    Integrable (fun k => ‖f (k+p)-f k‖^2) ∧
    (∫ k, ‖f (k+p)-f k‖^2) ≤ ‖p‖^2 * ∫ k, spatialGradientSquare f k := by
  let G := spatialGradientSquare f
  let D := fun (t : ℝ) (k : Spatial) => G (k+t • p)
  have hm : Continuous (Function.uncurry D) := (continuous_spatial_gradient_square hf).comp
    (show Continuous (fun z : ℝ × Spatial => z.2+z.1 • p) by fun_prop)
  have hshift (t : ℝ) : Integrable (D t) := (measurePreserving_add_right volume (t • p)).integrable_comp_of_integrable hG
  have heq (t : ℝ) : (∫ k, D t k) = ∫ k, G k := integral_add_right_eq_self G _
  have hi : Integrable (Function.uncurry D) (unitSegmentMeasure.prod volume) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hshift, ?_⟩
    change Integrable (fun t => ∫ k, ‖D t k‖) unitSegmentMeasure
    have hn (t k) : ‖D t k‖ = D t k := Real.norm_of_nonneg (spatial_gradient_nonneg _ _)
    simp_rw [hn,heq]
    exact integrable_const _
  have hM := hi.integral_prod_right.const_mul (‖p‖^2)
  have hDiff : Continuous (fun k => ‖f (k+p)-f k‖^2) := ((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous).norm.pow 2
  have hB := fun k => spatial_segment_bound hf k p
  have hI := hM.mono' hDiff.aestronglyMeasurable (ae_of_all _ (fun k =>
    (Real.norm_of_nonneg (sq_nonneg _)).le.trans (hB k)))
  refine ⟨hI,(integral_mono hI hM hB).trans_eq ?_⟩
  rw [integral_const_mul]
  congr 1
  have hswap := integral_integral_swap hi
  simpa only [Function.uncurry_apply_pair, heq, integral_const,measureReal_univ_eq_one,one_smul] using hswap.symm

/-- The actual Pauli direction of the Gaussian two-band Hamiltonian. -/
def twoBandSpatialBloch (m g σ : ℝ) (k : Spatial) : Spatial :=
  twoBandBloch m (twoBandSpatialHop g σ k)

private theorem twoBand_bloch_smooth {m : ℝ} (hm : 0 < m) : ContDiff ℝ 1 (twoBandBloch m) := by
  have hgap : ContDiff ℝ 1 (twoBandGap m) := by
    unfold twoBandGap
    exact (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun v => (by positivity : 0 < m^2+v^2).ne')
  have hv : ContDiff ℝ 1 (fun v : ℝ => v/twoBandGap m v) :=
    contDiff_id.div hgap (fun v => (twoBand_gap_pos hm v).ne')
  have hz : ContDiff ℝ 1 (fun v : ℝ => m/twoBandGap m v) :=
    contDiff_const.div hgap (fun v => (twoBand_gap_pos hm v).ne')
  have he : twoBandBloch m = fun v : ℝ =>
      (v/twoBandGap m v) • (spectralMarkSpatialUnit 0).val + (m/twoBandGap m v) • (spectralMarkSpatialUnit 2).val := by
    funext v
    ext j
    fin_cases j <;> simp [twoBandBloch,spectralMarkSpatialUnit,EuclideanSpace.single_apply]
  rw [he]
  exact (hv.smul contDiff_const).add (hz.smul contDiff_const)

private theorem twoBand_bloch_lipschitz {m : ℝ} (hm : 0 < m) :
    LipschitzWith ⟨m⁻¹,inv_nonneg.mpr hm.le⟩ (twoBandBloch m) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  change dist (twoBandBloch m v) (twoBandBloch m w) ≤ m⁻¹ * dist v w
  rw [dist_eq_norm,Real.dist_eq]
  have h := twoBand_transition_upper hm w v
  rw [twoBand_transition_distance hm] at h
  change ‖twoBandBloch m v-twoBandBloch m w‖^2/4 ≤ (w-v)^2/(4*m^2) at h
  have hsq : ‖twoBandBloch m v-twoBandBloch m w‖^2 ≤ (m⁻¹*|v-w|)^2 := by
    rw [mul_pow,inv_pow,sq_abs,inv_mul_eq_div]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)] at h
    apply (le_div_iff₀ (sq_pos_of_pos hm)).mpr
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hm.le) (abs_nonneg _))).mp hsq

/-- The 3 by 3 Jacobian of the actual unit vector has square-integrable
entries for every real hopping amplitude at positive mass and heat width. -/
theorem twoBand_spatial_bloch_gradient_integrable {m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (g : ℝ) :
    Integrable (spatialGradientSquare (twoBandSpatialBloch m g σ)) := by
  let n := twoBandSpatialBloch m g σ
  let t := twoBandSpatialHop g σ
  have ht : ContDiff ℝ 1 t := (twoBand_gaussian_hop_smooth g σ).of_le (by exact_mod_cast le_top)
  have hb := twoBand_bloch_smooth hm
  have hn : ContDiff ℝ 1 n := hb.comp ht
  obtain ⟨C,hC,hEnv⟩ := twoBand_gaussian_mark_envelope g hσ 1
  have hG : Integrable (fun k : Spatial => Real.exp (-(σ^2*‖k‖^2))) := by
    simpa only [twoBandSpatialHop,one_mul,abs_of_pos (Real.exp_pos _)] using
      twoBand_spatial_hop_integrable 1 hσ
  have hN (k : Spatial) : 0 ≤ spatialGradientSquare n k := spatial_gradient_nonneg _ _
  apply (hG.const_mul (3*(m⁻¹*C)^2)).mono' (continuous_spatial_gradient_square hn).aestronglyMeasurable
  filter_upwards with k
  rw [Real.norm_of_nonneg (hN k)]
  have he (j : Fin 3) : ‖fderiv ℝ n k (spectralMarkSpatialUnit j).val‖^2 ≤
      (m⁻¹*C)^2 * Real.exp (-(σ^2*‖k‖^2)) := by
    have hc := fderiv_comp k ((hb.differentiable le_rfl).differentiableAt (x := t k))
      ((ht.differentiable le_rfl).differentiableAt (x := k))
    have hLip : ‖fderiv ℝ (twoBandBloch m) (t k)‖ ≤ m⁻¹ :=
      norm_fderiv_le_of_lipschitz ℝ (twoBand_bloch_lipschitz hm)
    have hT := hEnv (fun _ => spectralMarkSpatialUnit j) k
    rw [iteratedFDeriv_one_apply] at hT
    have hN' : ‖fderiv ℝ n k (spectralMarkSpatialUnit j).val‖ ≤
        m⁻¹*(C*Real.exp (-(σ^2/2*‖k‖^2))) := by
      change ‖fderiv ℝ (twoBandBloch m ∘ t) k (spectralMarkSpatialUnit j).val‖ ≤ _
      rw [hc,ContinuousLinearMap.comp_apply]
      exact ((fderiv ℝ (twoBandBloch m) (t k)).le_opNorm _).trans
        (mul_le_mul hLip hT (norm_nonneg _) (inv_nonneg.mpr hm.le))
    apply (pow_le_pow_left₀ (norm_nonneg _) hN' 2).trans_eq
    rw [←mul_assoc,mul_pow,←Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  apply (Finset.sum_le_sum (fun j _ => he j)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Literal translated unit-vector bound for the occupied-to-empty transition
weight, with the Lebesgue Hilbert--Schmidt gradient and the factor 1/4. -/
theorem twoBand_spatial_weight_gradient {m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (g : ℝ) (p : Spatial) :
    (∫ k, twoBandSpatialWeight m g σ k p) ≤
      ‖p‖^2 * (∫ k, spatialGradientSquare (twoBandSpatialBloch m g σ) k) / 4 := by
  have hn : ContDiff ℝ 1 (twoBandSpatialBloch m g σ) := (twoBand_bloch_smooth hm).comp
    ((twoBand_gaussian_hop_smooth g σ).of_le (by exact_mod_cast le_top))
  have h := spatial_translation_energy hn (twoBand_spatial_bloch_gradient_integrable hm hσ g) p
  have he (k : Spatial) : twoBandSpatialWeight m g σ k p =
      ‖twoBandSpatialBloch m g σ (k+p)-twoBandSpatialBloch m g σ k‖^2/4 := twoBand_transition_distance hm _ _
  simp only [he,integral_div]
  exact div_le_div_of_nonneg_right h.2 (by norm_num)

end UV.SectorPlane
