import UV.ContinuationChargeRigidity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Exact three-dimensional polar Tonelli step for the temporal-contact
obstruction on the fixed spatial sphere and a single locked sector plane. -/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace UV

abbrev TemporalRayDirection := sphere (0 : ChargeSpatialMomentum) 1

/-- The directions carry actual unit vectors in three spatial dimensions. -/
theorem temporalRayDirection_norm (n : TemporalRayDirection) : ‖(n : ChargeSpatialMomentum)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp n.2

/-- Polar decomposition against ordinary spatial Lebesgue volume.
The transverse sphere is the actual sphere measure of the manuscript. -/
theorem temporal_lintegral_spatial_polar (f : ChargeSpatialMomentum → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ k, f k) = ∫⁻ n : TemporalRayDirection,
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * f (r • (n : ChargeSpatialMomentum)))
      ∂(volume : Measure ChargeSpatialMomentum).toSphere := by
  let μ : Measure ChargeSpatialMomentum := volume
  let e := (homeomorphUnitSphereProd ChargeSpatialMomentum).toMeasurableEquiv
  have hp : MeasurePreserving e (μ.comap Subtype.val)
      (μ.toSphere.prod (Measure.volumeIoiPow 2)) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using
      μ.measurePreserving_homeomorphUnitSphereProd
  have h := (MeasurePreserving.symm e hp).lintegral_comp_emb e.symm.measurableEmbedding
    (fun x : ({(0 : ChargeSpatialMomentum)}ᶜ : Set ChargeSpatialMomentum) => f x.1)
  rw [lintegral_subtype_comap (measurableSet_singleton _).compl f, restrict_compl_singleton] at h
  change (∫⁻ k, f k ∂μ) = _
  rw [← h]
  have he : (fun p : TemporalRayDirection × Ioi (0 : ℝ) => f (e.symm p).1) =
      fun p => f (p.2.1 • p.1.1) := by
    funext p
    change f (((homeomorphUnitSphereProd ChargeSpatialMomentum).symm p).1) = _
    rw [homeomorphUnitSphereProd_symm_apply_coe]
  have hm : Measurable (fun p : TemporalRayDirection × Ioi (0 : ℝ) =>
      f (p.2.1 • p.1.1)) := hf.comp ((measurable_subtype_coe.comp measurable_snd).smul
        (measurable_subtype_coe.comp measurable_fst))
  rw [he, lintegral_prod _ hm.aemeasurable]
  congr 1
  funext n
  unfold Measure.volumeIoiPow
  have hw : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ 2)) :=
    (measurable_subtype_coe.pow_const _).ennreal_ofReal
  have hfn : Measurable (fun r : Ioi (0 : ℝ) => f (r.1 • n.1)) :=
    hf.comp (measurable_subtype_coe.smul_const _)
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hfn]
  exact lintegral_subtype_comap (measurableSet_Ioi (a := (0 : ℝ)))
    (fun r : ℝ => ENNReal.ofReal (r ^ 2) * f (r • n.1))

/-- The harmonic radial weight has infinite mass on every positive tail. -/
theorem temporal_lintegral_radial_inv_eq_top {R : ℝ} (hR : 0 < R) :
    (∫⁻ r in Ioi R, ENNReal.ofReal r⁻¹) = ∞ := by
  by_contra hn
  have hm : AEStronglyMeasurable (fun r : ℝ => r⁻¹) (volume.restrict (Ioi R)) :=
    measurable_id.inv.aestronglyMeasurable
  have hnonneg : ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioi R), 0 ≤ r⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact inv_nonneg.mpr (hR.trans hr).le
  have hfi : HasFiniteIntegral (fun r : ℝ => r⁻¹) (volume.restrict (Ioi R)) := by
    rw [hasFiniteIntegral_iff_enorm]
    have he : (fun r : ℝ => ‖r⁻¹‖ₑ) =ᵐ[volume.restrict (Ioi R)]
        fun r => ENNReal.ofReal r⁻¹ := hnonneg.mono fun r hr => by
      change ‖r⁻¹‖ₑ = ENNReal.ofReal r⁻¹
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hr]
    rw [lintegral_congr_ae he]
    exact lt_top_iff_ne_top.mpr hn
  have hi_inv : IntegrableOn (fun r : ℝ => r⁻¹) (Ioi R) volume := ⟨hm, hfi⟩
  have hi : IntegrableOn (fun r : ℝ => r ^ (-1 : ℝ)) (Ioi R) volume := by
    simpa only [Real.rpow_neg_one] using hi_inv
  exact (lt_irrefl (-1 : ℝ)) ((integrableOn_Ioi_rpow_iff hR).mp hi)

/-- The criterion on a ray follows from eventual at-most-cubic growth of the
positive energy scale on that ray. -/
theorem temporal_radial_budget_of_at_most_cubic (scale : ℝ → ℝ)
    (hscale : ∀ r > 0, 0 < scale r) {A R₀ : ℝ} (hA : 0 < A)
    (hbound : ∀ r > R₀, scale r ≤ A * r ^ 3) (R : ℝ) :
    (∫⁻ r in Ioi R, ENNReal.ofReal (r ^ 2 / scale r)) = ∞ := by
  let S := max 1 (max R₀ R)
  have hS : 0 < S := zero_lt_one.trans_le (le_max_left _ _)
  have hmono : Ioi S ⊆ Ioi R := Ioi_subset_Ioi (le_max_right _ _ |>.trans (le_max_right _ _))
  apply top_unique
  calc
    ∞ = ENNReal.ofReal (A⁻¹) * ∫⁻ r in Ioi S, ENNReal.ofReal r⁻¹ := by
      rw [temporal_lintegral_radial_inv_eq_top hS, ENNReal.mul_top
        ((ENNReal.ofReal_pos.mpr (inv_pos.mpr hA)).ne')]
    _ = ∫⁻ r in Ioi S, ENNReal.ofReal (A⁻¹) * ENNReal.ofReal r⁻¹ := by
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ r in Ioi S, ENNReal.ofReal (r ^ 2 / scale r) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr₀ : 0 < r := hS.trans hr
      have hr₁ : R₀ < r := (le_max_left R₀ R).trans_lt ((le_max_right 1 _).trans_lt hr)
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hA.le)]
      apply ENNReal.ofReal_le_ofReal
      calc
        A⁻¹ * r⁻¹ = r ^ 2 / (A * r ^ 3) := by field_simp
        _ ≤ r ^ 2 / scale r := div_le_div_of_nonneg_left (sq_nonneg _) (hscale r hr₀) (hbound r hr₁)
    _ ≤ _ := lintegral_mono_set hmono

/-- Positive-solid-angle radial divergence forces the full nonnegative
four-momentum integral to be infinite. The radial lower estimate is for the
complete shared frequency integral in its original momentum routing. -/
theorem temporal_contact_polar_divergence {Sector : Type*} (plane : ChargePlane Sector)
    (F : ChargePlane Sector → ChargeSpatialMomentum × ℝ → ℝ≥0∞) (hF : Measurable (F plane))
    (s : Set TemporalRayDirection) (hs : MeasurableSet s)
    (hsolid : (volume : Measure ChargeSpatialMomentum).toSphere s ≠ 0)
    (scale : TemporalRayDirection → ℝ → ℝ)
    (hbound : ∀ n ∈ s, ∃ c > (0 : ℝ), ∃ R > (0 : ℝ), ∀ r > R,
      ENNReal.ofReal (c / scale n r) ≤ ∫⁻ ω, F plane (r • (n : ChargeSpatialMomentum), ω))
    (hrad : ∀ n ∈ s, ∀ R > 0, (∫⁻ r in Ioi R, ENNReal.ofReal (r ^ 2 / scale n r)) = ∞) :
    (∫⁻ z, F plane z ∂((volume : Measure ChargeSpatialMomentum).prod volume)) = ∞ := by
  have hm : Measurable (fun k => ∫⁻ ω, F plane (k, ω)) := hF.lintegral_prod_right'
  rw [lintegral_prod _ hF.aemeasurable, temporal_lintegral_spatial_polar _ hm]
  have htop (n : TemporalRayDirection) (hn : n ∈ s) :
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
      ∫⁻ ω, F plane (r • (n : ChargeSpatialMomentum), ω)) = ∞ := by
    obtain ⟨c, hc, R, hR, hl⟩ := hbound n hn
    apply top_unique
    calc
      ∞ = ENNReal.ofReal c * ∫⁻ r in Ioi R, ENNReal.ofReal (r ^ 2 / scale n r) := by
        rw [hrad n hn R hR, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']
      _ = ∫⁻ r in Ioi R, ENNReal.ofReal c * ENNReal.ofReal (r ^ 2 / scale n r) := by
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ r in Ioi R, ENNReal.ofReal (r ^ 2) *
          ∫⁻ ω, F plane (r • (n : ChargeSpatialMomentum), ω) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        rw [← ENNReal.ofReal_mul hc.le,
          show c * (r ^ 2 / scale n r) = r ^ 2 * (c / scale n r) by ring,
          ENNReal.ofReal_mul (sq_nonneg _)]
        exact mul_le_mul_left' (hl r hr) _
      _ ≤ _ := lintegral_mono_set (Ioi_subset_Ioi hR.le)
  apply top_unique
  calc
    ∞ = ∫⁻ _ in s, (∞ : ℝ≥0∞) ∂(volume : Measure ChargeSpatialMomentum).toSphere := by
      rw [lintegral_const, Measure.restrict_apply_univ, ENNReal.top_mul hsolid]
    _ ≤ ∫⁻ n in s, (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
          (∫⁻ ω, F plane (r • (n : ChargeSpatialMomentum), ω)))
          ∂(volume : Measure ChargeSpatialMomentum).toSphere := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hs] with n hn
      exact (htop n hn).ge
    _ ≤ _ := setLIntegral_le_lintegral _ _

end UV
