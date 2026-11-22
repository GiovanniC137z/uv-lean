import UV.NextOpticalCone

/-! Actual radial Dirac pair integrand and the necessary harmonic-weight
tail of its mixing coefficient, derived by polar integration. -/

noncomputable section

open Filter Set MeasureTheory Metric Matrix
open scoped Topology Matrix ENNReal InnerProductSpace

namespace UV.NextOpticalRadial

/-- The radial spinor, assigning the unit mass axis at the isolated point
where spatial normalization is undefined. -/
def radialSpinor (u v : ℝ → ℝ) (k : ChargeSpatialMomentum) : DiracMomentum :=
  if hk : k = 0 then FurtherOptical.massAxis
  else spinCoefficients (u ‖k‖) (v ‖k‖) (radialUnit k hk)

theorem radialSpinor_sphere {u v : ℝ → ℝ} (hUnit : ∀ r, u r ^ 2 + v r ^ 2 = 1)
    (k : ChargeSpatialMomentum) : ‖radialSpinor u v k‖ ^ 2 = 1 := by
  unfold radialSpinor
  split
  · simp [FurtherOptical.massAxis]
  · rw [spinCoefficients_norm_sq, hUnit]

theorem radialSpinor_measurable {u v : ℝ → ℝ} (hu : Measurable u) (hv : Measurable v) :
    Measurable (radialSpinor u v) := by
  let g (k : ChargeSpatialMomentum) : DiracMomentum :=
    WithLp.toLp 2 (Fin.cons (u ‖k‖) (fun i : Fin 3 => (v ‖k‖ * ‖k‖⁻¹) * k i))
  have hg : Measurable g := by
    unfold g
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).measurable.comp
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hu.comp measurable_norm
    · exact ((hv.comp measurable_norm).mul measurable_norm.inv).mul
        (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable
  have he : radialSpinor u v = ({0} : Set ChargeSpatialMomentum).piecewise
      (fun _ => FurtherOptical.massAxis) g := by
    funext k
    by_cases hk : k=0
    · simp [radialSpinor, hk]
    · simp only [radialSpinor, dif_neg hk, Set.piecewise, mem_singleton_iff, if_neg hk]
      simp only [spinCoefficients, g, radialUnit, PiLp.smul_apply, smul_eq_mul, mul_assoc]
  rw [he]
  exact measurable_const.piecewise (measurableSet_singleton _) hg

theorem radialSpinor_ray (u v : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (n : SectorPlane.UnitVector ChargeSpatialMomentum) :
    radialSpinor u v (r • (n : ChargeSpatialMomentum)) = spinCoefficients (u r) (v r) n := by
  have hn : ‖r • (n : ChargeSpatialMomentum)‖ = r := by
    simp [norm_smul, Real.norm_of_nonneg hr.le, n.property]
  have hk : r • (n : ChargeSpatialMomentum) ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact hr)
  have he : radialUnit (r • (n : ChargeSpatialMomentum)) hk = n := by
    apply Subtype.ext
    change ‖r • (n : ChargeSpatialMomentum)‖⁻¹ • (r • (n : ChargeSpatialMomentum)) = n
    rw [hn, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [radialSpinor, dif_neg hk, he, hn]

def radialPairWeight (u v : ℝ → ℝ) (p k : ChargeSpatialMomentum) : ℝ :=
  ‖radialSpinor u v (k+p) - radialSpinor u v k‖ ^ 2 / 2

theorem radialPairWeight_eq_trace {u v : ℝ → ℝ} (hUnit : ∀ r, u r ^ 2 + v r ^ 2 = 1)
    (p k : ChargeSpatialMomentum) :
    radialPairWeight u v p k =
      (((1-FurtherOptical.projector (radialSpinor u v (k+p))) *
        FurtherOptical.projector (radialSpinor u v k)).trace).re := by
  rw [ContinuationBoostSpectrum.equal_rank_projection_overlap
    (FurtherOptical.projector_adjoint _) (FurtherOptical.projector_adjoint _)
    (FurtherOptical.projector_idempotent _ (radialSpinor_sphere hUnit (k+p)))
    (FurtherOptical.projector_idempotent _ (radialSpinor_sphere hUnit k))
    ((FurtherOptical.projector_trace _).trans (FurtherOptical.projector_trace _).symm),
    FurtherOptical.projector_difference_sq, radialPairWeight]

def radialEuclideanDensity (u v : ℝ → ℝ) (m ω : ℝ) (p k : ChargeSpatialMomentum) : ℝ :=
  let D := FurtherOptical.energy m k + FurtherOptical.energy m (k+p)
  radialPairWeight u v p k * (2*D/(ω^2+D^2))

theorem radialEuclideanDensity_nonneg (u v : ℝ → ℝ) (m ω : ℝ)
    (p k : ChargeSpatialMomentum) : 0 ≤ radialEuclideanDensity u v m ω p k := by
  unfold radialEuclideanDensity radialPairWeight FurtherOptical.energy
  positivity

theorem radialEuclideanDensity_measurable {u v : ℝ → ℝ} (hu : Measurable u) (hv : Measurable v)
    (m ω : ℝ) (p : ChargeSpatialMomentum) : Measurable (radialEuclideanDensity u v m ω p) := by
  have hS := radialSpinor_measurable hu hv
  have hD : Measurable (fun k : ChargeSpatialMomentum =>
      FurtherOptical.energy m k + FurtherOptical.energy m (k+p)) := by
    unfold FurtherOptical.energy
    fun_prop
  unfold radialEuclideanDensity radialPairWeight
  exact (((hS.comp (measurable_id.add measurable_const)).sub hS).norm.pow_const 2 |>.div_const 2).mul
    ((measurable_const.mul hD).div (measurable_const.add (hD.pow_const 2)))

/-- Integrability of the actual canonical radial density at one nonzero
transfer forces the harmonic-weight tail condition for the mixing law. -/
theorem radialEuclideanDensity_requires_mixing_tail {E : Type*} [Norm E]
    (diamond : SectorPlane.Plane E) (u v : SectorPlane.Plane E → ℝ → ℝ)
    (hu : Measurable (u diamond)) (hv : Measurable (v diamond))
    (hUnit : ∀ r, u diamond r ^ 2 + v diamond r ^ 2 = 1)
    {m ω R : ℝ} (hm : 0 ≤ m) (hR : 0 < R) (hRm : m ≤ R)
    (p : ChargeSpatialMomentum) (hp : p ≠ 0) (hRp : ‖p‖ ≤ R) (hRω : |ω| ≤ R)
    (hi : Integrable (radialEuclideanDensity (u diamond) (v diamond) m ω p)) :
    IntegrableOn (fun r => (v diamond r)^2 / r) (Ioi R) := by
  let F := radialEuclideanDensity (u diamond) (v diamond) m ω p
  let f := fun r => (v diamond r)^2/r
  let C := 3*‖p‖^2/416
  have hC : 0 < C := by dsimp [C]; exact div_pos (mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hp) 2)) (by norm_num)
  have hf : Measurable f := (hv.pow_const 2).div measurable_id
  have hF := radialEuclideanDensity_measurable hu hv m ω p
  have hpw : ∀ n ∈ exteriorCone p, ∀ r > R,
      ENNReal.ofReal C * ENNReal.ofReal (f r) ≤ ENNReal.ofReal (r^2) *
        ENNReal.ofReal (F (r • (n : ChargeSpatialMomentum))) := by
    intro n hn r hr
    let n₀ : SectorPlane.UnitVector ChargeSpatialMomentum :=
      ⟨n, temporalRayDirection_norm n⟩
    have hr₀ : 0 < r := hR.trans hr
    have hkn : ‖r • (n : ChargeSpatialMomentum)‖ = r := by
      simp [norm_smul, Real.norm_of_nonneg hr₀.le, temporalRayDirection_norm n]
    have hk : r • (n : ChargeSpatialMomentum)+p ≠ 0 := by
      by_contra! hz
      have hs := eq_neg_of_add_eq_zero_left hz
      have he : ‖r • (n : ChargeSpatialMomentum)‖ = ‖p‖ := by simpa only [norm_neg] using congrArg norm hs
      linarith
    have hlo := radial_pair_integrand_cone_lower diamond u v hUnit n₀ p hr₀ hm
      (hRm.trans hr.le) (hRp.trans_lt hr) (hRω.trans hr.le) hn.le hk
    have hF_eq : F (r • (n : ChargeSpatialMomentum)) =
        (((1-FurtherOptical.projector (spinCoefficients (u diamond ‖r • (n : ChargeSpatialMomentum)+p‖)
          (v diamond ‖r • (n : ChargeSpatialMomentum)+p‖)
          (radialUnit (r • (n : ChargeSpatialMomentum)+p) hk))) *
          FurtherOptical.projector (spinCoefficients (u diamond r) (v diamond r) n₀)).trace).re *
        (2 * (FurtherOptical.energy m (r • (n : ChargeSpatialMomentum)) +
          FurtherOptical.energy m (r • (n : ChargeSpatialMomentum)+p)) /
          (ω^2+(FurtherOptical.energy m (r • (n : ChargeSpatialMomentum)) +
            FurtherOptical.energy m (r • (n : ChargeSpatialMomentum)+p))^2)) := by
      change radialEuclideanDensity (u diamond) (v diamond) m ω p (r • (n₀ : ChargeSpatialMomentum)) = _
      unfold radialEuclideanDensity
      dsimp only
      rw [radialPairWeight_eq_trace hUnit, radialSpinor_ray _ _ hr₀, radialSpinor, dif_neg hk]
    rw [← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul (sq_nonneg r)]
    apply ENNReal.ofReal_le_ofReal
    have he : C * f r = r^2 * (C * (v diamond r)^2 / r^3) := by
      dsimp [f]
      field_simp
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
    rw [hF_eq]
    exact hlo
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have he : (fun r => ‖f r‖ₑ) =ᵐ[volume.restrict (Ioi R)] fun r => ENNReal.ofReal (f r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hp : 0 ≤ f r := div_nonneg (sq_nonneg _) (hR.trans hr).le
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hp]
  rw [lintegral_congr_ae he]
  apply lt_top_iff_ne_top.mpr
  intro htop
  have hInf : ∀ n ∈ exteriorCone p, (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^2) *
      ENNReal.ofReal (F (r • (n : ChargeSpatialMomentum)))) = ∞ := by
    intro n hn
    apply top_unique
    calc
      ∞ = ENNReal.ofReal C * ∫⁻ r in Ioi R, ENNReal.ofReal (f r) := by
        rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC).ne']
      _ = ∫⁻ r in Ioi R, ENNReal.ofReal C * ENNReal.ofReal (f r) := by
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ r in Ioi R, ENNReal.ofReal (r^2) * ENNReal.ofReal (F (r • (n : ChargeSpatialMomentum))) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact hpw n hn r hr
      _ ≤ _ := lintegral_mono_set (Ioi_subset_Ioi hR.le)
  have hFull : (∫⁻ k, ENNReal.ofReal (F k)) = ∞ := by
    rw [temporal_lintegral_spatial_polar _ hF.ennreal_ofReal]
    apply top_unique
    calc
      ∞ = ∫⁻ _ in exteriorCone p, (∞ : ℝ≥0∞) ∂(volume : Measure ChargeSpatialMomentum).toSphere := by
        rw [lintegral_const, Measure.restrict_apply_univ, ENNReal.top_mul (exteriorCone_positive hp)]
      _ ≤ ∫⁻ n in exteriorCone p, (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^2) *
            ENNReal.ofReal (F (r • (n : ChargeSpatialMomentum))))
            ∂(volume : Measure ChargeSpatialMomentum).toSphere := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (exteriorCone_measurable p)] with n hn
        exact (hInf n hn).ge
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have hFinite := hi.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hFinite
  have hEq : (fun k => ‖F k‖ₑ) = fun k => ENNReal.ofReal (F k) := by
    funext k
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (radialEuclideanDensity_nonneg _ _ _ _ _ _)]
  change (∫⁻ k, ‖F k‖ₑ) < ∞ at hFinite
  rw [hEq, hFull] at hFinite
  exact lt_irrefl _ hFinite

end UV.NextOpticalRadial
