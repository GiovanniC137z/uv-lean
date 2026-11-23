import UV.ContinuePairBoostPhaseSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Invariant-mass disintegration of the moving two-particle measure.
The spherical coefficient is for ordinary Lebesgue measure, prior to
the diagram's separate Fourier normalization. -/

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace UV.PairCurvature

private theorem pair_radial_lintegral (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ k : ChargeSpatialMomentum, f ‖k‖) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (4 * π * r^2) * f r := by
  let μ : Measure ChargeSpatialMomentum := volume
  let e := homeomorphUnitSphereProd ChargeSpatialMomentum
  have hSphere : μ.toSphere univ = ENNReal.ofReal (4 * π) := by
    rw [μ.toSphere_apply_univ]
    have hdim : Module.finrank ℝ ChargeSpatialMomentum = 3 := by simp [ChargeSpatialMomentum]
    change (Module.finrank ℝ ChargeSpatialMomentum : ℝ≥0∞) * μ (Metric.ball 0 1) = _
    rw [hdim, show μ (Metric.ball 0 1) = ENNReal.ofReal (π * 4 / 3) by simp [μ, ChargeSpatialMomentum]]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (3 : ℕ))]
    congr 1
    ring
  have hpolar := μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
    e.measurableEmbedding (fun q => f q.2)
  simp only [homeomorphUnitSphereProd_apply_snd_coe] at hpolar
  have hdim : Module.finrank ℝ ChargeSpatialMomentum - 1 = 2 := by simp [ChargeSpatialMomentum]
  have hfρ : Measurable (fun r : Ioi (0 : ℝ) => f r.1) := hf.comp measurable_subtype_coe
  have hwρ : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1^2)) :=
    (measurable_subtype_coe.pow_const _).ennreal_ofReal
  calc
    (∫⁻ k : ChargeSpatialMomentum, f ‖k‖) =
        ∫⁻ k : ({0}ᶜ : Set ChargeSpatialMomentum), f ‖k.1‖ ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton (0 : ChargeSpatialMomentum)).compl
        (fun k : ChargeSpatialMomentum => f ‖k‖), restrict_compl_singleton]
    _ = ∫⁻ q : Metric.sphere (0 : ChargeSpatialMomentum) 1 × Ioi (0 : ℝ),
          f q.2 ∂μ.toSphere.prod (Measure.volumeIoiPow 2) := by
      simpa only [e, hdim] using hpolar
    _ = ENNReal.ofReal (4 * π) * ∫⁻ r : Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow 2 := by
      rw [lintegral_prod (fun q : Metric.sphere (0 : ChargeSpatialMomentum) 1 × Ioi (0 : ℝ) => f q.2)
        (hfρ.comp measurable_snd).aemeasurable]
      let c := ∫⁻ r : Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow 2
      change (∫⁻ _ : Metric.sphere (0 : ChargeSpatialMomentum) 1, c ∂μ.toSphere) = ENNReal.ofReal (4*π)*c
      rw [lintegral_const, hSphere, mul_comm]
    _ = _ := by
      rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ hwρ hfρ]
      change ENNReal.ofReal (4*π) *
        (∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.1^2) * f r.1 ∂(volume : Measure ℝ).comap Subtype.val) = _
      rw [← lintegral_const_mul _ (hwρ.mul hfρ)]
      simp_rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * π)]
      exact lintegral_subtype_comap measurableSet_Ioi (fun r => ENNReal.ofReal (4 * π * r^2) * f r)

private theorem pair_energy_sq_eq_rest (b : PairSpatialFrame) {m : ℝ} (hm : 0 < m) (y : ℝ)
    (v : PairTransverseCoordinates) :
    m^2 + ‖pairSpatialVector b y v‖^2 = restEnergySq (pairTransverseEnergySq m v) y := by
  have h := congrArg (· ^ 2) (pair_axis_energy b m 0 y v).1
  simp only [FurtherOptical.energy_sq] at h
  simpa only [oneParticleAxialEnergy, sq_sqrt (restEnergySq_pos (pairTransverseEnergySq_pos hm v) y).le]
    using h

private theorem rest_mass_phase_space (b : PairSpatialFrame) {m : ℝ} (hm : 0 < m)
    (p : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ k : ChargeSpatialMomentum,
        F (invariantMassSq m (p • b 0) k) *
          ENNReal.ofReal ((4 * FurtherOptical.energy m k * FurtherOptical.energy m (p • b 0-k))⁻¹)) =
      ∫⁻ k : ChargeSpatialMomentum, F (4 * (m^2 + ‖k‖^2)) *
        ENNReal.ofReal ((2 * sqrt (m^2 + ‖k‖^2) * sqrt (p^2 + 4 * (m^2 + ‖k‖^2)))⁻¹) := by
  let g := fun k : ChargeSpatialMomentum => F (4 * (m^2 + ‖k‖^2)) *
    ENNReal.ofReal ((2 * sqrt (m^2 + ‖k‖^2) * sqrt (p^2 + 4 * (m^2 + ‖k‖^2)))⁻¹)
  have hg : Measurable g := by unfold g; fun_prop
  have hf : Measurable (fun k => F (invariantMassSq m (p • b 0) k)) := by
    unfold invariantMassSq relativeEnergy FurtherOptical.energy
    fun_prop
  rw [pair_boosted_spatial_phase_space b hm p _ hf]
  let e := pairSpatialCoordinates b
  have he := (pairSpatialCoordinates_preserving b).symm e
  change _ = ∫⁻ k, g k
  rw [← he.lintegral_comp_emb e.symm.measurableEmbedding g]
  change _ = ∫⁻ q : ℝ × PairTransverseCoordinates, (g ∘ e.symm) q
    ∂(volume : Measure ℝ).prod (volume : Measure PairTransverseCoordinates)
  rw [lintegral_prod_symm' _ (hg.comp e.symm.measurable)]
  apply lintegral_congr
  intro v
  apply lintegral_congr
  intro y
  rw [pair_boosted_invariant_mass b hm]
  change _ = g ((pairSpatialCoordinates b).symm (y,v))
  rw [pairSpatialVector_eq]
  unfold g
  rw [pair_energy_sq_eq_rest b hm]
  let R := restEnergySq (pairTransverseEnergySq m v) y
  let γ := longitudinalLorentzFactor (pairTransverseEnergySq m v) p y
  have hR : 0 < R := restEnergySq_pos (pairTransverseEnergySq_pos hm v) y
  have hγ : 0 < γ := zero_lt_one.trans_le (longitudinalLorentzFactor_ge_one (pairTransverseEnergySq_pos hm v) p y)
  have hγsq : γ^2 = 1+p^2/(4*R) := sq_sqrt (by positivity)
  have hd : sqrt (p^2+4*R) = 2*γ*sqrt R := by
    have he : p^2+4*R = (2*γ*sqrt R)^2 := by
      rw [mul_pow,mul_pow,hγsq,sq_sqrt hR.le]
      field_simp [hR.ne']
      ring
    rw [he,sqrt_sq (by positivity)]
  congr 2
  change (4*γ*R)⁻¹ = (2*sqrt R*sqrt (p^2+4*R))⁻¹
  rw [hd]
  congr 1
  linear_combination -4*γ*sq_sqrt hR.le

/-- Against every nonnegative measurable invariant-mass test, the
spatial pair measure has the exact moving-frame threshold density. -/
theorem pair_invariant_mass_disintegration (b : PairSpatialFrame) {m : ℝ} (hm : 0 < m)
    (p : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ k : ChargeSpatialMomentum,
        F (invariantMassSq m (p • b 0) k) *
          ENNReal.ofReal ((4 * FurtherOptical.energy m k * FurtherOptical.energy m (p • b 0-k))⁻¹)) =
      ∫⁻ s in Ioi (4 * m^2),
        F s * ENNReal.ofReal (π / (4 * sqrt (p^2+s)) * sqrt (1-4*m^2/s)) := by
  rw [rest_mass_phase_space b hm p F hF]
  let f := fun r : ℝ => F (4 * (m^2 + r^2)) *
    ENNReal.ofReal ((2 * sqrt (m^2 + r^2) * sqrt (p^2 + 4 * (m^2 + r^2)))⁻¹)
  change (∫⁻ k : ChargeSpatialMomentum, f ‖k‖) = _
  rw [pair_radial_lintegral f (by unfold f; fun_prop)]
  let h := fun r : ℝ => 4 * (m^2 + r^2)
  have hD (x : ℝ) (_hx : x ∈ Ioi (0 : ℝ)) : HasDerivWithinAt h (8*x) (Ioi 0) x := by
    convert ((((hasDerivAt_id x).pow 2).const_add (m^2)).const_mul 4).hasDerivWithinAt (s := Ioi 0) using 1
    simp
    ring
  have hmono : StrictMonoOn h (Ioi 0) := by
    intro x hx y hy hxy
    have hx' : 0 < x := hx
    have hy' : 0 < y := hy
    dsimp [h]
    nlinarith [mul_pos (sub_pos.mpr hxy) (add_pos hx' hy')]
  have himage : h '' Ioi 0 = Ioi (4*m^2) := by
    ext s
    constructor
    · rintro ⟨r,hr,rfl⟩
      have hr' : 0 < r := hr
      change 4*m^2 < 4*(m^2+r^2)
      nlinarith [sq_pos_of_pos hr']
    · intro hs
      have hp : 0 < s/4-m^2 := by linarith [mem_Ioi.mp hs]
      refine ⟨sqrt (s/4-m^2), sqrt_pos.mpr hp, ?_⟩
      dsimp [h]
      rw [sq_sqrt hp.le]
      ring
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hD hmono.injOn]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr' : 0 < r := hr
  let R := m^2 + r^2
  have hR : 0 < R := by dsimp [R]; positivity
  have hE : 0 < sqrt R := sqrt_pos.mpr hR
  have hD' : 0 < sqrt (p^2+4*R) := sqrt_pos.mpr (by positivity)
  have hroot : sqrt (1-4*m^2/(4*R)) = r/sqrt R := by
    have heq : 1-4*m^2/(4*R) = r^2/R := by
      field_simp [hR.ne']
      dsimp [R]
      ring
    rw [heq, sqrt_div (sq_nonneg _), sqrt_sq hr'.le]
  change ENNReal.ofReal (4*π*r^2) * (F (4*R) *
    ENNReal.ofReal ((2*sqrt R*sqrt (p^2+4*R))⁻¹)) =
    ENNReal.ofReal |8*r| * (F (4*R) *
      ENNReal.ofReal (π/(4*sqrt (p^2+4*R))*sqrt (1-4*m^2/(4*R))))
  rw [hroot, abs_of_pos (by positivity : 0 < 8*r), mul_left_comm, mul_left_comm (ENNReal.ofReal (8*r)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*π*r^2), ← ENNReal.ofReal_mul (by positivity : 0 ≤ 8*r)]
  congr 2
  field_simp [hE.ne',hD'.ne']
  ring

end UV.PairCurvature
