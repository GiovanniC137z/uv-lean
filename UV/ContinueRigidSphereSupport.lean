import UV.ContinueRigidLawWeight
import UV.ContinueRigidThreshold
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! The rigid-source angular measure has full spatial support. This gives
strictly positive soft exponent at every nonzero charge and subluminal
nonzero speed, using the actual solid-angle measure. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Real Filter Asymptotics
open scoped ENNReal RealInnerProductSpace Topology

namespace UV.ContinueRigidLaw

open UV.SectorPlane

private def normDirection (n : Metric.sphere (0 : Spatial) 1) : Direction :=
  ⟨n.1, mem_sphere_zero_iff_norm.1 n.2⟩

private theorem continuous_normDirection : Continuous normDirection :=
  continuous_subtype_val.subtype_mk _

private theorem surjective_normDirection : Function.Surjective normDirection := by
  intro n
  exact ⟨⟨n.1, mem_sphere_zero_iff_norm.2 n.2⟩, Subtype.ext rfl⟩

private theorem isOpenPosMeasure_toSphere :
    IsOpenPosMeasure ((volume : Measure Spatial).toSphere) := by
  let X := ({0}ᶜ : Set Spatial)
  let μ := (volume : Measure Spatial)
  let h := homeomorphUnitSphereProd Spatial
  let r := Measure.volumeIoiPow (Module.finrank ℝ Spatial - 1)
  have ho : IsOpen X := isClosed_singleton.isOpen_compl
  haveI : IsOpenPosMeasure (μ.comap (Subtype.val : X → Spatial)) :=
    IsOpenPosMeasure.comap μ ho.isOpenEmbedding_subtypeVal
  have hmap : (μ.comap (Subtype.val : X → Spatial)).map h = μ.toSphere.prod r :=
    (μ.measurePreserving_homeomorphUnitSphereProd).map_eq
  haveI : IsOpenPosMeasure (μ.toSphere.prod r) :=
    hmap ▸ h.continuous.isOpenPosMeasure_map h.surjective
  constructor
  intro U hU hUn
  have hh := (hU.prod isOpen_univ).measure_ne_zero (μ.toSphere.prod r)
    (hUn.prod ⟨⟨1, mem_Ioi.mpr one_pos⟩, mem_univ _⟩)
  intro hz
  apply hh
  rw [Measure.prod_prod, hz, zero_mul]

theorem solidAngle_openPositive : IsOpenPosMeasure solidAngle := by
  haveI := isOpenPosMeasure_toSphere
  exact continuous_normDirection.isOpenPosMeasure_map surjective_normDirection

theorem solidAngle_mass : solidAngle univ = ENNReal.ofReal (4*π) := by
  unfold solidAngle
  change (((volume : Measure Spatial).toSphere).map normDirection) univ = _
  rw [Measure.map_apply continuous_normDirection.measurable MeasurableSet.univ, preimage_univ,
    Measure.toSphere_apply_univ, EuclideanSpace.volume_ball_fin_three]
  norm_num
  calc
    (3 : ℝ≥0∞) * ENNReal.ofReal (π*4/3) =
      ENNReal.ofReal 3 * ENNReal.ofReal (π*4/3) := by norm_num
    _ = ENNReal.ofReal 4 * ENNReal.ofReal π := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      congr 1
      ring
    _ = _ := by norm_num

theorem continuous_angularWeight (e : ℝ) {v : Spatial} (hv : ‖v‖ < 1) :
    Continuous (angularWeight e v) := by
  have hm : Continuous (fun n : Direction ↦ ⟪v, (n : Spatial)⟫) :=
    continuous_const.inner continuous_subtype_val
  have hd : Continuous (doppler v) := continuous_const.sub hm
  unfold angularWeight
  apply Continuous.div (by fun_prop) (hd.pow 2)
  intro n
  exact pow_ne_zero 2 ((sub_pos.mpr hv).trans_le (doppler_bounds v n).1).ne'

private theorem exists_nonparallel (v : Spatial) (hv : v ≠ 0) :
    ∃ n : Direction, 0 < ‖v‖^2 - ⟪v, (n : Spatial)⟫^2 := by
  let coord (i : Fin 3) : Direction :=
    ⟨EuclideanSpace.single i 1, by simp⟩
  have hi (i : Fin 3) : ⟪v, (coord i : Spatial)⟫ = v i := by
    change ⟪v, EuclideanSpace.single i 1⟫ = v i
    rw [EuclideanSpace.inner_single_right]
    simp
  by_cases h₀ : v 0 = 0
  · refine ⟨coord 0, ?_⟩
    rw [hi, h₀]
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using
      (sq_pos_of_pos (norm_pos_iff.mpr hv))
  · refine ⟨coord 1, ?_⟩
    rw [hi, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_pos_of_ne_zero h₀, sq_nonneg (v 2)]

theorem angularWeight_integral_pos (e : ℝ) {v : Spatial} (hv : ‖v‖ < 1)
    (he : e ≠ 0) (hv₀ : v ≠ 0) :
    0 < ∫ n, angularWeight e v n ∂solidAngle := by
  obtain ⟨n₀, hn₀⟩ := exists_nonparallel v hv₀
  have hd : 0 < doppler v n₀ := (sub_pos.mpr hv).trans_le (doppler_bounds v n₀).1
  have hn : 0 < angularWeight e v n₀ := by
    unfold angularWeight
    positivity
  have hm := (angularWeight_measurable e v).ennreal_ofReal
  haveI := solidAngle_openPositive
  haveI := finite_angularMeasure e hv
  have hs : (Function.support (angularWeight e v)).Nonempty := ⟨n₀, hn.ne'⟩
  have hos : IsOpen (Function.support (angularWeight e v)) :=
    isOpen_ne_fun (continuous_angularWeight e hv) continuous_const
  have heq : Function.support (fun n ↦ ENNReal.ofReal (angularWeight e v n)) =
      Function.support (angularWeight e v) := by
    ext n
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero]
    exact not_congr (le_antisymm_iff.trans (and_iff_left (angularWeight_nonneg e v n))).symm
  have hpos : 0 < angularMeasure e v univ := by
    rw [angularMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_pos_iff_support hm, heq]
    exact hos.measure_pos solidAngle hs
  rw [← angularMeasure_mass]
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)

/-- The charged edge with the original nonzero-coupling and nonzero-motion hypotheses. -/
theorem movingCharge_density_edge (e : ℝ) {a : ℝ} (ha : 0 < a)
    {v : Spatial} (hv : ‖v‖ < 1) (he : e ≠ 0) (hv₀ : v ≠ 0) :
    let α := ∫ n, angularWeight e v n ∂solidAngle
    let ν := dopplerRateMeasure (angularMeasure e v) a v
    let B := 2*a/(1-‖v‖)
    let C := (2*a)^α * exp (-(∫ n, angularWeight e v n * log (doppler v n) ∂solidAngle))
    let f := gammaPoissonDensity (residual ν B) α B
    emittedEnergyLaw ν B = volume.withDensity f ∧
      (fun x ↦ (f x).toReal) ~[𝓝[>] (0 : ℝ)] fun x ↦ C/Gamma α * x^(α-1) :=
  angularLaw_density_edge e ha hv (angularWeight_integral_pos e hv he hv₀)

end UV.ContinueRigidLaw
