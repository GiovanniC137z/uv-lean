import UV.AdvanceStableCartesian
import Mathlib.Analysis.Calculus.Deriv.Support

/-! Integration by parts for the actual sign of the axial readout.
The jump of the multiplier produces its explicit axial trace. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology

theorem runningAxialSign_measurable : Measurable axialSign := by
  unfold axialSign
  exact measurable_const.ite (measurableSet_Ioi (a := (0 : ℝ)))
    (measurable_const.ite (measurableSet_Iio (a := (0 : ℝ))) measurable_const)

theorem runningAxialSign_norm_le (x : ℝ) : ‖(axialSign x : ℂ)‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, axialSign]
  · rw [Complex.norm_real, Real.norm_eq_abs, axialSign_abs hx]

theorem integrable_runningAxialSign_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {x : X → ℝ} (hx : Measurable x) {f : X → ℂ} (hf : Integrable f μ) :
    Integrable (fun q => (axialSign (x q) : ℂ) * f q) μ := by
  have hs := (Complex.continuous_ofReal.measurable.comp
    (runningAxialSign_measurable.comp hx)).aestronglyMeasurable (μ := μ)
  apply hf.norm.mono' (hs.mul hf.aestronglyMeasurable)
  refine Eventually.of_forall fun q => ?_
  change ‖(axialSign (x q) : ℂ) * f q‖ ≤ ‖f q‖
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (runningAxialSign_norm_le _)

private theorem axial_sign_integral_deriv {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F)
    (hs : HasCompactSupport F) :
    (∫ x : ℝ, (axialSign x : ℂ) * deriv F x) = -(2 : ℂ) * F 0 := by
  have hmid : Integrable (deriv F) := hF.continuous_deriv_one.integrable_of_hasCompactSupport hs.deriv
  have hsign : Integrable (fun x => (axialSign x : ℂ) * deriv F x) :=
    integrable_runningAxialSign_mul (x := id) measurable_id hmid
  have hpos : (∫ x in Ioi (0 : ℝ), (axialSign x : ℂ) * deriv F x) =
      ∫ x in Ioi (0 : ℝ), deriv F x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [axialSign, show 0 < x from hx]
  have hneg : (∫ x in Iic (0 : ℝ), (axialSign x : ℂ) * deriv F x) =
      -(∫ x in Iic (0 : ℝ), deriv F x) := by
    rw [← integral_neg]
    apply setIntegral_congr_ae measurableSet_Iic
    have hz : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
    filter_upwards [hz] with x hn hx
    have h : x < 0 := lt_of_le_of_ne hx hn
    simp [axialSign, h, h.not_gt]
  have hpart := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hsign
  rw [compl_Ioi, hpos, hneg, hs.integral_Ioi_deriv_eq hF, hs.integral_Iic_deriv_eq hF] at hpart
  rw [← hpart]
  ring

private theorem axial_slice_compact {f : ℝ × Spatial → ℂ} (hs : HasCompactSupport f)
    (p : Spatial) : HasCompactSupport (fun x : ℝ => f (x, p)) :=
  HasCompactSupport.of_support_subset_isCompact (hs.image continuous_fst)
    (fun x hx => ⟨(x, p), subset_tsupport f hx, rfl⟩)

theorem running_spatial_slice_compact {f : ℝ × Spatial → ℂ} (hs : HasCompactSupport f)
    (x : ℝ) : HasCompactSupport (fun p : Spatial => f (x, p)) :=
  HasCompactSupport.of_support_subset_isCompact (hs.image continuous_snd)
    (fun p hp => ⟨(x, p), subset_tsupport f hp, rfl⟩)

private theorem integral_axialSign_axial_derivative {f : ℝ × Spatial → ℂ}
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    (∫ q : ℝ × Spatial, (axialSign q.1 : ℂ) * fderiv ℝ f q (1, 0)) =
      -(2 : ℂ) * (∫ p : Spatial, f (0, p)) := by
  let e : ℝ × Spatial := (1, 0)
  have hcont : Continuous (fun q => fderiv ℝ f q e) :=
    (hf.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const)
  have hi := hcont.integrable_of_hasCompactSupport (μ := volume) (hs.fderiv_apply ℝ e)
  have hi' := integrable_runningAxialSign_mul (μ := volume) measurable_fst hi
  change (∫ q : ℝ × Spatial, (axialSign q.1 : ℂ) * fderiv ℝ f q e) = _
  rw [← integral_const_mul]
  calc
    _ = ∫ p : Spatial, ∫ x : ℝ, (axialSign x : ℂ) * fderiv ℝ f (x, p) e :=
      integral_prod_symm _ hi'
    _ = _ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun p => ?_
      let g (x : ℝ) := f (x, p)
      have hg : ContDiff ℝ 1 g := hf.comp (contDiff_id.prodMk contDiff_const)
      have hderiv (x : ℝ) : deriv g x = fderiv ℝ f (x, p) e := by
        have ht : HasDerivAt (fun t : ℝ => (t, p)) e x :=
          (hasDerivAt_id x).prodMk (hasDerivAt_const x p)
        exact (((hf.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt x ht).deriv
      simp_rw [← hderiv]
      exact axial_sign_integral_deriv hg (axial_slice_compact hs p)

private theorem integral_axialSign_spatial_derivative {f : ℝ × Spatial → ℂ}
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (v : Spatial) :
    (∫ q : ℝ × Spatial, (axialSign q.1 : ℂ) * fderiv ℝ f q (0, v)) = 0 := by
  let e : ℝ × Spatial := (0, v)
  have hc : Continuous (fun q => fderiv ℝ f q e) :=
    (hf.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const)
  have hi := hc.integrable_of_hasCompactSupport (μ := volume) (hs.fderiv_apply ℝ e)
  have hi' := integrable_runningAxialSign_mul (μ := volume) measurable_fst hi
  change (∫ q : ℝ × Spatial, (axialSign q.1 : ℂ) * fderiv ℝ f q e) = _
  calc
    _ = ∫ x : ℝ, ∫ p : Spatial, (axialSign x : ℂ) * fderiv ℝ f (x, p) e :=
      integral_prod _ hi'
    _ = ∫ _x : ℝ, (0 : ℂ) := by
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      let g (p : Spatial) := f (x, p)
      have hg : ContDiff ℝ 1 g := hf.comp (contDiff_const.prodMk contDiff_id)
      have hgs : HasCompactSupport g := running_spatial_slice_compact hs x
      have hgi := hg.continuous.integrable_of_hasCompactSupport (μ := volume) hgs
      have hg'c : Continuous (fun p => fderiv ℝ g p v) :=
        (hg.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const)
      have hg'i := hg'c.integrable_of_hasCompactSupport (μ := volume) (hgs.fderiv_apply ℝ v)
      have hderiv (p : Spatial) : fderiv ℝ g p v = fderiv ℝ f (x, p) e := by
        let j : Spatial →L[ℝ] ℝ × Spatial := ContinuousLinearMap.inr ℝ ℝ Spatial
        have hj : HasFDerivAt (fun p' : Spatial => (x, p')) j p := by
          simpa only [j, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
            j.hasFDerivAt.const_add ((x : ℝ), (0 : Spatial))
        exact congrArg (fun L : Spatial →L[ℝ] ℂ => L v)
          (((hf.differentiable (by norm_num) _).hasFDerivAt).comp p hj).fderiv
      have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
        (f := fun _ : Spatial => (1 : ℂ)) (g := g) (v := v)
        (by simp) (by simpa using hg'i) (by simpa using hgi)
        (differentiable_const _) (hg.differentiable (by norm_num))
      have hZ : (∫ p : Spatial, fderiv ℝ g p v) = 0 := by simpa using hIBP
      dsimp only
      rw [integral_const_mul]
      simp_rw [← hderiv]
      rw [hZ, mul_zero]
    _ = _ := integral_zero _ _

/-- Differentiating in a Cartesian direction against the literal running
sign gives exactly its jump, with coefficient twice the axial component. -/
theorem integral_axialSign_directional_derivative {f : ℝ × Spatial → ℂ}
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (v : ℝ × Spatial) :
    (∫ q : ℝ × Spatial, (axialSign q.1 : ℂ) * fderiv ℝ f q v) =
      -(2 : ℂ) * (v.1 : ℂ) * (∫ p : Spatial, f (0, p)) := by
  let A (q : ℝ × Spatial) := (axialSign q.1 : ℂ) * fderiv ℝ f q (1, 0)
  let B (q : ℝ × Spatial) := (axialSign q.1 : ℂ) * fderiv ℝ f q (0, v.2)
  have hi (d : ℝ × Spatial) : Integrable (fun q : ℝ × Spatial =>
      (axialSign q.1 : ℂ) * fderiv ℝ f q d) := by
    apply integrable_runningAxialSign_mul measurable_fst
    have hc : Continuous (fun q => fderiv ℝ f q d) :=
      (hf.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const)
    exact hc.integrable_of_hasCompactSupport (μ := volume) (hs.fderiv_apply ℝ d)
  have hv : v = (v.1 • ((1 : ℝ), (0 : Spatial))) + ((0 : ℝ), v.2) := by
    cases v
    simp
  calc
    _ = ∫ q : ℝ × Spatial, (v.1 : ℂ) * A q + B q := by
      apply integral_congr_ae
      refine Eventually.of_forall fun q => ?_
      dsimp only [A, B]
      conv_lhs => rw [hv, map_add, map_smul]
      simp only [Complex.real_smul]
      ring
    _ = (v.1 : ℂ) * (∫ q, A q) + ∫ q, B q := by
      rw [integral_add ((hi (1, 0)).const_mul _) (hi (0, v.2)), integral_const_mul]
    _ = _ := by
      dsimp only [A, B]
      rw [integral_axialSign_axial_derivative hf hs, integral_axialSign_spatial_derivative hf hs]
      ring

end UV.SectorPlane
