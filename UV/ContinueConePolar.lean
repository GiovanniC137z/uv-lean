import UV.ResumeConeSquareRadial
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! Polar coordinates for functions of the axial slot and spatial norm in
the intrinsic four-dimensional sector-plane momentum measure. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Real
open scoped Interval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem spatial_radial_coefficient :
    (Module.finrank ℝ Spatial : ℝ) *
      (volume : Measure Spatial).real (Metric.ball 0 1) = 4 * π := by
  simp [Spatial, Measure.real, ENNReal.toReal_ofReal (show 0 ≤ π * 4 / 3 by positivity)]
  ring

private theorem spatial_radial_integral (f : ℝ → F) :
    (∫ p : Spatial, f ‖p‖) = (4 * π) • ∫ y in Ioi 0, y ^ 2 • f y := by
  rw [integral_fun_norm_addHaar volume, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, spatial_radial_coefficient]
  simp [Spatial]

private theorem axial_radial_integrable (G : ℝ × ℝ → F) (hG : AEStronglyMeasurable G volume)
    (hI : Integrable (fun q : ℝ × Spatial => G (q.1, ‖q.2‖))) :
    IntegrableOn (fun q : ℝ × ℝ => q.2 ^ 2 • G q) (univ ×ˢ Ioi 0) := by
  have hMeasure : (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Ioi 0) =
      (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)) := by
    change ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi 0) = _
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hG' : AEStronglyMeasurable (fun q : ℝ × ℝ => q.2 ^ 2 • G q)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
    have hW : AEStronglyMeasurable (fun q : ℝ × ℝ => q.2 ^ 2) volume :=
      (continuous_snd.pow 2).aestronglyMeasurable
    simpa only [hMeasure] using
      (hW.smul hG).restrict (s := univ ×ˢ Ioi (0 : ℝ))
  have hI' := (integrable_prod_iff hI.aestronglyMeasurable).mp hI
  rw [IntegrableOn, hMeasure]
  apply (integrable_prod_iff hG').mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [hI'.1] with x hx
    have h := (integrable_fun_norm_addHaar (volume : Measure Spatial)
      (f := fun y => G (x, y))).mp hx
    simpa [Spatial] using h
  · let f (x : ℝ) := ∫ p : Spatial, ‖G (x, ‖p‖)‖
    let g (x : ℝ) := ∫ y in Ioi (0 : ℝ), ‖y ^ 2 • G (x, y)‖
    have hf : Integrable f := hI'.2
    have hfg : f = fun x => (4 * π) * g x := by
      funext x
      unfold f g
      rw [spatial_radial_integral (fun y => ‖G (x, y)‖), smul_eq_mul]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      simp [norm_smul, Real.norm_of_nonneg (sq_nonneg y), smul_eq_mul]
    have hg : g = fun x => (4 * π)⁻¹ * f x := by
      funext x
      rw [congrFun hfg x, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    change Integrable g
    rw [hg]
    exact hf.const_mul (4 * π)⁻¹

private theorem polar_upper_image :
    polarCoord.symm '' (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) π) = univ ×ˢ Ioi (0 : ℝ) := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_prod, polarCoord_symm_apply]
    exact ⟨mem_univ _, mul_pos hz.1 (sin_pos_of_pos_of_lt_pi hz.2.1 hz.2.2)⟩
  · intro hq
    have hsrc : q ∈ polarCoord.source := by
      rw [polarCoord_source]
      exact Or.inr (ne_of_gt hq.2)
    have ht := polarCoord.map_source hsrc
    rw [polarCoord_target] at ht
    refine ⟨polarCoord q, ⟨ht.1, ?_, ht.2.2⟩, polarCoord.left_inv hsrc⟩
    have hsin : 0 < sin (polarCoord q).2 := by
      have h := congrArg Prod.snd (polarCoord.left_inv hsrc)
      rw [polarCoord_symm_apply] at h
      change (polarCoord q).1 * sin (polarCoord q).2 = q.2 at h
      exact pos_of_mul_pos_right (h ▸ hq.2) ht.1.le
    by_contra! h
    have hn : 0 < -(polarCoord q).2 := by
      rcases h.eq_or_lt with he | hl
      · simp only [he, sin_zero, lt_self_iff_false] at hsin
      · exact neg_pos.mpr hl
    have hp : -(polarCoord q).2 < π := by linarith [ht.2.1]
    have := sin_pos_of_pos_of_lt_pi hn hp
    rw [sin_neg] at this
    linarith


/-- The two radial substitutions keep the actual Lebesgue normalization.
Here the spatial polar factor is the area of the unit two-sphere. -/
theorem cone_polar_integral (G : ℝ × ℝ → F) (hG : AEStronglyMeasurable G volume)
    (hI : Integrable (fun q : ℝ × Spatial => G (q.1, ‖q.2‖))) :
    (∫ q : ℝ × Spatial, G (q.1, ‖q.2‖)) =
      (4 * π) • ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (0 : ℝ) π,
        (r ^ 3 * sin θ ^ 2) • G (r * cos θ, r * sin θ) := by
  let S := Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) π
  have hS : MeasurableSet S := measurableSet_Ioi.prod measurableSet_Ioo
  have hInj : InjOn polarCoord.symm S := polarCoord.symm.injOn.mono fun q hq => by
    change q ∈ polarCoord.target
    rw [polarCoord_target]
    exact ⟨hq.1, (neg_lt_zero.mpr pi_pos).trans hq.2.1, hq.2.2⟩
  let H (q : ℝ × ℝ) := q.2 ^ 2 • G q
  have hH : IntegrableOn H (univ ×ˢ Ioi 0) := axial_radial_integrable G hG hI
  have hDeriv (q : ℝ × ℝ) (_ : q ∈ S) :=
    (hasFDerivAt_polarCoord_symm q).hasFDerivWithinAt (s := S)
  have hTrans := integral_image_eq_integral_abs_det_fderiv_smul
    volume hS hDeriv hInj H
  have hTransI := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume hS hDeriv hInj H).mp (polar_upper_image.symm ▸ hH)
  rw [polar_upper_image] at hTrans
  simp only [det_fderivPolarCoordSymm] at hTrans hTransI
  have hEq (q : ℝ × ℝ) (hq : q ∈ S) :
      |q.1| • H (polarCoord.symm q) =
        (q.1 ^ 3 * sin q.2 ^ 2) • G (q.1 * cos q.2, q.1 * sin q.2) := by
    rw [abs_of_pos hq.1, polarCoord_symm_apply]
    dsimp [H]
    rw [smul_smul]
    congr 1
    ring
  have hSl := ae_restrict_mem (μ := volume) hS
  calc
    _ = ∫ x : ℝ, ∫ p : Spatial, G (x, ‖p‖) := integral_prod _ hI
    _ = (4 * π) • ∫ x : ℝ, ∫ y in Ioi 0, H (x, y) := by
      simp_rw [show ∀ x : ℝ, (∫ p : Spatial, G (x, ‖p‖)) =
        (4 * π) • ∫ y in Ioi 0, H (x, y) from
          fun x => spatial_radial_integral (fun y => G (x, y))]
      rw [integral_smul]
    _ = (4 * π) • ∫ q in univ ×ˢ Ioi 0, H q := by
      congr 1
      simpa only [setIntegral_univ] using (setIntegral_prod H hH).symm
    _ = _ := by
      rw [hTrans, setIntegral_congr_fun hS hEq]
      congr 1
      exact setIntegral_prod _ (hTransI.congr (hSl.mono hEq))

end UV.SectorPlane
