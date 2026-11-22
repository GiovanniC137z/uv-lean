import UV.ExtendShellMeasure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Local integrability through the massless Lorentz cone. The argument
uses the literal shell invariant in the four-momentum measure. A
measure-preserving axial translation depends on transverse momentum. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- The positive real inverse square root of the absolute shell variable. -/
def inverseRootAbs (x : ℝ) : ℝ := (Real.sqrt |x|)⁻¹

theorem inverseRootAbs_measurable : Measurable inverseRootAbs :=
  ((Real.continuous_sqrt.comp continuous_abs).measurable).inv

theorem inverseRootAbs_nonneg (x : ℝ) : 0 ≤ inverseRootAbs x :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem inverseRootAbs_neg (x : ℝ) : inverseRootAbs (-x) = inverseRootAbs x := by
  simp [inverseRootAbs]

theorem integrableOn_inverseRootAbs_Icc {R : ℝ} (hR : 0 < R) :
    IntegrableOn inverseRootAbs (Icc (-R) R) := by
  have hi : IntegrableOn inverseRootAbs (Icc (0 : ℝ) R) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    apply ((intervalIntegral.integrableOn_Ioo_rpow_iff hR).mpr
      (show (-1 : ℝ) < -1 / 2 by norm_num)).congr_fun ?_ measurableSet_Ioo
    intro x hx
    have hx₀ : 0 ≤ x := (mem_Ioo.mp hx).1.le
    change x ^ (-1 / 2 : ℝ) = inverseRootAbs x
    rw [inverseRootAbs, abs_of_nonneg hx₀, Real.sqrt_eq_rpow,
      show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx₀]
  have hm : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg _
  have hEmb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (MeasurableEquiv.neg ℝ).measurableEmbedding
  have hneg := (hm.integrableOn_comp_preimage (s := Icc (0 : ℝ) R) hEmb).mpr hi
  have hpre : (fun x : ℝ => -x) ⁻¹' Icc (0 : ℝ) R = Icc (-R) 0 := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre] at hneg
  simp only [Function.comp_def, inverseRootAbs_neg] at hneg
  rw [← Icc_union_Icc_eq_Icc (neg_nonpos.mpr hR.le) hR.le]
  exact hneg.union hi

/-- Translating the axial variable by a transverse-dependent amount
preserves the actual product volume. -/
theorem axialShear_preserves_volume {u : Spatial → ℝ} (hu : Measurable u) :
    MeasurePreserving (fun q : ℝ × Spatial => (q.1 + u q.2, q.2))
      ((volume : Measure ℝ).prod (volume : Measure Spatial))
      ((volume : Measure ℝ).prod (volume : Measure Spatial)) := by
  have hm : Measurable (fun q : ℝ × Spatial => (q.1 + u q.2, q.2)) :=
    (measurable_fst.add (hu.comp measurable_snd)).prodMk measurable_snd
  refine ⟨hm, Measure.ext_of_lintegral _ ?_⟩
  intro f hf
  rw [lintegral_map hf hm, lintegral_prod_symm' _ (show
    Measurable (fun q : ℝ × Spatial => f (q.1 + u q.2, q.2)) from hf.comp hm),
    lintegral_prod_symm' _ hf]
  apply lintegral_congr
  intro p
  have h := lintegral_map (hf.comp (measurable_id.prodMk (measurable_const (a := p))))
    (measurable_id.add_const (u p)) (μ := volume)
  change (∫⁻ t, f (t, p) ∂Measure.map (fun t : ℝ => t + u p) volume) =
    ∫⁻ t, f (t + u p, p) at h
  rw [map_add_right_eq_self volume (u p)] at h
  exact h.symm

theorem inverse_root_shell_le (x : ℝ) (p : Spatial) (hp : p ≠ 0) :
    inverseRootAbs (shellSquare x p) ≤ inverseRootAbs ‖p‖ *
      (inverseRootAbs (x - ‖p‖) + inverseRootAbs (x + ‖p‖)) := by
  let r := ‖p‖
  have hr : 0 < r := norm_pos_iff.mpr hp
  change inverseRootAbs (x ^ 2 - r ^ 2) ≤ _
  have he : x ^ 2 - r ^ 2 = (x - r) * (x + r) := by ring
  have hmul (u v : ℝ) : inverseRootAbs (u * v) =
      inverseRootAbs u * inverseRootAbs v := by
    simp [inverseRootAbs, abs_mul, Real.sqrt_mul (abs_nonneg u), mul_comm]
  have hinv {u : ℝ} (hu : r ≤ |u|) : inverseRootAbs u ≤ inverseRootAbs r := by
    unfold inverseRootAbs
    rw [abs_of_pos hr]
    exact inv_anti₀ (Real.sqrt_pos.mpr hr) (Real.sqrt_le_sqrt hu)
  rw [he, hmul]
  by_cases hx : 0 ≤ x
  · have hu : r ≤ |x + r| := le_trans (by linarith) (le_abs_self _)
    calc
      _ ≤ inverseRootAbs (x - r) * inverseRootAbs r :=
        mul_le_mul_of_nonneg_left (hinv hu) (inverseRootAbs_nonneg _)
      _ = inverseRootAbs r * inverseRootAbs (x - r) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (inverseRootAbs_nonneg _)) (inverseRootAbs_nonneg _)
  · have hu : r ≤ |x - r| := le_trans (by linarith [le_of_not_ge hx]) (neg_le_abs (x - r))
    calc
      _ ≤ inverseRootAbs r * inverseRootAbs (x + r) :=
        mul_le_mul_of_nonneg_right (hinv hu) (inverseRootAbs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (inverseRootAbs_nonneg _)) (inverseRootAbs_nonneg _)

/-- Local integrability of the inverse-root singularity through the
entire massless cone, including the tip, in four real coordinates. -/
theorem integrableOn_inverse_root_shell_box {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun q : ℝ × Spatial => inverseRootAbs (shellSquare q.1 q.2))
      (Icc (-R) R ×ˢ closedBall (0 : Spatial) R)
      ((volume : Measure ℝ).prod (volume : Measure Spatial)) := by
  let A := Icc (-2 * R) (2 * R)
  let B := closedBall (0 : Spatial) R
  let ax : ℝ → ℝ := A.indicator inverseRootAbs
  let rad : Spatial → ℝ := B.indicator (fun p => inverseRootAbs ‖p‖)
  have ha : Integrable ax := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    simpa only [neg_mul] using integrableOn_inverseRootAbs_Icc (by positivity : 0 < 2 * R)
  have hr : Integrable rad := by
    rw [show rad = B.indicator (fun p => inverseRootAbs ‖p‖) from rfl,
      integrable_indicator_iff isClosed_closedBall.measurableSet]
    have hb : volume B ≠ ∞ := (isCompact_closedBall (0 : Spatial) R).measure_lt_top.ne
    refine ((integrableOn_inv_norm_closedBall_spatial R).add
      (integrableOn_const (C := (1 : ℝ)) hb)).mono' (inverseRootAbs_measurable.comp
      continuous_norm.measurable).aestronglyMeasurable ?_
    refine Eventually.of_forall fun p => ?_
    rw [Real.norm_of_nonneg (inverseRootAbs_nonneg _)]
    change inverseRootAbs ‖p‖ ≤ ‖p‖⁻¹ + 1
    have hs : inverseRootAbs ‖p‖ ^ 2 = ‖p‖⁻¹ := by
      unfold inverseRootAbs
      rw [abs_of_nonneg (norm_nonneg _), inv_pow, Real.sq_sqrt (norm_nonneg _)]
    rw [← hs]
    nlinarith [sq_nonneg (inverseRootAbs ‖p‖ - 1 / 2)]
  have hP : Integrable (fun q : ℝ × Spatial => ax q.1 * rad q.2)
      ((volume : Measure ℝ).prod (volume : Measure Spatial)) := ha.mul_prod hr
  have hmPos := axialShear_preserves_volume continuous_norm.measurable
  have hmNeg := axialShear_preserves_volume continuous_norm.neg.measurable
  have hp := hmPos.integrable_comp_of_integrable hP
  have hq := hmNeg.integrable_comp_of_integrable hP
  have hg : Measurable (fun q : ℝ × Spatial => inverseRootAbs (shellSquare q.1 q.2)) :=
    inverseRootAbs_measurable.comp (by unfold shellSquare; fun_prop)
  refine ((hq.add hp).integrableOn).mono' hg.aestronglyMeasurable ?_
  have hn : ∀ᵐ p : Spatial ∂(volume : Measure Spatial), p ≠ 0 := by rw [ae_iff]; simp
  have hn' := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := (volume : Measure Spatial))).ae hn
  rw [ae_restrict_iff' (measurableSet_Icc.prod isClosed_closedBall.measurableSet)]
  filter_upwards [hn'] with q hq hbox
  have hx : |q.1| ≤ R := abs_le.mpr hbox.1
  have hy : ‖q.2‖ ≤ R := by simpa using hbox.2
  have hpos : q.1 + ‖q.2‖ ∈ A := by
    have h := abs_le.mp hx
    exact ⟨by linarith [h.1, norm_nonneg q.2], by linarith [h.2]⟩
  have hneg : q.1 - ‖q.2‖ ∈ A := by
    have h := abs_le.mp hx
    exact ⟨by linarith [h.1], by linarith [h.2, norm_nonneg q.2]⟩
  rw [Real.norm_of_nonneg (inverseRootAbs_nonneg _)]
  change inverseRootAbs (shellSquare q.1 q.2) ≤
    ax (q.1 + -‖q.2‖) * rad q.2 + ax (q.1 + ‖q.2‖) * rad q.2
  simp only [← sub_eq_add_neg, ax, rad, indicator_of_mem hpos, indicator_of_mem hneg,
    indicator_of_mem (show q.2 ∈ B from hbox.2)]
  have H := inverse_root_shell_le q.1 q.2 hq
  rwa [mul_add, mul_comm (inverseRootAbs ‖q.2‖) (inverseRootAbs (q.1 - ‖q.2‖)),
    mul_comm (inverseRootAbs ‖q.2‖) (inverseRootAbs (q.1 + ‖q.2‖))] at H

end UV.SectorPlane
