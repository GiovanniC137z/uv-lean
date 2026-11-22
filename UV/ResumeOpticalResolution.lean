import UV.ResumeOpticalOperator
import UV.ExtendShellMeasureNormalization
import Mathlib.MeasureTheory.Function.L2Space

/-! Complete positive intermediate-state resolutions on a fixed sector
plane. The state measure is the actual sum of the supplied channel
phase-space measures, with no counting condition on their supports. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory
open scoped InnerProductSpace InnerProduct ENNReal

variable {E H : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : Type*} {X : N → Type*} [∀ n, MeasurableSpace (X n)]

private theorem measurable_channel_embedding (n : N) :
    Measurable (Sigma.mk n : X n → Σ n, X n) :=
  measurable_iff_le_map.mpr (iInf_le
    (fun i => (inferInstance : MeasurableSpace (X i)).map (Sigma.mk i)) n)

/-- Disjoint positive intermediate channels on the selected plane.
Each supplied measure contains that channel's physical normalization. -/
def Plane.physicalIntermediateMeasure (diamond : Plane E)
    (phaseMeasure : Plane E → ∀ n, Measure (X n)) : Measure (Σ n, X n) :=
  Measure.sum (fun n => Measure.map (Sigma.mk n) (phaseMeasure diamond n))

theorem Plane.lintegral_physical_intermediate_measure (diamond : Plane E)
    (phaseMeasure : Plane E → ∀ n, Measure (X n))
    (F : (Σ n, X n) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂diamond.physicalIntermediateMeasure phaseMeasure) =
      ∑' n, ∫⁻ x, F (Sigma.mk n x) ∂phaseMeasure diamond n := by
  unfold Plane.physicalIntermediateMeasure
  rw [lintegral_sum_measure]
  apply tsum_congr
  intro n
  exact lintegral_map hF (measurable_channel_embedding n)

/-- The weighted square integral of an L² wave packet is exactly its
squared Hilbert norm, viewed as a nonnegative extended real. -/
theorem physical_packet_norm_sq_eq_lintegral {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} (f : Lp ℂ 2 μ) :
    ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  rw [Lp.norm_def, ← ENNReal.toReal_pow, ENNReal.ofReal_toReal (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)),
    eLpNorm_eq_lintegral_rpow_enorm (by norm_num) ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- A complete physical resolution is given by a complex-linear
isometric equivalence onto the actual L² direct channel measure. The
optical relation integrates the resolved normalizable packet on every
channel, and the total is finite. -/
theorem Plane.physical_optical_direct_resolution (diamond : Plane E)
    (T : Plane E → H →L[ℂ] H)
    (hS : (diamond.physicalScattering T)† * diamond.physicalScattering T = 1)
    (phaseMeasure : Plane E → ∀ n, Measure (X n))
    (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 (diamond.physicalIntermediateMeasure phaseMeasure)) (i : H) :
    let f := U (T diamond i)
    let W := ∑' n, ∫⁻ x, ENNReal.ofReal (‖f (Sigma.mk n x)‖ ^ 2) ∂phaseMeasure diamond n
    W ≠ ∞ ∧ 2 * (⟪i, T diamond i⟫_ℂ).im = W.toReal := by
  let f := U (T diamond i)
  have hM : Measurable (fun x : Σ n, X n => ENNReal.ofReal (‖f x‖ ^ 2)) :=
    (((Lp.stronglyMeasurable f).measurable.norm).pow_const 2).ennreal_ofReal
  have hW : (∑' n, ∫⁻ x, ENNReal.ofReal (‖f (Sigma.mk n x)‖ ^ 2) ∂phaseMeasure diamond n) =
      ENNReal.ofReal (‖T diamond i‖ ^ 2) := by
    rw [← diamond.lintegral_physical_intermediate_measure phaseMeasure _ hM,
      ← physical_packet_norm_sq_eq_lintegral]
    change ENNReal.ofReal (‖U (T diamond i)‖ ^ 2) = _
    rw [U.norm_map]
  dsimp only
  change (_ : ℝ≥0∞) ≠ ∞ ∧ _ = (∑' n, ∫⁻ x, ENNReal.ofReal (‖f (Sigma.mk n x)‖ ^ 2)
    ∂phaseMeasure diamond n).toReal
  rw [hW, ENNReal.toReal_ofReal (sq_nonneg _)]
  exact ⟨ENNReal.ofReal_ne_top, diamond.physical_optical_packet T hS i⟩

/-- In ordinary real integral notation each channel is absolutely
integrable, and the sum over all channels has the stated value. -/
theorem Plane.physical_optical_phase_space_sum (diamond : Plane E)
    (T : Plane E → H →L[ℂ] H)
    (hS : (diamond.physicalScattering T)† * diamond.physicalScattering T = 1)
    (phaseMeasure : Plane E → ∀ n, Measure (X n))
    (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 (diamond.physicalIntermediateMeasure phaseMeasure)) (i : H) :
    let f := U (T diamond i)
    (∀ n, Integrable (fun x => ‖f (Sigma.mk n x)‖ ^ 2) (phaseMeasure diamond n)) ∧
      HasSum (fun n => ∫ x, ‖f (Sigma.mk n x)‖ ^ 2 ∂phaseMeasure diamond n)
        (2 * (⟪i, T diamond i⟫_ℂ).im) := by
  let f := U (T diamond i)
  let mass (n : N) := ∫⁻ x, ENNReal.ofReal (‖f (Sigma.mk n x)‖ ^ 2) ∂phaseMeasure diamond n
  have h := diamond.physical_optical_direct_resolution T hS phaseMeasure U i
  change (∑' n, mass n) ≠ ∞ ∧ _ = (∑' n, mass n).toReal at h
  have hmeas (n : N) :
      AEStronglyMeasurable (fun x => ‖f (Sigma.mk n x)‖ ^ 2) (phaseMeasure diamond n) := by
    have hm : Measurable (fun x : X n => f (Sigma.mk n x)) :=
      (Lp.stronglyMeasurable f).measurable.comp (measurable_channel_embedding n)
    exact (hm.norm.pow_const 2).aestronglyMeasurable
  have hfinite (n : N) : mass n ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top h.1 n
  have he (n : N) : (∫ x, ‖f (Sigma.mk n x)‖ ^ 2 ∂phaseMeasure diamond n) = (mass n).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hmeas n)
  refine ⟨fun n => ?_, ?_⟩
  · exact (lintegral_ofReal_ne_top_iff_integrable (hmeas n)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp (hfinite n)
  · change HasSum (fun n => ∫ x, ‖f (Sigma.mk n x)‖ ^ 2 ∂phaseMeasure diamond n) _
    simp_rw [he]
    rw [h.2, ENNReal.tsum_toReal_eq hfinite]
    exact ENNReal.hasSum_toReal h.1

/-- In the one-particle case the intermediate resolution may use the
literal normalized signed shell measure on this plane. -/
theorem Plane.physical_optical_positive_shell (diamond : Plane E) (m : ℝ)
    (T : Plane E → H →L[ℂ] H)
    (hS : (diamond.physicalScattering T)† * diamond.physicalScattering T = 1)
    (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 (diamond.positiveShellMeasure m)) (i : H) :
    ENNReal.ofReal (2 * (⟪i, T diamond i⟫_ℂ).im) =
      ∫⁻ p : Spatial, ENNReal.ofReal (((2 * Real.pi) ^ 3 * (2 * shellFrequency m p))⁻¹) *
        ENNReal.ofReal (‖U (T diamond i) (diamond.physicalShellPoint m p)‖ ^ 2) := by
  let f := U (T diamond i)
  have hM : Measurable (fun q : ℝ × Spatial => ENNReal.ofReal (‖f q‖ ^ 2)) :=
    (((Lp.stronglyMeasurable f).measurable.norm).pow_const 2).ennreal_ofReal
  rw [diamond.physical_optical_packet T hS i, ← U.norm_map (T diamond i)]
  change ENNReal.ofReal (‖f‖ ^ 2) = _
  rw [physical_packet_norm_sq_eq_lintegral]
  exact diamond.positive_shell_measure_integral m _ hM

end UV.SectorPlane
