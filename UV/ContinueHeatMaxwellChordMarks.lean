import UV.ContinueHeatMaxwellChordDeriv
import Mathlib.MeasureTheory.Integral.Prod

/-! The first mark and direct contact integrated over their original
straight-chord parameter distributions on the Euclidean sector. -/

noncomputable section
namespace UV.HeatMaxwell
open UV.RelativeSoft UV.SectorPlane MeasureTheory Filter Set
open scoped RealInnerProductSpace Topology

abbrev heatCenteredLaw : Measure ℝ := volume.restrict (Ioc (-1/2) (1/2))
abbrev heatUnitLaw : Measure ℝ := volume.restrict (Ioc 0 1)
abbrev heatContactLaw := heatUnitLaw.prod heatUnitLaw

def heatFirstLocal (k : EuclideanPlaneMomentum) (s : ℝ) : EuclideanPlaneMomentum :=
  deriv (fun t : ℝ => heatSymbol (k+s • softLongitudinal.val+t • softTransverse.val)) 0

def heatContactLocal (k : EuclideanPlaneMomentum) (s : ℝ) : EuclideanPlaneMomentum :=
  deriv (deriv (fun t : ℝ => heatSymbol (k+s • softLongitudinal.val+t • softTransverse.val))) 0

def heatFirstChord (k : EuclideanPlaneMomentum) := heatChordMoment heatCenteredLaw id 0 (heatFirstLocal k)
def heatContactChord (k : EuclideanPlaneMomentum) :=
  heatChordMoment heatContactLaw (fun p : ℝ×ℝ => p.1-p.2) 0 (heatContactLocal k)

theorem heat_first_local_contDiff (k : EuclideanPlaneMomentum) : ContDiff ℝ 2 (heatFirstLocal k) := by
  have he := funext fun s => (heatSymbol_transverse_derivatives k s).1
  unfold heatFirstLocal
  rw [he]
  unfold heatShiftFactor
  fun_prop

theorem heat_contact_local_contDiff (k : EuclideanPlaneMomentum) : ContDiff ℝ 2 (heatContactLocal k) := by
  have he := funext fun s => (heatSymbol_transverse_derivatives k s).2
  unfold heatContactLocal
  rw [he]
  unfold heatShiftFactor
  fun_prop

theorem heat_centered_bound : ∀ᵐ s ∂heatCenteredLaw, |id s|≤1 := by
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(-1/2:ℝ)) (b:=1/2))] with s hs
  change |s|≤1
  exact abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩

theorem heat_contact_bound : ∀ᵐ p ∂heatContactLaw, |p.1-p.2|≤1 := by
  have hm : MeasurableSet {p : ℝ×ℝ | |p.1-p.2|≤1} := measurableSet_le (continuous_fst.sub continuous_snd).abs.measurable measurable_const
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=1))] with s hs
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=1))] with v hv
  exact abs_le.mpr ⟨by linarith [hs.1,hv.2],by linarith [hs.2,hv.1]⟩

theorem heat_contact_law_second : (∫ p : ℝ×ℝ, (p.1-p.2)^2 ∂heatContactLaw)=1/6 := by
  have hi : Integrable (fun p : ℝ×ℝ => (p.1-p.2)^2) heatContactLaw := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    filter_upwards [heat_contact_bound] with p hp
    simpa [Real.norm_eq_abs,abs_pow] using (pow_le_one₀ (abs_nonneg _) hp : |p.1-p.2|^2≤1)
  rw [integral_prod _ hi]
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using heatSecondMark_parameter_moment

theorem heat_first_chord_second (k : EuclideanPlaneMomentum) :
    deriv (deriv (heatFirstChord k)) 0 =
    (1/12:ℝ) • (Real.exp (-‖k‖^2) • heatCarrierVector k (heatH₁₁₂ ⟪k,softLongitudinal.val⟫ ⟪k,softTransverse.val⟫)) := by
  rw [heatFirstChord,heat_chord_second_at_zero measurable_id heat_centered_bound (heat_first_local_contDiff k)]
  have hm : (∫ s, (id s)^2 ∂heatCenteredLaw)=1/12 := by
    simpa only [id_eq,intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2)] using heatFirstMark_parameter_moment
  rw [hm]
  exact congrArg ((1/12:ℝ) • ·) (heatSymbol_mixed_mark_derivatives k).1

theorem heat_contact_chord_second (k : EuclideanPlaneMomentum) :
    deriv (deriv (heatContactChord k)) 0 =
    (1/6:ℝ) • (Real.exp (-‖k‖^2) • heatCarrierVector k (heatH₁₁₂₂ ⟪k,softLongitudinal.val⟫ ⟪k,softTransverse.val⟫)) := by
  rw [heatContactChord,heat_chord_second_at_zero (measurable_fst.sub measurable_snd) heat_contact_bound (heat_contact_local_contDiff k),heat_contact_law_second]
  exact congrArg ((1/6:ℝ) • ·) (heatSymbol_mixed_mark_derivatives k).2

end UV.HeatMaxwell
