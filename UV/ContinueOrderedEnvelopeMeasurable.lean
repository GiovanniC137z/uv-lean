import UV.ContinueOrderedEnvelopeSewing
import UV.ContinueOrderedCurrentPlane
import UV.ContinueWilsonGraphTwoPoint

/-! Measurability of full projected lines and of the two temporal currents. -/

noncomputable section

open MeasureTheory Filter UV.SectorPlane

namespace UV.SectorPlane

theorem measurable_orderedTransverseNumerator (P R : OrderedTwoBandPath) :
    Measurable (fun s : ℝ × Spatial => orderedTransverseNumerator P R s.1 s.2) := by
  have hneg : Continuous (fun s : ℝ × Spatial => (-s.1,-s.2)) := by fun_prop
  apply Finset.measurable_sum
  intro ij _
  apply (Complex.continuous_ofReal.measurable.comp ((measurable_orderedSpatialProjector _ _).comp measurable_snd)).mul
  exact (P.continuous_spatialCurrent _).measurable.mul (((R.continuous_spatialCurrent _).comp hneg).measurable)

theorem OrderedPhotonKind.measurable_sewn (kind : OrderedPhotonKind) (a : ℝ) (P R : OrderedTwoBandPath) :
    Measurable (kind.sewn a P R) := by
  have hneg : Continuous (fun s : ℝ × Spatial => (-s.1,-s.2)) := by fun_prop
  cases kind with
  | transverse =>
    exact (Complex.continuous_ofReal.measurable.comp (show Measurable
      (fun s : ℝ × Spatial => Real.exp (-(2*a*‖s.2‖))/(s.1^2+‖s.2‖^2)) by fun_prop)).mul
        (measurable_orderedTransverseNumerator P R)
  | coulomb =>
    exact (Complex.continuous_ofReal.measurable.comp (show Measurable
      (fun s : ℝ × Spatial => Real.exp (-(2*a*‖s.2‖))/‖s.2‖^2) by fun_prop)).mul
        ((P.continuous_density.measurable).mul ((R.continuous_density.comp hneg).measurable))

end UV.SectorPlane
