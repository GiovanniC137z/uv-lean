import UV.ContinueOrderedEnvelope
import UV.ContinueWilsonIncidenceRouting

/-! Mixed transverse and Coulomb envelopes on the sector chart. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped BigOperators

namespace UV.SectorPlane

/-- Carrier and spatial coordinates of the orthonormal four-plane. -/
def orderedPhotonChart : OSFourSpace ≃ᵐ ℝ × Spatial :=
  ((EuclideanSpace.measurableEquiv (Fin 4)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (EuclideanSpace.measurableEquiv (Fin 3)).symm)

theorem ordered_photon_chart_preserving : MeasurePreserving orderedPhotonChart volume volume :=
  ((MeasurePreserving.id (μ := (volume : Measure ℝ))).prod
    ((EuclideanSpace.volume_preserving_measurableEquiv (Fin 3)).symm _)).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).comp
      (EuclideanSpace.volume_preserving_measurableEquiv (Fin 4)))

@[simp] theorem ordered_photon_chart_time (p : OSFourSpace) : (orderedPhotonChart p).1 = p 0 := rfl

@[simp] theorem ordered_photon_chart_space (p : OSFourSpace) (j : Fin 3) :
    (orderedPhotonChart p).2 j = p j.succ := by
  change p ((0 : Fin 4).succAbove j) = p j.succ
  simp

inductive OrderedPhotonKind
  | transverse
  | coulomb

/-- The harmonic envelope in sector chart coordinates for either internal line. -/
def OrderedPhotonKind.envelope (kind : OrderedPhotonKind) (a : ℝ) (p : OSFourSpace) : ℝ :=
  match kind with
  | .transverse => orderedTransverseEnvelope a (orderedPhotonChart p)
  | .coulomb => orderedCoulombEnvelope a (orderedPhotonChart p)

theorem OrderedPhotonKind.measurable (kind : OrderedPhotonKind) (a : ℝ) :
    Measurable (kind.envelope a) := by
  cases kind
  · exact (measurable_orderedTransverseEnvelope a).comp orderedPhotonChart.measurable
  · exact (measurable_orderedCoulombEnvelope a).comp orderedPhotonChart.measurable

theorem OrderedPhotonKind.integrable (kind : OrderedPhotonKind) {a : ℝ} (ha : 0 < a) :
    Integrable (kind.envelope a) := by
  cases kind
  · exact ordered_photon_chart_preserving.integrable_comp_of_integrable (ordered_envelopes_integrable ha).1
  · exact ordered_photon_chart_preserving.integrable_comp_of_integrable (ordered_envelopes_integrable ha).2

theorem OrderedPhotonKind.nonneg (kind : OrderedPhotonKind) (a : ℝ) (p : OSFourSpace) :
    0 ≤ kind.envelope a p := by
  cases kind
  · exact (ordered_envelopes_nonneg a _).1
  · exact (ordered_envelopes_nonneg a _).2

theorem OrderedPhotonKind.le_one (kind : OrderedPhotonKind) {a : ℝ} (ha : 0 ≤ a) (p : OSFourSpace) :
    kind.envelope a p ≤ 1 := by
  cases kind
  · exact (ordered_envelopes_le_one ha _).1
  · exact (ordered_envelopes_le_one ha _).2

/-- Reversing the sector reverses the carrier coordinate and fixes the
spatial projection. Both line envelopes are invariant. -/
theorem OrderedPhotonKind.oriented {V : Type*} [Norm V] (kind : OrderedPhotonKind)
    (diamond : Plane V) (a : ℝ) (p : OSFourSpace) :
    kind.envelope a (diamond.osOrientedChart p) = kind.envelope a p := by
  have hs : (orderedPhotonChart (osTimeReflect p)).2 = (orderedPhotonChart p).2 := by
    ext i
    simp [osTimeReflect, Fin.succ_ne_zero]
  cases diamond with
  | mk s b G =>
    cases s
    · rfl
    · change kind.envelope a (osTimeReflect p) = _
      cases kind <;> simp [envelope,orderedTransverseEnvelope,orderedCoulombEnvelope,hs]

end UV.SectorPlane
