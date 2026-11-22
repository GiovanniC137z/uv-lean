import UV.NextOpticalTail
import UV.NextOpticalBandGeometry

/-! The compact-band upper estimate for the radial optical pair. The
solid angle of the allowed transverse tube controls its radial measure. -/

noncomputable section

open Filter Set MeasureTheory Metric
open scoped Topology ENNReal InnerProductSpace Pointwise

namespace UV.NextOpticalRadial

/-- The axis is a unit spatial coordinate direction on the frozen plane. -/
def spatialAxis : SectorPlane.UnitVector ChargeSpatialMomentum :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

private def transverseTube (δ : ℝ) : Set TemporalRayDirection :=
  {n | |(n : ChargeSpatialMomentum) 1| ≤ δ ∧ |(n : ChargeSpatialMomentum) 2| ≤ δ}

private theorem transverseTube_measurable (δ : ℝ) : MeasurableSet (transverseTube δ) := by
  have hc (i : Fin 3) : Continuous (fun n : TemporalRayDirection => |(n : ChargeSpatialMomentum) i|) :=
    continuous_abs.comp ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp continuous_subtype_val)
  exact (measurableSet_le (hc 1).measurable measurable_const).inter
    (measurableSet_le (hc 2).measurable measurable_const)

theorem transverseTube_measure_le {δ : ℝ} (hδ : 0 ≤ δ) :
    (volume : Measure ChargeSpatialMomentum).toSphere (transverseTube δ) ≤ ENNReal.ofReal (24*δ^2) := by
  let μ : Measure ChargeSpatialMomentum := volume
  let a : Fin 3 → ℝ := ![-1, -δ, -δ]
  let b : Fin 3 → ℝ := ![1, δ, δ]
  have hsub : Ioo (0:ℝ) 1 • (Subtype.val '' transverseTube δ) ⊆
      (EuclideanSpace.measurableEquiv (Fin 3)) ⁻¹' Icc a b := by
    rintro x ⟨t, ht, y, ⟨n, hn, rfl⟩, rfl⟩
    have h0 : |(n : ChargeSpatialMomentum) 0| ≤ 1 := by
      rw [← Real.norm_eq_abs, ← temporalRayDirection_norm n]
      exact PiLp.norm_apply_le (n : ChargeSpatialMomentum) 0
    have hle (z e : ℝ) (hz : |z| ≤ e) : -e ≤ t*z ∧ t*z ≤ e := by
      apply abs_le.mp
      rw [abs_mul, abs_of_pos ht.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans hz
    have h0' := hle _ _ h0
    have h1' := hle _ _ hn.1
    have h2' := hle _ _ hn.2
    show (∀ i, a i ≤ t * (n : ChargeSpatialMomentum) i) ∧
      ∀ i, t * (n : ChargeSpatialMomentum) i ≤ b i
    constructor <;> intro i <;> fin_cases i <;>
      first | exact h0'.1 | exact h1'.1 | exact h2'.1 | exact h0'.2 | exact h1'.2 | exact h2'.2
  rw [Measure.toSphere_apply' μ (transverseTube_measurable δ)]
  calc
    _ ≤ (Module.finrank ℝ ChargeSpatialMomentum : ℝ≥0∞) *
      μ ((EuclideanSpace.measurableEquiv (Fin 3)) ⁻¹' Icc a b) := by
        exact mul_le_mul_left' (measure_mono hsub) _
    _ = _ := by
      rw [(EuclideanSpace.volume_preserving_measurableEquiv (Fin 3)).measure_preimage ((measurableSet_Icc : MeasurableSet (Icc a b)).nullMeasurableSet),
        Real.volume_Icc_pi, Fin.prod_univ_three, finrank_euclideanSpace, Fintype.card_fin]
      change (3:ℝ≥0∞) * (ENNReal.ofReal (1-(-1)) *
        ENNReal.ofReal (δ-(-δ)) * ENNReal.ofReal (δ-(-δ))) = _
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ 1-(-1 : ℝ)) ,
        ← ENNReal.ofReal_mul (by linarith : 0 ≤ (1-(-1:ℝ))*(δ- -δ)),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
      congr 1
      ring

private theorem spinDeparture_le {u v : ℝ → ℝ}
    (hu : ∀ r, 0 ≤ u r) (hUnit : ∀ r, u r^2+v r^2 = 1) (k : ChargeSpatialMomentum) :
    ‖radialSpinor u v k - FurtherOptical.massAxis‖^2 ≤ 2*v ‖k‖^2 := by
  unfold radialSpinor
  split
  · simp; positivity
  · rename_i hk
    let n := radialUnit k hk
    have he : spinCoefficients 1 0 n = FurtherOptical.massAxis := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [spinCoefficients, FurtherOptical.massAxis]
      · simp [spinCoefficients, FurtherOptical.massAxis]
    change ‖spinCoefficients (u ‖k‖) (v ‖k‖) n - FurtherOptical.massAxis‖^2 ≤ 2*v ‖k‖^2
    rw [← he, spinCoefficients_difference_sq, zero_smul, sub_zero, norm_smul, n.property, mul_one,
      Real.norm_eq_abs, sq_abs]
    have hu₁ : u ‖k‖ ≤ 1 := by nlinarith [hUnit ‖k‖, sq_nonneg (v ‖k‖)]
    nlinarith [hUnit ‖k‖, mul_nonneg (hu ‖k‖) (sub_nonneg.mpr hu₁)]

theorem radialPairWeight_upper {u v : ℝ → ℝ}
    (hu : ∀ r, 0 ≤ u r) (hUnit : ∀ r, u r^2+v r^2 = 1) (p k : ChargeSpatialMomentum) :
    radialPairWeight u v p k ≤ 2*(v ‖k‖^2+v ‖k+p‖^2) := by
  let a := radialSpinor u v (k+p) - FurtherOptical.massAxis
  let b := radialSpinor u v k - FurtherOptical.massAxis
  unfold radialPairWeight
  rw [show radialSpinor u v (k+p) - radialSpinor u v k = a-b by dsimp [a,b]; abel]
  have hSq := (sq_le_sq₀ (norm_nonneg (a-b)) (by positivity)).2 (norm_sub_le a b)
  have ha : ‖a‖^2 ≤ 2*v ‖k+p‖^2 := spinDeparture_le hu hUnit (k+p)
  have hb : ‖b‖^2 ≤ 2*v ‖k‖^2 := spinDeparture_le hu hUnit k
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

end UV.NextOpticalRadial
