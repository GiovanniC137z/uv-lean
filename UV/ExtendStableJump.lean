import UV.ExtendStableChart

/-! The massive stable-half discontinuity on regular timelike charts.
The regulated multiplier hypotheses refer to those of the chart
jump. The finite-height expression is the original directed kernel
coefficient multiplied by the original inverse pole. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

def Plane.transverseStableHalfPairing (diamond : Plane E) (ε : Evolution)
    (ν : Measure Spatial) (a m : ℝ) (test : ℝ × Spatial → ℂ) (h : ℝ) : ℂ :=
  if hh : 0 < h then
    ∫ x : ℝ × Spatial,
      diamond.poleCoefficient ε ⟨h, hh⟩ x.1 *
        (diamond.stableHalfCoefficient ε a (x.1 + m ^ 2) h * test x)
      ∂(volume.prod ν)
  else 0

/-- The stable coefficient jump specialized to its literal kernel
on a compact chart. The coarea density is included in the test. -/
theorem Plane.transverse_stable_half_jump (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    (ν : Measure Spatial) [IsFiniteMeasure ν] (a : ℝ) {m : ℝ} (hm : 0 < m)
    (test : ℝ × Spatial → ℂ)
    (pos neg : ShellChartNumerator)
    (hpb : ∀ x, pos.base x =
      Complex.exp (((a * Real.sqrt (x.1 + m ^ 2) : ℝ) : ℂ) * Complex.I) * test x)
    (hnb : ∀ x, neg.base x =
      Complex.exp (((-(a * Real.sqrt (x.1 + m ^ 2)) : ℝ) : ℂ) * Complex.I) * test x)
    (hpr : ∀ h > 0, ∀ x, pos.base x + pos.error h x =
      diamond.stableHalfCoefficient εPos a (x.1 + m ^ 2) h * test x)
    (hnr : ∀ h > 0, ∀ x, neg.base x + neg.error h x =
      diamond.stableHalfCoefficient εNeg a (x.1 + m ^ 2) h * test x) :
    Tendsto (fun h => diamond.transverseStableHalfPairing εPos ν a m test h -
      diamond.transverseStableHalfPairing εNeg ν a m test h) (𝓝[>] (0 : ℝ))
      (𝓝 (complexShellPV (transverseTest ν
        (fun x => 2 * Complex.I * (Real.sin (a * Real.sqrt (x.1 + m ^ 2)) : ℂ) * test x)) -
        2 * (Real.pi : ℂ) * Complex.I * (Real.cos (a * m) : ℂ) * (∫ p, test (0, p) ∂ν))) := by
  have h := diamond.transverse_pole_jump εPos εNeg hPos hNeg ν pos neg
  have hf (n : ShellChartNumerator) (D : ℝ) : Integrable (fun p => n.base (D, p)) ν :=
    Integrable.of_bound
      (n.base_continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      n.baseBound (Eventually.of_forall fun p => n.base_norm (D, p))
  have hdiff : (fun D => transverseTest ν pos.base D - transverseTest ν neg.base D) =
      transverseTest ν (fun x =>
        2 * Complex.I * (Real.sin (a * Real.sqrt (x.1 + m ^ 2)) : ℂ) * test x) := by
    funext D
    unfold transverseTest
    rw [← integral_sub (hf pos D) (hf neg D)]
    apply integral_congr_ae
    refine Eventually.of_forall fun p => ?_
    dsimp only
    rw [hpb, hnb, ← sub_mul, stable_half_boundary_phase_difference]
  have hsum : (∫ p, (pos.base (0, p) + neg.base (0, p)) ∂ν) =
      (2 * (Real.cos (a * m) : ℂ)) * (∫ p, test (0, p) ∂ν) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine Eventually.of_forall fun p => ?_
    dsimp only
    rw [hpb, hnb, ← add_mul]
    simp only [zero_add]
    rw [stable_half_boundary_phase_sum a m hm.le]
  have hp (h : ℝ) : diamond.transverseStableHalfPairing εPos ν a m test h =
      diamond.transversePoleTest εPos ν pos h := by
    by_cases hh : 0 < h <;>
      simp [Plane.transverseStableHalfPairing, Plane.transversePoleTest, hh, hpr]
  have hn (h : ℝ) : diamond.transverseStableHalfPairing εNeg ν a m test h =
      diamond.transversePoleTest εNeg ν neg h := by
    by_cases hh : 0 < h <;>
      simp [Plane.transverseStableHalfPairing, Plane.transversePoleTest, hh, hnr]
  simp_rw [hp, hn]
  rw [hdiff, hsum] at h
  convert h using 2
  ring

end UV.SectorPlane
