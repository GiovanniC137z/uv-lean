import UV.ContinueConeSquareLog
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! A smooth compact test witnessing the logarithmic obstruction at
the origin of the four-dimensional massless cone. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Real Filter
open scoped ContDiff Topology

private def squareProbeProfile (r : ℝ) : ℝ :=
  Real.smoothTransition ((4 - r ^ 2) / 3)

private theorem square_probe_profile_continuous : Continuous squareProbeProfile :=
  (Real.smoothTransition.contDiff (n := 1)).continuous.comp
    ((continuous_const.sub (continuous_id.pow 2)).div_const 3)

private theorem square_probe_profile_one (r : ℝ) (hr : r ∈ Icc 0 1) :
    squareProbeProfile r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hrs := (sq_le_sq₀ hr.1 (by norm_num : 0 ≤ (1 : ℝ))).mpr hr.2
  linarith

private theorem square_probe_profile_zero (r : ℝ) (hr : 2 < r) :
    squareProbeProfile r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hrs := (sq_lt_sq₀ (by norm_num : 0 ≤ (2 : ℝ)) (by positivity : 0 ≤ r)).mpr hr
  linarith

/-- A radial smooth test with its compact profile retained, so other
terms in the same graph can be tested on the identical function. -/
theorem Plane.cone_square_smooth_radial_probe {E : Type*} [NormedAddCommGroup E] (diamond : Plane E)
    (ε : Evolution) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ (∀ r ∈ Icc 0 1, φ r = 1) ∧ (∀ r > 2, φ r = 0) ∧
      ContDiff ℝ ∞ (fun q => φ (coneEuclideanRadius q)) ∧ HasCompactSupport (fun q => φ (coneEuclideanRadius q)) ∧
      (∀ q, coneEuclideanRadius q ≤ 1 → φ (coneEuclideanRadius q) = 1) ∧
      Tendsto (fun h : Height => diamond.eta ε * (diamond.coneSquarePairing ε h φ).im)
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) atTop := by
  refine ⟨squareProbeProfile,square_probe_profile_continuous,square_probe_profile_one,square_probe_profile_zero,?_,?_,?_,?_⟩
  · have hSq (q : ℝ × Spatial) : (coneEuclideanRadius q) ^ 2 = q.1 ^ 2 + ‖q.2‖ ^ 2 :=
      sq_sqrt (by positivity)
    simp_rw [squareProbeProfile, hSq]
    have hNorm : ContDiff ℝ ∞ (fun q : ℝ × Spatial => ‖q.2‖ ^ 2) :=
      (contDiff_norm_sq ℝ (E := Spatial)).comp contDiff_snd
    exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub ((contDiff_fst.pow 2).add hNorm)).div_const 3)
  · apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × Spatial) 2)
    intro q hq
    apply square_probe_profile_zero
    have hr := lt_of_not_ge (show ¬ ‖q‖ ≤ 2 by simpa only [Metric.mem_closedBall,
      dist_zero_right] using hq)
    exact hr.trans_le (norm_le_coneEuclideanRadius q)
  · intro q hq
    exact square_probe_profile_one _ ⟨sqrt_nonneg _, hq⟩
  · exact diamond.cone_square_pairing_signed_im_tendsto ε zero_lt_one (by norm_num)
      square_probe_profile_continuous square_probe_profile_one square_probe_profile_zero

/-- The literal scalar square has a divergent imaginary pairing even
on a smooth compact four-momentum test that is one near the cone tip. -/
theorem Plane.cone_square_smooth_probe {E : Type*} [NormedAddCommGroup E] (diamond : Plane E)
    (ε : Evolution) :
    ∃ ψ : ℝ × Spatial → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ q, coneEuclideanRadius q ≤ 1 → ψ q = 1) ∧
      Tendsto (fun h : Height => diamond.eta ε *
        (∫ q : ℝ × Spatial, ψ q •
          (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2).im)
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) atTop := by
  obtain ⟨φ,_,_,_,hf,hs,hone,H⟩ := diamond.cone_square_smooth_radial_probe ε
  exact ⟨_,hf,hs,hone,H⟩

end UV.SectorPlane
