import UV.ContinueConeSquare
import UV.ContinueCarrierConeBounds

/-! The temporal and spatial-trace radial channels before and after
the angular change of variables in the actual four-momentum measure. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Real
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E]

/-- Radial pairing of the unweighted pole square with a quadratic
numerator in the axial slot and the spatial trace. -/
def Plane.coneQuadraticPairing (diamond : Plane E) (ε : Evolution) (h : Height)
    (A B : ℝ) (φ : ℝ → ℝ) : ℂ :=
  ∫ q : ℝ × Spatial,
    (φ (coneEuclideanRadius q) * (A * q.1 ^ 2 + B * ‖q.2‖ ^ 2)) •
      (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2

/-- The full four-momentum integral reduces to the actual quadratic
angular average, with two radial powers from its numerator. -/
theorem Plane.cone_quadratic_radial_integral (diamond : Plane E) (ε : Evolution) (h : Height)
    (A B : ℝ) {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hs : ∀ r > R, φ r = 0) :
    diamond.coneQuadraticPairing ε h A B φ =
      (2 * π ^ 2 : ℝ) • ∫ r in Ioi (0 : ℝ), (r * φ r) •
        (∫ θ in (0 : ℝ)..π, coneAngularWeight θ •
          ((A * ((1 + cos θ) / 2) + B * ((1 - cos θ) / 2)) •
            (coneAngularPole (diamond.eta ε) ((h : ℝ) / r ^ 2) θ) ^ 2)) := by
  let G (q : ℝ × ℝ) :=
    (φ (sqrt (q.1 ^ 2 + q.2 ^ 2)) * (A * q.1 ^ 2 + B * q.2 ^ 2)) •
      (diamond.poleCoefficient ε h (q.1 ^ 2 - q.2 ^ 2)) ^ 2
  have hG : Continuous G :=
    ((hc.comp (continuous_sqrt.comp ((continuous_fst.pow 2).add (continuous_snd.pow 2)))).mul
      ((continuous_const.mul (continuous_fst.pow 2)).add
        (continuous_const.mul (continuous_snd.pow 2)))).smul
      (((diamond.pole_coefficient_continuous ε h).comp
        ((continuous_fst.pow 2).sub (continuous_snd.pow 2))).pow 2)
  have hI : Integrable (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)) := by
    have hcont := hG.comp (continuous_fst.prodMk
      (continuous_norm.comp (continuous_snd : Continuous (Prod.snd : ℝ × Spatial → Spatial))))
    apply hcont.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × Spatial) R)
    intro q hq
    have hr := lt_of_not_ge (show ¬ ‖q‖ ≤ R by simpa only [Metric.mem_closedBall,
      dist_zero_right] using hq)
    have hφ := hs _ (hr.trans_le (norm_le_coneEuclideanRadius q))
    change (φ (coneEuclideanRadius q) * (A * q.1 ^ 2 + B * ‖q.2‖ ^ 2)) •
      (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2 = 0
    rw [hφ, zero_mul, zero_smul]
  change (∫ q : ℝ × Spatial, G (q.1, ‖q.2‖)) = _
  rw [cone_polar_integral G hG.aestronglyMeasurable hI]
  have hInner (r : ℝ) (hr : r ∈ Ioi 0) :
      (∫ θ in Ioo (0 : ℝ) π, (r ^ 3 * sin θ ^ 2) • G (r * cos θ, r * sin θ)) =
        (π / 2) • ((r * φ r) • (∫ θ in (0 : ℝ)..π, coneAngularWeight θ •
          ((A * ((1 + cos θ) / 2) + B * ((1 - cos θ) / 2)) •
            (coneAngularPole (diamond.eta ε) ((h : ℝ) / r ^ 2) θ) ^ 2))) := by
    have hr₀ : 0 < r := hr
    let t := (h : ℝ) / r ^ 2
    have ht : 0 < t := div_pos h.property (sq_pos_of_pos hr₀)
    let f (u : ℝ) :=
      (A * ((1 + u) / 2) + B * ((1 - u) / 2)) •
        (diamond.poleCoefficient ε ⟨t, ht⟩ u) ^ 2
    have hf : Continuous f :=
      ((continuous_const.mul ((continuous_const.add continuous_id).div_const 2)).add
        (continuous_const.mul ((continuous_const.sub continuous_id).div_const 2))).smul
        ((diamond.pole_coefficient_continuous ε ⟨t, ht⟩).pow 2)
    have hPoint (θ : ℝ) :
        (r ^ 3 * sin θ ^ 2) • G (r * cos θ, r * sin θ) =
          (r * φ r) • (sin θ ^ 2 • f (cos θ ^ 2 - sin θ ^ 2)) := by
      have hTrig := sin_sq_add_cos_sq θ
      have hR : sqrt ((r * cos θ) ^ 2 + (r * sin θ) ^ 2) = r := by
        rw [show (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 by
          linear_combination r ^ 2 * hTrig]
        exact sqrt_sq hr₀.le
      have hW : (r * cos θ) ^ 2 - (r * sin θ) ^ 2 = r ^ 2 * (cos θ ^ 2 - sin θ ^ 2) := by
        ring
      have hNum : A * (r * cos θ) ^ 2 + B * (r * sin θ) ^ 2 =
          r ^ 2 * (A * ((1 + (cos θ ^ 2 - sin θ ^ 2)) / 2) +
            B * ((1 - (cos θ ^ 2 - sin θ ^ 2)) / 2)) := by
        linear_combination (r ^ 2 * (A + B) / 2) * hTrig
      dsimp only [G, Prod.fst, Prod.snd]
      rw [hR, hW, hNum, diamond.pole_coefficient_polar ε h hr₀]
      simp only [f, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
        mul_pow]
      have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₀.ne'
      field_simp [hrC]
      rfl
    simp_rw [hPoint]
    rw [integral_smul, cone_polar_angular_integral hf, smul_comm (r * φ r)]
    simp only [f, coneAngularWeight, coneAngularPole, diamond.pole_coefficient_eq_inv,
      Plane.shiftedShellCoefficient, t]
  rw [setIntegral_congr_fun measurableSet_Ioi hInner, integral_smul, smul_smul]
  congr 1
  ring


theorem Plane.cone_temporal_radial_integral (diamond : Plane E) (ε : Evolution) (h : Height)
    {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hs : ∀ r > R, φ r = 0) :
    diamond.coneQuadraticPairing ε h 1 0 φ =
      (2 * π ^ 2 : ℝ) • ∫ r in Ioi (0 : ℝ),
        (r * φ r) • coneTemporalSecond (diamond.eta ε) ((h : ℝ) / r ^ 2) := by
  rw [diamond.cone_quadratic_radial_integral ε h 1 0 hc hs]
  simp only [coneTemporalSecond, one_mul, zero_mul, add_zero]

theorem Plane.cone_one_third_spatial_radial_integral (diamond : Plane E)
    (ε : Evolution) (h : Height) {φ : ℝ → ℝ} (hc : Continuous φ)
    {R : ℝ} (hs : ∀ r > R, φ r = 0) :
    diamond.coneQuadraticPairing ε h 0 (1 / 3) φ =
      (2 * π ^ 2 : ℝ) • ∫ r in Ioi (0 : ℝ),
        (r * φ r) • coneSpatialSecond (diamond.eta ε) ((h : ℝ) / r ^ 2) := by
  have hWeight (θ : ℝ) : 0 * ((1 + cos θ) / 2) + (1 / 3) * ((1 - cos θ) / 2) =
      (1 - cos θ) / 6 := by ring
  rw [diamond.cone_quadratic_radial_integral ε h 0 (1 / 3) hc hs]
  simp only [hWeight, coneSpatialSecond]

end UV.SectorPlane
