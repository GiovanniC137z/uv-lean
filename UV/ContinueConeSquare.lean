import UV.ContinueConePolar
import UV.ContinueConeAngularLaw

/-! The uncontracted square tested in actual four-dimensional
momentum coordinates on a fixed sector plane. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Filter Real
open scoped Interval Topology

def coneEuclideanRadius (q : ℝ × Spatial) : ℝ :=
  sqrt (q.1 ^ 2 + ‖q.2‖ ^ 2)

theorem norm_le_coneEuclideanRadius (q : ℝ × Spatial) :
    ‖q‖ ≤ coneEuclideanRadius q := by
  have hS : (coneEuclideanRadius q) ^ 2 = q.1 ^ 2 + ‖q.2‖ ^ 2 :=
    sq_sqrt (by positivity)
  have hS₀ : 0 ≤ coneEuclideanRadius q := sqrt_nonneg _
  rw [Prod.norm_def, max_le_iff]
  constructor
  · rw [Real.norm_eq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hS₀).mp (by rw [hS, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg _))
  · exact (sq_le_sq₀ (norm_nonneg _) hS₀).mp (by rw [hS]; exact le_add_of_nonneg_left (sq_nonneg _))

variable {E : Type*} [NormedAddCommGroup E]

/-- The square is taken after the coefficient readout of the literal
pole inverse on the chosen diamond, with its original height. -/
def Plane.coneSquarePairing (diamond : Plane E) (ε : Evolution) (h : Height)
    (φ : ℝ → ℝ) : ℂ :=
  ∫ q : ℝ × Spatial, φ (coneEuclideanRadius q) •
    (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2


/-- The squared coefficient is the literal vectorial square under
the same real-algebra embedding as the unsquared pole. -/
theorem Plane.cone_square_directed_integrand (diamond : Plane E) (ε : Evolution)
    (h : Height) (q : ℝ × Spatial) :
    directed ((diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2) =
      (diamond.poleInverse ε h (shellSquare q.1 q.2)) ^ 2 := by
  simp only [pow_two, directed_mul, diamond.pole_coefficient_eq_inv,
    Plane.shiftedShellCoefficient, diamond.pole_inverse_complex]

private theorem continuous_square_integrand (diamond : Plane E) (ε : Evolution) (h : Height)
    {φ : ℝ → ℝ} (hc : Continuous φ) :
    Continuous (fun q : ℝ × ℝ => φ (sqrt (q.1 ^ 2 + q.2 ^ 2)) •
      (diamond.poleCoefficient ε h (q.1 ^ 2 - q.2 ^ 2)) ^ 2) :=
  (hc.comp (continuous_sqrt.comp ((continuous_fst.pow 2).add (continuous_snd.pow 2)))).smul
    (((diamond.pole_coefficient_continuous ε h).comp
      ((continuous_fst.pow 2).sub (continuous_snd.pow 2))).pow 2)


theorem Plane.cone_square_integrand_continuous (diamond : Plane E) (ε : Evolution) (h : Height)
    {φ : ℝ → ℝ} (hc : Continuous φ) :
    Continuous (fun q : ℝ × Spatial => φ (coneEuclideanRadius q) •
      (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2) := by
  have hmap : Continuous (fun q : ℝ × Spatial => (q.1, ‖q.2‖)) :=
    continuous_fst.prodMk (continuous_norm.comp continuous_snd)
  have h := (continuous_square_integrand diamond ε h hc).comp hmap
  simpa only [Function.comp_def, coneEuclideanRadius, shellSquare] using h

theorem Plane.cone_square_integrand_compactSupport (diamond : Plane E) (ε : Evolution) (h : Height)
    {φ : ℝ → ℝ} {R : ℝ} (hs : ∀ r > R, φ r = 0) :
    HasCompactSupport (fun q : ℝ × Spatial => φ (coneEuclideanRadius q) •
      (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × Spatial) R)
  intro q hq
  have hr := lt_of_not_ge (show ¬ ‖q‖ ≤ R by simpa only [Metric.mem_closedBall,
    dist_zero_right] using hq)
  change φ (coneEuclideanRadius q) • _ = _
  rw [hs _ (hr.trans_le (norm_le_coneEuclideanRadius q)), zero_smul]

theorem Plane.pole_coefficient_polar (diamond : Plane E) (ε : Evolution) (h : Height)
    {r : ℝ} (hr : 0 < r) (u : ℝ) :
    diamond.poleCoefficient ε h (r ^ 2 * u) =
      ((r ^ 2)⁻¹ : ℝ) • diamond.poleCoefficient ε ⟨(h : ℝ) / r ^ 2,
        div_pos h.property (sq_pos_of_pos hr)⟩ u := by
  simp only [diamond.pole_coefficient_eq_inv, Plane.shiftedShellCoefficient,
    Complex.real_smul, Complex.ofReal_inv]
  have hScale : ((r ^ 2 * u : ℝ) : ℂ) + Complex.I * ((diamond.eta ε * (h : ℝ) : ℝ) : ℂ) =
      ((r ^ 2 : ℝ) : ℂ) *
        ((u : ℂ) + Complex.I * ((diamond.eta ε * ((h : ℝ) / r ^ 2) : ℝ) : ℂ)) := by
    push_cast
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    field_simp [hrC]
  rw [hScale, mul_inv]

/-- The exact imaginary part of the unweighted scalar square against
a continuous radial test, with the four-momentum Lebesgue factor. -/
theorem Plane.cone_square_pairing_im (diamond : Plane E) (ε : Evolution) (h : Height)
    {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hs : ∀ r > R, φ r = 0) :
    (diamond.coneSquarePairing ε h φ).im =
      diamond.eta ε * (2 * π ^ 2) * ∫ r in Ioi (0 : ℝ),
        φ r * coneSquareRadialWeight h r := by
  let G (q : ℝ × ℝ) := (φ (sqrt (q.1 ^ 2 + q.2 ^ 2)) •
    (diamond.poleCoefficient ε h (q.1 ^ 2 - q.2 ^ 2)) ^ 2 : ℂ).im
  have hG : Continuous G := Complex.continuous_im.comp (continuous_square_integrand diamond ε h hc)
  have hi := (diamond.cone_square_integrand_continuous ε h hc).integrable_of_hasCompactSupport
    (μ := volume)
    (diamond.cone_square_integrand_compactSupport ε h hs)
  have hGi : Integrable (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)) :=
    Complex.imCLM.integrable_comp hi
  rw [Plane.coneSquarePairing, ← Complex.imCLM_apply, ← Complex.imCLM.integral_comp_comm hi]
  change (∫ q : ℝ × Spatial, G (q.1, ‖q.2‖)) = _
  rw [cone_polar_integral G hG.aestronglyMeasurable hGi]
  have hEq (r : ℝ) (hr : r ∈ Ioi 0) :
      (∫ θ in Ioo (0 : ℝ) π, (r ^ 3 * sin θ ^ 2) • G (r * cos θ, r * sin θ)) =
        (π / 2 * diamond.eta ε) * (φ r * coneSquareRadialWeight h r) := by
    have hr0 : 0 < r := hr
    let t := (h : ℝ) / r ^ 2
    have ht : 0 < t := div_pos h.property (sq_pos_of_pos hr0)
    let f (u : ℝ) := (diamond.poleCoefficient ε ⟨t, ht⟩ u) ^ 2
    have hf : Continuous f := (diamond.pole_coefficient_continuous ε ⟨t, ht⟩).pow 2
    have hPoint (θ : ℝ) :
        (r ^ 3 * sin θ ^ 2) • G (r * cos θ, r * sin θ) =
          (r⁻¹ * φ r) • ((sin θ ^ 2 : ℝ) • f (cos θ ^ 2 - sin θ ^ 2)).im := by
      have hR : sqrt ((r * cos θ) ^ 2 + (r * sin θ) ^ 2) = r := by
        have htrig := sin_sq_add_cos_sq θ
        rw [show (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 by
          linear_combination r ^ 2 * htrig]
        exact sqrt_sq hr0.le
      have hW : (r * cos θ) ^ 2 - (r * sin θ) ^ 2 =
          r ^ 2 * (cos θ ^ 2 - sin θ ^ 2) := by ring
      dsimp only [G, Prod.fst, Prod.snd]
      rw [hR, hW, diamond.pole_coefficient_polar ε h hr0]
      simp only [f, smul_eq_mul, Complex.real_smul, mul_pow]
      simp only [← Complex.ofReal_pow, mul_assoc,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      field_simp [hr0.ne']
      rfl
    simp_rw [hPoint]
    rw [integral_smul]
    have hfI : IntegrableOn (fun θ : ℝ => sin θ ^ 2 • f (cos θ ^ 2 - sin θ ^ 2))
        (Ioo 0 π) :=
      (((continuous_sin.pow 2).smul (hf.comp
        ((continuous_cos.pow 2).sub (continuous_sin.pow 2)))).continuousOn.integrableOn_compact
          isCompact_Icc).mono_set Ioo_subset_Icc_self
    rw [show (∫ θ in Ioo (0 : ℝ) π,
      ((sin θ ^ 2 : ℝ) • f (cos θ ^ 2 - sin θ ^ 2)).im) =
        (∫ θ in Ioo (0 : ℝ) π, (sin θ ^ 2 : ℝ) • f (cos θ ^ 2 - sin θ ^ 2)).im from
      Complex.imCLM.integral_comp_comm hfI]
    rw [cone_polar_angular_integral hf]
    have hA : (∫ θ in (0 : ℝ)..π, ((1 - cos θ) / π : ℝ) • f (cos θ)) =
        (Complex.I * (diamond.eta ε : ℂ) - (t : ℂ)) / ((sqrt (1 + t ^ 2)) ^ 3 : ℝ) := by
      simpa only [f, diamond.pole_coefficient_eq_inv, Plane.shiftedShellCoefficient] using
        (cone_angular_square_cos ht (diamond.eta_sq ε))
    rw [hA, cone_square_radial_weight_eq hr0]
    simp only [Complex.real_smul, Complex.div_ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.ofReal_re, Complex.sub_im,
      zero_mul, one_mul, sub_zero, zero_add, smul_eq_mul, t]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hEq, integral_const_mul, smul_eq_mul]
  ring

end UV.SectorPlane
