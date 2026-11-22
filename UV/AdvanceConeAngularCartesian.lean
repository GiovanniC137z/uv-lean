import UV.AdvanceConeAngularProfile
import UV.ContinueConeSquare
import UV.ResumeStableCone

/-! Nonradial Cartesian pairings through the cone tip. Finite-height
expressions use the fixed sector-plane pole coefficient throughout. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Real Set
open scoped Interval Topology

/-- The actual normal test of a four-momentum function at positive radius. -/
def coneAngularAmplitude (f : ℝ × Spatial → ℂ) (r u : ℝ) : ℂ :=
  coneAxialMean (coneSpatialMean f) r u

theorem cone_angular_amplitude_continuous {f : ℝ × Spatial → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) : Continuous (Function.uncurry (coneAngularAmplitude f)) :=
  cone_axial_mean_continuous (cone_spatial_mean_continuous hf hs)

theorem cone_normal_point_radius {r u a : ℝ} (hr : 0 ≤ r) (hu : u ∈ Icc (-1 : ℝ) 1)
    (ha : a ^ 2 = 1) (ω : ConeSpatialSphere) :
    coneEuclideanRadius (a * (r * coneAxialCoordinate u),
      (r * coneSpatialCoordinate u) • (ω : Spatial)) = r := by
  unfold coneEuclideanRadius
  simp only [norm_smul, cone_spatial_direction_norm, mul_one,
    Real.norm_eq_abs, sq_abs, mul_pow]
  rw [ha, one_mul, cone_axial_coordinate_sq hu.1, cone_spatial_coordinate_sq hu.2,
    ← mul_add]
  have H : (1 + u) / 2 + (1 - u) / 2 = 1 := by ring
  rw [H, mul_one, sqrt_sq hr]

theorem cone_normal_point_shell {r u a : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1)
    (ha : a ^ 2 = 1) (ω : ConeSpatialSphere) :
    shellSquare (a * (r * coneAxialCoordinate u))
      ((r * coneSpatialCoordinate u) • (ω : Spatial)) = r ^ 2 * u := by
  unfold shellSquare
  simp only [norm_smul, cone_spatial_direction_norm, mul_one, Real.norm_eq_abs, sq_abs, mul_pow]
  rw [ha, one_mul, cone_axial_coordinate_sq hu.1, cone_spatial_coordinate_sq hu.2]
  ring

theorem cone_angular_amplitude_shell_mul (f : ℝ × Spatial → ℂ) (K : ℝ → ℂ) (r : ℝ)
    {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    coneAngularAmplitude (fun q => f q * K (shellSquare q.1 q.2)) r u =
      coneAngularAmplitude f r u * K (r ^ 2 * u) := by
  unfold coneAngularAmplitude coneAxialMean coneSpatialMean
  dsimp only [Prod.fst, Prod.snd]
  have h₁ (ω : ConeSpatialSphere) : shellSquare (r * coneAxialCoordinate u)
      ((r * coneSpatialCoordinate u) • (ω : Spatial)) = r ^ 2 * u := by
    simpa only [one_mul] using cone_normal_point_shell hu (a := 1) (by norm_num) ω
  have h₂ (ω : ConeSpatialSphere) : shellSquare (-(r * coneAxialCoordinate u))
      ((r * coneSpatialCoordinate u) • (ω : Spatial)) = r ^ 2 * u := by
    simpa only [neg_one_mul] using cone_normal_point_shell hu (a := -1) (by norm_num) ω
  simp_rw [h₁, h₂, integral_mul_const, Complex.real_smul]
  ring

theorem cone_angular_amplitude_zero_outside {f : ℝ × Spatial → ℂ} {R r u : ℝ}
    (hs : ∀ q, R < coneEuclideanRadius q → f q = 0) (hr : 0 ≤ r)
    (hR : R < r) (hu : u ∈ Icc (-1 : ℝ) 1) :
    coneAngularAmplitude f r u = 0 := by
  have hz (a : ℝ) (ha : a ^ 2 = 1) (ω : ConeSpatialSphere) :
      f (a * (r * coneAxialCoordinate u), (r * coneSpatialCoordinate u) • (ω : Spatial)) = 0 :=
    hs _ (by rwa [cone_normal_point_radius hr hu ha ω])
  have h₁ (ω : ConeSpatialSphere) :
      f (r * coneAxialCoordinate u, (r * coneSpatialCoordinate u) • (ω : Spatial)) = 0 := by
    simpa only [one_mul] using hz 1 (by norm_num) ω
  have h₂ (ω : ConeSpatialSphere) :
      f (-(r * coneAxialCoordinate u), (r * coneSpatialCoordinate u) • (ω : Spatial)) = 0 := by
    simpa only [neg_one_mul] using hz (-1) (by norm_num) ω
  simp [coneAngularAmplitude, coneAxialMean, coneSpatialMean, h₁, h₂]

theorem cone_angular_pairing_smul (c η t : ℝ) (n : ℕ) (f : ℝ → ℂ) :
    coneAngularPairing η t n (fun u => c • f u) = c • coneAngularPairing η t n f := by
  unfold coneAngularPairing
  rw [← intervalIntegral.integral_smul]
  congr 1
  funext u
  simp only [Complex.real_smul]
  ring

variable {E : Type*} [NormedAddCommGroup E]

/-- Finite-height polar decomposition of the actual four-momentum pole
pairing. The angular height is h/r², with the same oriented coefficient. -/
theorem Plane.cone_nonradial_polar_pairing (diamond : Plane E) (ε : Evolution) (h : Height)
    (n : ℕ) {f : ℝ × Spatial → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    (∫ q : ℝ × Spatial, f q * diamond.poleCoefficient ε h (shellSquare q.1 q.2) ^ n) =
      (2 * π ^ 2 : ℝ) • ∫ r in Ioi (0 : ℝ), (r ^ 3 * ((r ^ 2)⁻¹ : ℝ) ^ n) •
        coneAngularPairing (diamond.eta ε) ((h : ℝ) / r ^ 2) n (coneAngularAmplitude f r) := by
  let K (u : ℝ) := diamond.poleCoefficient ε h u ^ n
  have hK : Continuous K := (diamond.pole_coefficient_continuous ε h).pow n
  change (∫ q : ℝ × Spatial, f q * K (shellSquare q.1 q.2)) = _
  have hF : Continuous (fun q : ℝ × Spatial => f q * K (shellSquare q.1 q.2)) :=
    hf.mul (hK.comp shellSquare_continuous)
  have hS : HasCompactSupport (fun q : ℝ × Spatial => f q * K (shellSquare q.1 q.2)) :=
    hs.mul_right
  rw [cone_full_nonradial_normal_integral hF hS]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr₀ : 0 < r := hr
  have hA (θ : ℝ) :
      coneAngularAmplitude (fun q => f q * K (shellSquare q.1 q.2)) r (cos θ) =
        ((r ^ 2)⁻¹ : ℝ) ^ n •
          (coneAngularAmplitude f r (cos θ) *
            coneAngularPole (diamond.eta ε) ((h : ℝ) / r ^ 2) θ ^ n) := by
    rw [cone_angular_amplitude_shell_mul f K r ⟨neg_one_le_cos θ, cos_le_one θ⟩]
    unfold K
    rw [diamond.pole_coefficient_polar ε h hr₀]
    simp only [Complex.real_smul, mul_pow, Complex.ofReal_pow]
    rw [diamond.pole_coefficient_eq_inv, Plane.shiftedShellCoefficient]
    unfold coneAngularPole
    dsimp only
    ring
  change r ^ 3 • (∫ θ in (0 : ℝ)..π, coneAngularWeight θ •
    coneAngularAmplitude (fun q => f q * K (shellSquare q.1 q.2)) r (cos θ)) = _
  simp_rw [hA, smul_comm (coneAngularWeight _) (((r ^ 2)⁻¹ : ℝ) ^ n),
    intervalIntegral.integral_smul, smul_smul]
  rfl

/-- Radius-normalized amplitude for a quadratic numerator already present
in the Cartesian test. The values at r=0 are immaterial to the radial
pairing. -/
def coneQuadraticAngularAmplitude (f : ℝ × Spatial → ℂ) (r u : ℝ) : ℂ :=
  ((r ^ 2)⁻¹ : ℝ) • coneAngularAmplitude f r u

theorem cone_quadratic_amplitude_continuous_normal {f : ℝ × Spatial → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) (r : ℝ) : Continuous (coneQuadraticAngularAmplitude f r) :=
  continuous_const.smul ((cone_angular_amplitude_continuous hf hs).comp
    (continuous_const.prodMk continuous_id))

/-- Exact angular decomposition of a Cartesian squared pole with its two
numerator powers restored in the normalized amplitude. -/
theorem Plane.cone_nonradial_quadratic_pairing (diamond : Plane E) (ε : Evolution) (h : Height)
    {f : ℝ × Spatial → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    (∫ q : ℝ × Spatial, f q * diamond.poleCoefficient ε h (shellSquare q.1 q.2) ^ 2) =
      (2 * π ^ 2 : ℝ) • ∫ r in Ioi (0 : ℝ), r •
        coneAngularPairing (diamond.eta ε) ((h : ℝ) / r ^ 2) 2
          (coneQuadraticAngularAmplitude f r) := by
  rw [diamond.cone_nonradial_polar_pairing ε h 2 hf hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  change _ = r • coneAngularPairing _ _ 2 (fun u => ((r ^ 2)⁻¹ : ℝ) •
    coneAngularAmplitude f r u)
  rw [cone_angular_pairing_smul, smul_smul]
  congr 1
  field_simp [(show 0 < r from hr).ne']

end UV.SectorPlane
