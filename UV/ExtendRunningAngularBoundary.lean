import UV.ExtendRunningAngularJets

/-! Boundary limits of the unweighted pole terms with the literal axial
running sign. The positive-height inverse is always the original pole
coefficient of the fixed sector plane. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Real Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- The original sign-weighted pole pairing folds the odd part of the
compact Cartesian test at each positive height. -/
theorem Plane.cone_running_fold_pole (diamond : Plane E) (ε : Evolution) (h : Height)
    (n : ℕ) {f : ℝ × Spatial → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    (∫ q : ℝ × Spatial, axialSign q.1 •
      (f q * diamond.poleCoefficient ε h (shellSquare q.1 q.2) ^ n)) =
      ∫ q : ℝ × Spatial, coneRunningEvenTest f q *
        diamond.poleCoefficient ε h (shellSquare q.1 q.2) ^ n := by
  let K (q : ℝ × Spatial) := diamond.poleCoefficient ε h (shellSquare q.1 q.2) ^ n
  have hk : Continuous K :=
    ((diamond.pole_coefficient_continuous ε h).comp shellSquare_continuous).pow n
  have hif : Integrable (f * K) := (hf.mul hk).integrable_of_hasCompactSupport hs.mul_right
  apply cone_running_integral_even hif
  intro q
  dsimp only [K]
  rw [cone_axial_reflection_shell]

/-- Exact normalized four-momentum polar formula with the axial running
sign, whose angular effect is the half-difference of the two unit sheets. -/
theorem Plane.cone_running_nonradial_polar_pairing (diamond : Plane E) (ε : Evolution) (h : Height)
    (n : ℕ) {f : ℝ × Spatial → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    (∫ q : ℝ × Spatial, axialSign q.1 •
      (f q * diamond.poleCoefficient ε h (shellSquare q.1 q.2) ^ n)) =
      (2 * π ^ 2 : ℝ) • ∫ r in Ioi (0 : ℝ), (r ^ 3 * ((r ^ 2)⁻¹ : ℝ) ^ n) •
        coneAngularPairing (diamond.eta ε) ((h : ℝ) / r ^ 2) n
          (coneRunningAngularAmplitude f r) := by
  rw [diamond.cone_running_fold_pole ε h n hf hs,
    diamond.cone_nonradial_polar_pairing ε h n (cone_running_even_test_continuous hf)
      (cone_running_even_test_compactSupport hs)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hEq : coneAngularAmplitude (coneRunningEvenTest f) r = coneRunningAngularAmplitude f r :=
    funext fun u => cone_running_angular_amplitude_eq f r u (show 0 ≤ r from hr.le) hf
  dsimp only
  rw [hEq]

theorem cone_running_quadratic_amplitude_eq (f : ℝ × Spatial → ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hf : Continuous f) :
    coneQuadraticAngularAmplitude (coneRunningEvenTest f) r =
      coneRunningQuadraticAngularAmplitude f r := by
  funext u
  unfold coneQuadraticAngularAmplitude coneRunningQuadraticAngularAmplitude
  rw [cone_running_angular_amplitude_eq f r u hr hf]

/-- Exact quadratic numerator form, with the restored two radial powers. -/
theorem Plane.cone_running_nonradial_quadratic_pairing
    (diamond : Plane E) (ε : Evolution) (h : Height)
    {f : ℝ × Spatial → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    (∫ q : ℝ × Spatial, axialSign q.1 •
      (f q * diamond.poleCoefficient ε h (shellSquare q.1 q.2) ^ 2)) =
      (2 * π ^ 2 : ℝ) • ∫ r in Ioi (0 : ℝ), r •
        coneAngularPairing (diamond.eta ε) ((h : ℝ) / r ^ 2) 2
          (coneRunningQuadraticAngularAmplitude f r) := by
  rw [diamond.cone_running_fold_pole ε h 2 hf hs,
    diamond.cone_nonradial_quadratic_pairing ε h (cone_running_even_test_continuous hf)
      (cone_running_even_test_compactSupport hs)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [cone_running_quadratic_amplitude_eq f r (show 0 ≤ r from hr.le) hf]

/-- Exact full single-pole boundary on compact Cartesian C² tests with the
literal running sign on both ordered axial sheets. -/
theorem Plane.cone_running_smooth_single_limit (diamond : Plane E) (ε : Evolution)
    {f : ℝ × Spatial → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∃ R > (0 : ℝ),
      Tendsto (fun h : Height => ∫ q : ℝ × Spatial,
        axialSign q.1 • (f q * diamond.poleCoefficient ε h (shellSquare q.1 q.2)))
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
        (𝓝 ((2 * π ^ 2 : ℝ) • ∫ r in Ioc (0 : ℝ) R, r •
          coneAngularSingleBoundary (diamond.eta ε) (coneRunningAngularAmplitude f r))) := by
  let g := coneRunningEvenTest f
  obtain ⟨R, hR, hoff⟩ := cone_radial_cutoff_of_compact hs
  obtain ⟨C, hC, hj⟩ := cone_running_smooth_single_normal_jet hf R
  have hEq (r : ℝ) (hr : 0 ≤ r) :
      coneAngularAmplitude g r = coneRunningAngularAmplitude f r :=
    funext fun u => cone_running_angular_amplitude_eq f r u hr hf.continuous
  have hg : ∀ r ∈ Ioc (0 : ℝ) R, ‖coneAngularAmplitude g r 0‖ ≤ C ∧
      ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖coneAngularAmplitude g r u - coneAngularAmplitude g r 0‖ ≤ C * |u| := by
    intro r hr
    rw [hEq r hr.1.le]
    exact hj r hr
  have H := diamond.cone_nonradial_single_limit ε
    (cone_running_even_test_continuous hf.continuous)
    (cone_running_even_test_compactSupport hs) hR (cone_running_even_test_zero_outside hoff)
    hC hg
  have hre :
      (∫ r in Ioc (0 : ℝ) R, r • coneAngularSingleBoundary (diamond.eta ε)
        (coneAngularAmplitude g r)) =
      ∫ r in Ioc (0 : ℝ) R, r • coneAngularSingleBoundary (diamond.eta ε)
        (coneRunningAngularAmplitude f r) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only
    rw [hEq r hr.1.le]
  rw [hre] at H
  refine ⟨R, hR, H.congr (fun h => ?_)⟩
  have Hp := diamond.cone_running_fold_pole ε h 1 hf.continuous hs
  simpa only [pow_one, g] using Hp.symm

/-- Exact full squared pole boundary with the running sign and the actual
product of two continuous linear Cartesian momentum slots. -/
theorem Plane.cone_running_smooth_longitudinal_limit (diamond : Plane E) (ε : Evolution)
    {f : ℝ × Spatial → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (L M : (ℝ × Spatial) →L[ℝ] ℝ) :
    let F := fun q => (L q * M q) • f q
    ∃ R > (0 : ℝ), ∃ d : ℝ → ℂ,
      Tendsto (fun h : Height => ∫ q : ℝ × Spatial,
        axialSign q.1 • (F q * diamond.poleCoefficient ε h (shellSquare q.1 q.2) ^ 2))
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
        (𝓝 ((2 * π ^ 2 : ℝ) • ∫ r in Ioc (0 : ℝ) R, r •
          coneAngularSquareBoundary (diamond.eta ε) (coneRunningQuadraticAngularAmplitude F r)
            (d r))) := by
  let F := fun q => (L q * M q) • f q
  let g := coneRunningEvenTest F
  have hFc : Continuous F := (L.continuous.mul M.continuous).smul hf.continuous
  have hFs : HasCompactSupport F := hs.smul_left
  obtain ⟨R, hR, hoff⟩ := cone_radial_cutoff_of_compact hFs
  obtain ⟨d, C, hC, hj⟩ := cone_running_smooth_quadratic_normal_jet hf L M R
  have hEq (r : ℝ) (hr : 0 ≤ r) :
      coneQuadraticAngularAmplitude g r = coneRunningQuadraticAngularAmplitude F r :=
    cone_running_quadratic_amplitude_eq F r hr hFc
  have hg : ∀ r ∈ Ioc (0 : ℝ) R, ‖coneQuadraticAngularAmplitude g r 0‖ ≤ C ∧ ‖d r‖ ≤ C ∧
      ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖coneQuadraticAngularAmplitude g r u - coneQuadraticAngularAmplitude g r 0 -
          (u : ℂ) * d r‖ ≤ C * |u| ^ 2 := by
    intro r hr
    rw [hEq r hr.1.le]
    exact hj r hr
  have H := diamond.cone_nonradial_quadratic_limit ε
    (cone_running_even_test_continuous hFc) (cone_running_even_test_compactSupport hFs)
    hR (cone_running_even_test_zero_outside hoff) d hC hg
  have hre :
      (∫ r in Ioc (0 : ℝ) R, r • coneAngularSquareBoundary (diamond.eta ε)
        (coneQuadraticAngularAmplitude g r) (d r)) =
      ∫ r in Ioc (0 : ℝ) R, r • coneAngularSquareBoundary (diamond.eta ε)
        (coneRunningQuadraticAngularAmplitude F r) (d r) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only
    rw [hEq r hr.1.le]
  rw [hre] at H
  exact ⟨R, hR, d, H.congr (fun h => (diamond.cone_running_fold_pole ε h 2 hFc hFs).symm)⟩

end UV.SectorPlane
