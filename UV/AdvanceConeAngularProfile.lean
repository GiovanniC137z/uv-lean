import UV.AdvanceConeAngularGeometry

/-! A nonradial polar profile is the actual average over the two axial
sheets and the spatial unit sphere at each normal coordinate. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Real Set
open scoped Interval Topology

def coneAxialCoordinate (u : ℝ) : ℝ := sqrt ((1 + u) / 2)

def coneSpatialCoordinate (u : ℝ) : ℝ := sqrt ((1 - u) / 2)

theorem cone_axial_coordinate_sq {u : ℝ} (hu : -1 ≤ u) :
    coneAxialCoordinate u ^ 2 = (1 + u) / 2 := by
  unfold coneAxialCoordinate
  exact sq_sqrt (by linarith)

theorem cone_spatial_coordinate_sq {u : ℝ} (hu : u ≤ 1) :
    coneSpatialCoordinate u ^ 2 = (1 - u) / 2 := by
  unfold coneSpatialCoordinate
  exact sq_sqrt (by linarith)

private theorem coneAxialCoordinate_continuous : Continuous coneAxialCoordinate :=
  continuous_sqrt.comp ((continuous_const.add continuous_id).div_const 2)

private theorem coneSpatialCoordinate_continuous : Continuous coneSpatialCoordinate :=
  continuous_sqrt.comp ((continuous_const.sub continuous_id).div_const 2)

def coneAngularDirection (positive : Bool) (u : Icc (-1 : ℝ) 1)
    (ω : ConeSpatialSphere) : UnitVector IntrinsicFour :=
  ⟨WithLp.toLp 2 (Fin.cases
    (if positive then coneAxialCoordinate u.val else -coneAxialCoordinate u.val)
    (fun j => coneSpatialCoordinate u.val * (ω.val : Spatial) j)),
    by
      apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
      change ‖if positive then coneAxialCoordinate u.val else -coneAxialCoordinate u.val‖ ^ 2 +
        (∑ j : Fin 3, ‖coneSpatialCoordinate u.val * (ω.val : Spatial) j‖ ^ 2) = (1 : ℝ) ^ 2
      simp only [Real.norm_eq_abs, sq_abs]
      have hω := EuclideanSpace.norm_sq_eq (ω.val : Spatial)
      rw [cone_spatial_direction_norm, one_pow] at hω
      simp only [Real.norm_eq_abs, sq_abs] at hω
      have hnorm : (∑ j : Fin 3, (ω.val : Spatial) j ^ 2) = 1 := hω.symm
      simp_rw [mul_pow]
      rw [← Finset.mul_sum, hnorm, mul_one, cone_spatial_coordinate_sq u.property.2,
        one_pow]
      cases positive <;> simp [cone_axial_coordinate_sq u.property.1] <;> ring⟩

theorem coneAngularDirection_coordinate (positive : Bool) (u : Icc (-1 : ℝ) 1)
    (ω : ConeSpatialSphere) :
    coneCoordinate (coneAngularDirection positive u ω) = u.val := by
  change 2 * (if positive then coneAxialCoordinate u.val else -coneAxialCoordinate u.val) ^ 2 - 1 =
    u.val
  cases positive <;> simp [cone_axial_coordinate_sq u.property.1] <;> ring

/-- Branch-averaged axial profile. The signs label the two roots of the
Lorentzian angular invariant at fixed Euclidean radius. -/
def coneAxialMean (G : ℝ × ℝ → ℂ) (r u : ℝ) : ℂ :=
  (G (r * coneAxialCoordinate u, r * coneSpatialCoordinate u) +
    G (-(r * coneAxialCoordinate u), r * coneSpatialCoordinate u)) / 2

theorem cone_axial_mean_continuous {G : ℝ × ℝ → ℂ} (hG : Continuous G) :
    Continuous (Function.uncurry (coneAxialMean G)) := by
  have a : Continuous (fun q : ℝ × ℝ => q.1 * coneAxialCoordinate q.2) :=
    continuous_fst.mul (coneAxialCoordinate_continuous.comp continuous_snd)
  have b : Continuous (fun q : ℝ × ℝ => q.1 * coneSpatialCoordinate q.2) :=
    continuous_fst.mul (coneSpatialCoordinate_continuous.comp continuous_snd)
  exact ((hG.comp (a.prodMk b)).add (hG.comp (a.neg.prodMk b))).div_const 2

private theorem cone_axial_coordinate_trig (θ : ℝ) :
    coneAxialCoordinate (cos θ ^ 2 - sin θ ^ 2) = |cos θ| := by
  unfold coneAxialCoordinate
  rw [show (1 + (cos θ ^ 2 - sin θ ^ 2)) / 2 = cos θ ^ 2 by
    linarith only [sin_sq_add_cos_sq θ]
  ]
  exact sqrt_sq_eq_abs _

private theorem cone_spatial_coordinate_trig (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) π) :
    coneSpatialCoordinate (cos θ ^ 2 - sin θ ^ 2) = sin θ := by
  unfold coneSpatialCoordinate
  rw [show (1 - (cos θ ^ 2 - sin θ ^ 2)) / 2 = sin θ ^ 2 by
    linarith only [sin_sq_add_cos_sq θ]
  ]
  exact sqrt_sq (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le

private theorem cone_axial_mean_trig (G : ℝ × ℝ → ℂ) (r θ : ℝ)
    (hθ : θ ∈ Ioo (0 : ℝ) π) :
    coneAxialMean G r (cos θ ^ 2 - sin θ ^ 2) =
      (G (r * cos θ, r * sin θ) + G (r * cos (π - θ), r * sin (π - θ))) / 2 := by
  rw [coneAxialMean, cone_axial_coordinate_trig, cone_spatial_coordinate_trig θ hθ,
    cos_pi_sub, sin_pi_sub, mul_neg]
  rcases le_or_gt 0 (cos θ) with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, mul_neg, neg_neg, add_comm]

/-- Exact normalized cone-coordinate pairing for a general polar test.
The axial reflection enters only through the average of both roots. -/
theorem cone_axial_angular_integral {G : ℝ × ℝ → ℂ} (hG : Continuous G) (r : ℝ) :
    (∫ θ in Ioo (0 : ℝ) π, sin θ ^ 2 • G (r * cos θ, r * sin θ)) =
      (π / 2 : ℝ) • ∫ θ in (0 : ℝ)..π,
        coneAngularWeight θ • coneAxialMean G r (cos θ) := by
  let f (θ : ℝ) := sin θ ^ 2 • G (r * cos θ, r * sin θ)
  let a (θ : ℝ) := sin θ ^ 2 • coneAxialMean G r (cos θ ^ 2 - sin θ ^ 2)
  have hf : Continuous f :=
    (continuous_sin.pow 2).smul (hG.comp
      ((continuous_const.mul continuous_cos).prodMk (continuous_const.mul continuous_sin)))
  have hR : Continuous (fun θ => f (π - θ)) := hf.comp (continuous_const.sub continuous_id)
  have hRf : (∫ θ in (0 : ℝ)..π, f (π - θ)) = ∫ θ in (0 : ℝ)..π, f θ := by
    rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  have hpoint (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) π) :
      a θ = (2 : ℝ)⁻¹ • (f θ + f (π - θ)) := by
    dsimp only [a, f]
    rw [cone_axial_mean_trig G r θ hθ, sin_pi_sub]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hEq : (∫ θ in Ioo (0 : ℝ) π, f θ) = ∫ θ in Ioo (0 : ℝ) π, a θ := by
    rw [setIntegral_congr_fun measurableSet_Ioo hpoint]
    simp_rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le]
    rw [intervalIntegral.integral_smul,
      intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hR.intervalIntegrable _ _),
      hRf, ← two_smul ℝ, smul_smul]
    norm_num
  change (∫ θ in Ioo (0 : ℝ) π, f θ) = _
  rw [hEq]
  have hg : Continuous (coneAxialMean G r) :=
    (cone_axial_mean_continuous hG).comp (continuous_const.prodMk continuous_id)
  exact cone_polar_angular_integral hg

/-- Full four-momentum measure expressed using both axial roots and the
actual spatial sphere average, with the three-sphere area 2π². -/
theorem cone_full_nonradial_normal_integral {f : ℝ × Spatial → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) :
    (∫ q : ℝ × Spatial, f q) =
      (2 * π ^ 2 : ℝ) • ∫ r in Ioi (0 : ℝ), r ^ 3 • ∫ θ in (0 : ℝ)..π,
        coneAngularWeight θ • coneAxialMean (coneSpatialMean f) r (cos θ) := by
  rw [cone_full_nonradial_polar_integral hf hs]
  have hG := cone_spatial_mean_continuous hf hs
  simp_rw [mul_smul, integral_smul, cone_axial_angular_integral hG, smul_comm (_ ^ 3 : ℝ)
    (π / 2), integral_smul, smul_smul]
  congr 1
  ring

end UV.SectorPlane
