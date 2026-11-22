import UV.FurtherOpticalProjector
import UV.ContinuationSectorPlane

/-! The radial optical spinor and the ultraviolet cone estimate in the
intrinsic spatial chart of one locked sector plane. Spinor coefficients
have unit norm independently of the carrier pole direction. -/

noncomputable section

open Matrix
open scoped Matrix InnerProductSpace

namespace UV.NextOpticalRadial

/-- The direction of a nonzero intrinsic spatial momentum. -/
def radialUnit (k : ChargeSpatialMomentum) (hk : k ≠ 0) :
    SectorPlane.UnitVector ChargeSpatialMomentum :=
  ⟨‖k‖⁻¹ • k, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hk)⟩

theorem norm_smul_radialUnit (k : ChargeSpatialMomentum) (hk : k ≠ 0) :
    ‖k‖ • (radialUnit k hk : ChargeSpatialMomentum) = k := by
  change ‖k‖ • (‖k‖⁻¹ • k) = k
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hk), one_smul]

/-- The four coefficients of the radial optical Hamiltonian in the
mass and spatial Clifford slots. -/
def spinCoefficients (u v : ℝ) (n : SectorPlane.UnitVector ChargeSpatialMomentum) : DiracMomentum :=
  WithLp.toLp 2 (Fin.cons u (fun i : Fin 3 => (v • (n : ChargeSpatialMomentum)) i))

theorem spinCoefficients_norm_sq (u v : ℝ)
    (n : SectorPlane.UnitVector ChargeSpatialMomentum) :
    ‖spinCoefficients u v n‖ ^ 2 = u ^ 2 + v ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  change ‖u‖ ^ 2 + ∑ i : Fin 3, ‖(v • (n : ChargeSpatialMomentum)) i‖ ^ 2 = _
  rw [← EuclideanSpace.norm_sq_eq, norm_smul, n.property, mul_one]
  simp only [Real.norm_eq_abs, sq_abs]

theorem spinCoefficients_difference_sq (u₁ v₁ u₂ v₂ : ℝ)
    (n₁ n₂ : SectorPlane.UnitVector ChargeSpatialMomentum) :
    ‖spinCoefficients u₁ v₁ n₁ - spinCoefficients u₂ v₂ n₂‖ ^ 2 =
      (u₁-u₂)^2 + ‖v₁ • (n₁ : ChargeSpatialMomentum) - v₂ • (n₂ : ChargeSpatialMomentum)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  change ‖u₁-u₂‖ ^ 2 +
    ∑ i : Fin 3, ‖(v₁ • (n₁ : ChargeSpatialMomentum) - v₂ • (n₂ : ChargeSpatialMomentum)) i‖ ^ 2 = _
  rw [← EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

/-- Completing the square extracts the same transverse contribution
as orthogonal projection perpendicular to the second unit direction. -/
theorem transverse_difference_lower
    (n q : SectorPlane.UnitVector ChargeSpatialMomentum) (v w : ℝ) :
    v ^ 2 * (1 - ⟪(n : ChargeSpatialMomentum), (q : ChargeSpatialMomentum)⟫_ℝ ^ 2) ≤
      ‖w • (q : ChargeSpatialMomentum) - v • (n : ChargeSpatialMomentum)‖ ^ 2 := by
  rw [norm_sub_rev, norm_sub_sq_real, norm_smul, norm_smul, n.property, q.property,
    mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  nlinarith [sq_nonneg (w - v * ⟪(n : ChargeSpatialMomentum), (q : ChargeSpatialMomentum)⟫_ℝ)]

/-- The angular factor of the normalized second ray is the exact
transverse square of the transfer divided by the shifted norm squared. -/
theorem shifted_ray_transverse (r : ℝ)
    (n : SectorPlane.UnitVector ChargeSpatialMomentum) (p : ChargeSpatialMomentum)
    (hk : r • (n : ChargeSpatialMomentum) + p ≠ 0) :
    1 - ⟪(n : ChargeSpatialMomentum), (radialUnit (r • (n : ChargeSpatialMomentum)+p) hk :
      ChargeSpatialMomentum)⟫_ℝ ^ 2 =
      (‖p‖ ^ 2 - ⟪(n : ChargeSpatialMomentum), p⟫_ℝ ^ 2) /
        ‖r • (n : ChargeSpatialMomentum) + p‖ ^ 2 := by
  let k := r • (n : ChargeSpatialMomentum) + p
  let b := ⟪(n : ChargeSpatialMomentum), p⟫_ℝ
  have hs : ‖k‖ ^ 2 = r^2 + 2*r*b + ‖p‖^2 := by
    dsimp only [k, b]
    rw [norm_add_sq_real, norm_smul, n.property, mul_one, Real.norm_eq_abs, sq_abs,
      real_inner_smul_left]
    ring
  have hi : ⟪(n : ChargeSpatialMomentum), (radialUnit k hk : ChargeSpatialMomentum)⟫_ℝ =
      ‖k‖⁻¹ * (r+b) := by
    change ⟪(n : ChargeSpatialMomentum), ‖k‖⁻¹ • k⟫_ℝ = _
    rw [real_inner_smul_right]
    congr 1
    dsimp only [k, b]
    simp [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, n.property]
  change 1 - ⟪(n : ChargeSpatialMomentum), (radialUnit k hk : ChargeSpatialMomentum)⟫_ℝ ^ 2 =
    (‖p‖ ^ 2 - b ^ 2) / ‖k‖ ^ 2
  have hk2 : ‖k‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hk)
  rw [hi, eq_div_iff hk2, sub_mul, one_mul, mul_pow, inv_pow, mul_right_comm,
    inv_mul_cancel₀ hk2, one_mul, hs]
  ring

/-- The literal radial spin trace on one sector plane has the transverse
angular lower bound used in the exterior-cone test. -/
theorem radial_pair_trace_transverse {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (u v : SectorPlane.Plane E → ℝ → ℝ) (hUnit : ∀ r, u diamond r ^ 2 + v diamond r ^ 2 = 1)
    (r : ℝ) (n : SectorPlane.UnitVector ChargeSpatialMomentum) (p : ChargeSpatialMomentum)
    (hk : r • (n : ChargeSpatialMomentum)+p ≠ 0) :
    let k := r • (n : ChargeSpatialMomentum)+p
    let A := FurtherOptical.projector (spinCoefficients (u diamond ‖k‖) (v diamond ‖k‖)
      (radialUnit k hk))
    let B := FurtherOptical.projector (spinCoefficients (u diamond r) (v diamond r) n)
    (v diamond r)^2/2 *
      ((‖p‖^2 - ⟪(n : ChargeSpatialMomentum), p⟫_ℝ ^ 2) / ‖k‖^2) ≤ (((1-A)*B).trace).re := by
  dsimp only
  let k := r • (n : ChargeSpatialMomentum)+p
  let a := spinCoefficients (u diamond ‖k‖) (v diamond ‖k‖) (radialUnit k hk)
  let b := spinCoefficients (u diamond r) (v diamond r) n
  have ha : ‖a‖ ^ 2 = 1 := (spinCoefficients_norm_sq _ _ _).trans (hUnit _)
  have hb : ‖b‖ ^ 2 = 1 := (spinCoefficients_norm_sq _ _ _).trans (hUnit _)
  change (v diamond r)^2/2 * ((‖p‖^2 - ⟪(n : ChargeSpatialMomentum), p⟫_ℝ ^ 2) / ‖k‖^2) ≤
    (((1-FurtherOptical.projector a)*FurtherOptical.projector b).trace).re
  rw [ContinuationBoostSpectrum.equal_rank_projection_overlap
    (FurtherOptical.projector_adjoint a) (FurtherOptical.projector_adjoint b)
    (FurtherOptical.projector_idempotent a ha) (FurtherOptical.projector_idempotent b hb)
    ((FurtherOptical.projector_trace a).trans (FurtherOptical.projector_trace b).symm),
    FurtherOptical.projector_difference_sq, spinCoefficients_difference_sq]
  have h := transverse_difference_lower n (radialUnit k hk) (v diamond r) (v diamond ‖k‖)
  rw [shifted_ray_transverse r n p hk] at h
  linarith [sq_nonneg (u diamond ‖k‖ - u diamond r)]

/-- The two Euclidean time orderings supply the quantitative lower bound
when the momentum is farther out than the mass, transfer, and frequency. -/
theorem radial_temporal_resolvent_lower {m r ω : ℝ}
    (n : SectorPlane.UnitVector ChargeSpatialMomentum) (p : ChargeSpatialMomentum)
    (hr : 0 < r) (hm : 0 ≤ m) (hmr : m ≤ r) (hpr : ‖p‖ ≤ r) (hωr : |ω| ≤ r) :
    let D := FurtherOptical.energy m (r • (n : ChargeSpatialMomentum)) +
      FurtherOptical.energy m (r • (n : ChargeSpatialMomentum)+p)
    1/(13*r) ≤ 2*D/(ω^2+D^2) := by
  dsimp only
  let x := r • (n : ChargeSpatialMomentum)
  let D := FurtherOptical.energy m x + FurtherOptical.energy m (x+p)
  have hxr : ‖x‖ = r := by simp [x, norm_smul, Real.norm_of_nonneg hr.le, n.property]
  have hxpr : ‖x+p‖ ≤ 2*r := by linarith [norm_add_le x p]
  have h1 : r ≤ FurtherOptical.energy m x := by
    apply (sq_le_sq₀ hr.le (Real.sqrt_nonneg _)).1
    change r ^ 2 ≤ FurtherOptical.energy m x ^ 2
    rw [FurtherOptical.energy_sq, hxr]
    nlinarith [sq_nonneg m]
  have h2 (z : ChargeSpatialMomentum) : FurtherOptical.energy m z ≤ m + ‖z‖ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg hm (norm_nonneg _))).1
    change FurtherOptical.energy m z ^ 2 ≤ (m+‖z‖)^2
    rw [FurtherOptical.energy_sq]
    nlinarith [mul_nonneg hm (norm_nonneg z)]
  have hDr : r ≤ D := by
    dsimp [D]
    exact h1.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hD : D ≤ 5*r := by
    dsimp [D]
    linarith [h2 x, h2 (x+p)]
  have hDpos : 0 < D := hr.trans_le hDr
  have hω : ω^2 ≤ r^2 := by
    rw [← sq_abs ω]
    exact (sq_le_sq₀ (abs_nonneg _) hr.le).2 hωr
  change 1/(13*r) ≤ 2*D/(ω^2+D^2)
  rw [div_le_div_iff₀ (by positivity : 0 < 13*r) (by positivity : 0 < ω^2+D^2)]
  have hDsq := (sq_le_sq₀ hDpos.le (by positivity : 0 ≤ 5*r)).2 hD
  nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hDr)]

end UV.NextOpticalRadial
