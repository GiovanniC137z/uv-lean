import UV.NextOpticalRadial
import UV.FurtherTemporalPolar

/-! The positive-solid-angle ultraviolet test for the radial optical
spinor. The exterior cone sits in the fixed plane's spatial chart. -/

noncomputable section

open Filter Set MeasureTheory Metric Matrix
open scoped Topology Matrix ENNReal InnerProductSpace Pointwise

namespace UV.NextOpticalRadial

theorem radial_pair_integrand_cone_lower {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (u v : SectorPlane.Plane E → ℝ → ℝ) (hUnit : ∀ r, u diamond r ^ 2 + v diamond r ^ 2 = 1)
    {m r ω : ℝ} (n : SectorPlane.UnitVector ChargeSpatialMomentum) (p : ChargeSpatialMomentum)
    (hr : 0 < r) (hm : 0 ≤ m) (hmr : m ≤ r) (hpr : ‖p‖ < r) (hωr : |ω| ≤ r)
    (hc : |⟪(n : ChargeSpatialMomentum), p⟫_ℝ| ≤ ‖p‖/2)
    (hk : r • (n : ChargeSpatialMomentum)+p ≠ 0) :
    let k := r • (n : ChargeSpatialMomentum)+p
    let a := FurtherOptical.projector (spinCoefficients (u diamond ‖k‖) (v diamond ‖k‖)
      (radialUnit k hk))
    let b := FurtherOptical.projector (spinCoefficients (u diamond r) (v diamond r) n)
    let D := FurtherOptical.energy m (r • (n : ChargeSpatialMomentum)) + FurtherOptical.energy m k
    (3*‖p‖^2/416) * (v diamond r)^2 / r^3 ≤
      (((1-a)*b).trace).re * (2*D/(ω^2+D^2)) := by
  dsimp only
  let x := r • (n : ChargeSpatialMomentum)
  let k := x+p
  let a := FurtherOptical.projector (spinCoefficients (u diamond ‖k‖) (v diamond ‖k‖)
    (radialUnit k hk))
  let b := FurtherOptical.projector (spinCoefficients (u diamond r) (v diamond r) n)
  let D := FurtherOptical.energy m x + FurtherOptical.energy m k
  change (3*‖p‖^2/416) * (v diamond r)^2 / r^3 ≤ (((1-a)*b).trace).re * (2*D/(ω^2+D^2))
  have hx : ‖x‖ = r := by simp [x, norm_smul, Real.norm_of_nonneg hr.le, n.property]
  have hk₂ : ‖k‖ ≤ 2*r := by linarith [norm_add_le x p]
  have hb₂ : ⟪(n : ChargeSpatialMomentum), p⟫_ℝ ^ 2 ≤ (‖p‖/2)^2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hc
  have hpos : 0 < ‖k‖^2 := pow_pos (norm_pos_iff.mpr hk) _
  have hangular : 3*‖p‖^2/(16*r^2) ≤
      (‖p‖^2-⟪(n : ChargeSpatialMomentum), p⟫_ℝ^2)/‖k‖^2 := by
    have hlarge : ‖k‖^2 ≤ 4*r^2 := by
      nlinarith [(sq_le_sq₀ (norm_nonneg k) (by positivity)).2 hk₂]
    calc
      _ = (3*‖p‖^2/4)/(4*r^2) := by ring
      _ ≤ (3*‖p‖^2/4)/‖k‖^2 := div_le_div_of_nonneg_left (by positivity) hpos hlarge
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hpos.le
  have hTrace := radial_pair_trace_transverse diamond u v hUnit r n p hk
  have hEt := radial_temporal_resolvent_lower n p hr hm hmr hpr.le hωr
  have hLow := (mul_le_mul_of_nonneg_left hangular (by positivity : 0 ≤ (v diamond r)^2/2)).trans hTrace
  have hMul := mul_le_mul hLow hEt (by positivity : 0 ≤ 1/(13*r)) (by
    refine (show 0 ≤ (v diamond r)^2 / 2 * (3*‖p‖^2/(16*r^2)) by positivity).trans hLow)
  have hEq : (v diamond r)^2 / 2 * (3*‖p‖^2/(16*r^2)) * (1/(13*r)) =
      (3*‖p‖^2/416) * (v diamond r)^2 / r^3 := by
    field_simp
    ring
  rwa [hEq] at hMul

private theorem exists_nonzero_perpendicular (p : ChargeSpatialMomentum) :
    ∃ z : ChargeSpatialMomentum, z ≠ 0 ∧ ⟪z,p⟫_ℝ = 0 := by
  by_cases h : p 0 = 0 ∧ p 1 = 0
  · let z : ChargeSpatialMomentum := EuclideanSpace.single 0 1
    refine ⟨z, ?_, ?_⟩
    · intro hz
      have hz' := congrArg (fun x : ChargeSpatialMomentum => x 0) hz
      simp [z] at hz'
    · rw [PiLp.inner_apply, Fin.sum_univ_three]
      simp [z, h.1]
  · let z : ChargeSpatialMomentum := WithLp.toLp 2 ![-p 1, p 0, 0]
    refine ⟨z, ?_, ?_⟩
    · intro hz
      have h0 := congrArg (fun x : ChargeSpatialMomentum => x 0) hz
      have h1 := congrArg (fun x : ChargeSpatialMomentum => x 1) hz
      exact h ⟨by simpa [z] using h1, by simpa [z] using h0⟩
    · rw [PiLp.inner_apply, Fin.sum_univ_three]
      change p 0 * (-p 1) + p 1 * p 0 + p 2 * 0 = 0
      ring

/-- The strict transverse angular band in the actual unit sphere. -/
def exteriorCone (p : ChargeSpatialMomentum) : Set TemporalRayDirection :=
  {n | |⟪(n : ChargeSpatialMomentum),p⟫_ℝ| < ‖p‖/2}

theorem exteriorCone_measurable (p : ChargeSpatialMomentum) :
    MeasurableSet (exteriorCone p) :=
  measurableSet_lt (continuous_abs.comp (continuous_subtype_val.inner continuous_const)).measurable
    measurable_const

theorem exteriorCone_positive {p : ChargeSpatialMomentum} (hp : p ≠ 0) :
    (volume : Measure ChargeSpatialMomentum).toSphere (exteriorCone p) ≠ 0 := by
  let μ : Measure ChargeSpatialMomentum := volume
  let U : Set ChargeSpatialMomentum :=
    {k | 0 < ‖k‖ ∧ ‖k‖ < 1 ∧ |⟪k,p⟫_ℝ| < ‖k‖*(‖p‖/2)}
  have hInner : Continuous (fun k : ChargeSpatialMomentum => |⟪k,p⟫_ℝ|) :=
    continuous_abs.comp (continuous_id.inner continuous_const)
  have ho : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter
    ((isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt hInner (continuous_norm.mul continuous_const)))
  obtain ⟨z,hz,hzp⟩ := exists_nonzero_perpendicular p
  let n := radialUnit z hz
  have hn : ⟪(n : ChargeSpatialMomentum),p⟫_ℝ = 0 := by
    change ⟪‖z‖⁻¹ • z,p⟫_ℝ = 0
    rw [real_inner_smul_left, hzp, mul_zero]
  have hNu : U.Nonempty := by
    refine ⟨(1/2:ℝ) • (n : ChargeSpatialMomentum), ?_⟩
    change 0 < ‖(1/2:ℝ) • (n : ChargeSpatialMomentum)‖ ∧
        ‖(1/2:ℝ) • (n : ChargeSpatialMomentum)‖ < 1 ∧
          |⟪(1/2:ℝ) • (n : ChargeSpatialMomentum),p⟫_ℝ| <
            ‖(1/2:ℝ) • (n : ChargeSpatialMomentum)‖ * (‖p‖/2)
    rw [norm_smul, n.property, mul_one, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2),
      real_inner_smul_left, hn, mul_zero, abs_zero]
    exact ⟨by norm_num, by norm_num, by positivity⟩
  have hsub : U ⊆ Ioo (0:ℝ) 1 • (Subtype.val '' exteriorCone p) := by
    intro x hx
    have hx' : x ≠ 0 := norm_pos_iff.mp hx.1
    let n : TemporalRayDirection := ⟨(radialUnit x hx' : ChargeSpatialMomentum),
      mem_sphere_zero_iff_norm.mpr (radialUnit x hx').property⟩
    have hCone : n ∈ exteriorCone p := by
      change |⟪‖x‖⁻¹ • x,p⟫_ℝ| < ‖p‖/2
      rw [real_inner_smul_left, abs_mul, abs_of_nonneg (inv_nonneg.mpr hx.1.le), ← div_eq_inv_mul]
      exact (div_lt_iff₀ hx.1).2 (by simpa only [mul_comm] using hx.2.2)
    exact ⟨‖x‖, ⟨hx.1, hx.2.1⟩, (n : ChargeSpatialMomentum), ⟨n,hCone,rfl⟩,
      norm_smul_radialUnit x hx'⟩
  rw [Measure.toSphere_apply' μ (exteriorCone_measurable p)]
  refine mul_ne_zero ?_ ((ho.measure_pos μ hNu).trans_le (measure_mono hsub)).ne'
  simp [finrank_euclideanSpace]

end UV.NextOpticalRadial
