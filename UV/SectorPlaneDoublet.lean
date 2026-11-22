import UV.ContinueConeSquare
import UV.Obstructions
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The two internal Maxwell blocks of `eq:monomial-doublet-uv`. The
same internal index is carried around each contraction on the locked plane. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Matrix
open scoped Topology Matrix

/-- `μ₂` denotes the positive squared mass. The Boolean index labels the
internal block, independently of the N/A index of the fixed plane. -/
def doubletHessian (j : Bool) (z X μ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let J : ℝ := if j then 1 else 0
  !![(1 + 2 * J * z^2) * X + 2 * J * μ₂, z * X; z * X, X + μ₂]

def doubletResponse (j : Bool) (X μ₂ : ℝ) : ℝ := (if j then 2 else 0) * X - X^2 / (X + μ₂)

def doubletPropagator (j : Bool) (X μ₂ : ℝ) : ℝ := (X + (if j then 2 else 0) * μ₂)⁻¹

theorem doublet_schur_response (j : Bool) (z : ℝ) {X μ₂ : ℝ} (hX : 0 < X) (hμ : 0 < μ₂) :
    let H := doubletHessian j z X μ₂
    H 0 0 - H 0 1 * (H 1 1)⁻¹ * H 1 0 = (doubletPropagator j X μ₂)⁻¹ + z^2 * doubletResponse j X μ₂ := by
  cases j <;> simp [doubletHessian, doubletPropagator, doubletResponse] <;> field_simp [ne_of_gt (add_pos hX hμ)] <;> ring

theorem doublet_sewn_blocks {X μ₂ : ℝ} (hX : 0 < X) (hμ : 0 < μ₂) :
    doubletPropagator false X μ₂ * doubletResponse false X μ₂ = -(X / (X + μ₂)) ∧
    doubletPropagator true X μ₂ * doubletResponse true X μ₂ = X / (X + μ₂) := by
  constructor <;> simp [doubletPropagator, doubletResponse] <;>
    field_simp [hX.ne', ne_of_gt (add_pos hX hμ), show X + 2 * μ₂ ≠ 0 by positivity]
  all_goals ring

theorem doublet_second_order_cancels {X μ₂ : ℝ} (hX : 0 < X) (hμ : 0 < μ₂) :
    (doubletPropagator false X μ₂ * doubletResponse false X μ₂ +
      doubletPropagator true X μ₂ * doubletResponse true X μ₂) / 2 = 0 ∧
    (doubletResponse false X μ₂ + doubletResponse true X μ₂) / (2 * X) = μ₂ / (X + μ₂) := by
  obtain ⟨h₀, h₁⟩ := doublet_sewn_blocks hX hμ
  constructor
  · rw [h₀, h₁]; ring
  · simp [doubletResponse]; field_simp [hX.ne', ne_of_gt (add_pos hX hμ)]; ring

theorem doublet_relative_determinants {X μ₂ : ℝ} (hX : 0 < X) (hμ : 0 < μ₂) (z : ℝ) :
    (doubletHessian false z X μ₂).det / (doubletHessian false 0 X μ₂).det = 1 - z^2 * (X / (X+μ₂)) ∧
    (doubletHessian true z X μ₂).det / (doubletHessian true 0 X μ₂).det = 1 + z^2 * (X / (X+μ₂)) := by
  constructor <;> simp [doubletHessian, Matrix.det_fin_two] <;>
    field_simp [hX.ne', ne_of_gt (add_pos hX hμ), show X + 2 * μ₂ ≠ 0 by positivity]
  all_goals ring

def doubletTraceLog (z X μ₂ : ℝ) : ℝ :=
  (Real.log ((doubletHessian false z X μ₂).det / (doubletHessian false 0 X μ₂).det) +
    Real.log ((doubletHessian true z X μ₂).det / (doubletHessian true 0 X μ₂).det)) / 2

theorem doublet_trace_log {X μ₂ z : ℝ} (hX : 0 < X) (hμ : 0 < μ₂) (hz : |z| < 1) :
    doubletTraceLog z X μ₂ = Real.log (1 - z^4 * (X / (X+μ₂))^2) / 2 := by
  have hy : 0 < X/(X+μ₂) := div_pos hX (add_pos hX hμ)
  have hy₁ : X/(X+μ₂) < 1 := (div_lt_one (add_pos hX hμ)).mpr (lt_add_of_pos_right _ hμ)
  have hz₁ : z^2 < 1 := by nlinarith [sq_abs z, abs_nonneg z, (abs_lt.mp hz).1, (abs_lt.mp hz).2, mul_self_lt_mul_self (abs_nonneg z) hz]
  have hprod : z^2 * (X/(X+μ₂)) < 1 := by nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hy₁.le)]
  obtain ⟨h₀,h₁⟩ := doublet_relative_determinants hX hμ z
  rw [doubletTraceLog, h₀, h₁, ← Real.log_mul (by linarith) (by positivity)]
  congr 2
  ring

def doubletFourthCoefficient (X μ₂ : ℝ) : ℝ := -(X / (X+μ₂))^2 / 2

/-- Coefficient in the actual normalized determinant, obtained by dividing by
z⁴ at nonzero mixing and taking the two-sided limit. -/
theorem doublet_fourth_coefficient {X μ₂ : ℝ} (hX : 0 < X) (hμ : 0 < μ₂) :
    Tendsto (fun z => doubletTraceLog z X μ₂ / z^4) (𝓝[≠] (0 : ℝ)) (𝓝 (doubletFourthCoefficient X μ₂)) := by
  let y := (X / (X+μ₂))^2
  have H : HasDerivAt (fun t : ℝ => Real.log (1-t*y)) (-y) 0 := by
    convert (((hasDerivAt_const (0 : ℝ) 1).sub ((hasDerivAt_id (0 : ℝ)).mul_const y)).log (by simp)) using 1
    simp
  have H' : Tendsto (fun t : ℝ => t⁻¹ * Real.log (1-t*y)) (𝓝[≠] (0 : ℝ)) (𝓝 (-y)) := by
    simpa only [zero_add, zero_mul, sub_zero, Real.log_one, smul_eq_mul] using H.tendsto_slope_zero
  have hpow : Tendsto (fun z : ℝ => z^4) (𝓝[≠] (0 : ℝ)) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (continuous_pow 4).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact pow_ne_zero 4 (show z ≠ 0 from hz)
  have H'' := (H'.comp hpow).div_const 2
  change Tendsto _ _ (𝓝 (-y/2))
  refine H''.congr' ?_
  have hnear : ∀ᶠ z : ℝ in 𝓝 (0 : ℝ), |z| < 1 := by
    exact continuous_abs.continuousAt (Iio_mem_nhds (by norm_num : |(0:ℝ)|<1))
  filter_upwards [hnear.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))] with z hz
  rw [doublet_trace_log hX hμ hz]
  dsimp only [Function.comp_apply, y]
  ring

theorem doublet_fourth_uv_limit (μ₂ : ℝ) : Tendsto (fun X => doubletFourthCoefficient X μ₂) atTop (𝓝 (-(1:ℝ)/2)) := by
  have H := ((UV.ratio_shift_atTop 0 μ₂).pow 2).neg.div_const 2
  simpa [doubletFourthCoefficient] using H

/-- Intrinsic Euclidean squared momentum uses the assigned unit GT carrier
and the three spatial coordinates on the copy being integrated. -/
def Plane.doubletEuclideanX {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (diamond : Plane E) (q : ℝ × Spatial) : ℝ :=
  ‖q.1 • (diamond.Ghat : E)‖ ^ 2 + ‖q.2‖ ^ 2

/-- The fourth-order ring after the complete two-block internal trace fails
absolute convergence over the full four-momentum plane. -/
theorem Plane.doublet_fourth_not_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (diamond : Plane E) (μ₂ : ℝ) : ¬Integrable (fun q => doubletFourthCoefficient (diamond.doubletEuclideanX q) μ₂) := by
  letI : (volume : Measure (ℝ × Spatial)).IsAddHaarMeasure :=
    inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure Spatial)))
  apply UV.not_integrable_of_cocompact_nonzero_limit (volume : Measure (ℝ × Spatial)) (c := -(1:ℝ)/2) (by norm_num)
  apply (doublet_fourth_uv_limit μ₂).comp
  have h := (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).comp (tendsto_norm_cocompact_atTop (E := ℝ × Spatial))
  apply tendsto_atTop_mono (f := fun q : ℝ × Spatial => ‖q‖ ^ 2) _ h
  intro q
  have hq := sq_le_sq₀ (norm_nonneg q) (Real.sqrt_nonneg _) |>.mpr (norm_le_coneEuclideanRadius q)
  simpa [Plane.doubletEuclideanX, norm_smul, diamond.Ghat.property, coneEuclideanRadius,
    Real.sq_sqrt (add_nonneg (sq_nonneg q.1) (sq_nonneg ‖q.2‖))] using hq

end UV.SectorPlane
