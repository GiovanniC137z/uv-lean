import UV.RevisionLegacyStableTail
import UV.RevisionSourceGaussian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Weighted polar integration in the fixed four-dimensional Euclidean sector. -/

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal NNReal BigOperators

namespace UV

/-- Haar polar decomposition with an actual coordinate power. The radial
weight is allowed to be a measurable annulus indicator. -/
theorem stable_weighted_polar_integral (j : ℕ) (g : ℝ → ℝ) :
    (∫ x : ScalarMomentum, (x 0) ^ j * g ‖x‖) =
      (∫ n : sphere (0 : ScalarMomentum) 1, (n.1 0) ^ j ∂(volume : Measure ScalarMomentum).toSphere) *
        ∫ r in Ioi (0 : ℝ), r ^ (j + 3) * g r := by
  let μ : Measure ScalarMomentum := volume
  let e := (homeomorphUnitSphereProd ScalarMomentum).toMeasurableEquiv
  let f := fun x : ScalarMomentum => (x 0) ^ j * g ‖x‖
  have hp : MeasurePreserving e (μ.comap Subtype.val)
      (μ.toSphere.prod (Measure.volumeIoiPow 3)) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using
      μ.measurePreserving_homeomorphUnitSphereProd
  have h := (MeasurePreserving.symm e hp).integral_comp e.symm.measurableEmbedding
    (fun x : ({(0 : ScalarMomentum)}ᶜ : Set ScalarMomentum) => f x.1)
  rw [integral_subtype_comap (measurableSet_singleton _).compl f, restrict_compl_singleton] at h
  change (∫ x, f x ∂μ) = _
  rw [← h]
  have hpolar : (fun p : sphere (0 : ScalarMomentum) 1 × Ioi (0 : ℝ) =>
        f (e.symm p).1) = fun p => (p.1.1 0)^j * ((p.2.1)^j * g p.2.1) := by
    funext p
    change f (((homeomorphUnitSphereProd ScalarMomentum).symm p).1) = _
    rw [homeomorphUnitSphereProd_symm_apply_coe]
    have hn : ‖p.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
    unfold f
    rw [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_of_nonneg p.2.2.le, hn, mul_one, mul_pow]
    ring
  rw [hpolar, integral_prod_mul
    (fun n : sphere (0 : ScalarMomentum) 1 => (n.1 0) ^ j)
    (fun r : Ioi (0 : ℝ) => r.1 ^ j * g r.1)]
  congr 1
  unfold Measure.volumeIoiPow
  have hmeas : Measurable (fun r : Ioi (0 : ℝ) => Real.toNNReal (r.1 ^ 3)) :=
    (measurable_subtype_coe.pow_const _).real_toNNReal
  simp_rw [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul hmeas,
    integral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => Real.toNNReal (r ^ 3) • (r ^ j * g r))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _), smul_eq_mul, pow_add]
  ring

private theorem stable_gaussian_sixth_real :
    (∫ x : ℝ, x ^ 6 * exp (-(x ^ 2))) = 15 * Real.sqrt π / 8 := by
  have h1 := centered_gaussian_half_recurrence 0
  have h2 := centered_gaussian_half_recurrence 1
  have h3 := centered_gaussian_half_recurrence 2
  norm_num at h1 h2 h3
  rw [show (∫ x : ℝ, x ^ 6 * exp (-(x ^ 2))) = 2 * gaussianEvenMoment 0 3 from
      centered_gaussian_even_integral 3, h3, h2, h1, gaussianEvenMoment_zero_zero]
  ring

private theorem stable_gaussian_sixth_four :
    (∫ x : ScalarMomentum, (x 0) ^ 6 * exp (-(‖x‖ ^ 2))) = 15 * π ^ 2 / 8 := by
  let f : Fin 4 → ℝ → ℝ := fun i t =>
    if i = 0 then t ^ 6 * exp (-(t ^ 2)) else exp (-(t ^ 2))
  have hp := (PiLp.volume_preserving_ofLp (Fin 4)).integral_comp
    (EuclideanSpace.measurableEquiv (Fin 4)).measurableEmbedding
    (fun x : Fin 4 → ℝ => ∏ i, f i (x i))
  have he : (fun x : ScalarMomentum => ∏ i, f i (x i)) =
      fun x => (x 0) ^ 6 * exp (-(‖x‖ ^ 2)) := by
    funext x
    rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_neg_distrib, Real.exp_sum]
    simp only [Real.norm_eq_abs, sq_abs]
    simp [f, Fin.prod_univ_succ]
    ring
  change (∫ x : ScalarMomentum, ∏ i, f i (x i)) = ∫ x : Fin 4 → ℝ, ∏ i, f i (x i) at hp
  rw [← he, hp]
  change (∫ x : Fin 4 → ℝ, ∏ i, f i (x i) ∂Measure.pi (fun _ => volume)) = _
  rw [integral_fintype_prod_eq_prod f]
  simp only [f, Fin.prod_univ_succ, ↓reduceIte, Fin.succ_ne_zero, Finset.univ_unique, Finset.prod_singleton]
  rw [stable_gaussian_sixth_real]
  simp only [show (fun x : ℝ => exp (-(x ^ 2))) = (fun x : ℝ => exp (-1 * x ^ 2)) by
    funext x; rw [neg_one_mul]]
  rw [integral_gaussian, div_one]
  nlinarith [Real.sq_sqrt Real.pi_nonneg]

/-- Exact area-weighted sixth coordinate moment on the actual unit 3-sphere. -/
theorem stable_unit_sphere_coordinate_sixth :
    (∫ n : sphere (0 : ScalarMomentum) 1, (n.1 0) ^ 6 ∂(volume : Measure ScalarMomentum).toSphere) =
      5 * π ^ 2 / 32 := by
  have h := stable_weighted_polar_integral 6 (fun r => exp (-(r ^ 2)))
  rw [stable_gaussian_sixth_four] at h
  have hrad := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 9) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.rpow_two, show (9 : ℝ) = (9 : ℕ) by norm_num, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial] at hrad
  have hrad' : (∫ r in Ioi (0 : ℝ), r ^ (6 + 3 : ℕ) * exp (-(r ^ 2))) = 12 := by
    simpa only [Real.rpow_two, neg_one_mul, show (9 : ℝ) = (9 : ℕ) by norm_num,
      Real.rpow_natCast] using hrad
  rw [hrad'] at h
  linarith

/-- The exact coefficient of the borderline radial logarithm. -/
theorem stable_annular_sixth_log {R L : ℝ} (hR : 0 < R) (hRL : R ≤ L) :
    (∫ x : ScalarMomentum, (Ioc R L).indicator
      (fun r => (x 0) ^ 6 / r ^ 10) ‖x‖) =
      (5 * π ^ 2 / 32) * log (L / R) := by
  have h := stable_weighted_polar_integral 6 ((Ioc R L).indicator (fun r => (r ^ 10)⁻¹))
  rw [stable_unit_sphere_coordinate_sixth] at h
  have hL : (fun x : ScalarMomentum => (Ioc R L).indicator (fun r => (x 0) ^ 6 / r ^ 10) ‖x‖) =
      fun x : ScalarMomentum => (x 0) ^ 6 * (Ioc R L).indicator (fun r => (r ^ 10)⁻¹) ‖x‖ := by
    funext x
    by_cases hx : ‖x‖ ∈ Ioc R L
    · simp [hx, div_eq_mul_inv]
    · simp [hx]
  rw [hL, h]
  congr 1
  calc
    _ = ∫ r : ℝ in Ioi 0, (Ioc R L).indicator (fun r => r⁻¹) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      by_cases hmem : r ∈ Ioc R L
      · simp only [Set.indicator_of_mem hmem]
        have hrn : r ≠ 0 := (show 0 < r from hr).ne'
        field_simp
      · simp [hmem]
    _ = ∫ r : ℝ in Ioc R L, r⁻¹ := by
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        show Ioc R L ∩ Ioi (0 : ℝ) = Ioc R L from
          Set.inter_eq_left.mpr (fun _ hx => hR.trans hx.1)]
    _ = log (L / R) := by
      rw [← intervalIntegral.integral_of_le hRL]
      exact integral_inv (by rw [uIcc_of_le hRL]; exact fun h => hR.not_ge h.1)

end UV
