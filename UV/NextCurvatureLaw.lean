import UV.NextCurvatureGaussian
import Mathlib.Probability.ProductMeasure

/-! The common Gaussian preparation for the mean-zero torus on the fixed
sector plane. Coordinates are independent real Gaussian variables at each
signed-mode, field, and orthonormal color slot. A single product preparation
works at all depths and all spherical cutoffs. -/

noncomputable section

open MeasureTheory Real Filter
open scoped BigOperators ENNReal Topology

namespace UV.NextCurvatureLaw

open UV.FurtherCurvatureShell UV.FurtherCurvatureLine
open UV.RevisionCurvatureDeterminant (latticeFrequency)
open UV.NextCurvatureGaussian

abbrev MeanZeroMode := {k : TorusMode // k ≠ 0}
abbrev ModeSlot (n : ℕ) := MeanZeroMode × (Fin 2 × Fin n)

private instance baseGaussian_probability : IsProbabilityMeasure sourceGaussianBase where
  measure_univ := by
    let f (x : ℝ) := exp (-(x ^ 2)) / sqrt π
    have hi : Integrable f := by
      simpa [f] using (integrable_exp_neg_mul_sq (b := 1) one_pos).div_const (sqrt π)
    have hn : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ f x :=
      Eventually.of_forall fun _ => div_nonneg (exp_nonneg _) (sqrt_nonneg _)
    have hf : (∫ x : ℝ, f x) = 1 := by
      unfold f
      rw [integral_div]
      have hg : (∫ x : ℝ, exp (-(x ^ 2))) = sqrt π := by
        simpa using integral_gaussian (1 : ℝ)
      rw [hg, div_self (sqrt_pos.mpr pi_pos).ne']
    unfold sourceGaussianBase
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    change (∫⁻ x : ℝ, ENNReal.ofReal (f x)) = 1
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn, hf, ENNReal.ofReal_one]

private instance sourceGaussian_probability (v : ℝ) : IsProbabilityMeasure (sourceGaussian v) :=
  Measure.isProbabilityMeasure_map (by fun_prop : Measurable fun x : ℝ => sqrt (2*v) * x).aemeasurable

def commonGaussian (n : ℕ) : Measure (ModeSlot n → ℝ) :=
  Measure.infinitePi (fun _ => sourceGaussianBase)

instance commonGaussian_probability (n : ℕ) : IsProbabilityMeasure (commonGaussian n) := by
  unfold commonGaussian
  infer_instance

def depthGaussian (n : ℕ) (ℓ : ℝ) : Measure (ModeSlot n → ℝ) :=
  Measure.infinitePi (fun i => sourceGaussian (curvatureCovariance ℓ i.1))

instance depthGaussian_probability (n : ℕ) (ℓ : ℝ) :
    IsProbabilityMeasure (depthGaussian n ℓ) := by
  unfold depthGaussian
  infer_instance

def depthRescale {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ) (i : ModeSlot n) : ℝ :=
  sqrt (2 * curvatureCovariance ℓ i.1) * X i

/-- Every field and cutoff uses a restriction of the same standard product.
Rescaling its actual coordinates gives the product with the kinetic variances. -/
theorem commonGaussian_map_depthRescale (n : ℕ) (ℓ : ℝ) :
    (commonGaussian n).map (depthRescale ℓ) = depthGaussian n ℓ := by
  exact Measure.infinitePi_map_pi
    (μ := fun _ : ModeSlot n => sourceGaussianBase)
    (f := fun i x => sqrt (2 * curvatureCovariance ℓ i.1) * x)
    (fun _ => by fun_prop)

theorem depthRescale_jointly_measurable (n : ℕ) :
    Measurable (fun p : ℝ × (ModeSlot n → ℝ) => depthRescale p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  unfold depthRescale curvatureCovariance
  fun_prop

theorem depthGaussian_cylinder_marginal (n : ℕ) (ℓ : ℝ) (s : Finset (ModeSlot n)) :
    (depthGaussian n ℓ).map s.restrict =
      Measure.pi (fun i : s => sourceGaussian (curvatureCovariance ℓ i.1.1)) :=
  Measure.infinitePi_map_restrict _

private theorem curvatureCovariance_nonneg (ℓ : ℝ) (k : TorusMode) :
    0 ≤ curvatureCovariance ℓ k := by
  unfold curvatureCovariance
  positivity

theorem mode_covariance_le_boundary (ℓ : ℝ) (k : MeanZeroMode) :
    curvatureCovariance ℓ k ≤ (latticeFrequency k ^ 2)⁻¹ := by
  have hr : 0 < latticeFrequency k := (Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero (latticeHeight_ne_zero k.2))).trans_le
    (latticeHeight_le_latticeFrequency k)
  unfold curvatureCovariance
  apply inv_anti₀ (sq_pos_of_pos hr)
  exact le_mul_of_one_le_right (by positivity) (by linarith [exp_nonneg (-2*ℓ*latticeFrequency k)])

theorem mode_second_moment (n : ℕ) (ℓ : ℝ) (i : ModeSlot n) :
    (∫ X, X i ^ 2 ∂depthGaussian n ℓ) = curvatureCovariance ℓ i.1 := by
  have h := measurePreserving_eval_infinitePi
    (μ := fun j : ModeSlot n => sourceGaussian (curvatureCovariance ℓ j.1)) i
  calc
    _ = ∫ x : ℝ, x ^ 2 ∂sourceGaussian (curvatureCovariance ℓ i.1) := by
      have hs : Measurable fun x : ℝ => x ^ 2 := by fun_prop
      rw [← h.map_eq, integral_map h.measurable.aemeasurable hs.aestronglyMeasurable]
      rfl
    _ = _ := (sourceGaussian_even_moments (curvatureCovariance_nonneg ℓ i.1)).1

theorem mode_powers_integrable (n : ℕ) (ℓ : ℝ) (i : ModeSlot n) (q : ℕ) :
    Integrable (fun X => X i ^ q) (depthGaussian n ℓ) := by
  have h := measurePreserving_eval_infinitePi
    (μ := fun j : ModeSlot n => sourceGaussian (curvatureCovariance ℓ j.1)) i
  exact h.integrable_comp_of_integrable (sourceGaussian_power_integrable _ q)

/-- Transferring both endpoints of the same contraction gives the stated line, also
when the two endpoints belong to a single vertex. -/
theorem transferred_mode_second_moment (n : ℕ) (ℓ : ℝ) (i : ModeSlot n) :
    (∫ X, (exp (-ℓ * latticeFrequency i.1) * X i) ^ 2 ∂depthGaussian n ℓ) =
      curvatureLine ℓ i.1 := by
  simp_rw [mul_pow, integral_const_mul, mode_second_moment, curvatureLine, ← exp_nat_mul]
  congr 2
  ring

end UV.NextCurvatureLaw
