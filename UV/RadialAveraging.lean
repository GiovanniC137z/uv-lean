import UV.AnalyticScalar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Actual four-dimensional isotropic averages, derived from coordinate
sign changes and coordinate permutations preserving Euclidean volume. -/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators

namespace UV

def radialCoordinateSignChange (i : Fin 4) : ScalarMomentum ≃ₗᵢ[ℝ] ScalarMomentum :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j : Fin 4 => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

def radialCoordinateSwap (i j : Fin 4) : ScalarMomentum ≃ₗᵢ[ℝ] ScalarMomentum :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

theorem radialCoordinateSignChange_apply (i j : Fin 4) (q : ScalarMomentum) :
    radialCoordinateSignChange i q j = if j = i then -q j else q j := by
  unfold radialCoordinateSignChange
  rw [LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> rfl

theorem radialCoordinateSwap_apply (i j l : Fin 4) (q : ScalarMomentum) :
    radialCoordinateSwap i j q l = q (Equiv.swap i j l) := rfl

theorem radial_coordinate_product_integrable {g : ℝ → ℝ} (hg : Measurable g)
    (hw : Integrable (fun q : ScalarMomentum => ‖q‖ ^ 2 * g (‖q‖ ^ 2)))
    (i j : Fin 4) : Integrable (fun q : ScalarMomentum => q i * q j * g (‖q‖ ^ 2)) := by
  apply hw.norm.mono'
  · apply Measurable.aestronglyMeasurable
    exact ((by fun_prop : Continuous (fun q : ScalarMomentum => q i * q j)).measurable).mul
      (hg.comp (continuous_norm.pow 2).measurable)
  · filter_upwards with q
    have hi : ‖q i‖ ≤ ‖q‖ := PiLp.norm_apply_le q i
    have hj : ‖q j‖ ≤ ‖q‖ := PiLp.norm_apply_le q j
    simp only [norm_mul, norm_pow, Real.norm_of_nonneg (norm_nonneg q)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [pow_two] using mul_le_mul hi hj (norm_nonneg _) (norm_nonneg q)

theorem radial_coordinate_off_diagonal_integral (g : ℝ → ℝ) {i j : Fin 4} (hij : i ≠ j) :
    (∫ q : ScalarMomentum, q i * q j * g (‖q‖ ^ 2)) = 0 := by
  let R := radialCoordinateSignChange i
  have hchange := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
    (fun q : ScalarMomentum => q i * q j * g (‖q‖ ^ 2))
  have hpoint : (fun q : ScalarMomentum => R q i * R q j * g (‖R q‖ ^ 2)) =
      (fun q : ScalarMomentum => -(q i * q j * g (‖q‖ ^ 2))) := by
    funext q
    rw [R.norm_map]
    dsimp [R]
    rw [radialCoordinateSignChange_apply, radialCoordinateSignChange_apply,
      if_pos rfl, if_neg hij.symm]
    ring
  rw [hpoint, integral_neg] at hchange
  linarith

theorem radial_coordinate_diagonal_integrals_equal (g : ℝ → ℝ) (i j : Fin 4) :
    (∫ q : ScalarMomentum, q i * q i * g (‖q‖ ^ 2)) =
      ∫ q : ScalarMomentum, q j * q j * g (‖q‖ ^ 2) := by
  let R := radialCoordinateSwap i j
  have hchange := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
    (fun q : ScalarMomentum => q i * q i * g (‖q‖ ^ 2))
  have hpoint : (fun q : ScalarMomentum => R q i * R q i * g (‖R q‖ ^ 2)) =
      (fun q : ScalarMomentum => q j * q j * g (‖q‖ ^ 2)) := by
    funext q
    rw [R.norm_map]
    dsimp [R]
    rw [radialCoordinateSwap_apply, Equiv.swap_apply_left]
  rw [hpoint] at hchange
  exact hchange.symm

theorem radial_coordinate_diagonal_integral {g : ℝ → ℝ} (hg : Measurable g)
    (hw : Integrable (fun q : ScalarMomentum => ‖q‖ ^ 2 * g (‖q‖ ^ 2))) (i : Fin 4) :
    (∫ q : ScalarMomentum, q i * q i * g (‖q‖ ^ 2)) =
      (1 / 4 : ℝ) * ∫ q : ScalarMomentum, ‖q‖ ^ 2 * g (‖q‖ ^ 2) := by
  have hpoint : (fun q : ScalarMomentum => ‖q‖ ^ 2 * g (‖q‖ ^ 2)) =
      (fun q : ScalarMomentum => ∑ j : Fin 4, q j * q j * g (‖q‖ ^ 2)) := by
    funext q
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.norm_eq_abs, sq_abs, pow_two]
  have htotal : (∫ q : ScalarMomentum, ‖q‖ ^ 2 * g (‖q‖ ^ 2)) =
      ∑ j : Fin 4, ∫ q : ScalarMomentum, q j * q j * g (‖q‖ ^ 2) := by
    rw [hpoint, integral_finset_sum _ (fun j _ => radial_coordinate_product_integrable hg hw j j)]
  have hdiag (j : Fin 4) := radial_coordinate_diagonal_integrals_equal g j i
  simp_rw [hdiag] at htotal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at htotal
  linarith

/-- The four-dimensional isotropic average with its actual integrability
conclusion. The radial weight may be signed. -/
theorem radial_coordinate_average {g : ℝ → ℝ} (hg : Measurable g)
    (hw : Integrable (fun q : ScalarMomentum => ‖q‖ ^ 2 * g (‖q‖ ^ 2))) (i j : Fin 4) :
    Integrable (fun q : ScalarMomentum => q i * q j * g (‖q‖ ^ 2)) ∧
      (∫ q : ScalarMomentum, q i * q j * g (‖q‖ ^ 2)) =
        if i = j then (1 / 4 : ℝ) * ∫ q : ScalarMomentum, ‖q‖ ^ 2 * g (‖q‖ ^ 2) else 0 := by
  refine ⟨radial_coordinate_product_integrable hg hw i j, ?_⟩
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact radial_coordinate_diagonal_integral hg hw i
  · rw [if_neg hij]
    exact radial_coordinate_off_diagonal_integral g hij

end UV
