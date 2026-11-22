import UV.ContinueCarrierConeBounds
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod

/-! Spatial isotropy in the actual intrinsic four-momentum measure. Coordinate
permutations and individual sign flips are linear isometries of the normed
spatial chart, hence preserve Lebesgue measure. Fubini transfers the identities
to jointly integrable tensor tests on a selected sector plane. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Filter

/-- Exchange of two actual intrinsic spatial coordinates. -/
def coneSpatialSwap (i j : Fin 3) : Spatial ≃ₗᵢ[ℝ] Spatial :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

@[simp] theorem coneSpatialSwap_apply (i j k : Fin 3) (p : Spatial) :
    coneSpatialSwap i j p k = p (Equiv.swap i j k) := by
  change p ((Equiv.swap i j).symm k) = _
  rw [Equiv.symm_swap]

/-- A spatial coordinate reflection, leaving the other two slots fixed. -/
def coneSpatialFlip (j : Fin 3) : Spatial ≃ₗᵢ[ℝ] Spatial :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun k : Fin 3 =>
    if k = j then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] theorem coneSpatialFlip_apply (j k : Fin 3) (p : Spatial) :
    coneSpatialFlip j p k = if k = j then -p k else p k := by
  unfold coneSpatialFlip
  rw [LinearIsometryEquiv.piLpCongrRight_apply]
  by_cases h : k = j
  · subst k
    simp
  · simp [h]

@[simp] theorem coneSpatialSwap_norm (i j : Fin 3) (p : Spatial) :
    ‖coneSpatialSwap i j p‖ = ‖p‖ := (coneSpatialSwap i j).norm_map p

@[simp] theorem coneSpatialFlip_norm (j : Fin 3) (p : Spatial) :
    ‖coneSpatialFlip j p‖ = ‖p‖ := (coneSpatialFlip j).norm_map p

theorem coneSpatialSwap_measurePreserving (i j : Fin 3) :
    MeasurePreserving (coneSpatialSwap i j) volume volume :=
  (coneSpatialSwap i j).measurePreserving

theorem coneSpatialFlip_measurePreserving (j : Fin 3) :
    MeasurePreserving (coneSpatialFlip j) volume volume :=
  (coneSpatialFlip j).measurePreserving

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Permutation invariance of the spatial integral at each fixed carrier
frequency. Integrability is supplied in the joint statements below. -/
theorem cone_spatial_diagonal_integral_eq (G : ℝ × ℝ → F) (x : ℝ) (i j : Fin 3) :
    (∫ p : Spatial, p i ^ 2 • G (x, ‖p‖)) =
      ∫ p : Spatial, p j ^ 2 • G (x, ‖p‖) := by
  have H := (coneSpatialSwap_measurePreserving i j).integral_comp
    (coneSpatialSwap i j).toHomeomorph.measurableEmbedding
    (fun p : Spatial => p i ^ 2 • G (x, ‖p‖))
  calc
    _ = ∫ p : Spatial, coneSpatialSwap i j p i ^ 2 • G (x, ‖coneSpatialSwap i j p‖) := H.symm
    _ = _ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun p => ?_
      dsimp only
      rw [coneSpatialSwap_norm, coneSpatialSwap_apply, Equiv.swap_apply_left]

/-- Every mixed spatial numerator is odd under one actual coordinate flip. -/
theorem cone_spatial_offDiagonal_integral (G : ℝ × ℝ → F) (x : ℝ)
    (i j : Fin 3) (hij : i ≠ j) :
    (∫ p : Spatial, (p i * p j) • G (x, ‖p‖)) = 0 := by
  have H := (coneSpatialFlip_measurePreserving i).integral_comp
    (coneSpatialFlip i).toHomeomorph.measurableEmbedding
    (fun p : Spatial => (p i * p j) • G (x, ‖p‖))
  have hji : j ≠ i := hij.symm
  simp [hji] at H
  rw [integral_neg] at H
  exact (neg_eq_self ℝ F).mp H

/-- A temporal-spatial numerator is odd under the reflected spatial slot. -/
theorem cone_time_spatial_integral (G : ℝ × ℝ → F) (x : ℝ) (j : Fin 3) :
    (∫ p : Spatial, (x * p j) • G (x, ‖p‖)) = 0 := by
  have H := (coneSpatialFlip_measurePreserving j).integral_comp
    (coneSpatialFlip j).toHomeomorph.measurableEmbedding
    (fun p : Spatial => (x * p j) • G (x, ‖p‖))
  simp at H
  rw [integral_neg] at H
  exact (neg_eq_self ℝ F).mp H

private theorem spatial_coordinate_sq_le (p : Spatial) (j : Fin 3) : p j ^ 2 ≤ ‖p‖ ^ 2 := by
  have H := PiLp.norm_apply_le p j
  simpa only [Real.norm_eq_abs, sq_abs] using
    (sq_le_sq₀ (norm_nonneg (p j)) (norm_nonneg p)).mpr H

/-- Joint absolute convergence of the radial spatial second moment controls
all spatial diagonal and mixed components. -/
theorem cone_spatial_diagonal_integrable {G : ℝ × ℝ → F}
    (hG : AEStronglyMeasurable (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)))
    (hI : Integrable (fun q : ℝ × Spatial => ‖q.2‖ ^ 2 • G (q.1, ‖q.2‖))) (j : Fin 3) :
    Integrable (fun q : ℝ × Spatial => q.2 j ^ 2 • G (q.1, ‖q.2‖)) := by
  apply hI.norm.mono'
  · have hC : Continuous (fun q : ℝ × Spatial => q.2 j ^ 2) := by fun_prop
    exact hC.aestronglyMeasurable.smul hG
  · refine Eventually.of_forall fun q => ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right (spatial_coordinate_sq_le q.2 j) (norm_nonneg _)

theorem cone_spatial_offDiagonal_integrable {G : ℝ × ℝ → F}
    (hG : AEStronglyMeasurable (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)))
    (hI : Integrable (fun q : ℝ × Spatial => ‖q.2‖ ^ 2 • G (q.1, ‖q.2‖))) (i j : Fin 3) :
    Integrable (fun q : ℝ × Spatial => (q.2 i * q.2 j) • G (q.1, ‖q.2‖)) := by
  apply hI.norm.mono'
  · have hC : Continuous (fun q : ℝ × Spatial => q.2 i * q.2 j) := by fun_prop
    exact hC.aestronglyMeasurable.smul hG
  · refine Eventually.of_forall fun q => ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_mul]
    have hi := PiLp.norm_apply_le q.2 i
    have hj := PiLp.norm_apply_le q.2 j
    simp only [Real.norm_eq_abs] at hi hj
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [pow_two] using mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)

/-- A continuous compact test in actual four-momentum makes every polynomial
numerator below jointly integrable, before any use of Fubini. -/
theorem cone_radial_polynomial_integrable {G : ℝ × ℝ → F}
    (hG : Continuous (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)))
    (hs : HasCompactSupport (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)))
    {P : ℝ × Spatial → ℝ} (hP : Continuous P) :
    Integrable (fun q : ℝ × Spatial => P q • G (q.1, ‖q.2‖)) :=
  (hP.smul hG).integrable_of_hasCompactSupport hs.smul_left

/-- Actual four-momentum diagonal integral, with its exact spatial factor 1/3. -/
theorem cone_joint_spatial_diagonal {G : ℝ × ℝ → F}
    (hG : AEStronglyMeasurable (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)))
    (hI : Integrable (fun q : ℝ × Spatial => ‖q.2‖ ^ 2 • G (q.1, ‖q.2‖))) (j : Fin 3) :
    (∫ q : ℝ × Spatial, q.2 j ^ 2 • G (q.1, ‖q.2‖)) =
      (1 / 3 : ℝ) • ∫ q : ℝ × Spatial, ‖q.2‖ ^ 2 • G (q.1, ‖q.2‖) := by
  have hEq (i : Fin 3) :
      (∫ q : ℝ × Spatial, q.2 i ^ 2 • G (q.1, ‖q.2‖)) =
        ∫ q : ℝ × Spatial, q.2 j ^ 2 • G (q.1, ‖q.2‖) := by
    calc
      _ = ∫ x : ℝ, ∫ p : Spatial, p i ^ 2 • G (x, ‖p‖) :=
        integral_prod _ (cone_spatial_diagonal_integrable hG hI i)
      _ = ∫ x : ℝ, ∫ p : Spatial, p j ^ 2 • G (x, ‖p‖) :=
        integral_congr_ae (Eventually.of_forall fun x => cone_spatial_diagonal_integral_eq G x i j)
      _ = _ := (integral_prod _ (cone_spatial_diagonal_integrable hG hI j)).symm
  have hSum :
      (∫ q : ℝ × Spatial, ‖q.2‖ ^ 2 • G (q.1, ‖q.2‖)) =
        (3 : ℝ) • ∫ q : ℝ × Spatial, q.2 j ^ 2 • G (q.1, ‖q.2‖) := by
    calc
      _ = ∫ q : ℝ × Spatial, ∑ i : Fin 3, q.2 i ^ 2 • G (q.1, ‖q.2‖) := by
        apply integral_congr_ae
        refine Eventually.of_forall fun q => ?_
        dsimp only
        rw [EuclideanSpace.norm_sq_eq, Finset.sum_smul]
        simp only [Real.norm_eq_abs, sq_abs]
      _ = ∑ i : Fin 3, ∫ q : ℝ × Spatial, q.2 i ^ 2 • G (q.1, ‖q.2‖) :=
        integral_finset_sum _ fun i _ => cone_spatial_diagonal_integrable hG hI i
      _ = ∑ _i : Fin 3, ∫ q : ℝ × Spatial, q.2 j ^ 2 • G (q.1, ‖q.2‖) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hEq i
      _ = _ := by simp [← Nat.cast_smul_eq_nsmul ℝ]
  rw [hSum, smul_smul]
  norm_num

/-- All actual spatial mixed components cancel in the joint measure. -/
theorem cone_joint_spatial_offDiagonal {G : ℝ × ℝ → F}
    (hG : AEStronglyMeasurable (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)))
    (hI : Integrable (fun q : ℝ × Spatial => ‖q.2‖ ^ 2 • G (q.1, ‖q.2‖)))
    (i j : Fin 3) (hij : i ≠ j) :
    (∫ q : ℝ × Spatial, (q.2 i * q.2 j) • G (q.1, ‖q.2‖)) = 0 := by
  calc
    _ = ∫ x : ℝ, ∫ p : Spatial, (p i * p j) • G (x, ‖p‖) :=
      integral_prod _ (cone_spatial_offDiagonal_integrable hG hI i j)
    _ = 0 := by simp_rw [cone_spatial_offDiagonal_integral G _ i j hij]; exact integral_zero _ _

/-- The temporal-spatial components cancel whenever the actual joint integral
is absolutely convergent; the temporal dependence of G is unrestricted. -/
theorem cone_joint_time_spatial {G : ℝ × ℝ → F}
    (j : Fin 3) (hI : Integrable (fun q : ℝ × Spatial => (q.1 * q.2 j) • G (q.1, ‖q.2‖))) :
    (∫ q : ℝ × Spatial, (q.1 * q.2 j) • G (q.1, ‖q.2‖)) = 0 := by
  calc
    _ = ∫ x : ℝ, ∫ p : Spatial, (x * p j) • G (x, ‖p‖) := integral_prod _ hI
    _ = 0 := by simp_rw [cone_time_spatial_integral G _ j]; exact integral_zero _ _

/-- The spatial tensor of an actual continuous compact radial-in-space test is
exactly diagonal, with each diagonal entry equal to one third of its trace. -/
theorem cone_compact_spatial_tensor {G : ℝ × ℝ → F}
    (hG : Continuous (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)))
    (hs : HasCompactSupport (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)))
    (i j : Fin 3) :
    (∫ q : ℝ × Spatial, (q.2 i * q.2 j) • G (q.1, ‖q.2‖)) =
      if i = j then (1 / 3 : ℝ) •
        (∫ q : ℝ × Spatial, ‖q.2‖ ^ 2 • G (q.1, ‖q.2‖)) else 0 := by
  have hi : Integrable (fun q : ℝ × Spatial => ‖q.2‖ ^ 2 • G (q.1, ‖q.2‖)) :=
    cone_radial_polynomial_integrable hG hs (by fun_prop)
  by_cases hij : i = j
  · subst i
    simp only [ite_true, ← pow_two]
    exact cone_joint_spatial_diagonal hG.aestronglyMeasurable hi j
  · rw [if_neg hij]
    exact cone_joint_spatial_offDiagonal hG.aestronglyMeasurable hi i j hij

/-- All temporal-spatial entries of the same actual compact test vanish. -/
theorem cone_compact_time_spatial {G : ℝ × ℝ → F}
    (hG : Continuous (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)))
    (hs : HasCompactSupport (fun q : ℝ × Spatial => G (q.1, ‖q.2‖))) (j : Fin 3) :
    (∫ q : ℝ × Spatial, (q.1 * q.2 j) • G (q.1, ‖q.2‖)) = 0 :=
  cone_joint_time_spatial j (cone_radial_polynomial_integrable hG hs (by fun_prop))

end UV.SectorPlane
