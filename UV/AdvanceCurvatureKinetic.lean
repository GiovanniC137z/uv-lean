import UV.AdvanceCurvatureLines
import UV.AdvanceCurvatureAction

/-! Gradient and kinetic normalization of the literal signed torus modes.
Directional derivatives use the actual four unit vectors of the sector. -/

noncomputable section

open MeasureTheory Real
open scoped BigOperators

namespace UV.AdvanceCurvatureKinetic

open UV.ExtendCurvaturePotential UV.AdvanceCurvatureLines UV.ContinueCurvatureModes
open UV.ResumeCurvatureSmooth UV.ResumeCurvatureDistributions UV.NextCurvatureLaw
open UV.FurtherCurvatureShell UV.NextCurvatureGaussian UV.AdvanceCurvatureAction
open UV.RevisionCurvatureDeterminant (latticeFrequency)

private theorem phase_unitCoordinate (k : TorusMode) (j : Fin 4) :
    phaseLinear k (unitCoordinate j) = (k j : ℝ) := by
  rw [phaseLinear_apply]
  classical
  simp [unitCoordinate, EuclideanSpace.single_apply, mul_ite]

/-- Differentiation along the unit tangent vector sends each signed real
mode to its opposite with multiplier -k_j. -/
theorem fderiv_modeOnCover_unit (k : MeanZeroMode) (j : Fin 4) (x : Cover) :
    fderiv ℝ (modeOnCover k) x (unitCoordinate j) =
      -(k.1 j : ℝ) * realTorusMode (oppositeMode k) (coverPoint x) := by
  rw [realTorusMode_cover_eq]
  unfold modeOnCover
  rw [opposite_firstActive]
  change fderiv ℝ (if 0 < k.1 (firstActive k) then fun y => sqrt 2 • cos (phaseLinear k y)
      else fun y => sqrt 2 • sin (phaseLinear (-k.1) y)) x (unitCoordinate j) =
    -(k.1 j : ℝ) * (if 0 < -k.1 (firstActive k) then fun y => sqrt 2 • cos (phaseLinear (-k.1) y)
      else fun y => sqrt 2 • sin (phaseLinear (-(-k.1)) y)) x
  rcases lt_or_gt_of_ne (firstActive_value_ne_zero k) with hk | hk
  · rw [if_neg (not_lt_of_ge hk.le), if_pos (neg_pos.mpr hk)]
    have hh := ((phaseLinear (-k.1)).hasFDerivAt (x := x)).sin.const_smul (sqrt 2)
    change fderiv ℝ (sqrt 2 • fun y : Cover => sin (phaseLinear (-k.1) y)) x (unitCoordinate j) = _
    rw [hh.fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      phase_unitCoordinate, Pi.neg_apply, Int.cast_neg]
    simp only [smul_eq_mul]
    ring
  · rw [if_pos hk, if_neg (not_lt_of_ge (neg_nonpos.mpr hk.le)), neg_neg]
    have hh := ((phaseLinear k).hasFDerivAt (x := x)).cos.const_smul (sqrt 2)
    change fderiv ℝ (sqrt 2 • fun y : Cover => cos (phaseLinear k y)) x (unitCoordinate j) = _
    rw [hh.fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, phase_unitCoordinate]
    simp only [smul_eq_mul]
    ring

def torusFourierSum (s : Finset MeanZeroMode) (w : MeanZeroMode → ℝ) : ContinuousField :=
  ∑ k ∈ s, w k • realTorusMode k

def torusFourierGradient (s : Finset MeanZeroMode) (w : MeanZeroMode → ℝ) (j : Fin 4) : ContinuousField :=
  ∑ k ∈ s, (w k * -(k.1 j : ℝ)) • realTorusMode (oppositeMode k)

/-- The continuous gradient fields are the derivatives of the actual
periodic finite series on the Euclidean cover. -/
theorem torusFourierGradient_on_cover (s : Finset MeanZeroMode) (w : MeanZeroMode → ℝ)
    (j : Fin 4) (x : Cover) :
    fderiv ℝ (fun y => torusFourierSum s w (coverPoint y)) x (unitCoordinate j) =
      torusFourierGradient s w j (coverPoint x) := by
  have hm (k : MeanZeroMode) : DifferentiableAt ℝ (modeOnCover k) x :=
    ((modeOnCover_contDiff k 1).differentiable (by decide)) x
  simp only [torusFourierSum, torusFourierGradient, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, realTorusMode_cover_eq]
  rw [fderiv_fun_sum (fun k _ => (hm k).const_mul _)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_const_mul (hm k), ContinuousLinearMap.smul_apply, smul_eq_mul, fderiv_modeOnCover_unit,
    realTorusMode_cover_eq]
  ring

private theorem opposite_injective : Function.Injective oppositeMode :=
  (show Function.Involutive oppositeMode from oppositeMode_oppositeMode).injective

private theorem gradient_product_integral (w : MeanZeroMode → ℝ) (j : Fin 4) (k l : MeanZeroMode) :
    normalizedIntegral (((w k * -(k.1 j : ℝ)) • realTorusMode (oppositeMode k)) *
      ((w l * -(l.1 j : ℝ)) • realTorusMode (oppositeMode l))) =
      if k = l then (w k * (k.1 j : ℝ))^2 else 0 := by
  classical
  change (∫ x, (((w k * -(k.1 j : ℝ)) • realTorusMode (oppositeMode k)) *
    ((w l * -(l.1 j : ℝ)) • realTorusMode (oppositeMode l))) x ∂normalizedTorusVolume) = _
  simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
  have he (x : Torus) : (w k * -(k.1 j : ℝ) * realTorusMode (oppositeMode k) x) *
      (w l * -(l.1 j : ℝ) * realTorusMode (oppositeMode l) x) =
        ((w k * -(k.1 j : ℝ)) * (w l * -(l.1 j : ℝ))) *
          (realTorusMode (oppositeMode k) x * realTorusMode (oppositeMode l) x) := by ring
  simp_rw [he, integral_const_mul, real_mode_integral_orthonormal, opposite_injective.eq_iff]
  by_cases h : k = l
  · subst l
    simp only [if_true, mul_one]
    ring
  · simp [h]

private theorem gradient_norm_at_axis (s : Finset MeanZeroMode) (w : MeanZeroMode → ℝ) (j : Fin 4) :
    normalizedIntegral (torusFourierGradient s w j ^ 2) = ∑ k ∈ s, (w k * (k.1 j : ℝ))^2 := by
  classical
  simp only [torusFourierGradient, pow_two, Finset.sum_mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [gradient_product_integral, pow_two]
  rw [Finset.sum_eq_single_of_mem k hk]
  · simp
  · intro l hl hne
    simp [Ne.symm hne]

/-- The integrated squared four-gradient is exactly the diagonal
frequency-square sum of the normalized signed elementary coordinates. -/
theorem gradient_kinetic_diagonal (s : Finset MeanZeroMode) (w : MeanZeroMode → ℝ) :
    (∑ j : Fin 4, normalizedIntegral (torusFourierGradient s w j ^ 2)) =
      ∑ k ∈ s, latticeFrequency k ^ 2 * w k ^ 2 := by
  simp_rw [gradient_norm_at_axis, mul_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, latticeFrequency, sq_sqrt (by positivity), mul_comm]

/-- The boundary gradient and the same harmonically transferred gradient
supply exactly the two terms of the diagonal kinetic coefficient. -/
theorem copied_gradient_kinetic_diagonal (s : Finset MeanZeroMode) (ℓ : ℝ) (w : MeanZeroMode → ℝ) :
    (1/2 : ℝ) * (∑ j : Fin 4, normalizedIntegral (torusFourierGradient s w j ^ 2) +
      ∑ j : Fin 4, normalizedIntegral
        (torusFourierGradient s (fun k => exp (-ℓ * latticeFrequency k) * w k) j ^ 2)) =
      ∑ k ∈ s, (transferredKinetic ℓ k / 2) * w k ^ 2 := by
  rw [gradient_kinetic_diagonal, gradient_kinetic_diagonal, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold transferredKinetic boundaryKinetic
  rw [mul_pow, ← Real.exp_nat_mul]
  push_cast
  rw [show (2 : ℝ) * (-ℓ * latticeFrequency k) = -2 * ℓ * latticeFrequency k by ring]
  ring

def sphericalBoundaryGradient {n : ℕ} (Λ : ℝ) (Y : ModeSlot n → ℝ) (a : Fin 2)
    (j : Fin 4) (c : Fin n) : ContinuousField :=
  torusFourierGradient (retainedModes Λ) (fun k => Y (k,(a,c))) j

def sphericalCopiedGradient {n : ℕ} (Λ ℓ : ℝ) (Y : ModeSlot n → ℝ) (a : Fin 2)
    (j : Fin 4) (c : Fin n) : ContinuousField :=
  torusFourierGradient (retainedModes Λ) (fun k => exp (-ℓ * latticeFrequency k) * Y (k,(a,c))) j

/-- The four torus gradient terms of the source action give the actual
finite diagonal kinetic action used in the Gaussian determinant. -/
theorem spherical_sector_kinetic_action {n : ℕ} (Λ ℓ : ℝ) (Y : ModeSlot n → ℝ) :
    normalizedIntegral (kineticDensity (sphericalBoundaryGradient Λ Y 0) (sphericalBoundaryGradient Λ Y 1)
      (sphericalCopiedGradient Λ ℓ Y 0) (sphericalCopiedGradient Λ ℓ Y 1)) =
      kineticAction (transferredKinetic ℓ) (fun i : KineticSlot n (sphericalModes Λ) =>
        Y (⟨i.1.1, (mem_sphericalModes.mp i.1.2).1⟩, i.2)) := by
  let r := retainedModes Λ
  let D (a : Fin 2) (c : Fin n) := (1/2 : ℝ) *
    ((∑ j, normalizedIntegral (sphericalBoundaryGradient Λ Y a j c ^ 2)) +
      ∑ j, normalizedIntegral (sphericalCopiedGradient Λ ℓ Y a j c ^ 2))
  have hD (a : Fin 2) (c : Fin n) : D a c =
      ∑ k ∈ r, (transferredKinetic ℓ k / 2) * Y (k,(a,c)) ^ 2 :=
    copied_gradient_kinetic_diagonal r ℓ (fun k => Y (k,(a,c)))
  have hcomm (f : Fin 4 → Fin n → ℝ) : (∑ j, ∑ c, f j c) = ∑ c, ∑ j, f j c := Finset.sum_comm
  calc
    _ = ∑ a, ∑ c, D a c := by
      simp only [kineticDensity, D, map_smul, map_sum, map_add, smul_eq_mul, Fin.sum_univ_two,
        Finset.sum_add_distrib]
      simp_rw [hcomm]
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
      ring
    _ = ∑ a, ∑ c, ∑ k ∈ r, (transferredKinetic ℓ k / 2) * Y (k,(a,c)) ^ 2 := by simp_rw [hD]
    _ = ∑ k ∈ r, ∑ a, ∑ c, (transferredKinetic ℓ k / 2) * Y (k,(a,c)) ^ 2 := by
      let f (a : Fin 2) (c : Fin n) (k : MeanZeroMode) :=
        (transferredKinetic ℓ k / 2) * Y (k,(a,c)) ^ 2
      change (∑ a, ∑ c, ∑ k ∈ r, f a c k) = _
      calc
        _ = ∑ a, ∑ k ∈ r, ∑ c, f a c k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      classical
      let f (k : TorusMode) := if hk : k ≠ 0 then
        ∑ a, ∑ c, (transferredKinetic ℓ k / 2) * Y (⟨k, hk⟩,(a,c)) ^ 2 else 0
      have hsub : (∑ k ∈ r, f k.1) = ∑ k ∈ sphericalModes Λ, f k :=
        Finset.sum_subtype_of_mem f fun _ hk => (mem_sphericalModes.mp hk).1
      have h₁ : (∑ k ∈ r, ∑ a, ∑ c, (transferredKinetic ℓ k / 2) * Y (k,(a,c)) ^ 2) =
          ∑ k ∈ r, f k.1 := Finset.sum_congr rfl fun k _ => by simp [f, k.2]
      rw [h₁, hsub, ← Finset.sum_coe_sort]
      unfold kineticAction
      simp only [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun k _ => by simp [f, (mem_sphericalModes.mp k.2).1]

end UV.AdvanceCurvatureKinetic
