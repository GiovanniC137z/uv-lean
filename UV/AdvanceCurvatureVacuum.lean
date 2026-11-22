import UV.AdvanceCurvatureLines
import UV.AdvanceCurvatureWick
import UV.AdvanceCurvatureEnvelope
import UV.NextCurvatureFull

/-! The actual first vacuum coefficient on the fixed sector-plane torus.
The normalized Haar measure and the color basis keep their manuscript
normalization throughout the signed-mode contractions. -/

noncomputable section

open MeasureTheory Real Filter
open scoped BigOperators Topology

namespace UV.AdvanceCurvatureVacuum

open UV.ExtendCurvaturePotential UV.NextCurvatureLaw UV.NextCurvatureFourierSummability
open UV.FurtherCurvatureLine UV.AdvanceCurvatureLines UV.AdvanceCurvatureWick
open UV.AdvanceCurvatureEnvelope UV.FurtherCurvatureShell UV.FurtherCurvatureDeterminant
open UV.FurtherCurvatureGraph UV.NextCurvatureFull
open UV.RevisionCurvatureDeterminant (latticeFrequency)

/-- The squared norm of the source bracket, summed over both input colors
in the fixed orthonormal output basis. -/
def colorBracketSquare {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, (B c a b)^2

theorem colorBracketSquare_pos {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (hB : ∃ a b c, B c a b ≠ 0) : 0 < colorBracketSquare B := by
  obtain ⟨a,b,c,hc⟩ := hB
  have hc' : 0 < (B c a b)^2 := sq_pos_of_ne_zero hc
  have hca : (B c a b)^2 ≤ ∑ j, (B j a b)^2 :=
    Finset.single_le_sum (f := fun j => (B j a b)^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
  have hb : (∑ j, (B j a b)^2) ≤ ∑ j, ∑ i, (B i a j)^2 :=
    Finset.single_le_sum (f := fun j => ∑ i, (B i a j)^2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ b)
  have ha : (∑ j, ∑ i, (B i a j)^2) ≤ colorBracketSquare B :=
    Finset.single_le_sum (f := fun j => ∑ i, ∑ k, (B k j i)^2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
        (fun _ _ => sq_nonneg _))) (Finset.mem_univ a)
  exact hc'.trans_le (hca.trans (hb.trans ha))

private theorem squared_legShape (n : ℕ) (B : Fin n → Fin n → Fin n → ℝ)
    (ℓ : ℝ) (c : Fin n) (e : Leg n) (x : Torus) :
    (1/8 : ℝ) * legShape B ℓ c e x ^ 2 =
      (1/2 : ℝ) * ((B c e.1.1 e.2.1)^2 *
      ((curvatureLine ℓ e.1.2 * realTorusMode e.1.2 x ^ 2) *
        (curvatureLine ℓ e.2.2 * realTorusMode e.2.2 x ^ 2))) := by
  simp only [legShape, ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul, mul_pow]
  have h₁ : (derivativeWeight 0 ℓ e.1.2)^2 = 2 * curvatureLine ℓ e.1.2 := by
    linarith [transferWeight_sq_half ℓ e.1.2]
  have h₂ : (derivativeWeight 0 ℓ e.2.2)^2 = 2 * curvatureLine ℓ e.2.2 := by
    linarith [transferWeight_sq_half ℓ e.2.2]
  rw [h₁, h₂]
  ring

private theorem color_order {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) :
    (∑ c, ∑ a, ∑ b, (B c a b)^2) = colorBracketSquare B := by
  unfold colorBracketSquare
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

private theorem local_leg_square_sum {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (Λ ℓ : ℝ) (x : Torus) :
    (1/8 : ℝ) * (∑ c, ∑ e ∈ vertexLegs n Λ, legShape B ℓ c e x ^ 2) =
      (1/2 : ℝ) * colorBracketSquare B * (∑ k ∈ retainedModes Λ, curvatureLine ℓ k)^2 := by
  let A (k : MeanZeroMode) := curvatureLine ℓ k * realTorusMode k x ^ 2
  have hA : (∑ k ∈ retainedModes Λ, A k) = ∑ k ∈ retainedModes Λ, curvatureLine ℓ k :=
    localized_spherical_line_sum Λ ℓ x
  calc
    _ = (1/2 : ℝ) * ∑ c, ∑ e ∈ vertexLegs n Λ,
        (B c e.1.1 e.2.1)^2 * (A e.1.2 * A e.2.2) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => squared_legShape n B ℓ c e x
    _ = (1/2 : ℝ) * ∑ c, ∑ a, ∑ b,
        (B c a b)^2 * (∑ k ∈ retainedModes Λ, A k)^2 := by
      unfold vertexLegs
      simp only [Finset.sum_product]
      apply congrArg ((1/2 : ℝ) * ·)
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [pow_two]
      rw [Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
    _ = (1/2 : ℝ) * ((∑ c, ∑ a, ∑ b, (B c a b)^2) *
        (∑ k ∈ retainedModes Λ, A k)^2) := by simp only [Finset.sum_mul]
    _ = _ := by rw [color_order, hA, mul_assoc]

/-- Exact first vacuum coefficient for every literal spherical restriction.
The equal tadpole factors include both normal transfers at each endpoint. -/
theorem cutoff_vacuum_coefficient {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (Λ ℓ : ℝ) :
    (∫ X, cutoffBracketPotential B Λ ℓ X ∂commonGaussian n) =
      (1/2 : ℝ) * colorBracketSquare B * (∑ k ∈ retainedModes Λ, curvatureLine ℓ k)^2 := by
  rw [cutoffBracketPotential_diagonal_wick]
  let R : ℝ := (1/2 : ℝ) * colorBracketSquare B *
    (∑ k ∈ retainedModes Λ, curvatureLine ℓ k)^2
  have h : (1/8 : ℝ) • (∑ c, ∑ e ∈ vertexLegs n Λ, legShape B ℓ c e ^ 2) =
      (ContinuousMap.const Torus R : ContinuousField) := by
    ext x
    simpa only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, ContinuousMap.pow_apply,
      smul_eq_mul, ContinuousMap.const_apply, R] using local_leg_square_sum B Λ ℓ x
  have hi := congrArg normalizedIntegral h
  simp only [map_smul, map_sum, smul_eq_mul] at hi
  change (1/8 : ℝ) * (∑ c, ∑ e ∈ vertexLegs n Λ, normalizedIntegral (legShape B ℓ c e ^ 2)) = R
  rw [hi]
  change (∫ _x : Torus, R ∂normalizedTorusVolume) = R
  simp

/-- At fixed positive depth the first continuum vacuum coefficient of the
literal bracket is half the color norm times the square of the full
transferred contraction sum. This is the fixed-depth manuscript identity. -/
theorem continuum_vacuum_coefficient {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ X, fullBracketPotential B ℓ X ∂commonGaussian n) =
      (1/2 : ℝ) * colorBracketSquare B * (∑' k : MeanZeroMode, curvatureLine ℓ k)^2 := by
  have hV := (bracketPotential_power_integral_limit B hℓ 1).2.2
  simp only [pow_one] at hV
  simp_rw [cutoff_vacuum_coefficient B] at hV
  have hS := ((spherical_line_sum_limit hℓ).pow 2).const_mul ((1/2 : ℝ) * colorBracketSquare B)
  exact tendsto_nhds_unique hV hS

/-- The harmonic transfer from physical elementary coordinates before any
common-preparation rescaling. -/
def depthTransferredField {n : ℕ} (ℓ : ℝ) (Y : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) : ContinuousField :=
  ∑' k : MeanZeroMode, (exp (-ℓ * latticeFrequency k) * Y (k,(a,c))) • realTorusMode k

def depthBracketPotential {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (ℓ : ℝ)
    (Y : ModeSlot n → ℝ) : ℝ :=
  normalizedIntegral (bracketDensity B (depthTransferredField ℓ Y 0)
    (depthTransferredField ℓ Y 1))

theorem depthTransferredField_depthRescale {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) : depthTransferredField ℓ (depthRescale ℓ X) a c =
      fullTransferredField ℓ X a c := by
  unfold depthTransferredField fullTransferredField
  congr 1
  funext k
  simp only [transferredTerm, depthRescale, derivativeWeight, pow_zero, one_mul, mul_assoc]

theorem depthBracketPotential_depthRescale {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (ℓ : ℝ) (X : ModeSlot n → ℝ) :
    depthBracketPotential B ℓ (depthRescale ℓ X) = fullBracketPotential B ℓ X := by
  unfold depthBracketPotential fullBracketPotential
  have h (a : Fin 2) : depthTransferredField ℓ (depthRescale ℓ X) a = fullTransferredField ℓ X a :=
    funext (depthTransferredField_depthRescale ℓ X a)
  rw [h 0, h 1]

private theorem depthCoordinateScale_pos (ℓ : ℝ) (k : MeanZeroMode) :
    0 < sqrt (2 * curvatureCovariance ℓ k) := by
  have hk : 0 < latticeFrequency k := (Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero (latticeHeight_ne_zero k.2))).trans_le
      (latticeHeight_le_latticeFrequency k)
  unfold curvatureCovariance
  positivity

private def rescaleEquiv {n : ℕ} (ℓ : ℝ) : (ModeSlot n → ℝ) ≃ᵐ (ModeSlot n → ℝ) where
  toFun := depthRescale ℓ
  invFun Y i := Y i / sqrt (2 * curvatureCovariance ℓ i.1)
  left_inv X := by
    ext i
    change sqrt (2 * curvatureCovariance ℓ i.1) * X i / sqrt (2 * curvatureCovariance ℓ i.1) = X i
    rw [mul_comm, mul_div_cancel_right₀ _ (depthCoordinateScale_pos ℓ i.1).ne']
  right_inv Y := by
    ext i
    change sqrt (2 * curvatureCovariance ℓ i.1) * (Y i / sqrt (2 * curvatureCovariance ℓ i.1)) = Y i
    rw [mul_comm, div_mul_cancel₀ _ (depthCoordinateScale_pos ℓ i.1).ne']
  measurable_toFun := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i).const_mul _
  measurable_invFun := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i).div_const _

/-- The same continuum identity holds under the actual physical Gaussian
law with covariance Cℓ, using its literal transfer and bracket. -/
theorem continuum_vacuum_depthGaussian {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ Y, depthBracketPotential B ℓ Y ∂depthGaussian n ℓ) =
      (1/2 : ℝ) * colorBracketSquare B * (∑' k : MeanZeroMode, curvatureLine ℓ k)^2 := by
  have hp : MeasurePreserving (rescaleEquiv (n := n) ℓ) (commonGaussian n) (depthGaussian n ℓ) :=
    ⟨(rescaleEquiv ℓ).measurable, commonGaussian_map_depthRescale n ℓ⟩
  rw [← hp.integral_comp' (depthBracketPotential B ℓ)]
  change (∫ X, depthBracketPotential B ℓ (depthRescale ℓ X) ∂commonGaussian n) = _
  simp_rw [depthBracketPotential_depthRescale]
  exact continuum_vacuum_coefficient B hℓ

private theorem spherical_line_sum_eq (Λ ℓ : ℝ) :
    (∑ k ∈ retainedModes Λ, curvatureLine ℓ k) = ∑ k ∈ sphericalModes Λ, curvatureLine ℓ k :=
  Finset.sum_subtype_of_mem (curvatureLine ℓ) fun _ hk => (mem_sphericalModes.mp hk).1

def vacuumGraphCoeff {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) : Assignment 2 → ℝ :=
  fun _ => (1/2 : ℝ) * colorBracketSquare B

/-- The literal first vacuum term with the single common-depth determinant
is exactly the spherical two-line contraction sum used in the tail proof. -/
theorem spherical_vacuum_graph {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (Λ ℓ : ℝ) :
    sphericalGraphSum n Λ ℓ (vacuumGraphCoeff B) =
      sphericalDeterminant n Λ ℓ * (∫ X, cutoffBracketPotential B Λ ℓ X ∂commonGaussian n) := by
  rw [cutoff_vacuum_coefficient, spherical_line_sum_eq]
  change sphericalDeterminant n Λ ℓ *
      (∑ a ∈ Fintype.piFinset (fun _ : Fin 2 => sphericalModes Λ),
        ((1/2 : ℝ) * colorBracketSquare B) * ∏ e, curvatureLine ℓ (a e)) = _
  apply congrArg (sphericalDeterminant n Λ ℓ * ·)
  rw [← Finset.mul_sum]
  apply congrArg (((1/2 : ℝ) * colorBracketSquare B) * ·)
  calc
    _ = ∏ _ : Fin 2, ∑ k ∈ sphericalModes Λ, curvatureLine ℓ k :=
      Finset.sum_prod_piFinset (sphericalModes Λ) (fun (_ : Fin 2) k => curvatureLine ℓ k)
    _ = _ := by simp

/-- The same graph identification in the unrestricted source. The zero
depth case is determined by the original continuum determinant. -/
theorem continuum_vacuum_graph {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    fullGraphSum n ℓ (vacuumGraphCoeff B) =
      fullDeterminant n ℓ * (∫ X, fullBracketPotential B ℓ X ∂commonGaussian n) := by
  rcases hℓ.eq_or_lt with hzero | hpos
  · subst ℓ
    simp [fullGraphSum, fullDeterminant, hn.ne']
  · have hG := spherical_graph_limit hn hpos.le (vacuumGraphCoeff B)
      (B := |(1/2 : ℝ) * colorBracketSquare B|) (fun _ => le_rfl)
    have hV := (bracketPotential_power_integral_limit B hpos 1).2.2
    simp only [pow_one] at hV
    have hW := (positive_depth_determinant_limit n hpos).mul hV
    simp_rw [spherical_vacuum_graph B] at hG
    exact tendsto_nhds_unique hG hW

/-- The determinant-weighted literal vacuum coefficient is integrable
against the single finite nonnegative-depth source and is the limit of its
spherical analogs. The depth-zero atom needs no separate normalization. -/
theorem integrated_vacuum_coefficient_limit {n : ℕ} (hn : 0 < n)
    (B : Fin n → Fin n → Fin n → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ) :
    Integrable (fun ℓ => fullDeterminant n ℓ * (∫ X, fullBracketPotential B ℓ X ∂commonGaussian n)) μ ∧
    Tendsto (fun Λ : ℝ => ∫ ℓ, sphericalDeterminant n Λ ℓ *
      (∫ X, cutoffBracketPotential B Λ ℓ X ∂commonGaussian n) ∂μ) atTop
      (𝓝 (∫ ℓ, fullDeterminant n ℓ * (∫ X, fullBracketPotential B ℓ X ∂commonGaussian n) ∂μ)) := by
  have hG := integrated_full_graph_limit hn μ hμ (fun _ => vacuumGraphCoeff B)
    (B := |(1/2 : ℝ) * colorBracketSquare B|) (fun _ => measurable_const) (fun _ _ => le_rfl)
  have he := hμ.mono (fun _ h => continuum_vacuum_graph hn B h)
  refine ⟨hG.1.congr he, ?_⟩
  rw [← integral_congr_ae he]
  simpa only [spherical_vacuum_graph B] using hG.2

end UV.AdvanceCurvatureVacuum
