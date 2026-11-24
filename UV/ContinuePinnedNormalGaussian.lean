import UV.ContinuePinnedNormalDuration
import UV.ContinueNetworkFourier
import UV.ResidualCoercivity

/-! The equal-position normal-network heat integral with its full
dimension-dependent normalization and original incidence weights. -/

noncomputable section
open MeasureTheory Real Filter Set Matrix
open scoped ENNReal BigOperators Matrix RealInnerProductSpace
namespace UV

/-- Coordinates are grouped by normal component. Each edge sees its
literal squared displacement and the standard normal heat prefactor. -/
def pinnedNormalHeatProduct {L N d : ℕ} (A : Matrix (Fin L) (Fin N) ℝ) (D : ℝ)
    (t : Fin N → ℝ) (y : Fin d → EuclideanSpace ℝ (Fin L)) : ℝ :=
  ∏ e, (4*π*D*t e)^(-(d:ℝ)/2) *
    exp (∑ j, -((Aᵀ *ᵥ (y j).ofLp) e)^2/(4*D*t e))

theorem pinned_normal_rank {L : ℕ} {E : Type*} [Fintype E] (A : Matrix (Fin L) E ℝ)
    (hA : Function.Injective Aᵀ.mulVec) : A.rank = L := by
  rw [← Matrix.rank_transpose,Matrix.rank,← (LinearEquiv.ofInjective Aᵀ.mulVecLin hA).finrank_eq,
    Module.finrank_pi,Fintype.card_fin]

theorem pinned_normal_heat_integral {L N d : ℕ} (A : Matrix (Fin L) (Fin N) ℝ)
    (hA : Function.Injective Aᵀ.mulVec) {D : ℝ} (hD : 0 < D)
    (t : Fin N → ℝ) (ht : ∀ e, 0 < t e) :
    (∫ y : Fin d → EuclideanSpace ℝ (Fin L), pinnedNormalHeatProduct A D t y) =
      (4*π*D)^(-((N:ℝ)-L)*((d:ℝ)/2)) * (pinnedDurationPolynomial A t)^(-(d:ℝ)/2) := by
  let α : ℝ := (d:ℝ)/2
  let T := ∏ i, t i
  let a := 4*π*D
  let Q := residualGram Aᵀ (fun e => (t e)⁻¹)
  let P := (D⁻¹:ℝ) • Q
  let F := fun x : EuclideanSpace ℝ (Fin L) => exp (-(x.ofLp ⬝ᵥ (P *ᵥ x.ofLp))/4)
  have ha : 0 < a := by unfold a; positivity
  have hT : 0 < T := Finset.prod_pos fun e _ => ht e
  have hQ : Q.PosDef := by
    have hEq : Q = Aᵀᴴ * Matrix.diagonal (fun e => (t e)⁻¹) * Aᵀ := by
      unfold Q residualGram
      rw [conjTranspose_eq_transpose_of_trivial]
      congr!
    rw [hEq]
    exact (Matrix.PosDef.diagonal (fun e => inv_pos.mpr (ht e))).conjTranspose_mul_mul_same hA
  have hP : P.PosDef := hQ.smul (inv_pos.mpr hD)
  have hJ : 0 < Q.det := hQ.det_pos
  have he (x : EuclideanSpace ℝ (Fin L)) :
      -(x.ofLp ⬝ᵥ (P *ᵥ x.ofLp))/4 = ∑ e, -((Aᵀ *ᵥ x.ofLp) e)^2/(4*D*t e) := by
    unfold P Q
    rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,residualGram_scalar_identity,
      Finset.mul_sum,← Finset.sum_neg_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    field_simp [(ht e).ne',hD.ne']
  have hf (y : Fin d → EuclideanSpace ℝ (Fin L)) :
      pinnedNormalHeatProduct A D t y = (∏ e, (a*t e)^(-α)) * ∏ j, F (y j) := by
    unfold pinnedNormalHeatProduct F
    rw [Finset.prod_mul_distrib,← exp_sum,← exp_sum]
    simp_rw [he]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro e _
    have h : -(d:ℝ)/2 = -α := by unfold α; ring
    rw [h]
  have hF : (∫ x, F x) = sqrt ((4*π)^L/P.det) := by
    have h := congrArg (fun z : ℂ => RCLike.re z) (networkSPDWave_integral P hP 0)
    dsimp only at h
    rw [← integral_re (networkSPDWave_integrable P hP 0)] at h
    have he (x : EuclideanSpace ℝ (Fin L)) : RCLike.re (networkSPDWave P 0 x) = F x := by
      unfold networkSPDWave F
      simp only [inner_zero_left,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul]
      rfl
    simp_rw [he] at h
    simpa using h
  have hPref : (∏ e, (a*t e)^(-α)) = a^(-(N:ℝ)*α)*T^(-α) := by
    simp_rw [mul_rpow ha.le (ht _).le,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [Real.finset_prod_rpow _ _ (fun e _ => (ht e).le),← Real.rpow_natCast (a^(-α)) N,
      ← rpow_mul ha.le]
    congr 2
    ring
  have hDet : P.det = (D^L)⁻¹ * Q.det := by
    unfold P
    rw [Matrix.det_smul,Fintype.card_fin,inv_pow]
  have hQuad : (4*π)^L/P.det = a^L/Q.det := by
    unfold a
    rw [hDet,mul_pow,div_eq_mul_inv,div_eq_mul_inv,mul_inv,inv_inv]
    ring
  have hNorm : sqrt ((4*π)^L/P.det)^d = a^((L:ℝ)*α) * Q.det^(-α) := by
    rw [hQuad, sqrt_eq_rpow,← Real.rpow_natCast _ d,
      ← rpow_mul (div_nonneg (pow_nonneg ha.le _) hJ.le),
      show (1/2:ℝ)*(d:ℝ) = α by unfold α; ring,
      div_rpow (pow_nonneg ha.le _) hJ.le,← Real.rpow_natCast a L,← rpow_mul ha.le,
      div_eq_mul_inv,← rpow_neg hJ.le]
  have hΨ : pinnedDurationPolynomial A t = T*Q.det := by
    unfold pinnedDurationPolynomial retainedGramDet Q residualGram T
    rw [transpose_transpose]
    congr!
  simp_rw [hf]
  rw [integral_const_mul,integral_fintype_prod_volume_eq_pow F,Fintype.card_fin,hF,hPref,hNorm,hΨ]
  rw [show -(d:ℝ)/2 = -α by unfold α; ring]
  change a^(-(N:ℝ)*α)*T^(-α) * (a^((L:ℝ)*α)*Q.det^(-α)) =
      a^(-((N:ℝ)-L)*α) * (T*Q.det)^(-α)
  rw [mul_rpow hT.le hJ.le]
  calc
    _ = (a^(-(N:ℝ)*α)*a^((L:ℝ)*α)) * (T^(-α)*Q.det^(-α)) := by ring
    _ = _ := by rw [← rpow_add ha]; congr 2; ring

/-- Multiplication by the full normal Gaussian gives the same strict
rank criterion as its complementary incidence polynomial. -/
theorem pinned_normal_heat_duration_finite_iff {L N d : ℕ} (A : Matrix (Fin L) (Fin N) ℝ)
    (hA : Function.Injective Aᵀ.mulVec) {D : ℝ} (hD : 0 < D) (η : Fin N → ℝ) :
    (∫⁻ t, ENNReal.ofReal (retainedWidthDensity η t *
      (∫ y : Fin d → EuclideanSpace ℝ (Fin L), pinnedNormalHeatProduct A D t y))
        ∂directionalSchwingerMeasure (Fin N)) < ⊤ ↔
      ∀ S : Finset (Fin N), S.Nonempty → (d:ℝ)/2 * pinnedDurationNullity A S < ∑ i ∈ S, η i := by
  let c := (4*π*D)^(-((N:ℝ)-L)*((d:ℝ)/2))
  have hc : 0 < c := rpow_pos_of_pos (by positivity) _
  have hr : A.rank = Fintype.card (Fin L) := (pinned_normal_rank A hA).trans (Fintype.card_fin L).symm
  have he : ∀ᵐ t ∂directionalSchwingerMeasure (Fin N),
      ENNReal.ofReal (retainedWidthDensity η t *
      (∫ y : Fin d → EuclideanSpace ℝ (Fin L), pinnedNormalHeatProduct A D t y)) =
        ENNReal.ofReal c * pinnedDurationDensity A η ((d:ℝ)/2) t := by
    filter_upwards [retainedWidth_ae_positive (n := N)] with t ht
    rw [pinned_normal_heat_integral A hA hD t ht,pinnedDurationDensity,← ENNReal.ofReal_mul hc.le]
    congr 1
    unfold c
    ring_nf
  rw [lintegral_congr_ae he]
  exact (retainedIntegral_comparable _ _ _ _ _ (ENNReal.ofReal_ne_zero_iff.mpr hc)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (ae_of_all _ fun _ => ⟨le_rfl,le_rfl⟩)).trans
    (pinnedDurationDensity_finite_iff_faces A hr η (by positivity))

end UV
