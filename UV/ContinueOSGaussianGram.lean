import UV.ContinueOSQuarticLaw
import UV.ContinueOSJointPlane
import UV.ContinueMarkedPhotonGaussian

/-! Ordinary free massive covariance on the finite boundary probes and all
positive-depth point slots. Their simultaneous finite-dimensional laws are
obtained from one Fourier Gram kernel in the oriented Euclidean chart. -/

noncomputable section
open MeasureTheory Matrix
open scoped SchwartzMap FourierTransform ComplexConjugate RealInnerProductSpace Matrix

namespace UV

private def osPointWave (x k : OSFourSpace) : ℂ :=
  stableFourierPhase ((2*Real.pi) • k) x

private theorem osPointWave_sub (x y k : OSFourSpace) :
    osPointWave (x-y) k = osPointWave x k * conj (osPointWave y k) := by
  rw [osPointWave, stableFourierPhase_sub]
  simp [osPointWave, stableFourierPhase, ← Complex.exp_conj]

private theorem osInvFourier_wave (x : OSFourSpace) (f : OSFourSpace → ℂ) :
    𝓕⁻ f x = ∫ k, osPointWave x k * f k := by
  rw [Real.fourierIntegralInv_eq']
  congr 1
  funext k
  rw [osPointWave, stableFourierPhase, real_inner_smul_left, smul_eq_mul]
  push_cast
  ring_nf

private theorem osCovWeight_integrable {r m : ℝ} (hr : 0 < r) (hm : 0 < m) :
    Integrable (osCovWeight m r) := by
  have he := (stablePoissonMultiplier_integrable (a := r*(2*Real.pi)) (by positivity)).const_mul ((m^2)⁻¹)
  apply he.mono' (show Continuous (osCovWeight m r) by
    unfold osCovWeight osTransferSymbol osMassiveSymbol
    fun_prop (disch := intro k; positivity)).aestronglyMeasurable
  filter_upwards with k
  rw [Real.norm_of_nonneg (osCovWeight_bound hm hr.le k).1]
  unfold osCovWeight osTransferSymbol
  change _ ≤ (m^2)⁻¹ * Real.exp (-(r*(2*Real.pi))*‖k‖)
  rw [show -(r*(2*Real.pi))*‖k‖ = -r*(2*Real.pi*‖k‖) by ring, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ (sq_pos_of_pos hm)
    (by exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)))) (Real.exp_pos _).le

private theorem osCovWeight_inverse {r m : ℝ} (hr : 0 < r) (hm : 0 < m) (x : OSFourSpace) :
    (stableCoordinateCovariance r m x : ℂ) = ∫ k, osPointWave x k * (osCovWeight m r k : ℂ) := by
  rw [←osInvFourier_wave]
  have h := (Complex.continuous_ofReal.comp (stableCoordinateCovariance_continuous hr hm)).fourier_inversion
    (Complex.ofRealCLM.integrable_comp (stableCoordinateCovariance_integrable hr hm))
    (show Integrable (𝓕 (fun x => (stableCoordinateCovariance r m x : ℂ))) volume by
      rw [funext (osCovWeight_fourier hm hr)]
      exact Complex.ofRealCLM.integrable_comp (osCovWeight_integrable hr hm))
  rw [←funext (osCovWeight_fourier hm hr)]
  exact (congrFun h x).symm

/-- Fourier observable associated to an ordinary boundary test or a
fixed-depth point evaluation. The square of the transfer occurs only
when both arguments are point insertions. -/
def osQuarticFourierFeature (m r : ℝ) : OSQuarticSlot → OSFourSpace → ℂ
  | .inl i, k => 𝓕 (osBoundaryTestProbe m i) k
  | .inr x, k => (osTransferSymbol r k : ℂ) * conj (osPointWave x k)

def osQuarticGramEntry (m r : ℝ) (i j : OSQuarticSlot) (k : OSFourSpace) : ℂ :=
  conj (osQuarticFourierFeature m r i k) * (osCovWeight m 0 k : ℂ) * osQuarticFourierFeature m r j k

private theorem osQuarticGramEntry_swap (m r : ℝ) (i j : OSQuarticSlot) (k : OSFourSpace) :
    osQuarticGramEntry m r j i k = conj (osQuarticGramEntry m r i j k) := by
  simp only [osQuarticGramEntry, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

private theorem osQuarticGram_mixed (m r : ℝ) (x : OSFourSpace) (j : OSBoundaryTest) (k : OSFourSpace) :
    osQuarticGramEntry m r (.inr x) (.inl j) k =
      osPointWave x k * ((osCovWeight m r k : ℂ) * 𝓕 (osBoundaryTestProbe m j) k) := by
  simp [osQuarticGramEntry,osQuarticFourierFeature,osCovWeight]; ring

private theorem osQuarticGram_points (m r : ℝ) (x y k : OSFourSpace) :
    osQuarticGramEntry m r (.inr x) (.inr y) k = osPointWave (x-y) k * (osCovWeight m (2*r) k : ℂ) := by
  rw [osPointWave_sub, two_mul]
  simp [osQuarticGramEntry,osQuarticFourierFeature,osCovWeight,osTransferSymbol_add]; ring

/-- Fourier Gram representation for all four kinds of covariance entry. -/
theorem osQuarticCovariance_gram {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (i j : OSQuarticSlot) :
    osQuarticCovariance m r i j = (∫ k, osQuarticGramEntry m r i j k).re := by
  cases i with
  | inl i =>
    cases j with
    | inl j => simp only [osQuarticCovariance,osReflectedBlock,osReflectProbe_fourier,
        osTimeReflect_involutive _,osQuarticGramEntry,osQuarticFourierFeature]
    | inr y =>
      simp_rw [osQuarticGramEntry_swap m r (.inr y) (.inl i), osQuarticGram_mixed]
      rw [integral_conj, Complex.conj_re]
      exact congrArg Complex.re (osInvFourier_wave _ _)
  | inr x =>
    cases j with
    | inl j =>
      simp_rw [osQuarticGram_mixed]
      exact congrArg Complex.re (osInvFourier_wave _ _)
    | inr y =>
      simp_rw [osQuarticGram_points]
      exact congrArg Complex.re (osCovWeight_inverse (by positivity) hm (x-y))

theorem osQuarticGramEntry_integrable {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    (i j : OSQuarticSlot) : Integrable (osQuarticGramEntry m r i j) := by
  have hmixed (x : OSFourSpace) (j : OSBoundaryTest) :
      Integrable (osQuarticGramEntry m r (.inr x) (.inl j)) := by
    let f := osBoundaryTestProbe m j
    let F := SchwartzMap.fourierTransformCLM ℂ f
    rw [funext (osQuarticGram_mixed m r x j)]
    apply (F.integrable.norm.const_mul ((m^2)⁻¹)).mono'
    · have hc : Continuous (osCovWeight m r) := by
        unfold osCovWeight osTransferSymbol osMassiveSymbol
        fun_prop (disch := intro k; positivity)
      exact ((stableFourierPhase_continuous.comp (by fun_prop : Continuous (fun k : OSFourSpace =>
        ((2*Real.pi) • k, x)))).mul ((Complex.continuous_ofReal.comp hc).mul F.continuous)).aestronglyMeasurable
    · filter_upwards with k
      rw [norm_mul,osPointWave,stableFourierPhase_norm,one_mul,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (osCovWeight_bound hm hr.le k).1]
      exact mul_le_mul_of_nonneg_right (osCovWeight_bound hm hr.le k).2 (norm_nonneg _)
  cases i with
  | inl i =>
    cases j with
    | inl j => exact osOrdinaryBlock_integrable hm le_rfl _ _
    | inr x =>
      rw [show osQuarticGramEntry m r (.inl i) (.inr x) = _ from
        funext (osQuarticGramEntry_swap m r (.inr x) (.inl i))]
      exact (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp (hmixed x i)
  | inr x =>
    cases j with
    | inl j => exact hmixed x j
    | inr y =>
      rw [funext (osQuarticGram_points m r x y)]
      apply (osCovWeight_integrable (r := 2*r) (by positivity) hm).mono'
      · have hc : Continuous (osCovWeight m (2*r)) := by
          unfold osCovWeight osTransferSymbol osMassiveSymbol
          fun_prop (disch := intro k; positivity)
        exact ((stableFourierPhase_continuous.comp (by fun_prop : Continuous (fun k : OSFourSpace =>
          ((2*Real.pi) • k, x-y)))).mul (Complex.continuous_ofReal.comp hc)).aestronglyMeasurable
      · filter_upwards with k
        rw [norm_mul,osPointWave,stableFourierPhase_norm,one_mul,Complex.norm_real,
          Real.norm_of_nonneg (osCovWeight_bound hm (by positivity : 0 ≤ 2*r) k).1]

private theorem osQuarticGramEntry_real (m r : ℝ) (i j : OSQuarticSlot) (k : OSFourSpace) :
    (osQuarticGramEntry m r i j k).re = osCovWeight m 0 k *
      ((osQuarticFourierFeature m r i k).re * (osQuarticFourierFeature m r j k).re +
        (osQuarticFourierFeature m r i k).im * (osQuarticFourierFeature m r j k).im) := by
  simp [osQuarticGramEntry,Complex.mul_re,Complex.mul_im]; ring

/-- Every finite family of boundary and point insertions has a positive
semidefinite ordinary covariance. -/
theorem osQuarticCovariance_posSemidef {ι : Type*} [Fintype ι] {m r : ℝ}
    (hm : 0 < m) (hr : 0 < r) (s : ι → OSQuarticSlot) :
    Matrix.PosSemidef (R := ℝ) (fun i j => osQuarticCovariance m r (s i) (s j)) := by
  let K := fun i j => osQuarticGramEntry m r (s i) (s j)
  have h (i j : ι) : osQuarticCovariance m r (s i) (s j) = ∫ k, (K i j k).re := by
    rw [osQuarticCovariance_gram hm hr]
    exact (integral_re (osQuarticGramEntry_integrable hm hr _ _)).symm
  constructor
  · ext i j
    change osQuarticCovariance m r (s j) (s i) = osQuarticCovariance m r (s i) (s j)
    rw [h,h]
    congr 1
    ext k
    simpa only [Complex.conj_re] using congrArg Complex.re (osQuarticGramEntry_swap m r (s i) (s j) k)
  · intro t
    change 0 ≤ ∑ i, t i * ∑ j, osQuarticCovariance m r (s i) (s j) * t j
    simp_rw [h,Finset.mul_sum,← integral_mul_const,← integral_const_mul]
    have hi (i j : ι) := (((osQuarticGramEntry_integrable hm hr (s i) (s j)).re.mul_const (t j)).const_mul (t i))
    change 0 ≤ ∑ i, ∑ j, ∫ k, t i * ((K i j k).re * t j)
    have hinner (i : ι) : (∑ j, ∫ k, t i * ((K i j k).re * t j)) =
        ∫ k, ∑ j, t i * ((K i j k).re * t j) :=
      (integral_finset_sum Finset.univ (fun j _ => hi i j)).symm
    simp_rw [hinner]
    have ho (i : ι) : Integrable (fun k => ∑ j, t i * ((K i j k).re * t j)) :=
      integrable_finset_sum Finset.univ (fun j _ => hi i j)
    rw [←integral_finset_sum Finset.univ (fun i _ => ho i)]
    apply integral_nonneg
    intro k
    let A (i : ι) := (osQuarticFourierFeature m r (s i) k).re
    let B (i : ι) := (osQuarticFourierFeature m r (s i) k).im
    calc
      _ = osCovWeight m 0 k * ((∑ i, t i * A i)^2 + (∑ i, t i * B i)^2) := by
        simp only [sq,Finset.sum_mul,Finset.mul_sum]
        rw [←Finset.sum_add_distrib]
        simp_rw [←Finset.sum_add_distrib]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [K,A,B]
        rw [osQuarticGramEntry_real]
        ring
      _ ≥ 0 := mul_nonneg (osCovWeight_bound hm le_rfl k).1 (add_nonneg (sq_nonneg _) (sq_nonneg _))

end UV
