import UV.ContinueMarkedPhotonProjection

/-! A finite centered Gaussian projection with the characteristic function
of an arbitrary covariance D has exactly the eigenframe law used to
differentiate the physical source. Singular covariances are included. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace Matrix

namespace UV.MarkedPhoton

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private instance photonCoordinateProbability (d : ℝ) : IsProbabilityMeasure (sourceGaussian d) := by
  rw [sourceGaussian,UV.ContinueCurvatureGaussian.sourceGaussianBase_eq_gaussianReal]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance physicalLaw_probability (D : Matrix ι ι ℝ) (hD : D.PosSemidef) :
    IsProbabilityMeasure (photonProjectionLaw D hD) := by
  letI : IsProbabilityMeasure (coordinateLaw hD.1.eigenvalues) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun i => sourceGaussian (hD.1.eigenvalues i))))
  exact Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable (Matrix.mulVec (hD.1.eigenvectorUnitary : Matrix ι ι ℝ))
    (coordinateLaw hD.1.eigenvalues))

def photonCharacteristic (μ : Measure (ι → ℝ)) (t : ι → ℝ) : ℂ :=
  ∫ x, Complex.exp (((t ⬝ᵥ x : ℝ):ℂ)*Complex.I) ∂μ

omit [DecidableEq ι] in
private theorem characteristic_toLp (μ : Measure (ι → ℝ)) (t : EuclideanSpace ℝ ι) :
    charFun (μ.map (WithLp.toLp 2)) t = photonCharacteristic μ (WithLp.ofLp t) := by
  rw [charFun_apply,integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable (by fun_prop)]
  simp [photonCharacteristic,EuclideanSpace.inner_eq_star_dotProduct]

omit [DecidableEq ι] in
private theorem coordinateGaussian_characteristic (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (t : ι → ℝ) :
    photonCharacteristic (coordinateLaw d) t = Complex.exp (-((∑ i, d i * t i^2 : ℝ):ℂ)/2) := by
  have hp : photonCharacteristic (coordinateLaw d) t = charFun ((coordinateLaw d).map (WithLp.toLp 2)) (WithLp.toLp 2 t) := (characteristic_toLp _ _).symm
  rw [hp]
  unfold coordinateLaw
  rw [charFun_pi]
  have he (i : ι) : charFun (sourceGaussian (d i)) (t i) = Complex.exp (-((d i*t i^2:ℝ):ℂ)/2) := by
    rw [sourceGaussian,charFun_map_mul,UV.ContinueCurvatureGaussian.sourceGaussianBase_eq_gaussianReal,charFun_gaussianReal]
    have hs : ((Real.sqrt (2*d i):ℝ):ℂ)^2 = ((2*d i:ℝ):ℂ) := by
      rw [←Complex.ofReal_pow,Real.sq_sqrt (mul_nonneg (by norm_num) (hd i))]
    congr 1
    push_cast
    rw [mul_pow,hs]
    norm_num
    ring
  change (∏ i, charFun (sourceGaussian (d i)) (t i)) = _
  simp_rw [he]
  rw [←Complex.exp_sum]
  congr 1
  push_cast
  rw [←Finset.sum_div,←Finset.sum_neg_distrib]

theorem projectionLaw_characteristic (D : Matrix ι ι ℝ) (hD : D.PosSemidef) (t : ι → ℝ) :
    photonCharacteristic (photonProjectionLaw D hD) t = Complex.exp (-((t ⬝ᵥ (D *ᵥ t):ℝ):ℂ)/2) := by
  let U : Matrix ι ι ℝ := hD.1.eigenvectorUnitary
  let d := hD.1.eigenvalues
  have hchange : photonCharacteristic (photonProjectionLaw D hD) t = photonCharacteristic (coordinateLaw d) (t ᵥ* U) := by
    unfold photonProjectionLaw photonCharacteristic
    rw [integral_map (by fun_prop : AEMeasurable (Matrix.mulVec U) (coordinateLaw d)) (by fun_prop)]
    simp_rw [Matrix.dotProduct_mulVec]
  rw [hchange,coordinateGaussian_characteristic d hD.eigenvalues_nonneg]
  have hspec : D = U * Matrix.diagonal d * star U := hD.1.spectral_theorem
  have hqt : t ⬝ᵥ (D *ᵥ t) = ∑ i, d i * ((t ᵥ* U) i)^2 := by
    rw [hspec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,
      Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mulVec_transpose]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mulVec_diagonal]; ring
  rw [hqt]

/-- Uniqueness for the entire finite Gaussian law follows from the
Fourier transform, even when the physical covariance has a nullspace. -/
theorem gaussian_projection_law_eq (D : Matrix ι ι ℝ) (hD : D.PosSemidef) (μ : Measure (ι → ℝ))
    [IsFiniteMeasure μ] (hGaussian : ∀ t, photonCharacteristic μ t =
      Complex.exp (-((t ⬝ᵥ (D *ᵥ t):ℝ):ℂ)/2)) : μ = photonProjectionLaw D hD := by
  apply (MeasurableEquiv.toLp 2 (ι → ℝ)).map_measurableEquiv_injective
  apply Measure.ext_of_charFun
  funext t
  change charFun (μ.map (WithLp.toLp 2)) t = charFun ((photonProjectionLaw D hD).map (WithLp.toLp 2)) t
  rw [characteristic_toLp,characteristic_toLp,hGaussian,projectionLaw_characteristic]

/-- The actual Hessian trace identity for a general finite test projection
of a centered Gaussian field with covariance D and a common-action
multilinear kernel applied to its specified physical field insertions. -/
theorem marked_gaussian_projection_trace {F : Type*} [AddCommGroup F] [Module ℝ F] {r : ℕ}
    (D : Matrix ι ι ℝ) (hD : D.PosSemidef) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (hGaussian : ∀ t, photonCharacteristic μ t = Complex.exp (-((t ⬝ᵥ (D *ᵥ t):ℝ):ℂ)/2))
    (L : MultilinearMap ℝ (fun _ : Fin r => F) ℝ) (v : ι → F) :
    (D * physicalProjectedHessian D hD (physicalProjectedSource L v)).trace =
      r * ∫ y, physicalProjectedSource L v y ∂μ := by
  rw [gaussian_projection_law_eq D hD μ hGaussian]
  exact marked_physical_projection_trace D hD L v

end UV.MarkedPhoton
