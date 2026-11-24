import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! The finite Gaussian momentum-mixing comparison. The open
mean port and the actual closed source use the same two independent
Gaussian preparations, with the indicated shared coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators Matrix NNReal ENNReal
namespace UV.MarkedPhoton

/-- Once the quadratic is measurable in the observed field, the entire
correction to the independent contraction uses its conditional kernel. -/
theorem conditional_quadratic_correction {Ω : Type*} [m₀ : MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {μ : Measure[m₀] Ω} [SigmaFinite (μ.trim hm)]
    {quadratic port : Ω → ℝ} (covariance : ℝ)
    (hMeas : AEStronglyMeasurable[m] quadratic μ)
    (hPort : Integrable port μ) (hProduct : Integrable (quadratic * port) μ) :
    Integrable (fun x => (quadratic x - covariance) * μ[port|m] x) μ ∧
      (∫ x, quadratic x * port x ∂μ) - covariance * (∫ x, port x ∂μ) =
        ∫ x, (quadratic x - covariance) * μ[port|m] x ∂μ := by
  have hAE := condExp_mul_of_aestronglyMeasurable_left hMeas hProduct hPort
  have hCondProduct : Integrable (fun x => quadratic x * μ[port|m] x) μ :=
    integrable_condExp.congr hAE
  have hScaled : Integrable (fun x => covariance * μ[port|m] x) μ :=
    integrable_condExp.const_mul covariance
  simp_rw [sub_mul]
  refine ⟨hCondProduct.sub hScaled, ?_⟩
  have hPullout : (∫ x, quadratic x * μ[port|m] x ∂μ) = ∫ x, quadratic x * port x ∂μ :=
    (integral_congr_ae hAE.symm).trans (integral_condExp hm)
  rw [integral_sub hCondProduct hScaled, integral_const_mul, integral_condExp hm, hPullout]

/-- The correction sees just the projection of the conditional kernel onto
the finite span of the centered quadratic test functions in real `L²`. -/
theorem centered_quadratic_projection {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι]
    {μ : Measure Ω} (quadratic : ι → Ω → ℝ) (hQuadratic : ∀ i, MemLp (quadratic i) 2 μ)
    (conditionalPort : Ω → ℝ) (hPort : MemLp conditionalPort 2 μ) (i : ι) :
    let Q := fun j => (hQuadratic j).toLp (quadratic j)
    let span := Submodule.span ℝ (Set.range Q)
    letI : FiniteDimensional ℝ span := FiniteDimensional.span_of_finite ℝ (Set.finite_range Q)
    let projected := span.starProjection (hPort.toLp conditionalPort)
    (∫ x, quadratic i x * conditionalPort x ∂μ) = ∫ x, quadratic i x * projected x ∂μ := by
  dsimp only
  let Q := fun j => (hQuadratic j).toLp (quadratic j)
  let H := hPort.toLp conditionalPort
  let S := Submodule.span ℝ (Set.range Q)
  letI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range Q)
  have hQ : Q i ∈ S := Submodule.subset_span (Set.mem_range_self i)
  have orthogonal := S.starProjection_inner_eq_zero H (Q i) hQ
  rw [inner_sub_left, sub_eq_zero] at orthogonal
  rw [L2.inner_def, L2.inner_def] at orthogonal
  calc
    _ = ∫ x, inner ℝ (H x) (Q i x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hPort.coeFn_toLp, (hQuadratic i).coeFn_toLp] with x hH hQi
      change H x = conditionalPort x at hH
      change Q i x = quadratic i x at hQi
      rw [hH, hQi]
      simp [RCLike.inner_apply]
    _ = ∫ x, inner ℝ (S.starProjection H x) (Q i x) ∂μ := orthogonal
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(hQuadratic i).coeFn_toLp] with x hQi
      change Q i x = quadratic i x at hQi
      rw [hQi]
      simp [RCLike.inner_apply, S, H, Q]

def standardGaussianCoordinates (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (n : ℕ) : IsProbabilityMeasure (standardGaussianCoordinates n) := by
  unfold standardGaussianCoordinates
  infer_instance

private theorem standard_coordinate_preserving {n : ℕ} (i : Fin n) :
    MeasurePreserving (fun x : Fin n → ℝ => x i) (standardGaussianCoordinates n) (gaussianReal 0 1) :=
  measurePreserving_eval (μ := fun _ => gaussianReal 0 1) i

private theorem standard_coordinate_memLp {n : ℕ} (i : Fin n) (p : ℝ≥0) :
    MemLp (fun x : Fin n → ℝ => x i) p (standardGaussianCoordinates n) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) p).comp_measurePreserving (standard_coordinate_preserving i)

private theorem standard_coordinate_integrable {n : ℕ} (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i) (standardGaussianCoordinates n) :=
  (memLp_one_iff_integrable).mp (standard_coordinate_memLp i 1)

private theorem standard_coordinate_mean {n : ℕ} (i : Fin n) :
    (∫ x, x i ∂standardGaussianCoordinates n) = 0 := by
  have hm : AEMeasurable (fun x : Fin n → ℝ => x i) (standardGaussianCoordinates n) :=
    (measurable_pi_apply i).aemeasurable
  calc
    _ = ∫ y, y ∂Measure.map (fun x => x i) (standardGaussianCoordinates n) :=
      (integral_map hm (f := fun y : ℝ => y) aestronglyMeasurable_id).symm
    _ = _ := by rw [(standard_coordinate_preserving i).map_eq,integral_id_gaussianReal]

private theorem standard_coordinate_square_integrable {n : ℕ} (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => (x i)^2) (standardGaussianCoordinates n) :=
  (memLp_two_iff_integrable_sq (standard_coordinate_memLp i 2).aestronglyMeasurable).mp
    (standard_coordinate_memLp i 2)

private theorem standard_coordinate_square {n : ℕ} (i : Fin n) :
    (∫ x, (x i)^2 ∂standardGaussianCoordinates n) = 1 := by
  have hs : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable] at h
    simpa using h
  have hm : AEMeasurable (fun x : Fin n → ℝ => x i) (standardGaussianCoordinates n) :=
    (measurable_pi_apply i).aemeasurable
  calc
    _ = ∫ y, y^2 ∂Measure.map (fun x => x i) (standardGaussianCoordinates n) :=
      (integral_map hm (f := fun y : ℝ => y^2) (continuous_id.pow 2).aestronglyMeasurable).symm
    _ = _ := by rw [(standard_coordinate_preserving i).map_eq,hs]

private theorem standard_coordinate_pair_integrable {n : ℕ} (i j : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i*x j) (standardGaussianCoordinates n) := by
  refine (((standard_coordinate_square_integrable i).add (standard_coordinate_square_integrable j)).div_const 2).mono'
    ((measurable_pi_apply i).mul (measurable_pi_apply j)).aestronglyMeasurable ?_
  filter_upwards with x
  change ‖x i*x j‖ ≤ ((x i)^2+(x j)^2)/2
  rw [Real.norm_eq_abs,abs_mul]
  nlinarith [sq_abs (x i),sq_abs (x j),sq_nonneg (|x i|-|x j|)]

theorem standard_gaussian_coordinate_covariance {n : ℕ} (i j : Fin n) :
    (∫ x, x i*x j ∂standardGaussianCoordinates n) = if i=j then 1 else 0 := by
  by_cases hij : i=j
  · subst j
    simp_rw [← pow_two]
    rw [standard_coordinate_square,if_true]
  · have hInd : iIndepFun (fun (i : Fin n) (x : Fin n → ℝ) => x i) (standardGaussianCoordinates n) :=
      iIndepFun_pi (X := fun _ => id) (μ := fun _ => gaussianReal 0 1) (fun _ => aemeasurable_id)
    rw [(hInd.indepFun hij).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable,
      standard_coordinate_mean,standard_coordinate_mean,mul_zero,if_neg hij]

def gaussianExteriorSquare {n : ℕ} (u b : Fin n → ℝ) : ℝ :=
  (u ⬝ᵥ u)*(b ⬝ᵥ b)-(u ⬝ᵥ b)^2

def gaussianMixPort {n : ℕ} (b : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (if i=j then b ⬝ᵥ b else 0) - b i*b j

theorem exterior_square_shared_coordinate {n : ℕ} (σ : ℝ) (a z : Fin n → ℝ) :
    gaussianExteriorSquare a (a + σ • z) = σ^2 * gaussianExteriorSquare a z := by
  unfold gaussianExteriorSquare
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,smul_eq_mul]
  rw [dotProduct_comm z a]
  ring

private theorem gaussian_standard_normsq {n : ℕ} :
    Integrable (fun x : Fin n → ℝ => x ⬝ᵥ x) (standardGaussianCoordinates n) ∧
      (∫ x, x ⬝ᵥ x ∂standardGaussianCoordinates n) = n := by
  unfold dotProduct
  constructor
  · exact integrable_finset_sum _ fun i _ => standard_coordinate_pair_integrable i i
  · rw [integral_finset_sum _ (fun i _ => standard_coordinate_pair_integrable i i)]
    simp [standard_gaussian_coordinate_covariance]

private theorem independent_gaussian_exterior {n : ℕ} :
    Integrable (fun p => gaussianExteriorSquare p.1 p.2) ((standardGaussianCoordinates n).prod (standardGaussianCoordinates n)) ∧
      (∫ p, gaussianExteriorSquare p.1 p.2 ∂(standardGaussianCoordinates n).prod (standardGaussianCoordinates n)) =
        (n:ℝ)*(n-1) := by
  let μ := standardGaussianCoordinates n
  let f := fun (i j : Fin n) (p : (Fin n → ℝ) × (Fin n → ℝ)) =>
    (p.1 i*p.1 j)*(p.2 i*p.2 j)
  have hf (i j : Fin n) : Integrable (f i j) (μ.prod μ) :=
    (standard_coordinate_pair_integrable i j).mul_prod (standard_coordinate_pair_integrable i j)
  have hDot (p : (Fin n → ℝ) × (Fin n → ℝ)) : (p.1 ⬝ᵥ p.2)^2 = ∑ i, ∑ j, f i j p := by
    unfold dotProduct
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold f
    ring
  have hi : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 ⬝ᵥ p.2)^2) (μ.prod μ) := by
    simp_rw [hDot]
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hf i j
  have hs := gaussian_standard_normsq (n := n)
  have hP : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 ⬝ᵥ p.1)*(p.2 ⬝ᵥ p.2)) (μ.prod μ) :=
    hs.1.mul_prod hs.1
  have hd : (∫ p : (Fin n → ℝ) × (Fin n → ℝ), (p.1 ⬝ᵥ p.2)^2 ∂μ.prod μ) = n := by
    simp_rw [hDot]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hf i j)]
    have he (i : Fin n) : (∫ p, ∑ j, f i j p ∂μ.prod μ) = 1 := by
      rw [integral_finset_sum _ (fun j _ => hf i j)]
      have hPair (j : Fin n) : (∫ p, f i j p ∂μ.prod μ) = if i=j then 1 else 0 := by
        unfold f
        rw [integral_prod_mul (fun x : Fin n → ℝ => x i*x j) (fun x : Fin n → ℝ => x i*x j)]
        change (∫ x, x i*x j ∂standardGaussianCoordinates n) *
          (∫ x, x i*x j ∂standardGaussianCoordinates n) = _
        rw [standard_gaussian_coordinate_covariance]
        split_ifs <;> norm_num
      simp_rw [hPair]
      simp
    simp_rw [he]
    simp
  refine ⟨hP.sub hi,?_⟩
  unfold gaussianExteriorSquare
  change (∫ p, (p.1 ⬝ᵥ p.1)*(p.2 ⬝ᵥ p.2)-(p.1 ⬝ᵥ p.2)^2 ∂μ.prod μ) = _
  rw [integral_sub hP hi,integral_prod_mul (fun x => x ⬝ᵥ x) (fun x => x ⬝ᵥ x),hd]
  change (∫ x, x ⬝ᵥ x ∂standardGaussianCoordinates n) *
    (∫ x, x ⬝ᵥ x ∂standardGaussianCoordinates n) - n = _
  rw [hs.2]
  ring

/-- The positive closed exterior test sees only the independent part
of the mixed Gaussian background. At zero mixing the closed value is zero. -/
theorem gaussian_mixed_exterior_sewing {n : ℕ} (σ : ℝ) :
    Integrable (fun p => gaussianExteriorSquare p.1 (p.1+σ • p.2))
        ((standardGaussianCoordinates n).prod (standardGaussianCoordinates n)) ∧
      (∫ p, gaussianExteriorSquare p.1 (p.1+σ • p.2)
        ∂(standardGaussianCoordinates n).prod (standardGaussianCoordinates n)) = σ^2*(n:ℝ)*(n-1) := by
  simp_rw [exterior_square_shared_coordinate]
  have h := independent_gaussian_exterior (n := n)
  refine ⟨h.1.const_mul _,?_⟩
  rw [integral_const_mul,h.2,mul_assoc]

private def gaussianMixedVector {n : ℕ} (σ : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  p.1 + σ • p.2

private theorem gaussian_mixed_covariance {n : ℕ} (σ : ℝ) (i j : Fin n) :
    let μ := standardGaussianCoordinates n
    let b := gaussianMixedVector σ
    Integrable (fun p => b p i * b p j) (μ.prod μ) ∧
      (∫ p, b p i*b p j ∂μ.prod μ) = (1+σ^2)* (if i=j then 1 else 0) := by
  dsimp only
  let μ := standardGaussianCoordinates n
  let P := (Fin n → ℝ) × (Fin n → ℝ)
  let aa := fun p : P => p.1 i*p.1 j
  let az := fun p : P => p.1 i*p.2 j
  let za := fun p : P => p.1 j*p.2 i
  let zz := fun p : P => p.2 i*p.2 j
  have hAA : Integrable aa (μ.prod μ) := (measurePreserving_fst (μ := μ) (ν := μ)).integrable_comp_of_integrable
    (standard_coordinate_pair_integrable i j)
  have hAZ : Integrable az (μ.prod μ) := (standard_coordinate_integrable i).mul_prod (standard_coordinate_integrable j)
  have hZA : Integrable za (μ.prod μ) := (standard_coordinate_integrable j).mul_prod (standard_coordinate_integrable i)
  have hZZ : Integrable zz (μ.prod μ) := (measurePreserving_snd (μ := μ) (ν := μ)).integrable_comp_of_integrable
    (standard_coordinate_pair_integrable i j)
  have hA : (∫ p, aa p ∂μ.prod μ) = if i=j then 1 else 0 := by
    rw [integral_prod aa hAA]
    simpa [aa,μ,integral_const] using standard_gaussian_coordinate_covariance i j
  have hZ : (∫ p, zz p ∂μ.prod μ) = if i=j then 1 else 0 := by
    rw [integral_prod_symm zz hZZ]
    simpa [zz,μ,integral_const] using standard_gaussian_coordinate_covariance i j
  have hAZ₀ : (∫ p, az p ∂μ.prod μ) = 0 := by
    unfold az
    rw [integral_prod_mul (fun x : Fin n → ℝ => x i) (fun x : Fin n → ℝ => x j)]
    change (∫ x, x i ∂standardGaussianCoordinates n)*(∫ x, x j ∂standardGaussianCoordinates n) = 0
    rw [standard_coordinate_mean,zero_mul]
  have hZA₀ : (∫ p, za p ∂μ.prod μ) = 0 := by
    unfold za
    rw [integral_prod_mul (fun x : Fin n → ℝ => x j) (fun x : Fin n → ℝ => x i)]
    change (∫ x, x j ∂standardGaussianCoordinates n)*(∫ x, x i ∂standardGaussianCoordinates n) = 0
    rw [standard_coordinate_mean,zero_mul]
  have he (p : P) : gaussianMixedVector σ p i*gaussianMixedVector σ p j =
      aa p + σ*az p + σ*za p + σ^2*zz p := by
    simp only [gaussianMixedVector,Pi.add_apply,Pi.smul_apply,smul_eq_mul,aa,az,za,zz]
    ring
  simp_rw [he]
  have h1 : Integrable (fun p : P => aa p + σ*az p) (μ.prod μ) := hAA.add (hAZ.const_mul σ)
  have h2 : Integrable (fun p : P => aa p + σ*az p + σ*za p) (μ.prod μ) := h1.add (hZA.const_mul σ)
  refine ⟨h2.add (hZZ.const_mul (σ^2)),?_⟩
  change (∫ p, aa p + σ*az p + σ*za p + σ^2*zz p ∂μ.prod μ) = _
  rw [integral_add h2 (hZZ.const_mul _),integral_add h1 (hZA.const_mul _),
    integral_add hAA (hAZ.const_mul _),integral_const_mul,integral_const_mul,integral_const_mul,
    hA,hZ,hAZ₀,hZA₀]
  ring

/-- Averaging the open port before the photon sewing yields the isotropic
matrix with diagonal `(d−1)(1+σ²)`. -/
theorem gaussian_mixed_mean_port {n : ℕ} (σ : ℝ) (i j : Fin n) :
    let μ := standardGaussianCoordinates n
    let b := gaussianMixedVector σ
    Integrable (fun p => gaussianMixPort (b p) i j) (μ.prod μ) ∧
      (∫ p, gaussianMixPort (b p) i j ∂μ.prod μ) =
        ((n:ℝ)-1)*(1+σ^2)*(if i=j then 1 else 0) := by
  dsimp only
  let μ := standardGaussianCoordinates n
  let b := gaussianMixedVector (n := n) σ
  have hbi (r : Fin n) : Integrable (fun p => b p r*b p r) (μ.prod μ) :=
    (gaussian_mixed_covariance σ r r).1
  have hNormI : Integrable (fun p => b p ⬝ᵥ b p) (μ.prod μ) := by
    unfold dotProduct
    exact integrable_finset_sum _ fun r _ => hbi r
  have hNorm : (∫ p, b p ⬝ᵥ b p ∂μ.prod μ) = (n:ℝ)*(1+σ^2) := by
    unfold dotProduct
    rw [integral_finset_sum _ (fun r _ => hbi r)]
    have h (r : Fin n) : (∫ p, b p r*b p r ∂μ.prod μ) = 1+σ^2 := by
      simpa using (gaussian_mixed_covariance σ r r).2
    simp_rw [h]
    simp
    ring
  by_cases hij : i=j
  · subst j
    simp only [gaussianMixPort,if_true,mul_one]
    have hd : (∫ p, b p i*b p i ∂μ.prod μ) = 1+σ^2 := by
      simpa using (gaussian_mixed_covariance σ i i).2
    refine ⟨hNormI.sub (hbi i),?_⟩
    change (∫ p, b p ⬝ᵥ b p - b p i*b p i ∂μ.prod μ) = _
    rw [integral_sub hNormI (hbi i),hNorm,hd]
    ring
  · simp only [gaussianMixPort,if_neg hij,mul_zero,zero_sub]
    have h := gaussian_mixed_covariance σ i j
    refine ⟨h.1.neg,?_⟩
    rw [integral_neg,h.2,if_neg hij,mul_zero,neg_zero]

theorem gaussian_mixed_direct_trace {n : ℕ} (σ : ℝ) :
    let μ := standardGaussianCoordinates n
    (∑ i : Fin n, ∫ p, gaussianMixPort (gaussianMixedVector σ p) i i ∂μ.prod μ) =
      (n:ℝ)*(n-1)*(1+σ^2) := by
  dsimp only
  have h (i : Fin n) := (gaussian_mixed_mean_port σ i i).2
  simp_rw [h]
  simp [mul_assoc]

private theorem gaussian_port_centered_identity {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, ∑ j, (a i*a j - (if i=j then 1 else 0))*gaussianMixPort b i j) =
      gaussianExteriorSquare a b - ∑ i, gaussianMixPort b i i := by
  have hOne (i : Fin n) : (∑ j, a i*a j*gaussianMixPort b i j) =
      a i*a i*(b ⬝ᵥ b) - (a i*b i)*(a ⬝ᵥ b) := by
    unfold gaussianMixPort dotProduct
    simp_rw [mul_sub,Finset.sum_sub_distrib,mul_ite,mul_zero]
    have hDiag : (∑ j, if i=j then a i*a j*(∑ i, b i*b i) else 0) = a i*a i*(∑ i, b i*b i) := by simp
    rw [hDiag]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hTwo (i : Fin n) : (∑ j, (if i=j then 1 else 0)*gaussianMixPort b i j) = gaussianMixPort b i i := by
    simp_rw [ite_mul,one_mul,zero_mul]
    simp
  simp_rw [sub_mul,Finset.sum_sub_distrib,hOne,hTwo,Finset.sum_sub_distrib,← Finset.sum_mul]
  unfold gaussianExteriorSquare dotProduct
  rw [pow_two]

/-- The centered-quadratic correction is the entire difference
between the two prescriptions in this literal finite Gaussian example. -/
theorem gaussian_mixed_centered_correction {n : ℕ} (σ : ℝ) :
    let μ := standardGaussianCoordinates n
    let b := gaussianMixedVector (n := n) σ
    (∫ p, ∑ i, ∑ j, (p.1 i*p.1 j-(if i=j then 1 else 0))*gaussianMixPort (b p) i j ∂μ.prod μ) =
      -((n:ℝ)*(n-1)) := by
  dsimp only
  simp_rw [gaussian_port_centered_identity]
  have h := gaussian_mixed_exterior_sewing (n := n) σ
  have hTrace := gaussian_mixed_direct_trace (n := n) σ
  change (∫ p, gaussianExteriorSquare p.1 (p.1+σ • p.2) -
    ∑ i, gaussianMixPort (gaussianMixedVector σ p) i i
      ∂(standardGaussianCoordinates n).prod (standardGaussianCoordinates n)) = _
  rw [integral_sub h.1 (integrable_finset_sum _ (fun i _ => (gaussian_mixed_mean_port σ i i).1)),h.2,
    integral_finset_sum _ (fun i _ => (gaussian_mixed_mean_port σ i i).1),hTrace]
  ring

/-- With no independent mark, the closed action and its common background
variation vanish, while an open unit-coordinate probe has positive Hessian. -/
theorem gaussian_shared_zero_probe {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    let μ := (standardGaussianCoordinates n).prod (standardGaussianCoordinates n)
    (∀ (a h : Fin n → ℝ), gaussianExteriorSquare (a + h) (a + h) = 0) ∧
      0 < deriv (deriv (fun t : ℝ => ∫ p, gaussianExteriorSquare
        (t • (Pi.single i (1 : ℝ) : Fin n → ℝ)) p.1 ∂μ)) 0 := by
  dsimp only
  refine ⟨fun a h => by unfold gaussianExteriorSquare; ring, ?_⟩
  have hAxis (t : ℝ) (b : Fin n → ℝ) :
      gaussianExteriorSquare (t • (Pi.single i (1 : ℝ) : Fin n → ℝ)) b =
        t^2 * gaussianMixPort b i i := by
    unfold gaussianExteriorSquare gaussianMixPort dotProduct
    simp [Pi.single_apply]
    ring
  simp_rw [hAxis, integral_const_mul]
  have hPort : (∫ p, gaussianMixPort p.1 i i
      ∂(standardGaussianCoordinates n).prod (standardGaussianCoordinates n)) = (n:ℝ)-1 := by
    simpa [gaussianMixedVector] using (gaussian_mixed_mean_port 0 i i).2
  rw [hPort]
  have hFirst (t : ℝ) : deriv (fun x : ℝ => x^2*((n:ℝ)-1)) t = 2*t*((n:ℝ)-1) := by
    convert ((hasDerivAt_id t).pow 2 |>.mul_const ((n:ℝ)-1)).deriv using 1
    simp
  rw [funext hFirst]
  have hSecond : deriv (fun t : ℝ => 2*t*((n:ℝ)-1)) 0 = 2*((n:ℝ)-1) := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const ((n:ℝ)-1)).deriv
  rw [hSecond]
  have : (2:ℝ) ≤ n := by exact_mod_cast hn
  linarith

end UV.MarkedPhoton
