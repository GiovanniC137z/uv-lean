import UV.ContinueClosingPositiveSpectral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! First and second signed-energy moments of the compressed positive
spectral law, obtained from actual graph convergence on the operator domain. -/

noncomputable section

open Filter MeasureTheory Set ContinuousLinearMap
open scoped Topology InnerProductSpace ENNReal

namespace UV.SectorPlane

variable {H S : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]

private theorem closing_diagonal_real_apply (P : SourcePVM H) (x : H) {U : Set ℝ}
    (hU : MeasurableSet U) :
    (closingSpectralDiagonal P x).real U = ‖P.projection U x‖ ^ 2 := by
  rw [measureReal_def, closing_spectral_diagonal_apply P x hU, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem closing_simple_first_moment (P : SourcePVM H) (x : H) (f : SimpleFunc ℝ ℝ) :
    (∫ E, f E ∂closingSpectralDiagonal P x) = (⟪x, sourceSimpleSpectralIntegral P f x⟫_ℂ).re := by
  classical
  rw [f.integral_eq_sum f.integrable_of_isFiniteMeasure]
  simp only [sourceSimpleSpectralIntegral, sum_apply, smul_apply, inner_sum, inner_smul_right,
    Complex.re_sum, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro v _
  have hm := f.measurableSet_fiber v
  rw [closing_diagonal_real_apply P x hm, closing_projection_inner_self P hm,
    ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]

theorem closing_simple_second_moment (P : SourcePVM H) (C : SourceBorelCalculus P)
    (x : H) (f : SimpleFunc ℝ ℝ) :
    (∫ E, f E ^ 2 ∂closingSpectralDiagonal P x) = ‖sourceSimpleSpectralIntegral P f x‖ ^ 2 := by
  let g := f.map (fun t => t * t)
  have hg : C.operator g = C.operator f * C.operator f :=
    C.mul f f (sourceBoundedBorel_simple f) (sourceBoundedBorel_simple f)
  have hs : (C.operator f).adjoint = C.operator f :=
    (C.selfAdjoint f (sourceBoundedBorel_simple f)).star_eq
  rw [show (fun E => f E ^ 2) = g by funext E; exact pow_two _,
    closing_simple_first_moment P x g, ← sourceBorel_simple C g, hg, mul_apply, ← hs,
    adjoint_inner_right, hs, sourceBorel_simple C f]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

set_option maxHeartbeats 500000 in
theorem closing_diagonal_energy_second_moment {K : H →ₗ.[ℂ] H}
    (P : SourceSpectralResolution K) (x : K.domain) :
    Integrable (fun E => E ^ 2) (closingSpectralDiagonal P.measure (x : H)) ∧
      (∫ E, E ^ 2 ∂closingSpectralDiagonal P.measure (x : H)) = ‖K x‖ ^ 2 := by
  let μ := closingSpectralDiagonal P.measure (x : H)
  letI : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (closingSpectralDiagonal P.measure (x : H)))
  let U := fun n => sourceSimpleSpectralIntegral P.measure (sourceCoordinateApprox n) (x : H)
  have hT : Tendsto U atTop (𝓝 (K x)) :=
    (P.moment (x : H) (K x)).mp (K.mem_graph_iff.mpr ⟨x, rfl, rfl⟩)
  have hf (n : ℕ) : Measurable (fun E => (sourceCoordinateApprox n E) ^ 2) :=
    (sourceCoordinateApprox n).measurable.pow_const _
  have hi (n : ℕ) : Integrable (fun E => (sourceCoordinateApprox n E) ^ 2) μ := by
    obtain ⟨C, hC, hbound⟩ := (sourceBoundedBorel_simple (sourceCoordinateApprox n)).2
    refine (integrable_const (C ^ 2)).mono' (hf n).aestronglyMeasurable ?_
    exact Eventually.of_forall fun E => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using ((sq_le_sq₀ (abs_nonneg _) hC).mpr (hbound E))
  have hn (n : ℕ) : (∫ E, (sourceCoordinateApprox n E) ^ 2 ∂μ) = ‖U n‖ ^ 2 :=
    closing_simple_second_moment P.measure P.calculus (x : H) (sourceCoordinateApprox n)
  have hp (E : ℝ) : Tendsto (fun n => (sourceCoordinateApprox n E) ^ 2) atTop (𝓝 (E ^ 2)) :=
    (sourceCoordinateApprox_tendsto E).pow 2
  have hL : Tendsto (fun n => ∫⁻ E, ENNReal.ofReal ((sourceCoordinateApprox n E) ^ 2) ∂μ)
      atTop (𝓝 (ENNReal.ofReal (‖K x‖ ^ 2))) := by
    have heq (n : ℕ) : (∫⁻ E, ENNReal.ofReal ((sourceCoordinateApprox n E) ^ 2) ∂μ) =
        ENNReal.ofReal (‖U n‖ ^ 2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall fun _ => sq_nonneg _), hn n]
    simp_rw [heq]
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((hT.norm).pow 2)
  have hfinite : ∫⁻ E, ENNReal.ofReal (E ^ 2) ∂μ < ∞ := by
    calc
      _ = ∫⁻ E, liminf (fun n => ENNReal.ofReal ((sourceCoordinateApprox n E) ^ 2)) atTop ∂μ :=
        lintegral_congr fun E => ((ENNReal.continuous_ofReal.tendsto _).comp (hp E)).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ E, ENNReal.ofReal ((sourceCoordinateApprox n E) ^ 2) ∂μ) atTop :=
        lintegral_liminf_le fun n => (hf n).ennreal_ofReal
      _ = ENNReal.ofReal (‖K x‖ ^ 2) := hL.liminf_eq
      _ < ∞ := ENNReal.ofReal_lt_top
  have hI : Integrable (fun E : ℝ => E ^ 2) μ :=
    ⟨(continuous_id.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).mpr hfinite⟩
  have hD : Tendsto (fun n => ∫ E, (sourceCoordinateApprox n E) ^ 2 ∂μ) atTop
      (𝓝 (∫ E, E ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun E => 4 * E ^ 2)
      (fun n => (hf n).aestronglyMeasurable) (hI.const_mul 4) (fun n => ?_)
      (Eventually.of_forall hp)
    exact Eventually.of_forall fun E => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hb := (sq_le_sq₀ (abs_nonneg (sourceCoordinateApprox n E))
        (by positivity : 0 ≤ 2 * |E|)).mpr (sourceCoordinateApprox_bound n E)
      simpa only [sq_abs, mul_pow, show (2 : ℝ)^2 = 4 by norm_num] using hb
  simp_rw [hn] at hD
  exact ⟨hI, tendsto_nhds_unique hD ((hT.norm).pow 2)⟩

theorem closing_diagonal_energy_first_moment {K : H →ₗ.[ℂ] H}
    (P : SourceSpectralResolution K) (x : K.domain) :
    Integrable (fun E : ℝ => E) (closingSpectralDiagonal P.measure (x : H)) ∧
      (∫ E, E ∂closingSpectralDiagonal P.measure (x : H)) = (⟪(x : H), K x⟫_ℂ).re := by
  let μ := closingSpectralDiagonal P.measure (x : H)
  letI : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (closingSpectralDiagonal P.measure (x : H)))
  have hi : Integrable (fun E : ℝ => E) μ := by
    refine ((integrable_const (1 : ℝ)).add (closing_diagonal_energy_second_moment P x).1).mono'
      continuous_id.aestronglyMeasurable (Eventually.of_forall fun E => ?_)
    change ‖E‖ ≤ 1 + E^2
    rw [Real.norm_eq_abs]
    nlinarith only [sq_abs E, sq_nonneg (|E| - 1)]
  have hT : Tendsto (fun n => sourceSimpleSpectralIntegral P.measure (sourceCoordinateApprox n) (x : H))
      atTop (𝓝 (K x)) := (P.moment (x : H) (K x)).mp (K.mem_graph_iff.mpr ⟨x, rfl, rfl⟩)
  have hD : Tendsto (fun n => ∫ E, sourceCoordinateApprox n E ∂μ) atTop (𝓝 (∫ E, E ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun E => 2 * |E|)
      (fun n => (sourceCoordinateApprox n).measurable.aestronglyMeasurable)
      (hi.abs.const_mul 2) (fun n => Eventually.of_forall fun E => ?_)
      (Eventually.of_forall sourceCoordinateApprox_tendsto)
    simpa only [Real.norm_eq_abs] using sourceCoordinateApprox_bound n E
  have hf (n : ℕ) : (∫ E, sourceCoordinateApprox n E ∂μ) =
      (⟪(x : H), sourceSimpleSpectralIntegral P.measure (sourceCoordinateApprox n) (x : H)⟫_ℂ).re :=
    closing_simple_first_moment P.measure (x : H) (sourceCoordinateApprox n)
  simp_rw [hf] at hD
  have hF : Continuous (fun y : H => (⟪(x : H), y⟫_ℂ).re) :=
    Complex.continuous_re.comp (innerSL ℂ (x : H)).continuous
  exact ⟨hi, tendsto_nhds_unique hD ((hF.tendsto (K x)).comp hT)⟩

omit [CompleteSpace S] in
/-- The finite trace measure has a finite second moment whenever all
isometric slot vectors are in the domain of the spectral operator. -/
theorem closing_finite_trace_energy_second_moment {ι : Type*} [Fintype ι]
    {K : H →ₗ.[ℂ] H} (P : SourceSpectralResolution K) (J : S →ₗᵢ[ℂ] H)
    (b : OrthonormalBasis ι ℂ S) (hJ : ∀ v, J v ∈ K.domain) :
    let ν := ∑ i, closingSpectralDiagonal P.measure (J (b i))
    Integrable (fun E : ℝ => E^2) ν ∧
      (∫ E, E^2 ∂ν) = ∑ i, ‖K ⟨J (b i), hJ _⟩‖^2 := by
  dsimp only
  have hi (i : ι) :=
    (closing_diagonal_energy_second_moment P ⟨J (b i), hJ _⟩).1
  refine ⟨integrable_finset_sum_measure.mpr (fun i _ => hi i), ?_⟩
  rw [integral_finset_sum_measure (fun i _ => hi i)]
  exact Finset.sum_congr rfl fun i _ => (closing_diagonal_energy_second_moment P ⟨J (b i), hJ _⟩).2

end UV.SectorPlane
