import UV.FurtherCurvatureGraph
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! Integration of the uniform four-torus contraction tail over a finite
nonnegative-depth law. The law may have an atom at zero. -/

noncomputable section

open Filter Real MeasureTheory
open scoped BigOperators Topology

namespace UV.FurtherCurvatureGraph

open UV.FurtherCurvatureShell UV.FurtherCurvatureLine UV.FurtherCurvatureDeterminant
open UV.RevisionCurvatureDeterminant

private theorem determinant_measurable (n : ℕ) (Λ : ℝ) :
    Measurable fun ℓ : ℝ => sphericalDeterminant n Λ ℓ := by
  unfold sphericalDeterminant relativeDeterminant
  apply Measurable.inv
  apply Finset.measurable_prod
  intro k _
  fun_prop

private theorem line_measurable (k : TorusMode) :
    Measurable fun ℓ : ℝ => curvatureLine ℓ k := by
  unfold curvatureLine curvatureCovariance
  fun_prop

private theorem spherical_tail_measurable {I n : ℕ} (Λ M : ℝ)
    (coeff : ℝ → Assignment I → ℝ) (hc : ∀ a, Measurable (fun ℓ => coeff ℓ a)) :
    Measurable fun ℓ => sphericalTail n Λ ℓ M (coeff ℓ) := by
  unfold sphericalTail
  apply Finset.measurable_sum
  intro a _
  unfold absoluteTerm
  have habs : Measurable (fun ℓ => |coeff ℓ a|) := by
    simpa only [Real.norm_eq_abs] using (hc a).norm
  exact ((determinant_measurable n Λ).mul habs).mul
    (Finset.measurable_prod _ fun e _ => line_measurable (a e))

/-- For the fixed-sector contraction product the uniform absolute bound
can be integrated over any finite depth measure supported on ℓ ≥ 0. -/
theorem integrated_spherical_tail_uniform {I n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C > 0, ∀ {Λ M B : ℝ}, 0 ≤ Λ → 0 < M →
      ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], (∀ᵐ ℓ ∂μ, 0 ≤ ℓ) →
      ∀ coeff : ℝ → Assignment I → ℝ, (∀ a, Measurable (fun ℓ => coeff ℓ a)) →
      (∀ ℓ a, |coeff ℓ a| ≤ B) →
      Integrable (fun ℓ => sphericalTail n Λ ℓ M (coeff ℓ)) μ ∧
      (∫ ℓ, sphericalTail n Λ ℓ M (coeff ℓ) ∂μ) ≤
        (μ Set.univ).toReal * (C * B * M^(-s)) := by
  obtain ⟨C, hC, hb⟩ := spherical_tail_uniform (I := I) hn hs
  refine ⟨C, hC, fun {Λ M B} hΛ hM μ _ hμ coeff hm hc => ?_⟩
  have hnonneg (ℓ : ℝ) : 0 ≤ sphericalTail n Λ ℓ M (coeff ℓ) := by
    unfold sphericalTail
    apply Finset.sum_nonneg
    intro a _
    exact absolute_term_nonneg
      (relative_determinant_bounds (sphericalModes Λ) latticeFrequency ℓ n).1.le _ _
  have hub : ∀ᵐ ℓ ∂μ, sphericalTail n Λ ℓ M (coeff ℓ) ≤ C*B*M^(-s) := by
    filter_upwards [hμ] with ℓ hℓ
    exact hb hΛ hℓ hM (coeff ℓ) (hc ℓ)
  have hf : Integrable (fun ℓ => sphericalTail n Λ ℓ M (coeff ℓ)) μ :=
    Integrable.of_bound (spherical_tail_measurable Λ M coeff hm).aestronglyMeasurable
      (C*B*M^(-s)) (by
        filter_upwards [hub] with ℓ hℓ
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg ℓ)] using hℓ)
  refine ⟨hf, ?_⟩
  have hi := integral_mono_ae hf (integrable_const (C*B*M^(-s))) hub
  simpa only [integral_const, smul_eq_mul, Measure.real] using hi


/-- The full finite-cutoff absolute contraction sum goes to zero at the
depth-zero atom, including graphs with no internal line. -/
theorem zero_depth_absolute_graph_limit {I n : ℕ} (hn : 0 < n) {B : ℝ}
    (coeff : Assignment I → ℝ) (hc : ∀ a, |coeff a| ≤ B) :
    Tendsto (fun Λ : ℝ => ∑ a ∈ Fintype.piFinset (fun _ : Fin I => sphericalModes Λ),
      absoluteTerm (sphericalDeterminant n Λ 0) 0 coeff a) atTop (𝓝 0) := by
  obtain ⟨L, hL, hl⟩ := spherical_weighted_line_bound (s := 0) le_rfl
  let D : ℝ := (2:ℝ) * (I:ℝ)
  have hD : 0 ≤ D := by unfold D; positivity
  have hb := (abs_nonneg (coeff 0)).trans (hc 0)
  have ht := (zero_depth_polynomial_limit hn hD).const_mul (B * L^I)
  rw [mul_zero] at ht
  refine squeeze_zero' ?_ ?_ ht
  · filter_upwards with Λ
    apply Finset.sum_nonneg
    intro a _
    exact absolute_term_nonneg
      (relative_determinant_bounds (sphericalModes Λ) latticeFrequency 0 n).1.le _ _
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with Λ hΛ
    let H := sphericalDeterminant n Λ 0
    have hH : 0 ≤ H := (relative_determinant_bounds (sphericalModes Λ) latticeFrequency 0 n).1.le
    have he := hl hΛ (ℓ := 0) le_rfl
    simp only [effectiveRadius, add_zero] at he
    calc
      _ ≤ H * B * (∑ k ∈ sphericalModes Λ, weightedLine 0 0 k)^I :=
        finite_absolute_sum_bound hH le_rfl (sphericalModes Λ) coeff hc
      _ ≤ H * B * (L * (1+Λ)^(2:ℝ))^I := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => weightedLine_nonneg 0 0 k)) he _)
        (mul_nonneg hH hb)
      _ = (B*L^I)*(H*(1+Λ)^D) := by
        rw [mul_pow, ← Real.rpow_natCast ((1+Λ)^(2:ℝ)), ← Real.rpow_mul (by positivity)]
        ring

end UV.FurtherCurvatureGraph
