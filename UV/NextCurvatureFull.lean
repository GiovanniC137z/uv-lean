import UV.FurtherCurvatureIntegration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The unrestricted torus graph obtained from the same determinant and
internal lines as its spherical restrictions. The residual coefficients may
include bounded color factors, conservation indicators and fixed external
modes. The common normal depth is kept throughout. -/

noncomputable section

open Filter Real MeasureTheory
open scoped BigOperators Topology

namespace UV.NextCurvatureFull

open UV.FurtherCurvatureShell UV.FurtherCurvatureLine UV.FurtherCurvatureDeterminant
open UV.FurtherCurvatureGraph
open UV.RevisionCurvatureDeterminant

private def cutoffAssignments {I : ℕ} (Λ : ℝ) : Finset (Assignment I) :=
  Fintype.piFinset (fun _ : Fin I => sphericalModes Λ)

private def augmentedAssignments {I : ℕ} (Λ : ℝ) : Finset (Assignment I) :=
  Fintype.piFinset (fun _ : Fin I => insert 0 (sphericalModes Λ))

private theorem augmented_assignments_cofinal {I : ℕ} :
    Tendsto (augmentedAssignments (I := I)) atTop atTop := by
  refine tendsto_atTop.mpr (fun A => ?_)
  let R := ∑ a ∈ A, ∑ e : Fin I, latticeFrequency (a e)
  refine eventually_atTop.mpr ⟨R, fun Λ hΛ a ha => ?_⟩
  apply Fintype.mem_piFinset.mpr
  intro e
  by_cases he : a e = 0
  · simp [he]
  refine Finset.mem_insert_of_mem (mem_sphericalModes.mpr ⟨he, ?_⟩)
  have hin : latticeFrequency (a e) ≤ ∑ j : Fin I, latticeFrequency (a j) :=
    Finset.single_le_sum (f := fun j => latticeFrequency (a j))
      (fun _ _ => sqrt_nonneg _) (Finset.mem_univ e)
  have hnonneg (b : Assignment I) (_ : b ∈ A) :
      0 ≤ ∑ j : Fin I, latticeFrequency (b j) :=
    Finset.sum_nonneg (fun j _ => (sqrt_nonneg _ : 0 ≤ latticeFrequency (b j)))
  have houter : (∑ j : Fin I, latticeFrequency (a j)) ≤ R :=
    Finset.single_le_sum hnonneg ha
  exact hin.trans (houter.trans hΛ)

def curvatureGraphTerm {I : ℕ} (ℓ : ℝ) (coeff : Assignment I → ℝ) (a : Assignment I) : ℝ :=
  coeff a * ∏ e, curvatureLine ℓ (a e)

private theorem graph_term_eq_zero_of_zero_mode {I : ℕ} (ℓ : ℝ) (coeff : Assignment I → ℝ)
    (a : Assignment I) {e : Fin I} (he : a e = 0) :
    curvatureGraphTerm ℓ coeff a = 0 := by
  unfold curvatureGraphTerm
  rw [Finset.prod_eq_zero (Finset.mem_univ e) ?_, mul_zero]
  simp [he, curvatureLine, curvatureCovariance, latticeFrequency]

private theorem cutoff_sum_eq_augmented {I : ℕ} (Λ ℓ : ℝ) (coeff : Assignment I → ℝ) :
    (∑ a ∈ cutoffAssignments Λ, curvatureGraphTerm ℓ coeff a) =
      ∑ a ∈ augmentedAssignments Λ, curvatureGraphTerm ℓ coeff a := by
  apply Finset.sum_subset
  · intro a ha
    exact Fintype.mem_piFinset.mpr fun e =>
      Finset.mem_insert_of_mem (Fintype.mem_piFinset.mp ha e)
  · intro a ha ha'
    obtain ⟨e, he⟩ : ∃ e : Fin I, a e ∉ sphericalModes Λ := by
      by_contra! h
      exact ha' (Fintype.mem_piFinset.mpr h)
    exact graph_term_eq_zero_of_zero_mode ℓ coeff a
      ((Finset.mem_insert.mp (Fintype.mem_piFinset.mp ha e)).resolve_right he)

private theorem graph_term_norm_eq {I : ℕ} (ℓ : ℝ) (coeff : Assignment I → ℝ)
    (a : Assignment I) : ‖curvatureGraphTerm ℓ coeff a‖ = absoluteTerm 1 ℓ coeff a := by
  have hp : 0 ≤ ∏ e, curvatureLine ℓ (a e) := by
    apply Finset.prod_nonneg
    intro e _
    unfold curvatureLine curvatureCovariance
    positivity
  rw [curvatureGraphTerm, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hp,
    absoluteTerm, one_mul]

/-- The literal positive-depth assignment sum is absolutely summable, with
the product of the one-line sums as its positive majorant. Zero modes vanish
on an internal line and the empty product covers graphs without such lines. -/
theorem full_graph_term_norm_summable {I : ℕ} {ℓ B : ℝ} (hℓ : 0 < ℓ)
    (coeff : Assignment I → ℝ) (hc : ∀ a, |coeff a| ≤ B) :
    Summable (fun a => ‖curvatureGraphTerm ℓ coeff a‖) ∧
      ∑' a, ‖curvatureGraphTerm ℓ coeff a‖ ≤ B * (∑' k, weightedLine 0 ℓ k)^I := by
  obtain ⟨_, _, hline⟩ := full_weighted_line_bound (s := 0) le_rfl
  have hS := (hline hℓ).1
  have hB : 0 ≤ B := (abs_nonneg (coeff 0)).trans (hc 0)
  have hb (A : Finset (Assignment I)) :
      ∑ a ∈ A, ‖curvatureGraphTerm ℓ coeff a‖ ≤ B * (∑' k, weightedLine 0 ℓ k)^I := by
    let modes := A.biUnion fun a => Finset.univ.image a
    have hsub : A ⊆ Fintype.piFinset (fun _ : Fin I => modes) := by
      intro a ha
      exact Fintype.mem_piFinset.mpr fun e => Finset.mem_biUnion.mpr
        ⟨a, ha, Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩
    simp_rw [graph_term_norm_eq]
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun a _ _ => absolute_term_nonneg zero_le_one coeff a)).trans ?_
    refine (finite_absolute_sum_bound (s := 0) zero_le_one le_rfl modes coeff hc).trans ?_
    rw [one_mul]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => weightedLine_nonneg 0 ℓ k))
        (hS.sum_le_tsum _ (fun k _ => weightedLine_nonneg 0 ℓ k)) I) hB
  have hsum := summable_of_sum_le (fun a : Assignment I => norm_nonneg (curvatureGraphTerm ℓ coeff a)) hb
  exact ⟨hsum, hsum.tsum_le_of_sum_le hb⟩

def sphericalGraphSum {I : ℕ} (n : ℕ) (Λ ℓ : ℝ) (coeff : Assignment I → ℝ) : ℝ :=
  sphericalDeterminant n Λ ℓ * ∑ a ∈ cutoffAssignments Λ, curvatureGraphTerm ℓ coeff a

def fullGraphSum {I : ℕ} (n : ℕ) (ℓ : ℝ) (coeff : Assignment I → ℝ) : ℝ :=
  if 0 < ℓ then fullDeterminant n ℓ * ∑' a, curvatureGraphTerm ℓ coeff a else 0

private theorem spherical_graph_norm_bound {I n : ℕ} {Λ ℓ B : ℝ}
    (coeff : Assignment I → ℝ) (hc : ∀ a, |coeff a| ≤ B) :
    ‖sphericalGraphSum n Λ ℓ coeff‖ ≤
      sphericalDeterminant n Λ ℓ * B * (∑ k ∈ sphericalModes Λ, weightedLine 0 ℓ k)^I := by
  have hH : 0 ≤ sphericalDeterminant n Λ ℓ :=
    (relative_determinant_bounds (sphericalModes Λ) latticeFrequency ℓ n).1.le
  unfold sphericalGraphSum
  rw [norm_mul, Real.norm_of_nonneg hH]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hH).trans ?_
  simp_rw [graph_term_norm_eq, absoluteTerm, one_mul]
  rw [Finset.mul_sum]
  have heq :
      ∑ a ∈ cutoffAssignments Λ, sphericalDeterminant n Λ ℓ *
        (|coeff a| * ∏ e, curvatureLine ℓ (a e)) =
      ∑ a ∈ cutoffAssignments Λ, absoluteTerm (sphericalDeterminant n Λ ℓ) ℓ coeff a := by
    simp only [absoluteTerm, mul_assoc]
  rw [heq]
  exact finite_absolute_sum_bound (s := 0) hH le_rfl (sphericalModes Λ) coeff hc

/-- One determinant at the common depth bounds the complete spherical graph,
uniformly in the cutoff and in all nonnegative depths. -/
theorem spherical_graph_uniform {I n : ℕ} (hn : 0 < n) :
    ∃ C > 0, ∀ {Λ ℓ B : ℝ}, 0 ≤ Λ → 0 ≤ ℓ →
      ∀ coeff : Assignment I → ℝ, (∀ a, |coeff a| ≤ B) →
        ‖sphericalGraphSum n Λ ℓ coeff‖ ≤ C * B := by
  obtain ⟨L, hL, hl⟩ := spherical_weighted_line_bound (s := 0) le_rfl
  obtain ⟨P, hP, hp⟩ := spherical_determinant_polynomial_control hn (D := 2 * (I : ℝ)) (by positivity)
  refine ⟨L ^ I * P, by positivity, fun {Λ ℓ B} hΛ hℓ coeff hc => ?_⟩
  let R := effectiveRadius Λ ℓ
  let H := sphericalDeterminant n Λ ℓ
  have hR : 0 ≤ R := by
    unfold R effectiveRadius
    split
    · exact hΛ
    · exact le_min hΛ (inv_nonneg.mpr hℓ)
  have hH : 0 ≤ sphericalDeterminant n Λ ℓ :=
    (relative_determinant_bounds (sphericalModes Λ) latticeFrequency ℓ n).1.le
  have hB : 0 ≤ B := (abs_nonneg (coeff 0)).trans (hc 0)
  calc
    _ ≤ H * B * (∑ k ∈ sphericalModes Λ, weightedLine 0 ℓ k)^I :=
      spherical_graph_norm_bound coeff hc
    _ ≤ H * B * (L * (1+R)^(2:ℝ))^I := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => weightedLine_nonneg 0 ℓ k)) _ _)
        (mul_nonneg hH hB)
      simpa only [add_zero] using (hl hΛ hℓ)
    _ = L^I * B * (H * (1+R)^(2*(I:ℝ))) := by
      rw [mul_pow, ← Real.rpow_natCast ((1+R)^(2:ℝ)), ← Real.rpow_mul (by positivity)]
      ring
    _ ≤ (L^I * P)*B := by
      calc
        _ ≤ L^I * B * P := mul_le_mul_of_nonneg_left (hp hΛ hℓ) (by positivity)
        _ = _ := by ring

/-- For the same bounded residual coefficient, the spherical graphs converge
to the literal all-mode sum at positive depth, and to zero at the atom. -/
theorem spherical_graph_limit {I n : ℕ} (hn : 0 < n) {ℓ B : ℝ} (hℓ : 0 ≤ ℓ)
    (coeff : Assignment I → ℝ) (hc : ∀ a, |coeff a| ≤ B) :
    Tendsto (fun Λ : ℝ => sphericalGraphSum n Λ ℓ coeff) atTop (𝓝 (fullGraphSum n ℓ coeff)) := by
  rcases hℓ.eq_or_lt with hzero | hpos
  · subst ℓ
    rw [fullGraphSum, if_neg (by simp)]
    have hnorm (Λ : ℝ) : ‖sphericalGraphSum n Λ 0 coeff‖ ≤
        ∑ a ∈ cutoffAssignments Λ, absoluteTerm (sphericalDeterminant n Λ 0) 0 coeff a := by
      have hH : 0 ≤ sphericalDeterminant n Λ 0 :=
        (relative_determinant_bounds (sphericalModes Λ) latticeFrequency 0 n).1.le
      unfold sphericalGraphSum
      rw [norm_mul, Real.norm_of_nonneg hH]
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hH).trans_eq ?_
      simp_rw [graph_term_norm_eq, absoluteTerm, one_mul, Finset.mul_sum, mul_assoc]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hnorm (zero_depth_absolute_graph_limit hn coeff hc)
  · rw [fullGraphSum, if_pos hpos]
    have hsum : Summable (curvatureGraphTerm ℓ coeff) :=
      (full_graph_term_norm_summable hpos coeff hc).1.of_norm
    have hfin := hsum.hasSum.comp (augmented_assignments_cofinal (I := I))
    have hcut : Tendsto (fun Λ : ℝ => ∑ a ∈ cutoffAssignments Λ, curvatureGraphTerm ℓ coeff a)
        atTop (𝓝 (∑' a, curvatureGraphTerm ℓ coeff a)) := by
      simp_rw [cutoff_sum_eq_augmented]
      exact hfin
    exact (positive_depth_determinant_limit n hpos).mul hcut

private theorem sphericalGraphSum_measurable {I n : ℕ} (Λ : ℝ)
    (coeff : ℝ → Assignment I → ℝ) (hc : ∀ a, Measurable (fun ℓ => coeff ℓ a)) :
    Measurable fun ℓ => sphericalGraphSum n Λ ℓ (coeff ℓ) := by
  unfold sphericalGraphSum
  apply Measurable.mul
  · unfold sphericalDeterminant relativeDeterminant
    apply Measurable.inv
    apply Finset.measurable_prod
    intro k _
    fun_prop
  · apply Finset.measurable_sum
    intro a _
    apply (hc a).mul
    apply Finset.measurable_prod
    intro e _
    unfold curvatureLine curvatureCovariance
    fun_prop

/-- The common finite depth measure can include a zero atom. The unrestricted
coefficient, using the same residual terms as every spherical cutoff, is
integrable and equals the limit of the integrated cutoffs. -/
theorem integrated_full_graph_limit {I n : ℕ} (hn : 0 < n)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    {B : ℝ} (coeff : ℝ → Assignment I → ℝ) (hm : ∀ a, Measurable (fun ℓ => coeff ℓ a))
    (hc : ∀ ℓ a, |coeff ℓ a| ≤ B) :
    Integrable (fun ℓ => fullGraphSum n ℓ (coeff ℓ)) μ ∧
      Tendsto (fun Λ : ℝ => ∫ ℓ, sphericalGraphSum n Λ ℓ (coeff ℓ) ∂μ)
        atTop (𝓝 (∫ ℓ, fullGraphSum n ℓ (coeff ℓ) ∂μ)) := by
  obtain ⟨C, _, hb⟩ := spherical_graph_uniform (I := I) hn
  have hpoint : ∀ᵐ ℓ ∂μ, Tendsto (fun Λ : ℝ => sphericalGraphSum n Λ ℓ (coeff ℓ))
      atTop (𝓝 (fullGraphSum n ℓ (coeff ℓ))) := hμ.mono
        fun ℓ hℓ => spherical_graph_limit hn hℓ (coeff ℓ) (hc ℓ)
  have hconst : Integrable (fun _ : ℝ => C * B) μ := integrable_const _
  have hbound : ∀ᶠ Λ : ℝ in atTop, ∀ᵐ ℓ ∂μ, ‖sphericalGraphSum n Λ ℓ (coeff ℓ)‖ ≤ C * B := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with Λ hΛ
    exact hμ.mono fun ℓ hℓ => hb hΛ hℓ _ (hc ℓ)
  have hmeas : ∀ᶠ Λ : ℝ in atTop, AEStronglyMeasurable
      (fun ℓ => sphericalGraphSum n Λ ℓ (coeff ℓ)) μ :=
    Eventually.of_forall fun Λ => (sphericalGraphSum_measurable Λ coeff hm).aestronglyMeasurable
  have hmeas_seq : ∀ N : ℕ, AEStronglyMeasurable
      (fun ℓ => sphericalGraphSum n N ℓ (coeff ℓ)) μ :=
    fun N => (sphericalGraphSum_measurable (n := n) N coeff hm).aestronglyMeasurable
  have hpoint_seq : ∀ᵐ ℓ ∂μ, Tendsto (fun N : ℕ => sphericalGraphSum n N ℓ (coeff ℓ))
      atTop (𝓝 (fullGraphSum n ℓ (coeff ℓ))) :=
    hpoint.mono (fun ℓ h => h.comp tendsto_natCast_atTop_atTop)
  have hlimitmeas := aestronglyMeasurable_of_tendsto_ae atTop hmeas_seq hpoint_seq
  have hlimitbound : ∀ᵐ ℓ ∂μ, ‖fullGraphSum n ℓ (coeff ℓ)‖ ≤ C * B := by
    filter_upwards [hpoint, hμ] with ℓ ht hℓ
    exact le_of_tendsto ht.norm (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with Λ hΛ
      exact hb hΛ hℓ _ (hc ℓ))
  exact ⟨hconst.mono' hlimitmeas hlimitbound,
    tendsto_integral_filter_of_dominated_convergence _ hmeas hbound hconst hpoint⟩

private def highCoefficient {I : ℕ} (M : ℝ) (coeff : Assignment I → ℝ) (a : Assignment I) : ℝ :=
  if ∃ e, M < latticeFrequency (a e) then |coeff a| else 0

private theorem highCoefficient_bound {I : ℕ} {M B : ℝ} (coeff : Assignment I → ℝ)
    (hc : ∀ a, |coeff a| ≤ B) : ∀ a, |highCoefficient M coeff a| ≤ B := by
  have hB := (abs_nonneg (coeff 0)).trans (hc 0)
  intro a
  unfold highCoefficient
  split <;> simp [hc a, hB]

private theorem highCoefficient_measurable {I : ℕ} {M : ℝ} (coeff : ℝ → Assignment I → ℝ)
    (hc : ∀ a, Measurable (fun ℓ => coeff ℓ a)) (a : Assignment I) :
    Measurable (fun ℓ => highCoefficient M (coeff ℓ) a) := by
  by_cases h : ∃ e, M < latticeFrequency (a e)
  · simp only [highCoefficient, if_pos h]
    simpa only [Real.norm_eq_abs] using (hc a).norm
  · simpa only [highCoefficient, if_neg h] using (measurable_const : Measurable fun _ : ℝ => (0 : ℝ))

private theorem spherical_graph_sum_highCoefficient {I : ℕ} (n : ℕ) (Λ ℓ M : ℝ)
    (coeff : Assignment I → ℝ) :
    sphericalGraphSum n Λ ℓ (highCoefficient M coeff) = sphericalTail n Λ ℓ M coeff := by
  unfold sphericalGraphSum sphericalTail cutoffAssignments
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : ∃ e, M < latticeFrequency (a e)
  · simp [h, highCoefficient, curvatureGraphTerm, absoluteTerm, mul_assoc]
  · simp [h, highCoefficient, curvatureGraphTerm]

/-- The actual unrestricted absolute tail. At positive depth this multiplies
the convergent sum of the high assignments by one determinant. -/
def fullAbsoluteTail {I : ℕ} (n : ℕ) (ℓ M : ℝ) (coeff : Assignment I → ℝ) : ℝ :=
  fullGraphSum n ℓ (highCoefficient M coeff)

theorem spherical_absolute_tail_limit {I n : ℕ} (hn : 0 < n) {ℓ B : ℝ} (hℓ : 0 ≤ ℓ)
    (M : ℝ) (coeff : Assignment I → ℝ) (hc : ∀ a, |coeff a| ≤ B) :
    Tendsto (fun Λ : ℝ => sphericalTail n Λ ℓ M coeff) atTop
      (𝓝 (fullAbsoluteTail n ℓ M coeff)) := by
  simpa only [spherical_graph_sum_highCoefficient, fullAbsoluteTail] using
    spherical_graph_limit hn hℓ (highCoefficient M coeff) (highCoefficient_bound coeff hc)

/-- The finite-cutoff tail estimates pass to the actual unrestricted graph
and its shared depth integral, including measures with a zero atom. -/
theorem integrated_full_absolute_tail {I n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C > 0, ∀ {M B : ℝ}, 0 < M →
      ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], (∀ᵐ ℓ ∂μ, 0 ≤ ℓ) →
      ∀ coeff : ℝ → Assignment I → ℝ, (∀ a, Measurable (fun ℓ => coeff ℓ a)) →
      (∀ ℓ a, |coeff ℓ a| ≤ B) →
      Integrable (fun ℓ => fullAbsoluteTail n ℓ M (coeff ℓ)) μ ∧
      (∫ ℓ, fullAbsoluteTail n ℓ M (coeff ℓ) ∂μ) ≤
        (μ Set.univ).toReal * (C * B * M^(-s)) ∧
      Tendsto (fun Λ : ℝ => ∫ ℓ, sphericalTail n Λ ℓ M (coeff ℓ) ∂μ)
        atTop (𝓝 (∫ ℓ, fullAbsoluteTail n ℓ M (coeff ℓ) ∂μ)) := by
  obtain ⟨C, hC, hsphere⟩ := spherical_tail_uniform (I := I) hn hs
  refine ⟨C, hC, fun {M B} hM μ _ hμ coeff hm hc => ?_⟩
  have hi := integrated_full_graph_limit hn μ hμ (fun ℓ => highCoefficient M (coeff ℓ))
    (highCoefficient_measurable coeff hm) (fun ℓ => highCoefficient_bound (coeff ℓ) (hc ℓ))
  simp only [spherical_graph_sum_highCoefficient] at hi
  refine ⟨hi.1, ?_, hi.2⟩
  have hdom : ∀ᵐ ℓ ∂μ, fullAbsoluteTail n ℓ M (coeff ℓ) ≤ C*B*M^(-s) := by
    filter_upwards [hμ] with ℓ hℓ
    apply le_of_tendsto (spherical_absolute_tail_limit hn hℓ M (coeff ℓ) (hc ℓ))
    filter_upwards [eventually_ge_atTop (0:ℝ)] with Λ hΛ
    exact hsphere hΛ hℓ hM (coeff ℓ) (hc ℓ)
  simpa only [integral_const, smul_eq_mul, Measure.real] using
    integral_mono_ae hi.1 (integrable_const (C*B*M^(-s))) hdom

end UV.NextCurvatureFull
