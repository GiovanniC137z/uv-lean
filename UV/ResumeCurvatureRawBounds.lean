import UV.NextCurvatureFourierSummability
import Mathlib.Analysis.PSeries

/-! Polynomially regularized raw Gaussian Fourier coordinates on the same
four-torus. The regularization is the inverse cube of 1 plus the squared
Euclidean frequency, kept separate from the normal-depth transfer. -/

noncomputable section

open MeasureTheory Real Filter
open scoped BigOperators ENNReal NNReal

namespace UV.ResumeCurvatureRawBounds

open UV.FurtherCurvatureShell UV.NextCurvatureLaw
open UV.RevisionCurvatureDeterminant (latticeFrequency)

def rawRegularization (k : MeanZeroMode) : ℝ :=
  ((1 + latticeFrequency k ^ 2) ^ 3)⁻¹

theorem rawRegularization_nonneg (k : MeanZeroMode) : 0 ≤ rawRegularization k := by
  unfold rawRegularization
  positivity

private def shell (j : ℕ) : Finset MeanZeroMode :=
  (modeShell j).subtype (· ≠ 0)

private theorem mem_shell (j : ℕ) (k : MeanZeroMode) :
    k ∈ shell j ↔ latticeHeight k = j + 1 := by
  rw [shell, Finset.mem_subtype, mem_modeShell]

private theorem shell_card_le (j : ℕ) :
    ((shell j).card : ℝ) ≤ 80 * ((j+1 : ℕ) : ℝ) ^ 3 := by
  have hf : (shell j).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ modeShell j := by
    intro k hk
    obtain ⟨k', h',rfl⟩ := Finset.mem_map.mp hk
    exact Finset.mem_subtype.mp h'
  have h := Finset.card_le_card hf
  rw [Finset.card_map] at h
  exact (Nat.cast_le.mpr h).trans (modeShell_card j)

private theorem shell_pointwise_bound (j : ℕ) (k : MeanZeroMode) (hk : k ∈ shell j) :
    rawRegularization k ≤ (((j+1 : ℕ) : ℝ)^6)⁻¹ := by
  let R : ℝ := ((j+1 : ℕ) : ℝ)
  have hR : 0 < R := by positivity
  have hr : R ≤ latticeFrequency k := by
    simpa only [R, (mem_shell j k).1 hk] using latticeHeight_le_latticeFrequency k
  change ((1 + latticeFrequency k ^ 2)^3)⁻¹ ≤ (R^6)⁻¹
  apply inv_anti₀ (by positivity)
  rw [show (6:ℕ) = 2*3 by decide, pow_mul]
  apply pow_le_pow_left₀ (sq_nonneg _) _ 3
  exact (pow_le_pow_left₀ hR.le hr 2).trans (le_add_of_nonneg_left zero_le_one)

/-- The genuine lattice sum of the inverse-cubed elliptic multiplier is
finite by the four-dimensional signed cube shell count. -/
theorem rawRegularization_summable : Summable rawRegularization := by
  let s (j : ℕ) : Set MeanZeroMode := shell j
  have hcover (k : MeanZeroMode) : ∃! j : ℕ, k ∈ s j := by
    have hk := Nat.pos_of_ne_zero (latticeHeight_ne_zero k.2)
    refine ⟨latticeHeight k - 1, (mem_shell _ k).2 (by omega), ?_⟩
    intro y hy
    have he := (mem_shell y k).1 hy
    omega
  refine (summable_partition (fun k => rawRegularization_nonneg k) hcover).2 ⟨?_, ?_⟩
  · intro j
    letI : Fintype ((s j : Set MeanZeroMode)) := (shell j).fintypeCoeSort
    exact summable_of_finite_support (Set.toFinite _)
  have hsum : Summable (fun j : ℕ => 80 * (((j+1 : ℕ) : ℝ)^3)⁻¹) := by
    have hs : Summable (fun j : ℕ => ((j : ℝ)^3)⁻¹) :=
      Real.summable_nat_pow_inv.2 (by norm_num)
    exact ((summable_nat_add_iff 1).2 hs).mul_left _
  apply hsum.of_nonneg_of_le
  · intro j
    exact tsum_nonneg (fun _ => rawRegularization_nonneg _)
  intro j
  letI : Fintype ((s j : Set MeanZeroMode)) := (shell j).fintypeCoeSort
  let R : ℝ := ((j+1 : ℕ) : ℝ)
  have hR : 0 < R := by positivity
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _k : (s j : Set MeanZeroMode), (R^6)⁻¹ :=
      Finset.sum_le_sum fun k _ => shell_pointwise_bound _ k k.2
    _ = ((shell j).card : ℝ) * (R^6)⁻¹ := by
      simp [s, nsmul_eq_mul]
    _ ≤ (80*(R^3))*(R^6)⁻¹ :=
      mul_le_mul_of_nonneg_right (shell_card_le _) (by positivity)
    _ = _ := by change (80 * R ^ 3) * (R^6)⁻¹ = 80*(R^3)⁻¹; field_simp

private theorem eval_integrable_abs (n : ℕ) (i : ModeSlot n) :
    Integrable (fun X : ModeSlot n → ℝ => |X i|) (commonGaussian n) := by
  have hbase : sourceGaussian (1/2 : ℝ) = sourceGaussianBase := by
    unfold sourceGaussian
    norm_num
  have hf : Integrable (fun x : ℝ => |x|) sourceGaussianBase := by
    simpa only [hbase, norm_pow, pow_one, Real.norm_eq_abs] using
      (sourceGaussian_power_integrable (1/2) 1).norm
  have he := measurePreserving_eval_infinitePi (μ := fun _ : ModeSlot n => sourceGaussianBase) i
  unfold commonGaussian
  simpa only [Function.comp_def, Function.eval] using he.integrable_comp_of_integrable hf

private theorem eval_integral_abs (n : ℕ) (i : ModeSlot n) :
    (∫ X, |X i| ∂commonGaussian n) = ∫ x : ℝ, |x| ∂sourceGaussianBase := by
  have h := measurePreserving_eval_infinitePi (μ := fun _ : ModeSlot n => sourceGaussianBase) i
  rw [← h.map_eq, integral_map h.measurable.aemeasurable
    (by fun_prop : Measurable (fun x : ℝ => |x|)).aestronglyMeasurable]
  rfl

private theorem ae_rawCommon_summable (n : ℕ) :
    ∀ᵐ X ∂commonGaussian n,
      Summable fun i : ModeSlot n => rawRegularization i.1 * |X i| := by
  let w (i : ModeSlot n) := rawRegularization i.1
  let f (i : ModeSlot n) (X : ModeSlot n → ℝ) := w i * |X i|
  have hw (i : ModeSlot n) : 0 ≤ w i := rawRegularization_nonneg i.1
  have hs : Summable w := by
    apply (summable_prod_of_nonneg hw).2
    refine ⟨fun _ => summable_of_finite_support (Set.toFinite _), ?_⟩
    simp only [w, tsum_fintype, Finset.sum_const, nsmul_eq_mul]
    exact rawRegularization_summable.mul_left _
  have hfi (i : ModeSlot n) : Integrable (f i) (commonGaussian n) :=
    (eval_integrable_abs n i).const_mul _
  have hn (i : ModeSlot n) (X : ModeSlot n → ℝ) : 0 ≤ f i X :=
    mul_nonneg (hw i) (abs_nonneg _)
  have hg (i : ModeSlot n) : AEMeasurable (fun X => ENNReal.ofReal (f i X)) (commonGaussian n) :=
    (hfi i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  let m := ∫ x : ℝ, |x| ∂sourceGaussianBase
  have hm : 0 ≤ m := integral_nonneg abs_nonneg
  have hintegral (i : ModeSlot n) :
      (∫⁻ X, ENNReal.ofReal (f i X) ∂commonGaussian n) = ENNReal.ofReal (w i * m) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi i) (Eventually.of_forall (hn i))]
    dsimp only [f, m]
    rw [integral_const_mul, eval_integral_abs]
  have hfinite : (∫⁻ X, (∑' i, ENNReal.ofReal (f i X)) ∂commonGaussian n) ≠ ∞ := by
    rw [lintegral_tsum hg]
    simp_rw [hintegral]
    let a (i : ModeSlot n) : ℝ≥0 := ⟨w i * m, mul_nonneg (hw i) hm⟩
    have he (i : ModeSlot n) : ENNReal.ofReal (w i * m) = (a i : ℝ≥0∞) :=
      ENNReal.ofReal_eq_coe_nnreal (mul_nonneg (hw i) hm)
    simp_rw [he]
    exact ENNReal.tsum_coe_ne_top_iff_summable_coe.2 (hs.mul_right m)
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hg) hfinite] with X hX
  let a (i : ModeSlot n) : ℝ≥0 := ⟨f i X, hn i X⟩
  have he (i : ModeSlot n) : ENNReal.ofReal (f i X) = (a i : ℝ≥0∞) :=
    ENNReal.ofReal_eq_coe_nnreal (hn i X)
  simp_rw [he] at hX
  change Summable fun i => (a i : ℝ)
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.1 hX.ne

private theorem rescaleFactor_le_two (ℓ : ℝ) (k : MeanZeroMode) :
    sqrt (2 * UV.FurtherCurvatureLine.curvatureCovariance ℓ k) ≤ 2 := by
  have hr : 1 ≤ latticeFrequency k := by
    have hi : (1:ℝ) ≤ (latticeHeight k : ℝ) :=
      Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (latticeHeight_ne_zero k.2))
    exact hi.trans (latticeHeight_le_latticeFrequency k)
  have hc : (latticeFrequency k ^ 2)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ hr
  apply (sqrt_le_left zero_le_two).2
  have hm := (mode_covariance_le_boundary ℓ k).trans hc
  linarith

/-- All real depths use the same probability-one set for summability of the
regularized raw readouts. This estimate uses the original variance bound. -/
theorem ae_regularized_coordinates_summable (n : ℕ) :
    ∀ᵐ X ∂commonGaussian n, ∀ ℓ : ℝ,
      Summable fun i : ModeSlot n => rawRegularization i.1 * |depthRescale ℓ X i| := by
  filter_upwards [ae_rawCommon_summable n] with X hX
  intro ℓ
  apply (hX.mul_left 2).of_nonneg_of_le (fun _ => mul_nonneg (rawRegularization_nonneg _) (abs_nonneg _))
  intro i
  unfold depthRescale
  rw [abs_mul, abs_of_nonneg (sqrt_nonneg _), ← mul_assoc, ← mul_assoc, mul_comm 2 (rawRegularization i.1)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rescaleFactor_le_two ℓ i.1) (rawRegularization_nonneg _))
    (abs_nonneg _)

end UV.ResumeCurvatureRawBounds
