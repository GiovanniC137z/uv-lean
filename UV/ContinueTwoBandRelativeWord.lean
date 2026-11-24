import UV.ContinueTwoBandResolvent
import UV.RealDegree
import Mathlib.MeasureTheory.Integral.Prod

/-! The complete relative temporal words on the locked Euclidean plane.
The subtraction is pointwise at the original four-momentum, before either
factor is integrated. No restriction on the real hopping strength is used. -/

noncomputable section
open MeasureTheory Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator

namespace UV.SectorPlane

def twoBandSpatialHop (g σ : ℝ) (k : Spatial) : ℝ := g * Real.exp (-(σ^2 * ‖k‖^2))

@[fun_prop] theorem continuous_twoBandSpatialHop (g σ : ℝ) : Continuous (twoBandSpatialHop g σ) := by
  unfold twoBandSpatialHop
  fun_prop

theorem twoBand_spatial_hop_integrable (g : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun k => |twoBandSpatialHop g σ k|) := by
  have h := (integrable_real_degree_gaussian (μ := (volume : Measure Spatial))
    (a := σ^2) (D := 0) (by positivity) le_rfl).const_mul (|g|/2)
  convert h using 1
  ext k
  simp [twoBandSpatialHop, abs_mul, abs_of_pos (Real.exp_pos _)]
  ring

theorem continuous_twoBandResolvent {m : ℝ} (hm : 0 < m) :
    Continuous (fun x : ℝ × ℝ => twoBandResolvent m x.1 x.2) := by
  have hd : Continuous (fun x : ℝ × ℝ => ((twoBandInversionFactor m x.1 x.2 : ℝ) : ℂ)) := by
    unfold twoBandInversionFactor
    fun_prop
  have hInv := hd.inv₀ (fun x => Complex.ofReal_ne_zero.mpr (by
    unfold twoBandInversionFactor
    positivity))
  apply continuous_matrix
  intro i j
  change Continuous (fun x : ℝ × ℝ =>
    ((twoBandInversionFactor m x.1 x.2 : ℂ)⁻¹) * twoBandNumerator m x.1 x.2 i j)
  apply hInv.mul
  fin_cases i <;> fin_cases j <;> simp [twoBandNumerator] <;> fun_prop

/-- Finite multiplication in increasing order of the labelled marks. -/
def twoBandOrderedProduct (A : ℕ → TwoBandMatrix) : ℕ → TwoBandMatrix
  | 0 => 1
  | n+1 => twoBandOrderedProduct A n * A n

private theorem twoBand_ordered_norm {C : ℝ} (hC : 0 ≤ C) (A : ℕ → TwoBandMatrix)
    (hA : ∀ j, ‖A j‖ ≤ C) (n : ℕ) : ‖twoBandOrderedProduct A n‖ ≤ C^n := by
  induction n with
  | zero => simp [twoBandOrderedProduct]
  | succ n ih =>
    rw [twoBandOrderedProduct, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (hA n) (norm_nonneg _) (pow_nonneg hC n))

private theorem twoBand_ordered_difference {C : ℝ} (hC : 1 ≤ C) (A B : ℕ → TwoBandMatrix)
    (d : ℕ → ℝ) (hA : ∀ j, ‖A j‖ ≤ C) (hB : ∀ j, ‖B j‖ ≤ C)
    (hd : ∀ j, ‖A j - B j‖ ≤ d j) (n : ℕ) :
    ‖twoBandOrderedProduct A n - twoBandOrderedProduct B n‖ ≤ C^n * ∑ j ∈ range n, d j := by
  have hNonneg : 0 ≤ C := le_trans zero_le_one hC
  induction n with
  | zero => simp [twoBandOrderedProduct]
  | succ n ih =>
    let a := twoBandOrderedProduct A n
    let b := twoBandOrderedProduct B n
    have he : a*A n - b*B n = (a-b)*A n + b*(A n-B n) := by noncomm_ring
    change ‖a*A n - b*B n‖ ≤ _
    rw [he, sum_range_succ, pow_succ]
    have hDn : 0 ≤ d n := (norm_nonneg _).trans (hd n)
    calc
      _ ≤ ‖(a-b)*A n‖ + ‖b*(A n-B n)‖ := norm_add_le _ _
      _ ≤ (C^n * ∑ j ∈ range n, d j)*C + C^n*d n := add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul ih (hA n) (norm_nonneg _) (mul_nonneg
          (pow_nonneg hNonneg n) (sum_nonneg fun j _ => (norm_nonneg _).trans (hd j)))))
        ((norm_mul_le _ _).trans (mul_le_mul (twoBand_ordered_norm hNonneg B hB n) (hd n)
          (norm_nonneg _) (pow_nonneg hNonneg n)))
      _ ≤ (C^n*C) * (∑ j ∈ range n, d j + d n) := by
        rw [mul_add, mul_right_comm]
        exact add_le_add_left (mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (pow_nonneg hNonneg n) hC) hDn) _

def twoBandRelativeWord (m g σ : ℝ) (n : ℕ) (b : ℕ → ℝ) (c : ℕ → Spatial)
    (p : ℝ × Spatial) : ℂ :=
  (twoBandOrderedProduct
    (fun j => twoBandResolvent m (twoBandSpatialHop g σ (p.2+c j)) (p.1+b j)) n -
   twoBandOrderedProduct (fun j => twoBandResolvent m 0 (p.1+b j)) n).trace

theorem twoBand_relative_word_bound {m : ℝ} (hm : 0 < m) (g σ : ℝ) (n : ℕ)
    (b : ℕ → ℝ) (c : ℕ → Spatial) (p : ℝ × Spatial) :
    ‖twoBandRelativeWord m g σ n b c p‖ ≤
      (2 * (max 1 m⁻¹)^n) * ∑ j ∈ range n,
        (twoBandFrequencyBound m (p.1+b j))^2 * |twoBandSpatialHop g σ (p.2+c j)| := by
  let A := fun j => twoBandResolvent m (twoBandSpatialHop g σ (p.2+c j)) (p.1+b j)
  let B := fun j => twoBandResolvent m 0 (p.1+b j)
  let d := fun j => (twoBandFrequencyBound m (p.1+b j))^2 * |twoBandSpatialHop g σ (p.2+c j)|
  have hR (v ξ : ℝ) : ‖twoBandResolvent m v ξ‖ ≤ max 1 m⁻¹ := by
    obtain ⟨h₁,h₂⟩ := twoBand_resolvent_bound hm v ξ
    exact (h₁.trans h₂).trans (le_max_right _ _)
  have hd (j : ℕ) : ‖A j - B j‖ ≤ d j := by
    simpa only [A, B, d, sub_zero, mul_comm] using
      twoBand_resolvent_difference_bound hm (twoBandSpatialHop g σ (p.2+c j)) 0 (p.1+b j)
  let D := twoBandOrderedProduct A n - twoBandOrderedProduct B n
  have hk := twoBand_ordered_difference (le_max_left 1 m⁻¹) A B d
    (fun j => hR _ _) (fun j => hR _ _) hd n
  change ‖D.trace‖ ≤ _
  rw [mul_assoc]
  exact (twoBand_trace_norm D).trans (mul_le_mul_of_nonneg_left hk (by norm_num))

theorem continuous_twoBandOrderedProduct {E : Type*} [TopologicalSpace E]
    (A : ℕ → E → TwoBandMatrix) (hA : ∀ j, Continuous (A j)) (n : ℕ) :
    Continuous (fun x => twoBandOrderedProduct (fun j => A j x) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact ih.matrix_mul (hA n)

set_option maxHeartbeats 1200000 in
theorem twoBand_relative_word_integrable {m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (g : ℝ) (n : ℕ) (b : ℕ → ℝ) (c : ℕ → Spatial) :
    Integrable (twoBandRelativeWord m g σ n b c) ∧
      (∫ p, ‖twoBandRelativeWord m g σ n b c p‖) ≤
        2 * (max 1 m⁻¹)^n * n * (Real.pi / m) * ∫ k, |twoBandSpatialHop g σ k| := by
  let F := fun ω => (twoBandFrequencyBound m ω)^2
  let H := fun k => |twoBandSpatialHop g σ k|
  let W := fun j (p : ℝ × Spatial) => F (p.1+b j) * H (p.2+c j)
  have hF : Integrable F := (twoBand_frequency_integral hm).1
  have hH : Integrable H := twoBand_spatial_hop_integrable g hσ
  have hTF (j : ℕ) := measurePreserving_add_right (volume : Measure ℝ) (b j)
  have hTH (j : ℕ) := measurePreserving_add_right (volume : Measure Spatial) (c j)
  have hW (j : ℕ) : Integrable (W j) :=
    ((hTF j).integrable_comp_of_integrable hF).mul_prod ((hTH j).integrable_comp_of_integrable hH)
  have contR := continuous_twoBandResolvent hm
  have hA (j : ℕ) : Continuous (fun p : ℝ × Spatial =>
      twoBandResolvent m (twoBandSpatialHop g σ (p.2+c j)) (p.1+b j)) := by
    have hs : Continuous (fun p : ℝ × Spatial => p.2+c j) := continuous_snd.add continuous_const
    have hf : Continuous (fun p : ℝ × Spatial => p.1+b j) := continuous_fst.add continuous_const
    have hc : Continuous (fun p : ℝ × Spatial => (twoBandSpatialHop g σ (p.2+c j), p.1+b j)) :=
      (((continuous_twoBandSpatialHop g σ).comp hs).prodMk hf)
    change Continuous ((fun x : ℝ × ℝ => twoBandResolvent m x.1 x.2) ∘
      (fun p : ℝ × Spatial => (twoBandSpatialHop g σ (p.2+c j), p.1+b j)))
    exact contR.comp hc
  have hB (j : ℕ) : Continuous (fun p : ℝ × Spatial => twoBandResolvent m 0 (p.1+b j)) := by
    have hf : Continuous (fun p : ℝ × Spatial => p.1+b j) := continuous_fst.add continuous_const
    have hc : Continuous (fun p : ℝ × Spatial => ((0:ℝ), p.1+b j)) := continuous_const.prodMk hf
    change Continuous ((fun x : ℝ × ℝ => twoBandResolvent m x.1 x.2) ∘
      (fun p : ℝ × Spatial => ((0:ℝ), p.1+b j)))
    exact contR.comp hc
  have hWord : Continuous (twoBandRelativeWord m g σ n b c) :=
    ((continuous_twoBandOrderedProduct _ hA n).sub
      (continuous_twoBandOrderedProduct _ hB n)).matrix_trace
  let C := 2 * (max 1 m⁻¹)^n
  have hi := (integrable_finset_sum (range n) (fun j _ => hW j)).const_mul C
  have hb (p : ℝ × Spatial) : ‖twoBandRelativeWord m g σ n b c p‖ ≤ C * ∑ j ∈ range n, W j p :=
    twoBand_relative_word_bound hm g σ n b c p
  have hI := hi.mono' hWord.aestronglyMeasurable (ae_of_all _ hb)
  refine ⟨hI, (integral_mono hI.norm hi hb).trans_eq ?_⟩
  have hEq (j : ℕ) : (∫ p, W j p) = (Real.pi / m) * ∫ k, H k := by
    change (∫ p : ℝ × Spatial, F (p.1+b j) * H (p.2+c j)
      ∂(volume : Measure ℝ).prod volume) = _
    have hLeft := (hTF j).integral_comp (Homeomorph.addRight (b j)).measurableEmbedding F
    have hRight := (hTH j).integral_comp (Homeomorph.addRight (c j)).measurableEmbedding H
    exact (integral_prod_mul (fun ω => F (ω+b j)) (fun k => H (k+c j))).trans
      (congrArg₂ (· * ·) (hLeft.trans (twoBand_frequency_integral hm).2) hRight)
  change (∫ p, C * ∑ j ∈ range n, W j p) = _
  rw [integral_const_mul, integral_finset_sum (range n) (fun j _ => hW j)]
  simp_rw [hEq]
  simp [C, H, mul_assoc]

end UV.SectorPlane
