import UV.ContinueNetworkPolynomialNormTerms
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Compact

/-! The Gaussian L¹ integral is uniformly equivalent to the coefficient
ℓ¹ norm on a fixed finite complex polynomial space. Positivity follows
from evaluation of the whole polynomial on an open set. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace UV

variable {d : ℕ} {ι : Type*} [Fintype ι]

def directionalCoefficientL1 (a : ι → ℂ) : ℝ :=
  ∑ j, ‖a j‖

private theorem directionalCoefficientL1_nonneg (a : ι → ℂ) :
    0 ≤ directionalCoefficientL1 a :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem directionalCoefficientL1_eq_zero_iff (a : ι → ℂ) :
    directionalCoefficientL1 a = 0 ↔ a = 0 := by
  unfold directionalCoefficientL1
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => norm_nonneg _)]
  simp only [Finset.mem_univ, forall_const, norm_eq_zero, funext_iff, Pi.zero_apply]

private theorem directionalCoefficientL1_mul (r : ℝ) (a : ι → ℂ) :
    directionalCoefficientL1 (fun j => (r : ℂ)*a j) = |r| * directionalCoefficientL1 a := by
  simp only [directionalCoefficientL1, norm_mul, Complex.norm_real, Real.norm_eq_abs, Finset.mul_sum]

private theorem directionalCoefficientL1_continuous :
    Continuous (directionalCoefficientL1 (ι:=ι)) :=
  continuous_finset_sum _ (fun j _ => (continuous_apply j).norm)

private theorem directionalGaussianIntegral_terms_smul (c : ℝ) (w : Fin d → ℝ)
    (γ : ι → (Fin d →₀ ℕ)) (r : ℝ) (a : ι → ℂ) :
    directionalGaussianIntegral c w (directionalPolynomialOfTerms γ (fun j => (r : ℂ)*a j)) =
      |r| * directionalGaussianIntegral c w (directionalPolynomialOfTerms γ a) := by
  unfold directionalGaussianIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with k
  simp only [directionalGaussianIntegrand, directionalPolynomialOfTerms_eval,
    mul_assoc, ← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs]

private theorem directionalGaussianIntegral_terms_zero (c : ℝ) (w : Fin d → ℝ)
    (γ : ι → (Fin d →₀ ℕ)) :
    directionalGaussianIntegral c w (directionalPolynomialOfTerms γ (0 : ι → ℂ)) = 0 := by
  have h := directionalGaussianIntegral_terms_smul c w γ 0 (0 : ι → ℂ)
  simpa only [Complex.ofReal_zero, zero_mul, abs_zero] using h

theorem directionalGaussianIntegral_terms_continuous {c : ℝ} (hc : 0 < c) {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) (γ : ι → (Fin d →₀ ℕ)) :
    Continuous (fun a : ι → ℂ => directionalGaussianIntegral c w (directionalPolynomialOfTerms γ a)) := by
  rw [continuous_iff_continuousAt]
  intro a
  let F (b : ι → ℂ) := directionalGaussianIntegrand c w (directionalPolynomialOfTerms γ b)
  let G (k : DirectionalMomentum d) := (‖a‖+1)*∑ j, directionalGaussianMonomial c w (γ j) k
  have hG : Integrable G := (integrable_finset_sum _
    (fun j _ => directionalGaussianMonomial_integrable hc hw (γ j))).const_mul (‖a‖+1)
  have hnear : ∀ᶠ b in 𝓝 a, ‖b‖ < ‖a‖+1 := by
    exact continuous_norm.continuousAt.eventually_lt continuousAt_const (by linarith)
  change Tendsto (fun b => ∫ k, F b k) (𝓝 a) (𝓝 (∫ k, F a k))
  apply tendsto_integral_filter_of_dominated_convergence G
  · exact Eventually.of_forall fun b =>
      (directionalGaussianIntegrand_terms_integrable hc hw γ b).aestronglyMeasurable
  · filter_upwards [hnear] with b hb
    refine Eventually.of_forall fun k => ?_
    rw [Real.norm_of_nonneg (directionalGaussianIntegrand_nonneg c w _ k)]
    refine (directionalGaussianIntegrand_term_bound c w γ b k).trans ?_
    unfold G
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
      ((norm_le_pi_norm b j).trans hb.le) (directionalGaussianMonomial_nonneg c w _ k)
  · exact hG
  · refine Eventually.of_forall fun k => ?_
    have hK : Continuous (fun b => F b k) := by
      unfold F directionalGaussianIntegrand
      simp only [directionalPolynomialOfTerms_eval]
      exact ((continuous_finset_sum _ (fun j _ =>
        (continuous_apply j).mul continuous_const)).norm).mul continuous_const
    exact hK.continuousAt.tendsto

/-- For fixed positive Gaussian weights and fixed distinct monomials, the
Gaussian integral of the absolute polynomial is equivalent to the sum
of the norms of its coefficients. The constants are uniform in all
complex coefficient vectors. -/
theorem directionalGaussianIntegral_terms_norm_equivalent {c : ℝ} (hc : 0 < c)
    {w : Fin d → ℝ} (hw : ∀ i, 0 < w i) (γ : ι ↪ (Fin d →₀ ℕ)) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ a : ι → ℂ,
      L * directionalCoefficientL1 a ≤
        directionalGaussianIntegral c w (directionalPolynomialOfTerms γ a) ∧
      directionalGaussianIntegral c w (directionalPolynomialOfTerms γ a) ≤
        U * directionalCoefficientL1 a := by
  classical
  let F (a : ι → ℂ) := directionalGaussianIntegral c w (directionalPolynomialOfTerms γ a)
  let M (j : ι) := ∫ k, directionalGaussianMonomial c w (γ j) k
  let U := 1+∑ j, M j
  let S : Set (ι → ℂ) := {a | directionalCoefficientL1 a = 1}
  have hM (j : ι) : 0 ≤ M j :=
    integral_nonneg (directionalGaussianMonomial_nonneg c w (γ j))
  have hU : 0 < U := by dsimp [U]; linarith [Finset.sum_nonneg (fun j _ => hM j) (s := Finset.univ)]
  have hupper (a : ι → ℂ) : F a ≤ U * directionalCoefficientL1 a := by
    refine (directionalGaussianIntegral_term_bound hc hw γ a).trans ?_
    rw [directionalCoefficientL1, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [mul_comm ‖a j‖]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hsum : M j ≤ ∑ j, M j :=
      Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ j)
    dsimp [U]
    linarith
  have hnorm (a : ι → ℂ) (ha : a ≠ 0) : 0 < directionalCoefficientL1 a :=
    lt_of_le_of_ne (directionalCoefficientL1_nonneg a)
      (Ne.symm fun h => ha ((directionalCoefficientL1_eq_zero_iff a).1 h))
  have hrescale (a : ι → ℂ) (ha : a ≠ 0) :
      (fun j => (((directionalCoefficientL1 a)⁻¹ : ℝ) : ℂ)*a j) ∈ S := by
    change directionalCoefficientL1 (fun j => (((directionalCoefficientL1 a)⁻¹ : ℝ) : ℂ)*a j) = 1
    rw [directionalCoefficientL1_mul, abs_of_pos (inv_pos.mpr (hnorm a ha)),
      inv_mul_cancel₀ (hnorm a ha).ne']
  by_cases hS : S.Nonempty
  · have hCompact : IsCompact S := by
      apply (isCompact_closedBall (0 : ι → ℂ) 1).of_isClosed_subset
      · exact isClosed_eq directionalCoefficientL1_continuous continuous_const
      · intro a ha
        rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
        intro j
        have h := Finset.single_le_sum (f := fun k => ‖a k‖)
          (fun k _ => norm_nonneg (a k)) (Finset.mem_univ j)
        exact h.trans_eq ha
    obtain ⟨u,hu,huMin⟩ := hCompact.exists_isMinOn hS
      (directionalGaussianIntegral_terms_continuous hc hw γ).continuousOn
    have hu₀ : u ≠ 0 := by
      intro he
      have hs' : directionalCoefficientL1 u = 1 := hu
      rw [(directionalCoefficientL1_eq_zero_iff u).2 he] at hs'
      norm_num at hs'
    refine ⟨F u,U,directionalGaussianIntegral_terms_pos hc hw γ hu₀,hU,fun a => ⟨?_, hupper a⟩⟩
    by_cases ha : a = 0
    · rw [ha, (directionalCoefficientL1_eq_zero_iff _).2 rfl, mul_zero, directionalGaussianIntegral_terms_zero c w γ]
    · have hh := huMin (hrescale a ha)
      change F u ≤ F (fun j => (((directionalCoefficientL1 a)⁻¹ : ℝ) : ℂ)*a j) at hh
      dsimp only [F] at hh
      rw [directionalGaussianIntegral_terms_smul, abs_of_pos (inv_pos.mpr (hnorm a ha)), ←
        div_eq_inv_mul] at hh
      exact (le_div_iff₀ (hnorm a ha)).1 hh
  · refine ⟨1,U,zero_lt_one,hU,fun a => ⟨?_,hupper a⟩⟩
    have ha : a = 0 := not_ne_iff.mp (fun h => hS ⟨_,hrescale a h⟩)
    rw [ha, (directionalCoefficientL1_eq_zero_iff _).2 rfl, mul_zero, directionalGaussianIntegral_terms_zero c w γ]

end UV
