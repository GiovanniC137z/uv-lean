import UV.ContinueRelativeSpectralMoment
import UV.ContinueRelativeSpectralResolvent

/-! Combining scalar positive-measure rigidity with the strict diagonal
test of a charged rest mode. -/

noncomputable section

namespace UV.RelativeSpectrum

open Filter MeasureTheory UV.ContinueRelativeSpectralMoment
open scoped ComplexInnerProductSpace Topology

/-- The real carrier frequency multiplies the axial Clifford eigenvalue
in the free inverse. The final carrier contraction gives the spectral
pole with the corresponding signed energy. -/
theorem free_rest_factor_on_unit_eigenspinor
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {f : H} (hf : ‖f‖ = 1) (m ω : ℝ) {ε : ℝ} (hε : ε^2 = 1) :
    (ε:ℂ) * inner ℂ f ((((m:ℂ)+((ε*ω:ℝ):ℂ)*Complex.I)⁻¹) • f) = kernel ω (ε*m) := by
  have hc : (ε:ℂ)*(ε:ℂ) = 1 := by exact_mod_cast (sq ε).symm.trans hε
  have hi : (ε:ℂ)⁻¹ = (ε:ℂ) := inv_eq_of_mul_eq_one_right hc
  have hinner : inner ℂ f f = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f
    rw [hf] at h
    exact h.trans (show (1:ℂ)^2 = 1 by norm_num)
  rw [inner_smul_right,hinner,mul_one]
  conv_lhs => arg 1; rw [← hi]
  rw [← mul_inv_rev]
  have he : ((m:ℂ)+((ε*ω:ℝ):ℂ)*Complex.I) * (ε:ℂ) = (ω:ℂ)*Complex.I+(ε*m:ℝ) := by
    push_cast
    linear_combination (ω:ℂ)*Complex.I*hc
  rw [he,kernel]

/-- In a single incoming unit carrier eigenspinor, rapid agreement with the
free pole at high frequencies and a strict fixed-frequency diagonal response
exclude a positive unsubtracted spectral law. -/
theorem no_positive_rest_fibre_from_diagonal
    (g : ℝ → ℂ) (ell : ℝ) {w : ℝ}
    (hdefect : g w ≠ kernel w ell)
    {ω : ℕ → ℝ} (hω : ∀ n, 0 < ω n) (htop : Tendsto ω atTop atTop)
    (herr : Tendsto (fun n => (((ω n)^3 : ℝ) : ℂ) * (g (ω n) - kernel (ω n) ell)) atTop (𝓝 0)) :
    ¬ ∃ μ : Measure ℝ, (∀ n, Integrable (kernel (ω n)) μ) ∧
      (∀ n, g (ω n) = coefficient μ (ω n)) ∧ g w = coefficient μ w := by
  rintro ⟨μ,hi,hg,hw⟩
  have he : μ = Measure.dirac ell := by
    apply measure_eq_dirac_of_resolvent_error hω htop hi
    simpa only [← hg] using herr
  apply hdefect
  rw [hw,he,coefficient,integral_dirac]


theorem no_positive_rest_fibre_of_weighted_resolvent
    {A H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace A] {ν : Measure A} {d : A → ENNReal}
    (hd : AEMeasurable d ν) (hdpos : ∀ᵐ a ∂ν, d a ≠ 0) [IsProbabilityMeasure (ν.withDensity d)]
    {m w ε : ℝ} (hm : 0 < m) (hε : ε^2 = 1)
    (f : H) (hf : ‖f‖ = 1) {R : A → H}
    (hR : AEStronglyMeasurable R (ν.withDensity d)) (K : A → H → H) (K₀ : H → H)
    (hEq : ∀ᵐ a ∂(ν.withDensity d), f = (m:ℂ) • R a + K a (R a))
    (hSkew : ∀ᵐ a ∂(ν.withDensity d), (inner ℂ (R a) (K a (R a))).re = 0)
    (y : H) (hy : y = ((m:ℂ)+((ε*w:ℝ):ℂ)*Complex.I)⁻¹ • f)
    (hFreeEq : f = (m:ℂ) • y + K₀ y) (hFreeSkew : (inner ℂ y (K₀ y)).re = 0)
    (hNontrivial : ¬ ∀ᵐ a ∂ν, K a y = K₀ y)
    (g : ℝ → ℂ) (hg : g w = (ε:ℂ) * ∫ a, inner ℂ f (R a) ∂(ν.withDensity d))
    {ω : ℕ → ℝ} (hω : ∀ n, 0 < ω n) (htop : Tendsto ω atTop atTop)
    (herr : Tendsto (fun n => (((ω n)^3 : ℝ) : ℂ) * (g (ω n) - kernel (ω n) (ε*m))) atTop (𝓝 0)) :
    ¬ ∃ μ : Measure ℝ, (∀ n, Integrable (kernel (ω n)) μ) ∧
      (∀ n, g (ω n) = coefficient μ (ω n)) ∧ g w = coefficient μ w := by
  apply no_positive_rest_fibre_from_diagonal g (ε*m) _ hω htop herr
  intro h
  have hdg := reweighted_relative_resolvent_diagonal_obstruction hd hdpos hm f y _ hy
    hR K K₀ hEq hSkew hFreeEq hFreeSkew hNontrivial
  apply hdg
  have heR : ε ≠ 0 := by
    intro h0
    simp [h0] at hε
  have he : (ε:ℂ) ≠ 0 := by exact_mod_cast heR
  apply mul_left_cancel₀ he
  rw [← hg,h,hy,free_rest_factor_on_unit_eigenspinor hf m w hε]

end UV.RelativeSpectrum
