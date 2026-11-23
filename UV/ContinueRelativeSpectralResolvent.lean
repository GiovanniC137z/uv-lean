import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The positive mean-square test for a mass plus a skew-adjoint operator,
on the Hilbert space of the fixed charged sector. -/

noncomputable section

namespace UV.RelativeSpectrum

open Filter MeasureTheory Complex
open scoped ComplexInnerProductSpace ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A solution of the shifted operator equation obeys the exact real
quadratic identity. Only the diagonal part of skew adjointness is needed,
so this also applies to a solution belonging to an unbounded domain. -/
theorem skew_shift_resolvent_energy (m : ℝ) {f z w : H}
    (hf : f = (m:ℂ) • z + w) (hskew : (inner ℂ z w).re = 0) :
    (inner ℂ f z).re = m * ‖z‖^2 := by
  have hr : (inner ℂ f z).re = (inner ℂ z f).re := inner_re_symm (𝕜 := ℂ) f z
  rw [hr,hf,inner_add_right,inner_smul_right,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hskew,add_zero]
  exact congrArg (fun a => m*a) (inner_self_eq_norm_sq (𝕜 := ℂ) z)

theorem skew_shift_resolvent_bound {m : ℝ} (hm : 0 < m) {f z w : H}
    (hf : f = (m:ℂ) • z + w) (hskew : (inner ℂ z w).re = 0) :
    ‖z‖ ≤ ‖f‖ / m := by
  by_cases hz : z = 0
  · rw [hz,norm_zero]
    positivity
  · have he := skew_shift_resolvent_energy m hf hskew
    have hle : (inner ℂ f z).re ≤ ‖f‖ * ‖z‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    rw [he,pow_two,← mul_assoc,mul_le_mul_iff_left₀ (norm_pos_iff.mpr hz)] at hle
    exact (le_div_iff₀ hm).mpr (by rwa [mul_comm])

/-- The mean-square resolvent identity along an incoming mode whose free
inverse is a scalar multiple of that mode. Only its diagonal coefficient
is needed to evaluate the mixed term. -/
theorem relative_resolvent_diagonal_variance [CompleteSpace H]
    {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m) (f y : H) (c : ℂ) (hy : y = c • f)
    {R : A → H} (hR : MemLp R 2 μ)
    (henergy : ∀ᵐ a ∂μ, (inner ℂ f (R a)).re = m * ‖R a‖^2) :
    (∫ a, ‖R a-y‖^2 ∂μ) =
      m⁻¹ * (∫ a, inner ℂ f (R a) ∂μ).re -
        2 * (star c * (∫ a, inner ℂ f (R a) ∂μ)).re + ‖y‖^2 := by
  have hRi := hR.integrable one_le_two
  have hSq := (memLp_two_iff_integrable_sq_norm hR.aestronglyMeasurable).mp hR
  have hFy := hRi.const_inner (𝕜 := ℂ) y
  have hRe : Integrable (fun a => (inner ℂ y (R a)).re) μ := hFy.re
  have hre (a : A) : ‖R a-y‖^2 = ‖R a‖^2 - 2 * (inner ℂ y (R a)).re + ‖y‖^2 := by
    rw [@norm_sub_sq ℂ,inner_re_symm (𝕜 := ℂ) (R a) y]
    rfl
  simp_rw [hre]
  have hA := integral_add (hSq.sub (hRe.const_mul 2))
    (integrable_const (μ := μ) (‖y‖^2))
  simp only [Pi.sub_apply] at hA
  rw [hA,integral_sub hSq (hRe.const_mul 2),integral_const_mul,integral_const,measureReal_univ_eq_one,one_smul]
  have hFred : (∫ a, (inner ℂ f (R a)).re ∂μ) = (∫ a, inner ℂ f (R a) ∂μ).re :=
    integral_re (hRi.const_inner (𝕜 := ℂ) f)
  have hYred : (∫ a, (inner ℂ y (R a)).re ∂μ) = (∫ a, inner ℂ y (R a) ∂μ).re :=
    integral_re hFy
  have hE : m * (∫ a, ‖R a‖^2 ∂μ) = (∫ a, inner ℂ f (R a) ∂μ).re := by
    rw [← integral_const_mul, ← hFred]
    exact integral_congr_ae (henergy.mono fun _ h => h.symm)
  have hS : (∫ a, ‖R a‖^2 ∂μ) = m⁻¹ * (∫ a, inner ℂ f (R a) ∂μ).re := by
    rw [← hE,← mul_assoc,inv_mul_cancel₀ hm.ne',one_mul]
  rw [hS,hYred,integral_inner hRi y]
  have hin : inner ℂ y (∫ a, R a ∂μ) = star c * inner ℂ f (∫ a, R a ∂μ) := by
    rw [hy,inner_smul_left]
    rfl
  rw [integral_inner hRi f,hin]

theorem relative_resolvent_ae_eq_of_diagonal_eq [CompleteSpace H]
    {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m) (f y : H) (c : ℂ) (hy : y = c • f)
    {R : A → H} (hR : MemLp R 2 μ)
    (henergy : ∀ᵐ a ∂μ, (inner ℂ f (R a)).re = m * ‖R a‖^2)
    (hfree : (inner ℂ f y).re = m * ‖y‖^2)
    (hdiag : (∫ a, inner ℂ f (R a) ∂μ) = inner ℂ f y) :
    R =ᵐ[μ] fun _ => y := by
  have hs : star c * inner ℂ f y = inner ℂ y y := by
    calc
      _ = inner ℂ (c • f) y := (inner_smul_left f y c).symm
      _ = _ := congrArg (fun z => inner ℂ z y) hy.symm
  have hyy : (inner ℂ y y).re = ‖y‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) y
  have hzero : (∫ a, ‖R a-y‖^2 ∂μ) = 0 := by
    rw [relative_resolvent_diagonal_variance hm f y c hy hR henergy,
      hdiag,hfree,hs,hyy,← mul_assoc,inv_mul_cancel₀ hm.ne',one_mul]
    ring
  have hL : MemLp (fun a => R a-y) 2 μ := hR.sub (memLp_const y)
  have hI := (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mp hL
  have hz := (integral_eq_zero_iff_of_nonneg (fun a => sq_nonneg ‖R a-y‖) hI).mp hzero
  filter_upwards [hz] with a ha
  simpa only [Pi.zero_apply,pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0),norm_eq_zero,sub_eq_zero]
    using ha

/-- With the interacting and free equations on the same Hilbert sector,
any positive-probability test of the interaction on the free solution
rules out even a single free diagonal resolvent coefficient. -/
theorem relative_resolvent_diagonal_obstruction [CompleteSpace H]
    {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m) (f y : H) (c : ℂ) (hy : y = c • f)
    {R : A → H} (hR : MemLp R 2 μ) (K : A → H → H) (K₀ : H → H)
    (hEq : ∀ᵐ a ∂μ, f = (m:ℂ) • R a + K a (R a))
    (hSkew : ∀ᵐ a ∂μ, (inner ℂ (R a) (K a (R a))).re = 0)
    (hFreeEq : f = (m:ℂ) • y + K₀ y) (hFreeSkew : (inner ℂ y (K₀ y)).re = 0)
    (hNontrivial : ¬ ∀ᵐ a ∂μ, K a y = K₀ y) :
    (∫ a, inner ℂ f (R a) ∂μ) ≠ inner ℂ f y := by
  intro hdiag
  have henergy := (hEq.and hSkew).mono fun _ ha => skew_shift_resolvent_energy m ha.1 ha.2
  have hy' := relative_resolvent_ae_eq_of_diagonal_eq hm f y c hy hR henergy
    (skew_shift_resolvent_energy m hFreeEq hFreeSkew) hdiag
  apply hNontrivial
  filter_upwards [hy', hEq] with a ha hb
  change R a = y at ha
  rw [ha,hFreeEq,add_right_inj] at hb
  exact hb.symm

theorem reweighted_relative_resolvent_diagonal_obstruction [CompleteSpace H]
    {A : Type*} [MeasurableSpace A] {ν : Measure A} {d : A → ℝ≥0∞}
    (hd : AEMeasurable d ν) (hdpos : ∀ᵐ a ∂ν, d a ≠ 0)
    [IsProbabilityMeasure (ν.withDensity d)]
    {m : ℝ} (hm : 0 < m) (f y : H) (c : ℂ) (hy : y = c • f)
    {R : A → H} (hR : AEStronglyMeasurable R (ν.withDensity d)) (K : A → H → H) (K₀ : H → H)
    (hEq : ∀ᵐ a ∂(ν.withDensity d), f = (m:ℂ) • R a + K a (R a))
    (hSkew : ∀ᵐ a ∂(ν.withDensity d), (inner ℂ (R a) (K a (R a))).re = 0)
    (hFreeEq : f = (m:ℂ) • y + K₀ y) (hFreeSkew : (inner ℂ y (K₀ y)).re = 0)
    (hNontrivial : ¬ ∀ᵐ a ∂ν, K a y = K₀ y) :
    (∫ a, inner ℂ f (R a) ∂(ν.withDensity d)) ≠ inner ℂ f y := by
  have hLp : MemLp R 2 (ν.withDensity d) :=
    MemLp.of_bound hR (‖f‖/m) ((hEq.and hSkew).mono fun _ h => skew_shift_resolvent_bound hm h.1 h.2)
  have hne : ¬ ∀ᵐ a ∂(ν.withDensity d), K a y = K₀ y := by
    intro h
    apply hNontrivial
    have ht := (withDensity_absolutelyContinuous' hd hdpos).ae_eq h
    exact ht
  exact relative_resolvent_diagonal_obstruction (μ := ν.withDensity d) hm f y c hy hLp K K₀ hEq hSkew hFreeEq hFreeSkew hne

end UV.RelativeSpectrum
