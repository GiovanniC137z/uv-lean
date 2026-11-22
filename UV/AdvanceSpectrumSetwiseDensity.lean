import UV.AdvanceSpectrumCompletion
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-! The density of a finite restriction of the setwise-positive matrix
spectral measure. Positivity is derived on the common trace measure. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

variable {α : Type*} [MeasurableSpace α]

private theorem complex_quadratic_nonneg {a b : ℝ} {c : ℂ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : ‖c‖^2 ≤ a*b) (u v : ℝ) :
    0 ≤ a + (u^2+v^2)*b - 2*(u*c.re+v*c.im) := by
  let S := u^2+v^2
  let L := u*c.re+v*c.im
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hL : L^2 ≤ S*(a*b) := by
    calc
      _ ≤ S*(c.re^2+c.im^2) := by dsimp [S,L]; nlinarith [sq_nonneg (u*c.im-v*c.re)]
      _ ≤ S*(a*b) := by
        apply mul_le_mul_of_nonneg_left _ hS
        rw [Complex.sq_norm, Complex.normSq_apply] at hc
        nlinarith only [hc]
  have hsum : 0 ≤ a+S*b := by positivity
  change 0 ≤ a+S*b-2*L
  by_contra! hn
  have hh : a+S*b < 2*L := by linarith
  have hsq := (sq_lt_sq₀ hsum (hsum.trans hh.le)).2 hh
  nlinarith [sq_nonneg (a-S*b)]

private theorem complex_det_of_quadratic {a b : ℝ} {c : ℂ} (hb : 0 ≤ b)
    (h : ∀ u v : ℝ, 0 ≤ a+(u^2+v^2)*b-2*(u*c.re+v*c.im)) :
    ‖c‖^2 ≤ a*b := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  by_cases hz : b = 0
  · have hre : c.re = 0 := by
      by_contra hne
      have hh := h ((a+1)/(2*c.re)) 0
      rw [hz] at hh
      have he : ((a+1)/(2*c.re))*c.re = (a+1)/2 := by field_simp
      simp only [mul_zero, add_zero, zero_mul, he] at hh
      linarith
    have him : c.im = 0 := by
      by_contra hne
      have hh := h 0 ((a+1)/(2*c.im))
      rw [hz] at hh
      have he : ((a+1)/(2*c.im))*c.im = (a+1)/2 := by field_simp
      simp only [mul_zero, add_zero, zero_mul, zero_add, he] at hh
      linarith
    simp [hz, hre, him]
  · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hz)
    have hh := h (c.re/b) (c.im/b)
    have he : a + ((c.re/b)^2+(c.im/b)^2)*b - 2*((c.re/b)*c.re+(c.im/b)*c.im) =
        a - (c.re*c.re+c.im*c.im)/b := by field_simp; ring
    rw [he] at hh
    exact (div_le_iff₀ hbp).1 (sub_nonneg.mp hh)

/-- Measure-level setwise determinant positivity yields pointwise
determinant positivity for integrable scalar densities. -/
theorem setwise_density_det_nonnegative {μ : Measure α} {a b : α → ℝ} {c : α → ℂ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : Integrable c μ)
    (ha₀ : ∀ᵐ s ∂μ, 0 ≤ a s) (hb₀ : ∀ᵐ s ∂μ, 0 ≤ b s)
    (hset : ∀ S, MeasurableSet S → ‖∫ s in S, c s ∂μ‖^2 ≤
      (∫ s in S, a s ∂μ)*(∫ s in S, b s ∂μ)) :
    ∀ᵐ s ∂μ, 0 ≤ a s ∧ 0 ≤ b s ∧ ‖c s‖^2 ≤ a s*b s := by
  have hquad (u v : ℝ) : ∀ᵐ s ∂μ,
      0 ≤ a s+(u^2+v^2)*b s-2*(u*(c s).re+v*(c s).im) := by
    have hreF : Integrable (fun s => (c s).re) μ := Complex.reCLM.integrable_comp hc
    have himF : Integrable (fun s => (c s).im) μ := Complex.imCLM.integrable_comp hc
    have hab := ha.add (hb.const_mul (u^2+v^2))
    have hc' := ((hreF.const_mul u).add (himF.const_mul v)).const_mul 2
    apply ae_nonneg_of_forall_setIntegral_nonneg (hab.sub hc')
    intro S hS _
    simp only [Pi.sub_apply]
    rw [integral_sub hab.integrableOn hc'.integrableOn]
    simp only [Pi.add_apply]
    rw [integral_add ha.integrableOn (hb.const_mul _).integrableOn,
      integral_const_mul, integral_const_mul,
      integral_add (hreF.const_mul _).integrableOn (himF.const_mul _).integrableOn,
      integral_const_mul, integral_const_mul]
    have hre := Complex.reCLM.integral_comp_comm (μ := μ.restrict S) hc.integrableOn
    have him := Complex.imCLM.integral_comp_comm (μ := μ.restrict S) hc.integrableOn
    change (∫ s in S, (c s).re ∂μ) = (∫ s in S, c s ∂μ).re at hre
    change (∫ s in S, (c s).im ∂μ) = (∫ s in S, c s ∂μ).im at him
    rw [hre, him]
    exact complex_quadratic_nonneg (setIntegral_nonneg_of_ae ha₀)
      (setIntegral_nonneg_of_ae hb₀) (hset S hS) u v
  have hrat : ∀ᵐ s ∂μ, ∀ u v : ℚ,
      0 ≤ a s+((u:ℝ)^2+(v:ℝ)^2)*b s-2*((u:ℝ)*(c s).re+(v:ℝ)*(c s).im) :=
    ae_all_iff.2 fun u => ae_all_iff.2 fun v => hquad u v
  filter_upwards [ha₀, hb₀, hrat] with s has hbs hrat'
  refine ⟨has,hbs,complex_det_of_quadratic hbs ?_⟩
  exact DenseRange.induction_on₂ (Rat.denseRange_cast (𝕜 := ℝ))
    (p := fun u v => 0 ≤ a s+(u^2+v^2)*b s-2*(u*(c s).re+v*(c s).im))
    (isClosed_le continuous_const (by fun_prop)) hrat'

theorem finite_complex_withDensity_rnDeriv_eq {μ : Measure α} [SigmaFinite μ]
    {ν : ComplexMeasure α} (hν : ν ≪ᵥ μ.toENNRealVectorMeasure) :
    μ.withDensityᵥ (ν.rnDeriv μ) = ν := by
  have hac := (ComplexMeasure.absolutelyContinuous_ennreal_iff ν μ.toENNRealVectorMeasure).1 hν
  have hRe := SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hac.1
  have hIm := SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hac.2
  ext1 S hS
  have hC := ν.integrable_rnDeriv μ
  rw [withDensityᵥ_apply hC hS]
  apply Complex.ext
  · have he := Complex.reCLM.integral_comp_comm (μ := μ.restrict S) hC.integrableOn
    change (∫ s in S, ν.re.rnDeriv μ s ∂μ) = (∫ s in S, ν.rnDeriv μ s ∂μ).re at he
    rw [← he, ← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hS, hRe]
    rfl
  · have he := Complex.imCLM.integral_comp_comm (μ := μ.restrict S) hC.integrableOn
    change (∫ s in S, ν.im.rnDeriv μ s ∂μ) = (∫ s in S, ν.rnDeriv μ s ∂μ).im at he
    rw [← he, ← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hS, hIm]
    rfl

/-- Absolute continuity of the complex cross entry follows directly from
the setwise determinant inequality. -/
theorem finite_setwise_cross_absolutelyContinuous {ν₁ ν₂ : Measure α} (νc : ComplexMeasure α)
    (hset : ∀ S, MeasurableSet S → ‖νc S‖^2 ≤ ν₁.real S*ν₂.real S) :
    νc ≪ᵥ (ν₁+ν₂).toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro S hS hz
  rw [Measure.toENNRealVectorMeasure_apply_measurable hS, Measure.add_apply, add_eq_zero] at hz
  have h := hset S hS
  simp only [measureReal_def, hz.1, ENNReal.toReal_zero, zero_mul] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (νc S)])

/-- The actual finite measures have common Radon–Nikodym densities
whose two-by-two matrix is positive almost everywhere. -/
theorem finite_setwise_spectral_density {ν₁ ν₂ : Measure α}
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (νc : ComplexMeasure α)
    (hset : ∀ S, MeasurableSet S → ‖νc S‖^2 ≤ ν₁.real S*ν₂.real S) :
    let μ := ν₁+ν₂
    let a := fun s => (ν₁.rnDeriv μ s).toReal
    let b := fun s => (ν₂.rnDeriv μ s).toReal
    let c := νc.rnDeriv μ
    Integrable a μ ∧ Integrable b μ ∧ Integrable c μ ∧
    (∀ S, MeasurableSet S →
      (∫ s in S, a s ∂μ) = ν₁.real S ∧
      (∫ s in S, b s ∂μ) = ν₂.real S ∧
      (∫ s in S, c s ∂μ) = νc S) ∧
    (∀ᵐ s ∂μ, 0 ≤ a s ∧ 0 ≤ b s ∧ ‖c s‖^2 ≤ a s*b s) := by
  dsimp only
  have hac₁ : ν₁ ≪ ν₁+ν₂ := (Measure.le_add_right le_rfl).absolutelyContinuous
  have hac₂ : ν₂ ≪ ν₁+ν₂ := (Measure.le_add_left le_rfl).absolutelyContinuous
  have hCeq := finite_complex_withDensity_rnDeriv_eq
    (finite_setwise_cross_absolutelyContinuous νc hset)
  have hInt₁ := Measure.integrable_toReal_rnDeriv (μ := ν₁) (ν := ν₁+ν₂)
  have hInt₂ := Measure.integrable_toReal_rnDeriv (μ := ν₂) (ν := ν₁+ν₂)
  have hIntC := νc.integrable_rnDeriv (ν₁+ν₂)
  have hEq (S : Set α) (hS : MeasurableSet S) :
      (∫ s in S, (ν₁.rnDeriv (ν₁+ν₂) s).toReal ∂(ν₁+ν₂)) = ν₁.real S ∧
      (∫ s in S, (ν₂.rnDeriv (ν₁+ν₂) s).toReal ∂(ν₁+ν₂)) = ν₂.real S ∧
      (∫ s in S, νc.rnDeriv (ν₁+ν₂) s ∂(ν₁+ν₂)) = νc S := by
    refine ⟨Measure.setIntegral_toReal_rnDeriv hac₁ S, Measure.setIntegral_toReal_rnDeriv hac₂ S, ?_⟩
    rw [← withDensityᵥ_apply hIntC hS, hCeq]
  refine ⟨hInt₁,hInt₂,hIntC,hEq,?_⟩
  apply setwise_density_det_nonnegative hInt₁ hInt₂ hIntC
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg)
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg)
  intro S hS
  obtain ⟨h₁,h₂,hc⟩ := hEq S hS
  rw [h₁,h₂,hc]
  exact hset S hS

end UV.RevisionSpectrum
