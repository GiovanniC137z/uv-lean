import UV.ContinueOpeningGaussianTotal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Totality of the standard Gaussian phase waves and differentiation
of Fourier tests on densities with an integrable first moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ComplexInnerProductSpace ComplexConjugate ENNReal

namespace UV

theorem opening_gaussian_wave_total :
    (Submodule.span ℂ (Set.range openingGaussianWave)).topologicalClosure=⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro g hg
  have hL1 : Integrable (⇑g) openingGaussianLaw :=
    memLp_one_iff_integrable.mp ((Lp.memLp g).mono_exponent (by norm_num : (1:ℝ≥0∞)≤2))
  have hz (t : ℝ) : (∫ x, g x*openingFourierWave t x ∂openingGaussianLaw)=0 := by
    have h := hg (openingGaussianWave (-t))
      ((Submodule.span ℂ (Set.range openingGaussianWave)).le_topologicalClosure
      (Submodule.subset_span (Set.mem_range_self (-t))))
    rw [←h,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [opening_gaussian_wave_ae (-t)] with x hx
    rw [hx,RCLike.inner_apply,opening_fourier_wave_conj,neg_neg]
  apply Lp.ext
  exact (opening_fourier_density_unique hL1 hz).trans (Lp.coeFn_zero ℂ 2 openingGaussianLaw).symm

/-- Equality of the full negative-frequency tests identifies two L¹ densities. -/
theorem opening_fourier_test_injective {μ : Measure ℝ} [IsFiniteMeasure μ] {f g : ℝ → ℂ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (heq : ∀ t, (∫ x, f x * openingFourierWave (-t) x ∂μ) = ∫ x, g x * openingFourierWave (-t) x ∂μ) :
    f =ᵐ[μ] g := by
  suffices hz : f-g =ᵐ[μ] 0 by
    filter_upwards [hz] with x hx
    exact sub_eq_zero.mp hx
  apply opening_fourier_density_unique (hf.sub hg)
  intro t
  have h := heq (-t)
  rw [neg_neg] at h
  simp only [Pi.sub_apply,sub_mul,integral_sub (opening_wave_mul_integrable hf t) (opening_wave_mul_integrable hg t),h,sub_self]

/-- Differentiation under the Fourier integral with the negative-frequency
convention requires only one absolutely integrable coordinate moment. -/
theorem opening_fourier_test_hasDerivAt {μ : Measure ℝ} {g : ℝ → ℂ} (hg : Integrable g μ)
    (hxg : Integrable (fun x : ℝ => (x:ℂ)*g x) μ) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, g x*openingFourierWave (-s) x ∂μ)
      (∫ x, (-Complex.I)*((x:ℂ)*g x)*openingFourierWave (-t) x ∂μ) t := by
  let F := fun (s x : ℝ) => g x*openingFourierWave (-s) x
  let D := fun (s x : ℝ) => (-Complex.I)*((x:ℂ)*g x)*openingFourierWave (-s) x
  have hD (s) : Integrable (D s) μ := opening_wave_mul_integrable (hxg.const_mul (-Complex.I)) (-s)
  have hder (x s : ℝ) : HasDerivAt (fun t => F t x) (D s x) s := by
    have he := (((((hasDerivAt_id (s:ℂ)).neg).mul_const (x:ℂ)).mul_const Complex.I).cexp).comp_ofReal
    convert he.const_mul (g x) using 1
    · ext t
      simp [F,openingFourierWave]
    · dsimp [D,openingFourierWave]
      push_cast
      ring
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ) (x₀:=t) (F:=F) (F':=D) (bound:=fun x : ℝ => ‖(x:ℂ)*g x‖)
    (show (0:ℝ)<1 by norm_num) (Eventually.of_forall fun s => (opening_wave_mul_integrable hg (-s)).aestronglyMeasurable)
    (opening_wave_mul_integrable hg (-t)) (hD t).aestronglyMeasurable ?_ hxg.norm
    (Eventually.of_forall fun x s _ => hder x s)).2
  exact Eventually.of_forall fun x s _ => by
    simp only [D,norm_mul,norm_neg,Complex.norm_I,opening_fourier_wave_norm,one_mul,mul_one,le_refl]

/-- Every vector in the Gaussian Hilbert space has an integrable first moment. -/
theorem opening_gaussian_first_moment_integrable (g : OpeningGaussianCarrier) :
    Integrable (fun x : ℝ => (x:ℂ)*g x) openingGaussianLaw := by
  have hx : MemLp (fun x : ℝ => (x:ℂ)) 2 openingGaussianLaw :=
    (memLp_id_gaussianReal' 2 (by norm_num)).ofReal
  exact hx.integrable_mul (Lp.memLp g)

/-- Fourier tests of Hilbert vectors are their inner products against the phase waves. -/
theorem opening_gaussian_test_inner (g : OpeningGaussianCarrier) (t : ℝ) :
    ⟪openingGaussianWave t,g⟫ = ∫ x, g x * openingFourierWave (-t) x ∂openingGaussianLaw := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [opening_gaussian_wave_ae t] with x hx
  rw [hx,RCLike.inner_apply,opening_fourier_wave_conj]

/-- Differentiation of all phase-wave matrix elements identifies the actual unbounded
coordinate multiplier, including square-integrability of the resulting vector. -/
theorem opening_gaussian_position_of_test_derivative (u v : OpeningGaussianCarrier)
    (h : ∀ t, HasDerivAt (fun s => ⟪openingGaussianWave s,u⟫) ((-Complex.I)*⟪openingGaussianWave t,v⟫) t) :
    (fun x : ℝ => (x:ℂ)*u x) =ᵐ[openingGaussianLaw] ⇑v := by
  have hi (z : OpeningGaussianCarrier) : Integrable (⇑z) openingGaussianLaw :=
    memLp_one_iff_integrable.mp ((Lp.memLp z).mono_exponent (by norm_num : (1:ℝ≥0∞)≤2))
  have hm := opening_gaussian_first_moment_integrable u
  apply opening_fourier_test_injective hm (hi v)
  intro t
  have h1 := h t
  simp only [opening_gaussian_test_inner] at h1
  have h2 := (opening_fourier_test_hasDerivAt (hi u) hm t).unique h1
  simp_rw [mul_assoc (-Complex.I)] at h2
  rw [integral_const_mul] at h2
  exact mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) h2

end UV
