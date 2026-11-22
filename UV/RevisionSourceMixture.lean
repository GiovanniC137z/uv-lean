import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Fixed-depth covariance matching and the covariance of squared observables
under one shared random depth. The conditional Wick identities are explicit
hypotheses, so the integration step also applies to non-Gaussian pairs with
the same conditional second and fourth moments. -/

open Filter MeasureTheory
open scoped Topology

namespace UV

variable {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]

/-- If the three raw second moments coincide, the two smeared observables
agree almost surely. For centered fields these are exactly the three
covariance blocks in the manuscript. -/
theorem eq_ae_of_matched_second_moments (μ : Measure Ω) (X Y : Ω → ℝ)
    (hx : Integrable (fun ω => X ω ^ 2) μ)
    (hy : Integrable (fun ω => Y ω ^ 2) μ)
    (hxy : Integrable (fun ω => X ω * Y ω) μ)
    (hxx : (∫ ω, X ω ^ 2 ∂μ) = ∫ ω, Y ω ^ 2 ∂μ)
    (hcross : (∫ ω, X ω * Y ω ∂μ) = ∫ ω, Y ω ^ 2 ∂μ) : X =ᵐ[μ] Y := by
  have hpoly : (fun ω => (X ω - Y ω) ^ 2) =
      fun ω => (X ω ^ 2 - 2 * (X ω * Y ω)) + Y ω ^ 2 := by
    funext ω
    ring
  have hmul := hxy.const_mul (2 : ℝ)
  have hi : Integrable (fun ω => (X ω - Y ω) ^ 2) μ := by
    rw [hpoly]
    exact (hx.sub hmul).add hy
  have hz : (∫ ω, (X ω - Y ω) ^ 2 ∂μ) = 0 := by
    have hsum := integral_add (hx.sub hmul) hy
    have hsub := integral_sub hx hmul
    simp only [Pi.sub_apply] at hsum
    rw [hpoly, hsum, hsub, integral_const_mul, hxx, hcross]
    ring
  have he := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (fun ω =>
    sq_nonneg (X ω - Y ω))) hi).mp hz
  filter_upwards [he] with ω hω
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hω)

/-- Fixed-depth determinism holds simultaneously on a countable test core. -/
theorem eq_ae_on_countable_test_core {I : Type*} [Countable I]
    (μ : Measure Ω) (X Y : I → Ω → ℝ)
    (h : ∀ i, X i =ᵐ[μ] Y i) : ∀ᵐ ω ∂μ, ∀ i, X i ω = Y i ω :=
  ae_all_iff.mpr h

/-- Nonnegative slice densities obey Fubini under integrability of their
conditional expectations and almost-everywhere slice integrability. -/
theorem integrable_depth_of_nonnegative_slices (w : Measure D) [IsProbabilityMeasure w]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : D × Ω → ℝ}
    (hf : AEStronglyMeasurable f (w.prod μ)) (hn : ∀ z, 0 ≤ f z)
    (hslice : ∀ᵐ r ∂w, Integrable (fun ω => f (r, ω)) μ)
    {m : D → ℝ} (hm : Integrable m w)
    (hmean : ∀ᵐ r ∂w, (∫ ω, f (r, ω) ∂μ) = m r) : Integrable f (w.prod μ) := by
  refine (integrable_prod_iff hf).mpr ⟨hslice, hm.congr ?_⟩
  filter_upwards [hmean] with r hr
  simpa only [Real.norm_of_nonneg (hn _)] using hr.symm

/-- Polarization of the fourth-moment formula for the four centered
Gaussian observables `X`, `Y`, `X + Y`, and `X - Y` yields the conditional
Wick identity for the squares. Here `v` is the common second moment and
`c` is the mixed second moment. -/
theorem square_wick_of_scalar_fourth_moments (μ : Measure Ω) (X Y : Ω → ℝ) (v c : ℝ)
    (hx : Integrable (fun ω => X ω ^ 4) μ)
    (hy : Integrable (fun ω => Y ω ^ 4) μ)
    (hp : Integrable (fun ω => (X ω + Y ω) ^ 4) μ)
    (hm : Integrable (fun ω => (X ω - Y ω) ^ 4) μ)
    (hX : (∫ ω, X ω ^ 4 ∂μ) = 3 * v ^ 2)
    (hY : (∫ ω, Y ω ^ 4 ∂μ) = 3 * v ^ 2)
    (hPlus : (∫ ω, (X ω + Y ω) ^ 4 ∂μ) = 3 * (2 * v + 2 * c) ^ 2)
    (hMinus : (∫ ω, (X ω - Y ω) ^ 4 ∂μ) = 3 * (2 * v - 2 * c) ^ 2) :
    (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ) = v ^ 2 + 2 * c ^ 2 := by
  have hpol : (fun ω => X ω ^ 2 * Y ω ^ 2) = fun ω => (1 / 12 : ℝ) *
      (((X ω + Y ω) ^ 4 + (X ω - Y ω) ^ 4) - 2 * X ω ^ 4 - 2 * Y ω ^ 4) := by
    funext ω
    ring
  have hIntSub := integral_sub ((hp.add hm).sub (hx.const_mul 2)) (hy.const_mul 2)
  have hIntSub' := integral_sub (hp.add hm) (hx.const_mul 2)
  have hIntAdd := integral_add hp hm
  simp only [Pi.sub_apply, Pi.add_apply] at hIntSub hIntSub'
  rw [hpol, integral_const_mul, hIntSub, hIntSub', hIntAdd,
    integral_const_mul, integral_const_mul, hX, hY, hPlus, hMinus]
  ring

/-- Fourth cumulant of a centered depth mixture with the given conditional
second and fourth moments on a common probability space. -/
theorem shared_depth_fourth_cumulant (w : Measure D) [IsProbabilityMeasure w]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : D × Ω → ℝ) (v : D → ℝ)
    (hx₂ : Integrable (fun z => X z ^ 2) (w.prod μ))
    (hx₄ : Integrable (fun z => X z ^ 4) (w.prod μ))
    (hv₂ : ∀ᵐ r ∂w, (∫ ω, X (r, ω) ^ 2 ∂μ) = v r)
    (hv₄ : ∀ᵐ r ∂w, (∫ ω, X (r, ω) ^ 4 ∂μ) = 3 * v r ^ 2) :
    (∫ z, X z ^ 4 ∂(w.prod μ)) - 3 * (∫ z, X z ^ 2 ∂(w.prod μ)) ^ 2 =
      3 * ((∫ r, v r ^ 2 ∂w) - (∫ r, v r ∂w) ^ 2) := by
  have hx₂' : (∫ z, X z ^ 2 ∂(w.prod μ)) = ∫ r, v r ∂w :=
    (integral_prod _ hx₂).trans (integral_congr_ae hv₂)
  have hx₄' : (∫ z, X z ^ 4 ∂(w.prod μ)) = 3 * ∫ r, v r ^ 2 ∂w := by
    rw [integral_prod _ hx₄, ← integral_const_mul]
    exact integral_congr_ae hv₄
  rw [hx₄', hx₂']
  ring

/-- The covariance of two squares under a shared depth is the averaged
conditional covariance plus the variance of their common conditional
variance. The displayed fourth-moment identity is the conditional Wick rule. -/
theorem shared_depth_square_covariance (w : Measure D) [IsProbabilityMeasure w]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : D × Ω → ℝ) (v c : D → ℝ)
    (hx₂ : Integrable (fun z => X z ^ 2) (w.prod μ))
    (hy₂ : Integrable (fun z => Y z ^ 2) (w.prod μ))
    (hxy : Integrable (fun z => X z ^ 2 * Y z ^ 2) (w.prod μ))
    (hv₂ : Integrable (fun r => v r ^ 2) w)
    (hc₂ : Integrable (fun r => c r ^ 2) w)
    (hX : ∀ᵐ r ∂w, (∫ ω, X (r, ω) ^ 2 ∂μ) = v r)
    (hY : ∀ᵐ r ∂w, (∫ ω, Y (r, ω) ^ 2 ∂μ) = v r)
    (hXY : ∀ᵐ r ∂w, (∫ ω, X (r, ω) ^ 2 * Y (r, ω) ^ 2 ∂μ) =
      v r ^ 2 + 2 * c r ^ 2) :
    (∫ z, X z ^ 2 * Y z ^ 2 ∂(w.prod μ)) -
      (∫ z, X z ^ 2 ∂(w.prod μ)) * (∫ z, Y z ^ 2 ∂(w.prod μ)) =
      2 * (∫ r, c r ^ 2 ∂w) + ((∫ r, v r ^ 2 ∂w) - (∫ r, v r ∂w) ^ 2) := by
  have h₂X : (∫ z, X z ^ 2 ∂(w.prod μ)) = ∫ r, v r ∂w :=
    (integral_prod _ hx₂).trans (integral_congr_ae hX)
  have h₂Y : (∫ z, Y z ^ 2 ∂(w.prod μ)) = ∫ r, v r ∂w :=
    (integral_prod _ hy₂).trans (integral_congr_ae hY)
  have hxy' : (∫ z, X z ^ 2 * Y z ^ 2 ∂(w.prod μ)) =
      (∫ r, v r ^ 2 ∂w) + 2 * (∫ r, c r ^ 2 ∂w) := by
    rw [integral_prod _ hxy, ← integral_const_mul, ← integral_add hv₂ (hc₂.const_mul 2)]
    exact integral_congr_ae hXY
  rw [h₂X, h₂Y, hxy']
  ring

/-- The conditional correlation contribution tends to zero under the square
of the variance as common integrable majorant. -/
theorem shared_depth_correlation_square_limit {R : Type*} (l : Filter R)
    [l.IsCountablyGenerated] (w : Measure D) (v : D → ℝ) (c : R → D → ℝ)
    (hmeas : ∀ᶠ x in l, AEStronglyMeasurable (c x) w)
    (hbound : ∀ᶠ x in l, ∀ᵐ r ∂w, |c x r| ≤ v r)
    (hv : Integrable (fun r => v r ^ 2) w)
    (hlim : ∀ᵐ r ∂w, Tendsto (fun x => c x r) l (𝓝 0)) :
    Tendsto (fun x => ∫ r, c x r ^ 2 ∂w) l (𝓝 0) := by
  have hdom := tendsto_integral_filter_of_dominated_convergence
      (F := fun x r => c x r ^ 2) (f := fun _ => (0 : ℝ)) (fun r => v r ^ 2)
      (hmeas.mono fun _ hx => hx.pow 2) ?_ hv ?_
  · simpa using hdom
  · filter_upwards [hbound] with x hx
    filter_upwards [hx] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hr 2
  · filter_upwards [hlim] with r hr
    simpa using hr.pow 2

/-- The cluster limit is exactly the depth variance when the conditional
Gaussian prediction holds at each separation. -/
theorem shared_depth_square_covariance_limit {R : Type*} (l : Filter R)
    [l.IsCountablyGenerated] (w : Measure D) (v : D → ℝ) (c : R → D → ℝ)
    (cov : R → ℝ)
    (hcov : cov =ᶠ[l] (fun x =>
      2 * (∫ r, c x r ^ 2 ∂w) + ((∫ r, v r ^ 2 ∂w) - (∫ r, v r ∂w) ^ 2)))
    (hmeas : ∀ᶠ x in l, AEStronglyMeasurable (c x) w)
    (hbound : ∀ᶠ x in l, ∀ᵐ r ∂w, |c x r| ≤ v r)
    (hv : Integrable (fun r => v r ^ 2) w)
    (hlim : ∀ᵐ r ∂w, Tendsto (fun x => c x r) l (𝓝 0)) :
    Tendsto cov l (𝓝 ((∫ r, v r ^ 2 ∂w) - (∫ r, v r ∂w) ^ 2)) := by
  have hc := shared_depth_correlation_square_limit l w v c hmeas hbound hv hlim
  have hc' := (hc.const_mul 2).add_const ((∫ r, v r ^ 2 ∂w) - (∫ r, v r ∂w) ^ 2)
  exact (by simpa only [mul_zero, zero_add] using hc' :
    Tendsto (fun x => 2 * (∫ r, c x r ^ 2 ∂w) + ((∫ r, v r ^ 2 ∂w) - (∫ r, v r ∂w) ^ 2))
      l (𝓝 ((∫ r, v r ^ 2 ∂w) - (∫ r, v r ∂w) ^ 2))).congr' hcov.symm

end UV
