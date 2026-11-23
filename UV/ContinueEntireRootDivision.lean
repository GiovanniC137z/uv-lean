import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic

/-! Removing one isolated zero with its full multiplicity preserves
finite exponential type and yields decay on the imaginary frequency axis. -/

noncomputable section

open Complex Filter Set Metric
open scoped Topology

namespace UV

theorem entire_divide_isolated_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hn : ∃ z, f z ≠ 0)
    {a : ℂ} (ha : f a = 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g a ≠ 0 ∧
      ∀ z, f z = (z-a)^n*g z := by
  classical
  have hA := hf.differentiableOn.analyticOnNhd (s := univ) isOpen_univ
  have hnon : ¬∀ᶠ z in 𝓝 a, f z = 0 := by
    intro he
    obtain ⟨p,hp⟩ := hn
    exact hp (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ a) he (mem_univ p))
  obtain ⟨n,u,hu,hnz,he⟩ := ((hA a (mem_univ a)).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnon
  have he' : ∀ᶠ z in 𝓝 a, f z = (z-a)^n*u z := he
  have hnpos : n ≠ 0 := by
    intro h
    have := he'.self_of_nhds
    simp [h,ha] at this
    exact hnz this.symm
  let g := Function.update (fun z => f z/(z-a)^n) a (u a)
  have hga : g a = u a := Function.update_self ..
  have haway (z : ℂ) (hz : z ≠ a) : g z = f z/(z-a)^n := Function.update_of_ne hz ..
  have hlocal : g =ᶠ[𝓝 a] u := by
    filter_upwards [he'] with z hz
    by_cases h : z = a
    · simpa only [h] using hga
    · rw [haway z h,hz]
      exact mul_div_cancel_left₀ _ (pow_ne_zero n (sub_ne_zero.mpr h))
  refine ⟨n,Nat.pos_of_ne_zero hnpos,g,?_,hga ▸ hnz,?_⟩
  · intro z
    by_cases h : z = a
    · exact h ▸ hu.differentiableAt.congr_of_eventuallyEq hlocal
    · apply ((hf z).div (((differentiableAt_id.sub_const a).pow n)) (pow_ne_zero n (sub_ne_zero.mpr h))).congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds h] with w hw using haway w hw
  · intro z
    by_cases h : z = a
    · simp [h,ha,hnpos]
    · rw [haway z h]
      field_simp [sub_ne_zero.mpr h]

theorem entire_quotient_growth {f g : ℂ → ℂ} (hg : Differentiable ℂ g) {a : ℂ} {n : ℕ}
    (he : ∀ z, f z = (z-a)^n*g z) {A B : ℝ} (hB : 0 ≤ B) (hb : ∀ z, ‖f z‖ ≤ Real.exp (A+B*‖z‖)) :
    ∃ C : ℝ, ∀ z, ‖g z‖ ≤ Real.exp (C+B*‖z‖) := by
  obtain ⟨K,hK⟩ := (isCompact_closedBall a 1).exists_bound_of_continuousOn hg.continuous.continuousOn
  use max A K
  intro z
  by_cases hz : z ∈ closedBall a 1
  · apply (hK z hz).trans
    have ht := mul_nonneg hB (norm_nonneg z)
    linarith [le_max_right A K, Real.add_one_le_exp (max A K+B*‖z‖)]
  · have hle : 1 ≤ ‖z-a‖ := (lt_of_not_ge (fun h => hz (by simpa only [mem_closedBall,dist_eq_norm] using h))).le
    have hle' := one_le_pow₀ hle (n := n)
    calc
      ‖g z‖ ≤ ‖(z-a)^n‖*‖g z‖ := by rw [norm_pow]; exact le_mul_of_one_le_left (norm_nonneg _) hle'
      _ = ‖f z‖ := by rw [he z,norm_mul]
      _ ≤ _ := (hb z).trans (Real.exp_le_exp.mpr (add_le_add_right (le_max_left A K) _))

theorem imaginary_displacement_escapes (a : ℂ) :
    Tendsto (fun t : ℝ => ‖(t:ℂ)*Complex.I-a‖) (cocompact ℝ) atTop := by
  have ht : Tendsto (fun t : ℝ => ‖t‖-‖a‖) (cocompact ℝ) atTop :=
    by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right (cocompact ℝ) (-‖a‖) (tendsto_norm_cocompact_atTop (E := ℝ))
  apply tendsto_atTop_mono _ ht
  intro t
  have h := norm_le_norm_sub_add ((t:ℂ)*Complex.I) a
  simp only [norm_mul, Complex.norm_I,mul_one,Complex.norm_real] at h
  linarith

theorem entire_quotient_imaginary_decay {f g : ℂ → ℂ} {a c : ℂ} {n : ℕ}
    (hpos : 0 < n) (he : ∀ z, f z = (z-a)^n*g z)
    (ht : Tendsto (fun t : ℝ => f ((t:ℂ)*Complex.I)) (cocompact ℝ) (𝓝 c)) :
    Tendsto (fun t : ℝ => g ((t:ℂ)*Complex.I)) (cocompact ℝ) (𝓝 0) := by
  have hnorm := imaginary_displacement_escapes a
  have hi := tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hnorm)
  have hv := ht.mul (hi.pow n)
  rw [zero_pow hpos.ne',mul_zero] at hv
  apply hv.congr'
  filter_upwards [hnorm.eventually (eventually_gt_atTop (0:ℝ))] with t ht'
  have hn : (t:ℂ)*Complex.I-a ≠ 0 := norm_pos_iff.mp ht'
  change f ((t:ℂ)*Complex.I) * (((t:ℂ)*Complex.I-a)⁻¹)^n = _
  rw [he,inv_pow]
  field_simp [hn]

end UV
