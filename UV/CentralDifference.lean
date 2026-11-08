import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-! The genuine sixth central difference of a six-times continuously
differentiable function. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV

def sixthSymmetricDifference (b : ℝ → ℝ) (h : ℝ) : ℝ :=
  b (3 * h) - 6 * b (2 * h) + 15 * b h - 20 * b 0 +
    15 * b (-h) - 6 * b (-2 * h) + b (-3 * h)

theorem sixthSymmetricDifference_taylor (b : ℝ → ℝ) (s : Set ℝ) (h : ℝ) :
    sixthSymmetricDifference (taylorWithinEval b 6 s 0) h =
      iteratedDerivWithin 6 b s 0 * h ^ 6 := by
  unfold sixthSymmetricDifference
  simp [taylor_within_apply, smul_eq_mul]
  ring

theorem sixthSymmetricDifference_tendsto {b : ℝ → ℝ} (hf : ContDiffAt ℝ 6 b 0) :
    Tendsto (fun h : ℝ => sixthSymmetricDifference b h / h ^ 6) (𝓝[≠] 0)
      (𝓝 (iteratedDeriv 6 b 0)) := by
  obtain ⟨u, hu, hbu⟩ := hf.contDiffOn (m := 6) le_rfl (by simp)
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu
  let s := Ioo l r
  have h0 : (0 : ℝ) ∈ s := ⟨hl, hr⟩
  have hs : s ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds hl hr
  have hb : ContDiffOn ℝ 6 b s := hbu.mono hsub
  let T := taylorWithinEval b 6 s 0
  have ht : Tendsto (fun x : ℝ => (b x - T x) / x ^ 6) (𝓝 0) (𝓝 0) := by
    have hh := Real.taylor_tendsto (n := 6) (f := b) (x₀ := 0) (convex_Ioo l r) h0 hb
    have hh' : Tendsto (fun x : ℝ => (b x - T x) / x ^ 6) (𝓝[s] 0) (𝓝 0) := by
      simpa only [sub_zero] using hh
    rwa [nhdsWithin_eq_nhds.mpr hs] at hh'
  have hT0 : T 0 = b 0 := taylorWithinEval_self b 6 s 0
  have hcoef : iteratedDerivWithin 6 b s 0 = iteratedDeriv 6 b 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo l r) hf h0
  have hpoly (h : ℝ) : sixthSymmetricDifference T h = iteratedDeriv 6 b 0 * h ^ 6 := by
    rw [sixthSymmetricDifference_taylor, hcoef]
  have hrem (c : ℝ) (hc : c ≠ 0) :
      Tendsto (fun h : ℝ => (b (c * h) - T (c * h)) / h ^ 6) (𝓝[≠] 0) (𝓝 0) := by
    have hscale : Tendsto (fun h : ℝ => c * h) (𝓝[≠] 0) (𝓝 0) := by
      have hccont : ContinuousAt (fun h : ℝ => c * h) 0 := by fun_prop
      simpa only [mul_zero] using hccont.tendsto.mono_left nhdsWithin_le_nhds
    have hh := (ht.comp hscale).mul_const (c ^ 6)
    simp only [zero_mul] at hh
    convert hh using 1
    funext h
    by_cases hh0 : h = 0
    · simp [hh0]
    · dsimp only [Function.comp_apply]
      field_simp [hc, hh0]
  have hsum := ((((((hrem 3 (by norm_num)).sub ((hrem 2 (by norm_num)).const_mul 6)).add
      ((hrem 1 (by norm_num)).const_mul 15)).add
      ((hrem (-1) (by norm_num)).const_mul 15)).sub
      ((hrem (-2) (by norm_num)).const_mul 6)).add
      (hrem (-3) (by norm_num))).add_const (iteratedDeriv 6 b 0)
  norm_num only [zero_mul, sub_zero, zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hh
  have hp := hpoly h
  dsimp only [sixthSymmetricDifference] at hp
  have hid : sixthSymmetricDifference b h =
      (b (3 * h) - T (3 * h)) - 6 * (b (2 * h) - T (2 * h)) +
      15 * (b h - T h) + 15 * (b (-h) - T (-h)) -
      6 * (b (-2 * h) - T (-2 * h)) + (b (-3 * h) - T (-3 * h)) +
      iteratedDeriv 6 b 0 * h ^ 6 := by
    unfold sixthSymmetricDifference
    rw [← hp, hT0]
    ring
  simp only [one_mul, neg_one_mul]
  rw [hid]
  field_simp

end UV
