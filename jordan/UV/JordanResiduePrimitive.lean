import UV.ContourResidue
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Lean 4.32.2 compatibility port: use the generic linear-map identity lemma.

Genuine primitive integration for parametrized curves. This file does
not identify a general rectifiable Jordan contour with a smooth curve or
assume a Cauchy/residue formula as contour data. -/

noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology

namespace UV

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]

/-- The actual parametrized curve integral of a complex derivative is its
endpoint difference. All chain rules and real fundamental-theorem steps
are derived for the chosen C1 parameter. -/
theorem parametrizedContourIntegral_primitive {a b : ℂ} {f g : ℂ → Z} {U : Set ℂ}
    (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U)
    (hf : ContinuousOn f U) (hg : ∀ z ∈ U, HasDerivAt g (f z) z) :
    parametrizedContourIntegral f γ = g b-g a := by
  have hfc : ContinuousOn (fun t : ℝ => f (γ.extend t)) (Icc (0 : ℝ) 1) :=
    hf.comp hγ.continuousOn hmap
  have hgcont : ContinuousOn g U := fun z hz => (hg z hz).continuousAt.continuousWithinAt
  have hgc : ContinuousOn (fun t : ℝ => g (γ.extend t)) (Icc (0 : ℝ) 1) :=
    hgcont.comp hγ.continuousOn hmap
  have hi : IntervalIntegrable
      (fun t : ℝ => derivWithin γ.extend (Icc (0 : ℝ) 1) t • f (γ.extend t)) volume 0 1 :=
    ((hγ.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl).smul hfc).intervalIntegrable_of_Icc zero_le_one
  rw [parametrizedContourIntegral_eq]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hgc
    (fun t ht => ?_) hi
  · simpa using hFTC
  have hdt := (hγ.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
  have hc := ((hg (γ.extend t) (hmap (Ioo_subset_Icc_self ht))).hasFDerivAt.restrictScalars ℝ).comp_hasDerivWithinAt t hdt
  have hnhds : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using
    hc.hasDerivAt hnhds

/-- An actual primitive gives zero integral on a closed C1 curve. -/
theorem parametrizedContourIntegral_primitive_closed {a : ℂ} {f g : ℂ → Z} {U : Set ℂ}
    (γ : Path a a) (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U)
    (hf : ContinuousOn f U) (hg : ∀ z ∈ U, HasDerivAt g (f z) z) :
    parametrizedContourIntegral f γ = 0 := by
  rw [parametrizedContourIntegral_primitive γ hγ hmap hf hg, sub_self]

/-- Disk holomorphy constructs a primitive and then proves Cauchy's theorem
for arbitrary shaped closed C1 curves in that disk. -/
theorem parametrizedContourIntegral_eq_zero_in_ball {a c : ℂ} {r : ℝ} {f : ℂ → Z}
    (γ : Path a a) (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) (ball c r))
    (hf : DifferentiableOn ℂ f (ball c r)) : parametrizedContourIntegral f γ = 0 := by
  obtain ⟨g, hg⟩ := hf.isExactOn_ball
  exact parametrizedContourIntegral_primitive_closed γ hγ hmap hf.continuousOn hg

end UV
