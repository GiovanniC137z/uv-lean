import UV.JordanResiduePrimitive
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Winding data are represented by a genuine exponential/argument lift.
The contour integral is computed from that geometric lift by differentiating
the exponential identity and applying the real fundamental theorem. No
contour integral or residue identity is part of the lift data. -/

noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology

namespace UV

/-- A smooth logarithmic lift of the translated nonzero curve. Such a lift
describes geometric argument continuation, independently of curve integrals. -/
structure C1ContourLogLift {a b : ℂ} (γ : Path a b) (p : ℂ) where
  value : ℝ → ℂ
  c1 : ContDiffOn ℝ 1 value (Icc (0 : ℝ) 1)
  exponential : ∀ t ∈ Icc (0 : ℝ) 1, exp (value t) = γ.extend t-p

theorem contourLogLift_avoids_pole {a b p : ℂ} {γ : Path a b}
    (L : C1ContourLogLift γ p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : γ.extend t ≠ p := by
  intro h
  have he := L.exponential t ht
  rw [h, sub_self] at he
  exact exp_ne_zero _ he

theorem contourLogLift_closed_integer_jump {a p : ℂ} {γ : Path a a}
    (L : C1ContourLogLift γ p) :
    ∃ n : ℤ, L.value 1-L.value 0 = (n : ℂ)*(2*Real.pi*I) := by
  have he : exp (L.value 1) = exp (L.value 0) := by
    rw [L.exponential 1 ⟨zero_le_one, le_rfl⟩,
      L.exponential 0 ⟨le_rfl, zero_le_one⟩]
    simp
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp he
  exact ⟨n, by linear_combination hn⟩

/-- The winding integer is the geometric argument increment of the chosen
lift; no integral occurs in this definition. -/
def contourLiftWinding {a p : ℂ} {γ : Path a a} (L : C1ContourLogLift γ p) : ℤ :=
  Classical.choose (contourLogLift_closed_integer_jump L)

theorem contourLiftWinding_spec {a p : ℂ} {γ : Path a a} (L : C1ContourLogLift γ p) :
    L.value 1-L.value 0 = (contourLiftWinding L : ℂ)*(2*Real.pi*I) :=
  Classical.choose_spec (contourLogLift_closed_integer_jump L)

/-- The Cauchy kernel integral is computed from a genuine argument lift,
not assumed to be its winding number. -/
theorem parametrizedContourIntegral_cauchyKernel_of_lift {a b p : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1)) (L : C1ContourLogLift γ p) :
    parametrizedContourIntegral (fun z : ℂ => (z-p)⁻¹) γ = L.value 1-L.value 0 := by
  have hder : ∀ t ∈ Icc (0 : ℝ) 1,
      derivWithin γ.extend (Icc (0 : ℝ) 1) t =
        exp (L.value t)*derivWithin L.value (Icc (0 : ℝ) 1) t := by
    intro t ht
    have hdl := (L.c1.differentiableOn (by norm_num) t ht).hasDerivWithinAt.cexp
    have hde := hdl.congr_of_mem (fun s hs => (L.exponential s hs).symm) ht
    have hdg := ((hγ.differentiableOn (by norm_num) t ht).hasDerivWithinAt.sub_const p)
    exact (hdg.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht)).symm.trans
      (hde.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht))
  rw [parametrizedContourIntegral_eq]
  have hEq : (∫ t in (0 : ℝ)..1,
      derivWithin γ.extend (Icc (0 : ℝ) 1) t • (γ.extend t-p)⁻¹) =
      ∫ t in (0 : ℝ)..1, derivWithin L.value (Icc (0 : ℝ) 1) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    dsimp only
    rw [hder t ht', ← L.exponential t ht']
    simp only [smul_eq_mul]
    field_simp
  rw [hEq]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one L.c1.continuousOn
  · intro t ht
    exact (L.c1.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · exact (L.c1.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl).intervalIntegrable_of_Icc zero_le_one

theorem parametrizedContourIntegral_cauchyKernel_winding {a p : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1)) (L : C1ContourLogLift γ p) :
    parametrizedContourIntegral (fun z : ℂ => (z-p)⁻¹) γ =
      (contourLiftWinding L : ℂ)*(2*Real.pi*I) := by
  rw [parametrizedContourIntegral_cauchyKernel_of_lift γ hγ L, contourLiftWinding_spec L]

theorem normalizedContour_cauchyKernel_positive {a p : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1)) (L : C1ContourLogLift γ p)
    (hpos : contourLiftWinding L = 1) :
    (2*Real.pi*I : ℂ)⁻¹ * parametrizedContourIntegral (fun z : ℂ => (z-p)⁻¹) γ = 1 := by
  rw [parametrizedContourIntegral_cauchyKernel_winding γ hγ L, hpos]
  rw [Int.cast_one, one_mul, inv_mul_cancel₀ (by simp [Real.pi_ne_zero])]

end UV
