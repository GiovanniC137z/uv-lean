import UV.RectifiableContourIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-! Primitive integration along genuinely Lipschitz curves. The chain rule
is used almost everywhere; the endpoint identity comes from the proved
Lipschitz fundamental theorem. No everywhere differentiability is needed. -/

noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology NNReal Interval

namespace UV

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
  [FiniteDimensional ℝ Z]

/-- The primitive theorem for a Lipschitz curve whenever the primitive's
composition is Lipschitz on the parameter interval. Both actual curve
integrability and the endpoint formula are derived by a.e. chain rules. -/
theorem lipschitzContour_primitive_properties {a b : ℂ} {f G : ℂ → Z} {U : Set ℂ}
    {K B : ℝ≥0} (γ : Path a b) (hγ : LipschitzWith K γ.extend)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U)
    (hG : ∀ z ∈ U, HasDerivAt G (f z) z)
    (hcomp : LipschitzOnWith B (fun t : ℝ => G (γ.extend t)) (Icc (0 : ℝ) 1)) :
    parametrizedContourIntegrable f γ ∧ parametrizedContourIntegral f γ = G b-G a := by
  have he : (fun t => derivWithin γ.extend (Icc (0 : ℝ) 1) t • f (γ.extend t))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        derivWithin (fun t : ℝ => G (γ.extend t)) (Icc (0 : ℝ) 1) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [(ae_restrict_of_ae hγ.ae_differentiableAt_real),
      ae_restrict_mem measurableSet_Ioo] with t hdt ht
    have hc := ((hG _ (hmap (Ioo_subset_Icc_self ht))).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hdt.hasDerivAt
    have hc' : HasDerivAt (fun t : ℝ => G (γ.extend t)) (deriv γ.extend t • f (γ.extend t)) t := by
      simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul] using hc
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
      hc'.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one t (Ioo_subset_Icc_self ht))]
  have he' : (fun t => derivWithin γ.extend (Icc (0 : ℝ) 1) t • f (γ.extend t))
      =ᵐ[volume.restrict (Ι (0 : ℝ) 1)]
        derivWithin (fun t : ℝ => G (γ.extend t)) (Icc (0 : ℝ) 1) := by
    simpa only [uIoc_of_le zero_le_one] using he
  obtain ⟨hi, hFTC⟩ := lipschitzOn_derivWithin_properties zero_le_one hcomp
  refine ⟨(parametrizedContourIntegrable_iff f γ).mpr
    ((intervalIntegrable_congr_ae he').mpr hi), ?_⟩
  rw [parametrizedContourIntegral_eq, intervalIntegral.integral_congr_ae_restrict he', hFTC]
  simp

/-- On a convex domain a genuine bound for the primitive derivative
constructs the required Lipschitz composition, so it is not supplied as an
extra chain-rule or endpoint premise. -/
theorem lipschitzContour_primitive_on_convex {a b : ℂ} {f G : ℂ → Z} {U : Set ℂ}
    {K B : ℝ≥0} (γ : Path a b) (hγ : LipschitzWith K γ.extend)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U) (hU : Convex ℝ U)
    (hG : ∀ z ∈ U, HasDerivAt G (f z) z) (hbound : ∀ z ∈ U, ‖f z‖₊ ≤ B) :
    parametrizedContourIntegrable f γ ∧ parametrizedContourIntegral f γ = G b-G a := by
  have hLip : LipschitzOnWith B G U := hU.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun z hz => (hG z hz).hasDerivWithinAt) hbound
  exact lipschitzContour_primitive_properties γ hγ hmap hG
    (hLip.comp hγ.lipschitzOnWith hmap)

/-- Holomorphic primitives integrate to zero on closed Lipschitz curves
under the same derived convex-domain admission. -/
theorem lipschitzContour_primitive_closed_on_convex {a : ℂ} {f G : ℂ → Z} {U : Set ℂ}
    {K B : ℝ≥0} (γ : Path a a) (hγ : LipschitzWith K γ.extend)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U) (hU : Convex ℝ U)
    (hG : ∀ z ∈ U, HasDerivAt G (f z) z) (hbound : ∀ z ∈ U, ‖f z‖₊ ≤ B) :
    parametrizedContourIntegral f γ = 0 := by
  simpa using (lipschitzContour_primitive_on_convex γ hγ hmap hU hG hbound).2

end UV
