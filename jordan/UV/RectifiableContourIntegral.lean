import UV.ContourResidue
import UV.LipschitzFTC
import Mathlib.Topology.Order.ProjIcc

/-! Actual integral estimates for Lipschitz representatives of rectifiable
curves. No C1 regularity is imposed. The derivative integral is justified
by the genuine Lipschitz fundamental theorem, not by formal differentiation
of an arbitrary singular parameterization. -/

/- Ported from the verified UV 4.24 development to Lean/mathlib 4.32.2;
the speed definition is unfolded explicitly in the a.e. comparison. -/

noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology NNReal

namespace UV

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

/-- Endpoint values do not affect the curve integral. On the interval's
interior the within derivative is the actual ordinary derivative. -/
theorem contour_derivWithin_ae {a b : ℂ} (γ : Path a b) :
    (fun t => derivWithin γ.extend (Icc (0 : ℝ) 1) t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      deriv γ.extend := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)

theorem parametrizedContour_lipschitz_speed_integrable {a b : ℂ} (γ : Path a b) {K : ℝ≥0}
    (hγ : LipschitzWith K γ.extend) :
    IntervalIntegrable (parametrizedContourSpeed γ) volume 0 1 := by
  have he := (contour_derivWithin_ae γ).fun_comp norm
  rw [← uIoc_of_le zero_le_one] at he
  exact (intervalIntegrable_congr_ae he).mpr (lipschitz_deriv_intervalIntegrable hγ 0 1).norm

/-- Every continuous readout along a Lipschitz curve is genuinely curve
integrable; measurability and an integrable derivative majorant are derived. -/
theorem parametrizedContour_lipschitz_integrable {a b : ℂ} (γ : Path a b) {K : ℝ≥0}
    (hγ : LipschitzWith K γ.extend) {f : ℂ → Z}
    (hf : ContinuousOn (fun t : ℝ => f (γ.extend t)) (Icc (0 : ℝ) 1)) :
    parametrizedContourIntegrable f γ := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  let F : ℝ → Z := Set.IccExtend zero_le_one (fun t : Icc (0 : ℝ) 1 => f (γ.extend t))
  have hF : Continuous F := continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_restrict.mp hf)
  have hm : AEStronglyMeasurable
      (fun t : ℝ => derivWithin γ.extend (Icc (0 : ℝ) 1) t • f (γ.extend t))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have hmain : AEStronglyMeasurable (fun t : ℝ => deriv γ.extend t • F t)
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      (aestronglyMeasurable_deriv γ.extend _).smul hF.aestronglyMeasurable
    apply hmain.congr
    filter_upwards [contour_derivWithin_ae γ, ae_restrict_mem measurableSet_Ioc] with t ht htI
    rw [ht]
    rw [show F t = f (γ.extend t) from Set.IccExtend_of_mem zero_le_one _ ⟨htI.1.le, htI.2⟩]
  exact parametrizedContour_integrable_of_bound γ
    (parametrizedContour_lipschitz_speed_integrable γ hγ) hm hB

/-- The actual integrated speed is bounded by the representative's
Lipschitz length budget. Arc-length representatives have the geometric
length as this budget. -/
theorem parametrizedContourLength_le_lipschitz {a b : ℂ} (γ : Path a b) {K : ℝ≥0}
    (hγ : LipschitzWith K γ.extend) : parametrizedContourLength γ ≤ K := by
  have he := (contour_derivWithin_ae γ).fun_comp norm
  have hle : (∫ t in (0 : ℝ)..1, ‖deriv γ.extend t‖) ≤ ∫ _t in (0 : ℝ)..1, (K : ℝ) :=
    intervalIntegral.integral_mono_on zero_le_one
      (lipschitz_deriv_intervalIntegrable hγ 0 1).norm intervalIntegrable_const
      (fun _ _ => norm_deriv_le_of_lipschitz hγ)
  rw [parametrizedContourLength]
  have hi : (∫ t in (0 : ℝ)..1, parametrizedContourSpeed γ t) = ∫ t in (0 : ℝ)..1, ‖deriv γ.extend t‖ :=
    intervalIntegral.integral_congr_ae_restrict (by
      change (fun t => ‖derivWithin γ.extend (Icc (0 : ℝ) 1) t‖)
        =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)] (fun t => ‖deriv γ.extend t‖)
      simpa only [uIoc_of_le zero_le_one, Function.comp_def] using he)
  rw [hi]
  simpa using hle

/-- The source's actual observable contour error on any Lipschitz
representative, with its integrated length and no C1 hypothesis. -/
theorem observable_lipschitzContour_error
    {H Q : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    {a b : ℂ} {κ : ℝ≥0}
    (KX KY : ℂ → H →L[ℂ] H) (U : ℂ → H →L[ℂ] Q) (V : ℂ → Q →L[ℂ] H)
    (γ : Path a b) {B ε Lout Lin : ℝ}
    (hγ : LipschitzWith κ γ.extend)
    (hX : ContinuousOn (fun t : ℝ =>
      (U (γ.extend t)).comp ((Ring.inverse (KX (γ.extend t))).comp (V (γ.extend t)))) (Icc (0 : ℝ) 1))
    (hY : ContinuousOn (fun t : ℝ =>
      (U (γ.extend t)).comp ((Ring.inverse (KY (γ.extend t))).comp (V (γ.extend t)))) (Icc (0 : ℝ) 1))
    (hε0 : 0 ≤ ε) (hLo : 0 ≤ Lout) (hq : B*ε < 1)
    (hKY : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (KY (γ.extend t)))
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖Ring.inverse (KY (γ.extend t))‖ ≤ B)
    (hε : ∀ t ∈ Icc (0 : ℝ) 1, ‖KX (γ.extend t)-KY (γ.extend t)‖ ≤ ε)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, ‖U (γ.extend t)‖ ≤ Lout)
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, ‖V (γ.extend t)‖ ≤ Lin) :
    (∀ t ∈ Icc (0 : ℝ) 1, IsUnit (KX (γ.extend t))) ∧
    ‖(2*Real.pi*I : ℂ)⁻¹ •
        parametrizedContourIntegral (fun z => (U z).comp ((Ring.inverse (KX z)).comp (V z))) γ-
      (2*Real.pi*I : ℂ)⁻¹ •
        parametrizedContourIntegral (fun z => (U z).comp ((Ring.inverse (KY z)).comp (V z))) γ‖ ≤
      parametrizedContourLength γ/(2*Real.pi)*Lout*Lin*B^2*ε/(1-B*ε) := by
  have hden : 0 < 1-B*ε := sub_pos.mpr hq
  have he (z : ℂ) : KY z-(KY z-KX z) = KX z := by abel
  refine ⟨fun t ht => ?_, ?_⟩
  · have hx := (response_inverse_perturbation (hKY t ht) (hB t ht)
      (show ‖KY (γ.extend t)-KX (γ.extend t)‖ ≤ ε by simpa only [norm_sub_rev] using hε t ht) hq).1
    rwa [he] at hx
  · have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖(U (γ.extend t)).comp ((Ring.inverse (KX (γ.extend t))).comp (V (γ.extend t)))-
          (U (γ.extend t)).comp ((Ring.inverse (KY (γ.extend t))).comp (V (γ.extend t)))‖ ≤
          Lout*Lin*B^2*ε/(1-B*ε) := by
      intro t ht
      rw [← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
      have hh := (response_schur_error (hKY t ht) (hB t ht)
        (show ‖KY (γ.extend t)-KX (γ.extend t)‖ ≤ ε by simpa only [norm_sub_rev] using hε t ht)
        hq (U (γ.extend t)) (V (γ.extend t))).2.2
      rw [he] at hh
      apply hh.trans
      gcongr
      · exact hU t ht
      · exact hV t ht
    exact (normalizedContour_difference_le γ (parametrizedContour_lipschitz_speed_integrable γ hγ)
      (parametrizedContour_lipschitz_integrable γ hγ hX)
      (parametrizedContour_lipschitz_integrable γ hγ hY) hbound).trans_eq (by ring)

end UV
