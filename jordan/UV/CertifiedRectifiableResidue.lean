import UV.SimplyConnectedContourCauchy
import UV.RectifiableContourWinding
import UV.JordanResidueAnalytic
import UV.RectifiableArcPath

/-! Lean 4.32.2 compatibility port: use the current path extension evaluation lemma.

 Actual rough-contour residue formulas in a certified simply-connected
analytic domain. The geometric winding and removable regular part determine
the integral; no residue identity is supplied as contour data. These results
do not assert the separate Jordan-to-simply-connected-domain theorem. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology unitInterval NNReal

namespace UV

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
  [FiniteDimensional ℂ Z]

/-- A genuine Lipschitz contour of geometric winding one computes the
simple-pole residue in its specified simply-connected analytic domain. -/
theorem simplyConnectedContour_simplePole_residue
    {a p : ℂ} {κ : ℝ≥0} {U : Set ℂ} [SimplyConnectedSpace U] {G : ℂ → Z}
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend) (hU : IsOpen U)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hpos : lipschitzContourWinding γ havoid = 1)
    (hp : p ∈ U) (hG : AnalyticOnNhd ℂ G U) :
    (2*Real.pi*Complex.I : ℂ)⁻¹ • parametrizedContourIntegral (fun z => (z-p)⁻¹ • G z) γ =
      simplePoleResidue (fun z => (z-p)⁻¹ • G z) p := by
  let H := dslope G p
  have hH : AnalyticOnNhd ℂ H U := analyticOnNhd_dslope hG hp
  have hcH : ContinuousOn H U := fun z hz => (hH z hz).continuousAt.continuousWithinAt
  have hk : ContinuousOn (fun t : ℝ => (γ.extend t-p)⁻¹) (Icc (0 : ℝ) 1) :=
    (γ.continuous_extend.continuousOn.sub continuousOn_const).inv₀
      (fun t ht => sub_ne_zero.mpr (havoid t ht))
  have hconst : parametrizedContourIntegrable (fun z => (z-p)⁻¹ • G p) γ :=
    parametrizedContour_lipschitz_integrable γ hLip (hk.smul continuousOn_const)
  have hregular : parametrizedContourIntegrable H γ :=
    parametrizedContour_lipschitz_integrable γ hLip
      (hcH.comp γ.continuous_extend.continuousOn hmap)
  have hsplit : parametrizedContourIntegral (fun z => (z-p)⁻¹ • G z) γ =
      parametrizedContourIntegral (fun z => (z-p)⁻¹ • G p) γ+
        parametrizedContourIntegral H γ := by
    rw [← parametrizedContourIntegral_add γ hconst hregular]
    apply parametrizedContourIntegral_congr
    intro t ht
    dsimp only [H]
    rw [dslope_of_ne _ (havoid t ht)]
    simp only [slope, vsub_eq_sub, smul_sub]
    abel
  have hzero : parametrizedContourIntegral H γ = 0 :=
    simplyConnectedContour_cauchy hLip hU (fun t => by
      simpa only [Path.extend_apply γ t.property] using hmap t.property) hH
  have hres : simplePoleResidue (fun z => (z-p)⁻¹ • G z) p = G p := by
    obtain ⟨r,hr,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
    exact simplePole_residue (mem_ball_self hr)
      (fun z hz => (hG z (hsub hz)).differentiableAt.differentiableWithinAt)
      (fun _ _ _ => rfl)
  rw [hsplit,hzero,add_zero,parametrizedContourIntegral_smul_const,smul_smul,
    lipschitzContour_normalized_cauchyKernel_positive γ hLip havoid hpos,one_smul,hres]

/-- A raw analytic scalar denominator constructs the numerator and regular
part on the entire certified domain before the rough-contour formula is used. -/
theorem simplyConnectedContour_simple_denominator_residue
    {a p : ℂ} {κ : ℝ≥0} {U : Set ℂ} [SimplyConnectedSpace U]
    {k : ℂ → ℂ} {n : ℂ → Z}
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend) (hU : IsOpen U)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hpos : lipschitzContourWinding γ havoid = 1)
    (hp : p ∈ U) (hk : AnalyticOnNhd ℂ k U) (hn : AnalyticOnNhd ℂ n U)
    (hzero : k p = 0) (hderiv : deriv k p ≠ 0)
    (honly : ∀ z ∈ U, z ≠ p → k z ≠ 0) :
    (2*Real.pi*Complex.I : ℂ)⁻¹ • parametrizedContourIntegral (fun z => (k z)⁻¹ • n z) γ =
      simplePoleResidue (fun z => (k z)⁻¹ • n z) p := by
  let G : ℂ → Z := fun z => (dslope k p z)⁻¹ • n z
  obtain ⟨hG,_,hf,hres⟩ :=
    analytic_simple_denominator_regular_part hp hk hn hzero hderiv honly
  have hcontour : parametrizedContourIntegral (fun z => (k z)⁻¹ • n z) γ =
      parametrizedContourIntegral (fun z => (z-p)⁻¹ • G z) γ :=
    parametrizedContourIntegral_congr γ (fun t ht => hf _ (hmap ht) (havoid t ht))
  rw [hcontour,simplyConnectedContour_simplePole_residue γ hLip hU hmap havoid hpos hp hG]
  have hresG : simplePoleResidue (fun z => (z-p)⁻¹ • G z) p = G p := by
    obtain ⟨r,hr,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
    exact simplePole_residue (mem_ball_self hr)
      (fun z hz => (hG z (hsub hz)).differentiableAt.differentiableWithinAt)
      (fun _ _ _ => rfl)
  exact hresG.trans hres.symm

/-- Distinct enclosed simple zeros are allowed. This bounds actual residue
coefficients, after proving both rough-contour residue formulas. -/
theorem simplyConnectedContour_simple_denominator_residue_error
    {a pX pY : ℂ} {κ : ℝ≥0} {U : Set ℂ} [SimplyConnectedSpace U]
    {kX kY : ℂ → ℂ} {nX nY : ℂ → Z} {C : ℝ}
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend) (hU : IsOpen U)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U)
    (havoidX : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ pX)
    (havoidY : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ pY)
    (hposX : lipschitzContourWinding γ havoidX = 1)
    (hposY : lipschitzContourWinding γ havoidY = 1)
    (hpX : pX ∈ U) (hpY : pY ∈ U)
    (hkX : AnalyticOnNhd ℂ kX U) (hkY : AnalyticOnNhd ℂ kY U)
    (hnX : AnalyticOnNhd ℂ nX U) (hnY : AnalyticOnNhd ℂ nY U)
    (hzeroX : kX pX = 0) (hzeroY : kY pY = 0)
    (hderivX : deriv kX pX ≠ 0) (hderivY : deriv kY pY ≠ 0)
    (honlyX : ∀ z ∈ U, z ≠ pX → kX z ≠ 0)
    (honlyY : ∀ z ∈ U, z ≠ pY → kY z ≠ 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(kX (γ.extend t))⁻¹ • nX (γ.extend t)-
        (kY (γ.extend t))⁻¹ • nY (γ.extend t)‖ ≤ C) :
    ‖simplePoleResidue (fun z => (kX z)⁻¹ • nX z) pX-
        simplePoleResidue (fun z => (kY z)⁻¹ • nY z) pY‖ ≤
      parametrizedContourLength γ/(2*Real.pi)*C := by
  have hckX : ContinuousOn kX U := fun z hz => (hkX z hz).continuousAt.continuousWithinAt
  have hckY : ContinuousOn kY U := fun z hz => (hkY z hz).continuousAt.continuousWithinAt
  have hcnX : ContinuousOn nX U := fun z hz => (hnX z hz).continuousAt.continuousWithinAt
  have hcnY : ContinuousOn nY U := fun z hz => (hnY z hz).continuousAt.continuousWithinAt
  have hcX : ContinuousOn (fun t : ℝ => (kX (γ.extend t))⁻¹ • nX (γ.extend t))
      (Icc (0 : ℝ) 1) :=
    ((hckX.comp γ.continuous_extend.continuousOn hmap).inv₀
      (fun t ht => honlyX _ (hmap ht) (havoidX t ht))).smul
      (hcnX.comp γ.continuous_extend.continuousOn hmap)
  have hcY : ContinuousOn (fun t : ℝ => (kY (γ.extend t))⁻¹ • nY (γ.extend t))
      (Icc (0 : ℝ) 1) :=
    ((hckY.comp γ.continuous_extend.continuousOn hmap).inv₀
      (fun t ht => honlyY _ (hmap ht) (havoidY t ht))).smul
      (hcnY.comp γ.continuous_extend.continuousOn hmap)
  rw [← simplyConnectedContour_simple_denominator_residue γ hLip hU hmap havoidX
      hposX hpX hkX hnX hzeroX hderivX honlyX,
    ← simplyConnectedContour_simple_denominator_residue γ hLip hU hmap havoidY
      hposY hpY hkY hnY hzeroY hderivY honlyY]
  exact normalizedContour_difference_le γ
    (parametrizedContour_lipschitz_speed_integrable γ hLip)
    (parametrizedContour_lipschitz_integrable γ hLip hcX)
    (parametrizedContour_lipschitz_integrable γ hLip hcY) hbound

omit [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
  [FiniteDimensional ℂ Z] in
/-- Every point of the constructed arc-length curve is a point of the
original geometric contour. -/
theorem rectifiableArcPath_mapsTo {a b : ℂ} (γ : Path a b)
    (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1)) {U : Set ℂ}
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U) :
    MapsTo (rectifiableArcPath γ hBV).extend (Icc (0 : ℝ) 1) U := by
  intro t ht
  have hm : (rectifiableArcPath γ hBV).extend t ∈ γ.extend '' Icc (0 : ℝ) 1 := by
    rw [← rectifiableArcPath_image γ hBV]
    exact mem_image_of_mem _ ht
  obtain ⟨s,hs,heq⟩ := hm
  exact heq ▸ hmap hs

/-- For an arbitrary continuous rectifiable parameterization the actual
arc-length representative gives the original geometric-length error factor. -/
theorem rectifiableArcPath_simple_denominator_residue_error
    {a pX pY : ℂ} {U : Set ℂ} [SimplyConnectedSpace U]
    {kX kY : ℂ → ℂ} {nX nY : ℂ → Z} {C : ℝ}
    (γ : Path a a) (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1))
    (hU : IsOpen U) (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U)
    (havoidX : ∀ t ∈ Icc (0 : ℝ) 1, (rectifiableArcPath γ hBV).extend t ≠ pX)
    (havoidY : ∀ t ∈ Icc (0 : ℝ) 1, (rectifiableArcPath γ hBV).extend t ≠ pY)
    (hposX : lipschitzContourWinding (rectifiableArcPath γ hBV) havoidX = 1)
    (hposY : lipschitzContourWinding (rectifiableArcPath γ hBV) havoidY = 1)
    (hpX : pX ∈ U) (hpY : pY ∈ U)
    (hkX : AnalyticOnNhd ℂ kX U) (hkY : AnalyticOnNhd ℂ kY U)
    (hnX : AnalyticOnNhd ℂ nX U) (hnY : AnalyticOnNhd ℂ nY U)
    (hzeroX : kX pX = 0) (hzeroY : kY pY = 0)
    (hderivX : deriv kX pX ≠ 0) (hderivY : deriv kY pY ≠ 0)
    (honlyX : ∀ z ∈ U, z ≠ pX → kX z ≠ 0)
    (honlyY : ∀ z ∈ U, z ≠ pY → kY z ≠ 0)
    (hbound : ∀ z ∈ γ.extend '' Icc (0 : ℝ) 1,
      ‖(kX z)⁻¹ • nX z-(kY z)⁻¹ • nY z‖ ≤ C) :
    ‖simplePoleResidue (fun z => (kX z)⁻¹ • nX z) pX-
        simplePoleResidue (fun z => (kY z)⁻¹ • nY z) pY‖ ≤
      (rectifiablePathLength γ : ℝ)/(2*Real.pi)*C := by
  have hm := rectifiableArcPath_mapsTo γ hBV hmap
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(kX ((rectifiableArcPath γ hBV).extend t))⁻¹ •
          nX ((rectifiableArcPath γ hBV).extend t)-
        (kY ((rectifiableArcPath γ hBV).extend t))⁻¹ •
          nY ((rectifiableArcPath γ hBV).extend t)‖ ≤ C := by
    intro t ht
    apply hbound
    rw [← rectifiableArcPath_image γ hBV]
    exact mem_image_of_mem _ ht
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 0 ⟨le_rfl,zero_le_one⟩)
  exact (simplyConnectedContour_simple_denominator_residue_error _
    (rectifiableArcPath_lipschitz γ hBV) hU hm havoidX havoidY hposX hposY
    hpX hpY hkX hkY hnX hnY hzeroX hzeroY hderivX hderivY honlyX honlyY hb).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (rectifiableArcPath_length_le γ hBV)
        (by positivity : 0 ≤ 2*Real.pi)) hC)

end UV
