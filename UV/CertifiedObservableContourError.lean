import UV.CertifiedMatrixContourResidue
import UV.MatrixObservableNeumannError

/-! The full observable residue error on certified rough contours. The
matrix quotient, pole residues, Neumann error and geometric-length factor
are all derived for the same endpoint maps and actual inverse observables.
The simply-connected-domain certificate remains an explicit hypothesis. -/

noncomputable section
open Set Metric Complex
open scoped Topology Matrix.Norms.L2Operator NNReal

namespace UV

variable {n i o : Type*} [Fintype n] [DecidableEq n]
  [Fintype i] [DecidableEq i] [Fintype o] [DecidableEq o]

private theorem matrixContour_observable_continuousOn
    {a p : ℂ} {U : Set ℂ}
    {K : ℂ → Matrix n n ℂ} {Lout : ℂ → Matrix o n ℂ} {Lin : ℂ → Matrix n i ℂ}
    (γ : Path a a) (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hK : AnalyticOnNhd ℂ K U) (hLout : AnalyticOnNhd ℂ Lout U)
    (hLin : AnalyticOnNhd ℂ Lin U)
    (honly : ∀ z ∈ U, z ≠ p → (K z).det ≠ 0) :
    ContinuousOn (fun t : ℝ => matrixInverseObservable K Lout Lin (γ.extend t))
      (Icc (0 : ℝ) 1) := by
  have hd : ContinuousOn (fun z => (K z).det) U :=
    fun z hz => (matrixContour_det_analyticOnNhd hK z hz).continuousAt.continuousWithinAt
  have hn : ContinuousOn (matrixObservableAdjugateNumerator K Lout Lin) U :=
    fun z hz => (matrixContour_numerator_analyticOnNhd hK hLout hLin z hz).continuousAt.continuousWithinAt
  simpa only [matrix_observable_adjugate_quotient] using
    ((hd.comp γ.continuous_extend.continuousOn hmap).inv₀
      (fun t ht => honly _ (hmap ht) (havoid t ht))).smul
      (hn.comp γ.continuous_extend.continuousOn hmap)

/-- Exact source error factor for actual matrix observable residues at
possibly different simple poles, on a certified Lipschitz contour. -/
theorem simplyConnectedContour_matrix_observable_residue_error
    {a pX pY : ℂ} {κ : ℝ≥0} {U : Set ℂ} [SimplyConnectedSpace U]
    {KX KY : ℂ → Matrix n n ℂ} {Lout : ℂ → Matrix o n ℂ} {Lin : ℂ → Matrix n i ℂ}
    {B ε Lo Li : ℝ}
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend) (hU : IsOpen U)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U)
    (havoidX : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ pX)
    (havoidY : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ pY)
    (hposX : lipschitzContourWinding γ havoidX = 1)
    (hposY : lipschitzContourWinding γ havoidY = 1)
    (hpX : pX ∈ U) (hpY : pY ∈ U)
    (hKX : AnalyticOnNhd ℂ KX U) (hKY : AnalyticOnNhd ℂ KY U)
    (hLout : AnalyticOnNhd ℂ Lout U) (hLin : AnalyticOnNhd ℂ Lin U)
    (hzeroX : (KX pX).det = 0) (hzeroY : (KY pY).det = 0)
    (hderivX : deriv (fun z => (KX z).det) pX ≠ 0)
    (hderivY : deriv (fun z => (KY z).det) pY ≠ 0)
    (honlyX : ∀ z ∈ U, z ≠ pX → (KX z).det ≠ 0)
    (honlyY : ∀ z ∈ U, z ≠ pY → (KY z).det ≠ 0)
    (hq : B*ε < 1)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖(KY (γ.extend t))⁻¹‖ ≤ B)
    (hε : ∀ t ∈ Icc (0 : ℝ) 1, ‖KX (γ.extend t)-KY (γ.extend t)‖ ≤ ε)
    (hLo : ∀ t ∈ Icc (0 : ℝ) 1, ‖Lout (γ.extend t)‖ ≤ Lo)
    (hLi : ∀ t ∈ Icc (0 : ℝ) 1, ‖Lin (γ.extend t)‖ ≤ Li) :
    ‖simplePoleResidue (matrixInverseObservable KX Lout Lin) pX-
        simplePoleResidue (matrixInverseObservable KY Lout Lin) pY‖ ≤
      parametrizedContourLength γ/(2*Real.pi)*Lo*Li*B^2*ε/(1-B*ε) := by
  letI : Nonempty n := not_isEmpty_iff.mp (fun h => by
    letI := h
    simp only [Matrix.det_isEmpty,one_ne_zero] at hzeroX)
  have hcX := matrixContour_observable_continuousOn γ hmap havoidX hKX hLout hLin honlyX
  have hcY := matrixContour_observable_continuousOn γ hmap havoidY hKY hLout hLin honlyY
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖matrixInverseObservable KX Lout Lin (γ.extend t)-
        matrixInverseObservable KY Lout Lin (γ.extend t)‖ ≤ Lo*Li*B^2*ε/(1-B*ε) := by
    intro t ht
    exact matrix_observable_neumann_error _ _ _ _ (honlyY _ (hmap ht) (havoidY t ht))
      (hB t ht) (hε t ht) hq (hLo t ht) (hLi t ht)
  rw [← simplyConnectedContour_matrix_observable_residue γ hLip hU hmap havoidX
      hposX hpX hKX hLout hLin hzeroX hderivX honlyX,
    ← simplyConnectedContour_matrix_observable_residue γ hLip hU hmap havoidY
      hposY hpY hKY hLout hLin hzeroY hderivY honlyY]
  exact (normalizedContour_difference_le γ
    (parametrizedContour_lipschitz_speed_integrable γ hLip)
    (parametrizedContour_lipschitz_integrable γ hLip hcX)
    (parametrizedContour_lipschitz_integrable γ hLip hcY) hbound).trans_eq (by ring)

/-- The same actual residue error for an arbitrary continuous rectifiable
contour, with the original geometric total variation as the length. Positive
orientation is certified on its constructed arc-length representative. -/
theorem rectifiableArcPath_matrix_observable_residue_error
    {a pX pY : ℂ} {U : Set ℂ} [SimplyConnectedSpace U]
    {KX KY : ℂ → Matrix n n ℂ} {Lout : ℂ → Matrix o n ℂ} {Lin : ℂ → Matrix n i ℂ}
    {B ε Lo Li : ℝ}
    (γ : Path a a) (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1))
    (hU : IsOpen U) (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) U)
    (havoidX : ∀ t ∈ Icc (0 : ℝ) 1, (rectifiableArcPath γ hBV).extend t ≠ pX)
    (havoidY : ∀ t ∈ Icc (0 : ℝ) 1, (rectifiableArcPath γ hBV).extend t ≠ pY)
    (hposX : lipschitzContourWinding (rectifiableArcPath γ hBV) havoidX = 1)
    (hposY : lipschitzContourWinding (rectifiableArcPath γ hBV) havoidY = 1)
    (hpX : pX ∈ U) (hpY : pY ∈ U)
    (hKX : AnalyticOnNhd ℂ KX U) (hKY : AnalyticOnNhd ℂ KY U)
    (hLout : AnalyticOnNhd ℂ Lout U) (hLin : AnalyticOnNhd ℂ Lin U)
    (hzeroX : (KX pX).det = 0) (hzeroY : (KY pY).det = 0)
    (hderivX : deriv (fun z => (KX z).det) pX ≠ 0)
    (hderivY : deriv (fun z => (KY z).det) pY ≠ 0)
    (honlyX : ∀ z ∈ U, z ≠ pX → (KX z).det ≠ 0)
    (honlyY : ∀ z ∈ U, z ≠ pY → (KY z).det ≠ 0)
    (hq : B*ε < 1)
    (hB : ∀ z ∈ γ.extend '' Icc (0 : ℝ) 1, ‖(KY z)⁻¹‖ ≤ B)
    (hε : ∀ z ∈ γ.extend '' Icc (0 : ℝ) 1, ‖KX z-KY z‖ ≤ ε)
    (hLo : ∀ z ∈ γ.extend '' Icc (0 : ℝ) 1, ‖Lout z‖ ≤ Lo)
    (hLi : ∀ z ∈ γ.extend '' Icc (0 : ℝ) 1, ‖Lin z‖ ≤ Li) :
    ‖simplePoleResidue (matrixInverseObservable KX Lout Lin) pX-
        simplePoleResidue (matrixInverseObservable KY Lout Lin) pY‖ ≤
      (rectifiablePathLength γ : ℝ)/(2*Real.pi)*Lo*Li*B^2*ε/(1-B*ε) := by
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (rectifiableArcPath γ hBV).extend t ∈ γ.extend '' Icc (0 : ℝ) 1 := by
    rw [← rectifiableArcPath_image γ hBV]
    exact mem_image_of_mem _ ht
  have h0 : γ.extend 0 ∈ γ.extend '' Icc (0 : ℝ) 1 :=
    mem_image_of_mem _ ⟨le_rfl,zero_le_one⟩
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε _ h0)
  have hLo0 : 0 ≤ Lo := (norm_nonneg _).trans (hLo _ h0)
  have hLi0 : 0 ≤ Li := (norm_nonneg _).trans (hLi _ h0)
  have hden : 0 < 1-B*ε := sub_pos.mpr hq
  have hC : 0 ≤ Lo*Li*B^2*ε/(1-B*ε) := by positivity
  have hb := simplyConnectedContour_matrix_observable_residue_error _
    (rectifiableArcPath_lipschitz γ hBV) hU (rectifiableArcPath_mapsTo γ hBV hmap)
    havoidX havoidY hposX hposY hpX hpY hKX hKY hLout hLin hzeroX hzeroY
    hderivX hderivY honlyX honlyY hq
    (fun t ht => hB _ (hmem t ht)) (fun t ht => hε _ (hmem t ht))
    (fun t ht => hLo _ (hmem t ht)) (fun t ht => hLi _ (hmem t ht))
  calc
    _ ≤ parametrizedContourLength (rectifiableArcPath γ hBV)/(2*Real.pi)*
        (Lo*Li*B^2*ε/(1-B*ε)) := hb.trans_eq (by ring)
    _ ≤ (rectifiablePathLength γ : ℝ)/(2*Real.pi)*(Lo*Li*B^2*ε/(1-B*ε)) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (rectifiableArcPath_length_le γ hBV)
          (by positivity : 0 ≤ 2*Real.pi)) hC
    _ = _ := by ring

end UV
