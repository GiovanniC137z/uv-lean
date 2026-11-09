import UV.CompatibleOperatorResidues

/-! The complete source observable error in arbitrary compatible induced
operator norms. Finite-dimensional coordinates are used only for determinant
and pole algebra; every norm constant stays in its original operator space. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology unitInterval Matrix.Norms.L2Operator NNReal

namespace UV

variable {H In Out : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup In] [NormedSpace ℂ In]
  [NormedAddCommGroup Out] [NormedSpace ℂ Out] [CompleteSpace Out]
  [FiniteDimensional ℂ H]
  {n : Type*} [Fintype n] [DecidableEq n]
  (e : (H →L[ℂ] H) ≃ₐ[ℂ] Matrix n n ℂ)

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
private theorem compatibleOperator_nontrivial_of_determinant_zero
    (A : H →L[ℂ] H) (hzero : (e A).det = 0) : Nontrivial H := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · letI := hs
    exfalso
    have hA : A = 1 := Subsingleton.elim _ _
    have hdet : (e A).det = 1 := by rw [hA,map_one,Matrix.det_one]
    exact zero_ne_one (hzero.symm.trans hdet)
  · exact hn

/-- All hypotheses are the source's geometric, analytic and original-norm
boundary data. The filling, quotient, residues, exact constant and strict
visibility consequence are proved; pole locations need not agree. -/
theorem observable_rectifiable_jordan_residue_error_compatible
    {a pX pY : ℂ}
    {KX KY : ℂ → H →L[ℂ] H} {Lout : ℂ → H →L[ℂ] Out} {Lin : ℂ → In →L[ℂ] H}
    {B ε Lo Li : ℝ}
    (γ : Path a a) (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1))
    (hinj : InjOn γ.extend (Ico (0 : ℝ) 1))
    (hpX : pX ∈ jordanInterior (jordanPathCarrier γ))
    (hpY : pY ∈ jordanInterior (jordanPathCarrier γ))
    (hposX : lipschitzContourWinding (rectifiableArcPath γ hBV)
      (rectifiableJordanArc_avoids γ hBV hpX) = 1)
    (hposY : lipschitzContourWinding (rectifiableArcPath γ hBV)
      (rectifiableJordanArc_avoids γ hBV hpY) = 1)
    (hKX : AnalyticOnNhd ℂ KX (jordanFilledRegion (jordanPathCarrier γ)))
    (hKY : AnalyticOnNhd ℂ KY (jordanFilledRegion (jordanPathCarrier γ)))
    (hLout : AnalyticOnNhd ℂ Lout (jordanFilledRegion (jordanPathCarrier γ)))
    (hLin : AnalyticOnNhd ℂ Lin (jordanFilledRegion (jordanPathCarrier γ)))
    (hzeroX : compatibleOperatorDeterminant e KX pX = 0) (hzeroY : compatibleOperatorDeterminant e KY pY = 0)
    (hderivX : deriv (fun z => compatibleOperatorDeterminant e KX z) pX ≠ 0)
    (hderivY : deriv (fun z => compatibleOperatorDeterminant e KY z) pY ≠ 0)
    (honlyX : ∀ z ∈ jordanInterior (jordanPathCarrier γ), z ≠ pX → compatibleOperatorDeterminant e KX z ≠ 0)
    (honlyY : ∀ z ∈ jordanInterior (jordanPathCarrier γ), z ≠ pY → compatibleOperatorDeterminant e KY z ≠ 0)
    (hYboundary : ∀ z ∈ jordanPathCarrier γ, IsUnit (KY z))
    (hq : B*ε < 1)
    (hB : ∀ z ∈ jordanPathCarrier γ, ‖Ring.inverse (KY z)‖ ≤ B)
    (hε : ∀ z ∈ jordanPathCarrier γ, ‖KX z-KY z‖ ≤ ε)
    (hLo : ∀ z ∈ jordanPathCarrier γ, ‖Lout z‖ ≤ Lo)
    (hLi : ∀ z ∈ jordanPathCarrier γ, ‖Lin z‖ ≤ Li) :
    let RX := simplePoleResidue (compatibleOperatorObservable KX Lout Lin) pX
    let RY := simplePoleResidue (compatibleOperatorObservable KY Lout Lin) pY
    let E := (rectifiablePathLength γ : ℝ)/(2*Real.pi)*Lo*Li*B^2*ε/(1-B*ε)
    ‖RX-RY‖ ≤ E ∧ ∀ lower : ℝ, lower ≤ ‖RY‖ → E < lower → RX ≠ 0 := by
  letI : Nontrivial H := compatibleOperator_nontrivial_of_determinant_zero e (KX pX) hzeroX
  let C := jordanPathCarrier γ
  let α := rectifiableArcPath γ hBV
  have hmap : MapsTo α.extend (Icc (0 : ℝ) 1) C :=
    fun _ ht => jordanArcPath_mem_boundary γ hBV ht
  have hXboundary : ∀ z ∈ C, compatibleOperatorDeterminant e KX z ≠ 0 := by
    intro z hz
    have hY : IsUnit (KY z) := hYboundary z hz
    have he : KY z-(KY z-KX z) = KX z := by abel
    have hu := (response_inverse_perturbation hY
      (hB z hz)
      (show ‖KY z-KX z‖ ≤ ε by simpa only [norm_sub_rev] using hε z hz) hq).1
    rw [he] at hu
    exact (compatibleOperator_isUnit_iff e (KX z)).mp hu
  have hXF : ∀ z ∈ jordanFilledRegion C, z ≠ pX → compatibleOperatorDeterminant e KX z ≠ 0 := by
    intro z hz hzp
    rw [jordanFilledRegion_eq_union] at hz
    exact hz.elim (fun hc => hXboundary z hc) (fun hi => honlyX z hi hzp)
  have hYF : ∀ z ∈ jordanFilledRegion C, z ≠ pY → compatibleOperatorDeterminant e KY z ≠ 0 := by
    intro z hz hzp
    rw [jordanFilledRegion_eq_union] at hz
    exact hz.elim (fun hc => (compatibleOperator_isUnit_iff e (KY z)).mp (hYboundary z hc))
      (fun hi => honlyY z hi hzp)
  have hpxF : pX ∈ jordanFilledRegion C := by
    rw [jordanFilledRegion_eq_union]
    exact Or.inr hpX
  have hpyF : pY ∈ jordanFilledRegion C := by
    rw [jordanFilledRegion_eq_union]
    exact Or.inr hpY
  have hb := jordanContour_compatibleOperator_residue_error e
    (isJordanCurve_of_simple_closedPath γ hinj) α (rectifiableArcPath_lipschitz γ hBV)
    hmap (rectifiableJordanArc_avoids γ hBV hpX) (rectifiableJordanArc_avoids γ hBV hpY)
    hposX hposY hpxF hpyF hKX hKY hLout hLin hzeroX hzeroY hderivX hderivY hXF hYF hq
    (fun t ht => hB _ (hmap ht)) (fun t ht => hε _ (hmap ht))
    (fun t ht => hLo _ (hmap ht)) (fun t ht => hLi _ (hmap ht))
  have h0 : γ.extend 0 ∈ C := mem_image_of_mem _ ⟨le_rfl,zero_le_one⟩
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε _ h0)
  have hLo0 : 0 ≤ Lo := (norm_nonneg _).trans (hLo _ h0)
  have hLi0 : 0 ≤ Li := (norm_nonneg _).trans (hLi _ h0)
  have hden : 0 < 1-B*ε := sub_pos.mpr hq
  have hC0 : 0 ≤ Lo*Li*B^2*ε/(1-B*ε) := by positivity
  have herror : ‖simplePoleResidue (compatibleOperatorObservable KX Lout Lin) pX-
      simplePoleResidue (compatibleOperatorObservable KY Lout Lin) pY‖ ≤
      (rectifiablePathLength γ : ℝ)/(2*Real.pi)*Lo*Li*B^2*ε/(1-B*ε) := by
    calc
      _ ≤ parametrizedContourLength α/(2*Real.pi)*(Lo*Li*B^2*ε/(1-B*ε)) :=
        hb.trans_eq (by ring)
      _ ≤ (rectifiablePathLength γ : ℝ)/(2*Real.pi)*(Lo*Li*B^2*ε/(1-B*ε)) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (rectifiableArcPath_length_le γ hBV)
            (by positivity : 0 ≤ 2*Real.pi)) hC0
      _ = _ := by ring
  exact ⟨herror,fun _ hl hm => pole_residue_nonzero_of_error herror hl hm⟩


end UV
