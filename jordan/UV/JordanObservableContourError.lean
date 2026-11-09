import UV.JordanContourGeometry
import UV.CertifiedMatrixContourResidue
import UV.MatrixObservableNeumannError
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-! Observable residue errors for arbitrary rectifiable Jordan contours.
The simple original path constructs its genuine Jordan property. The proved
Schoenflies theorem supplies a filling inside its actual filled region.
Analyticity is required only near that region, and no simply-connected
neighbourhood, filling or residue identity is a hypothesis. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology unitInterval Matrix.Norms.L2Operator NNReal

namespace UV

/-- The actual bounded complementary components of the contour. -/
def jordanInterior (C : Set ℂ) : Set ℂ :=
  complexPlaneHomeomorph ⁻¹' Schoenflies.inside (complexPlaneHomeomorph '' C)

theorem jordanInterior_not_mem_boundary {C : Set ℂ} {p : ℂ}
    (hp : p ∈ jordanInterior C) : p ∉ C := by
  intro hpc
  exact Schoenflies.inside_subset_compl hp (mem_image_of_mem complexPlaneHomeomorph hpc)

theorem jordanFilledRegion_eq_union (C : Set ℂ) :
    jordanFilledRegion C = C ∪ jordanInterior C := by
  ext z
  constructor
  · rintro (⟨w,hw,he⟩ | hi)
    · exact Or.inl ((complexPlaneHomeomorph.injective he) ▸ hw)
    · exact Or.inr hi
  · rintro (hz | hi)
    · exact Or.inl (mem_image_of_mem complexPlaneHomeomorph hz)
    · exact Or.inr hi

/-- The proved Jordan filling annihilates an actual holomorphic contour
integral. The open analytic locus is constructed from neighbourhood
analyticity of the filled region, rather than supplied as a stronger domain. -/
theorem jordanContour_cauchy_scalar
    {a : ℂ} {κ : ℝ≥0} {C : Set ℂ} {f : ℂ → ℂ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C))
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) C)
    (hf : AnalyticOnNhd ℂ f (jordanFilledRegion C)) :
    parametrizedContourIntegral f γ = 0 := by
  obtain ⟨φ,hφ,hclosed⟩ := jordanContour_path_nullhomotopy C hC γ (fun t => by
    simpa only [Path.extend_apply γ t.property] using hmap t.property)
  exact lipschitzContour_holomorphic_nullhomotopy hLip (isOpen_analyticAt ℂ f)
    φ (fun s t => hf _ (hφ s t)) hclosed (fun _ hz => hz)

/-- Continuous dual separation extends the actual scalar Cauchy theorem
to every complete complex normed readout space, with no finite-dimensional
restriction on the input or output channels. -/
theorem jordanContour_cauchy
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    {a : ℂ} {κ : ℝ≥0} {C : Set ℂ} {f : ℂ → Z}
    (hC : Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C))
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) C)
    (hf : AnalyticOnNhd ℂ f (jordanFilledRegion C)) :
    parametrizedContourIntegral f γ = 0 := by
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro L
  have hfc : ContinuousOn f (jordanFilledRegion C) :=
    fun z hz => (hf z hz).continuousAt.continuousWithinAt
  have hi : parametrizedContourIntegrable f γ :=
    parametrizedContour_lipschitz_integrable γ hLip
      (hfc.comp
        γ.continuous_extend.continuousOn (fun _ ht => subset_jordanFilledRegion C (hmap ht)))
  have hLf : AnalyticOnNhd ℂ (fun z => L (f z)) (jordanFilledRegion C) :=
    fun z hz => (L.analyticAt (f z)).comp (hf z hz)
  have hzero := jordanContour_cauchy_scalar hC γ hLip hmap hLf
  rwa [parametrizedContourIntegral_clm γ L hi] at hzero

section Residues

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]

/-- The Cauchy kernel and the regular part are integrated separately; the
regular part vanishes by the constructed Jordan filling. -/
theorem jordanContour_simplePole_integral
    {a p : ℂ} {κ : ℝ≥0} {C : Set ℂ} {G : ℂ → Z}
    (hC : Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C))
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) C)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hpos : lipschitzContourWinding γ havoid = 1)
    (hp : p ∈ jordanFilledRegion C)
    (hG : AnalyticOnNhd ℂ G (jordanFilledRegion C)) :
    (2*Real.pi*Complex.I : ℂ)⁻¹ • parametrizedContourIntegral (fun z => (z-p)⁻¹ • G z) γ = G p := by
  let H := dslope G p
  have hH : AnalyticOnNhd ℂ H (jordanFilledRegion C) := analyticOnNhd_dslope hG hp
  have hmapF : MapsTo γ.extend (Icc (0 : ℝ) 1) (jordanFilledRegion C) :=
    fun _ ht => subset_jordanFilledRegion C (hmap ht)
  have hcH : ContinuousOn H (jordanFilledRegion C) :=
    fun z hz => (hH z hz).continuousAt.continuousWithinAt
  have hk : ContinuousOn (fun t : ℝ => (γ.extend t-p)⁻¹) (Icc (0 : ℝ) 1) :=
    (γ.continuous_extend.continuousOn.sub continuousOn_const).inv₀
      (fun t ht => sub_ne_zero.mpr (havoid t ht))
  have hconst : parametrizedContourIntegrable (fun z => (z-p)⁻¹ • G p) γ :=
    parametrizedContour_lipschitz_integrable γ hLip (hk.smul continuousOn_const)
  have hregular : parametrizedContourIntegrable H γ :=
    parametrizedContour_lipschitz_integrable γ hLip
      (hcH.comp γ.continuous_extend.continuousOn hmapF)
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
  rw [hsplit,jordanContour_cauchy hC γ hLip hmap hH,add_zero,
    parametrizedContourIntegral_smul_const,smul_smul,
    lipschitzContour_normalized_cauchyKernel_positive γ hLip havoid hpos,one_smul]

/-- The actual simple denominator constructs its numerator and its residue
on the filled region before the Jordan-contour calculation is applied. -/
theorem jordanContour_simple_denominator_residue
    {a p : ℂ} {κ : ℝ≥0} {C : Set ℂ} {k : ℂ → ℂ} {n : ℂ → Z}
    (hC : Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C))
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) C)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hpos : lipschitzContourWinding γ havoid = 1) (hp : p ∈ jordanFilledRegion C)
    (hk : AnalyticOnNhd ℂ k (jordanFilledRegion C))
    (hn : AnalyticOnNhd ℂ n (jordanFilledRegion C))
    (hzero : k p = 0) (hderiv : deriv k p ≠ 0)
    (honly : ∀ z ∈ jordanFilledRegion C, z ≠ p → k z ≠ 0) :
    (2*Real.pi*Complex.I : ℂ)⁻¹ • parametrizedContourIntegral (fun z => (k z)⁻¹ • n z) γ =
      simplePoleResidue (fun z => (k z)⁻¹ • n z) p := by
  let G : ℂ → Z := fun z => (dslope k p z)⁻¹ • n z
  obtain ⟨hG,_,hrepr,hres⟩ :=
    analytic_simple_denominator_regular_part hp hk hn hzero hderiv honly
  have hcontour : parametrizedContourIntegral (fun z => (k z)⁻¹ • n z) γ =
      parametrizedContourIntegral (fun z => (z-p)⁻¹ • G z) γ :=
    parametrizedContourIntegral_congr γ (fun t ht =>
      hrepr _ (subset_jordanFilledRegion C (hmap ht)) (havoid t ht))
  rw [hcontour,jordanContour_simplePole_integral hC γ hLip hmap havoid hpos hp hG]
  exact hres.symm

end Residues

section Matrices

variable {n i o : Type*} [Fintype n] [DecidableEq n]
  [Fintype i] [DecidableEq i] [Fintype o] [DecidableEq o]

theorem jordanContour_matrix_observable_residue
    {a p : ℂ} {κ : ℝ≥0} {C : Set ℂ}
    {K : ℂ → Matrix n n ℂ} {Lout : ℂ → Matrix o n ℂ} {Lin : ℂ → Matrix n i ℂ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C))
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) C)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hpos : lipschitzContourWinding γ havoid = 1) (hp : p ∈ jordanFilledRegion C)
    (hK : AnalyticOnNhd ℂ K (jordanFilledRegion C))
    (hLout : AnalyticOnNhd ℂ Lout (jordanFilledRegion C))
    (hLin : AnalyticOnNhd ℂ Lin (jordanFilledRegion C))
    (hzero : (K p).det = 0) (hderiv : deriv (fun z => (K z).det) p ≠ 0)
    (honly : ∀ z ∈ jordanFilledRegion C, z ≠ p → (K z).det ≠ 0) :
    (2*Real.pi*Complex.I : ℂ)⁻¹ • parametrizedContourIntegral (matrixInverseObservable K Lout Lin) γ =
      simplePoleResidue (matrixInverseObservable K Lout Lin) p := by
  have he : matrixInverseObservable K Lout Lin =
      fun z => ((K z).det)⁻¹ • matrixObservableAdjugateNumerator K Lout Lin z :=
    funext (matrix_observable_adjugate_quotient K Lout Lin)
  rw [he]
  exact jordanContour_simple_denominator_residue hC γ hLip hmap havoid hpos hp
    (matrixContour_det_analyticOnNhd hK)
    (matrixContour_numerator_analyticOnNhd hK hLout hLin) hzero hderiv honly

private theorem jordan_observable_continuousOn
    {a p : ℂ} {C : Set ℂ}
    {K : ℂ → Matrix n n ℂ} {Lout : ℂ → Matrix o n ℂ} {Lin : ℂ → Matrix n i ℂ}
    (γ : Path a a) (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) C)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hK : AnalyticOnNhd ℂ K (jordanFilledRegion C))
    (hLout : AnalyticOnNhd ℂ Lout (jordanFilledRegion C))
    (hLin : AnalyticOnNhd ℂ Lin (jordanFilledRegion C))
    (honly : ∀ z ∈ jordanFilledRegion C, z ≠ p → (K z).det ≠ 0) :
    ContinuousOn (fun t : ℝ => matrixInverseObservable K Lout Lin (γ.extend t))
      (Icc (0 : ℝ) 1) := by
  have hmapF : MapsTo γ.extend (Icc (0 : ℝ) 1) (jordanFilledRegion C) :=
    fun _ ht => subset_jordanFilledRegion C (hmap ht)
  have hd : ContinuousOn (fun z => (K z).det) (jordanFilledRegion C) :=
    fun z hz => (matrixContour_det_analyticOnNhd hK z hz).continuousAt.continuousWithinAt
  have hn : ContinuousOn (matrixObservableAdjugateNumerator K Lout Lin) (jordanFilledRegion C) :=
    fun z hz => (matrixContour_numerator_analyticOnNhd hK hLout hLin z hz).continuousAt.continuousWithinAt
  have hc :=
    ((hd.comp γ.continuous_extend.continuousOn hmapF).inv₀
      (fun t ht => honly _ (hmapF ht) (havoid t ht))).smul
      (hn.comp γ.continuous_extend.continuousOn hmapF)
  change ContinuousOn
    (fun t : ℝ => ((K (γ.extend t)).det)⁻¹ •
      matrixObservableAdjugateNumerator K Lout Lin (γ.extend t))
    (Icc (0 : ℝ) 1) at hc
  simpa only [matrix_observable_adjugate_quotient] using hc

/-- The actual observable-residue error needs only analyticity near the
filled Jordan region. Its Cauchy geometry is derived from Schoenflies. -/
theorem jordanContour_matrix_observable_residue_error
    {a pX pY : ℂ} {κ : ℝ≥0} {C : Set ℂ}
    {KX KY : ℂ → Matrix n n ℂ} {Lout : ℂ → Matrix o n ℂ} {Lin : ℂ → Matrix n i ℂ}
    {B ε Lo Li : ℝ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C))
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend)
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) C)
    (havoidX : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ pX)
    (havoidY : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ pY)
    (hposX : lipschitzContourWinding γ havoidX = 1)
    (hposY : lipschitzContourWinding γ havoidY = 1)
    (hpX : pX ∈ jordanFilledRegion C) (hpY : pY ∈ jordanFilledRegion C)
    (hKX : AnalyticOnNhd ℂ KX (jordanFilledRegion C))
    (hKY : AnalyticOnNhd ℂ KY (jordanFilledRegion C))
    (hLout : AnalyticOnNhd ℂ Lout (jordanFilledRegion C))
    (hLin : AnalyticOnNhd ℂ Lin (jordanFilledRegion C))
    (hzeroX : (KX pX).det = 0) (hzeroY : (KY pY).det = 0)
    (hderivX : deriv (fun z => (KX z).det) pX ≠ 0)
    (hderivY : deriv (fun z => (KY z).det) pY ≠ 0)
    (honlyX : ∀ z ∈ jordanFilledRegion C, z ≠ pX → (KX z).det ≠ 0)
    (honlyY : ∀ z ∈ jordanFilledRegion C, z ≠ pY → (KY z).det ≠ 0)
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
  have hcX := jordan_observable_continuousOn γ hmap havoidX hKX hLout hLin honlyX
  have hcY := jordan_observable_continuousOn γ hmap havoidY hKY hLout hLin honlyY
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖matrixInverseObservable KX Lout Lin (γ.extend t)-
        matrixInverseObservable KY Lout Lin (γ.extend t)‖ ≤ Lo*Li*B^2*ε/(1-B*ε) := by
    intro t ht
    exact matrix_observable_neumann_error _ _ _ _
      (honlyY _ (subset_jordanFilledRegion C (hmap ht)) (havoidY t ht))
      (hB t ht) (hε t ht) hq (hLo t ht) (hLi t ht)
  rw [← jordanContour_matrix_observable_residue hC γ hLip hmap havoidX
      hposX hpX hKX hLout hLin hzeroX hderivX honlyX,
    ← jordanContour_matrix_observable_residue hC γ hLip hmap havoidY
      hposY hpY hKY hLout hLin hzeroY hderivY honlyY]
  exact (normalizedContour_difference_le γ
    (parametrizedContour_lipschitz_speed_integrable γ hLip)
    (parametrizedContour_lipschitz_integrable γ hLip hcX)
    (parametrizedContour_lipschitz_integrable γ hLip hcY) hbound).trans_eq (by ring)

end Matrices

def jordanPathCarrier {a : ℂ} (γ : Path a a) : Set ℂ := γ.extend '' Icc (0 : ℝ) 1

theorem jordanArcPath_mem_boundary {a : ℂ} (γ : Path a a)
    (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (rectifiableArcPath γ hBV).extend t ∈ jordanPathCarrier γ := by
  change (rectifiableArcPath γ hBV).extend t ∈ γ.extend '' Icc (0 : ℝ) 1
  rw [← rectifiableArcPath_image γ hBV]
  exact mem_image_of_mem _ ht

theorem rectifiableJordanArc_avoids {a p : ℂ} (γ : Path a a)
    (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1))
    (hp : p ∈ jordanInterior (jordanPathCarrier γ)) :
    ∀ t ∈ Icc (0 : ℝ) 1, (rectifiableArcPath γ hBV).extend t ≠ p := by
  intro t ht he
  exact jordanInterior_not_mem_boundary hp (he ▸ jordanArcPath_mem_boundary γ hBV ht)

section SourceStatement

variable {n i o : Type*} [Fintype n] [DecidableEq n]
  [Fintype i] [DecidableEq i] [Fintype o] [DecidableEq o]

/-- The literal source proposition for an arbitrary positively oriented
rectifiable simple contour. The Jordan filling is proved, boundary X
invertibility follows from Neumann, poles may differ, and readout residues
may vanish. The only orientation data are genuine geometric winding ones
on the actual ordered arc-length representative. -/
theorem observable_rectifiable_jordan_residue_error
    {a pX pY : ℂ}
    {KX KY : ℂ → Matrix n n ℂ} {Lout : ℂ → Matrix o n ℂ} {Lin : ℂ → Matrix n i ℂ}
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
    (hzeroX : (KX pX).det = 0) (hzeroY : (KY pY).det = 0)
    (hderivX : deriv (fun z => (KX z).det) pX ≠ 0)
    (hderivY : deriv (fun z => (KY z).det) pY ≠ 0)
    (honlyX : ∀ z ∈ jordanInterior (jordanPathCarrier γ), z ≠ pX → (KX z).det ≠ 0)
    (honlyY : ∀ z ∈ jordanInterior (jordanPathCarrier γ), z ≠ pY → (KY z).det ≠ 0)
    (hYboundary : ∀ z ∈ jordanPathCarrier γ, (KY z).det ≠ 0)
    (hq : B*ε < 1)
    (hB : ∀ z ∈ jordanPathCarrier γ, ‖(KY z)⁻¹‖ ≤ B)
    (hε : ∀ z ∈ jordanPathCarrier γ, ‖KX z-KY z‖ ≤ ε)
    (hLo : ∀ z ∈ jordanPathCarrier γ, ‖Lout z‖ ≤ Lo)
    (hLi : ∀ z ∈ jordanPathCarrier γ, ‖Lin z‖ ≤ Li) :
    let RX := simplePoleResidue (matrixInverseObservable KX Lout Lin) pX
    let RY := simplePoleResidue (matrixInverseObservable KY Lout Lin) pY
    let E := (rectifiablePathLength γ : ℝ)/(2*Real.pi)*Lo*Li*B^2*ε/(1-B*ε)
    ‖RX-RY‖ ≤ E ∧ ∀ lower : ℝ, lower ≤ ‖RY‖ → E < lower → RX ≠ 0 := by
  letI : Nonempty n := not_isEmpty_iff.mp (fun h => by
    letI := h
    simp only [Matrix.det_isEmpty,one_ne_zero] at hzeroX)
  let C := jordanPathCarrier γ
  let α := rectifiableArcPath γ hBV
  have hmap : MapsTo α.extend (Icc (0 : ℝ) 1) C :=
    fun _ ht => jordanArcPath_mem_boundary γ hBV ht
  have hXboundary : ∀ z ∈ C, (KX z).det ≠ 0 := by
    intro z hz
    have hY : IsUnit (KY z) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hYboundary z hz))
    have he : KY z-(KY z-KX z) = KX z := by abel
    have hu := (response_inverse_perturbation hY
      (by simpa only [Matrix.nonsing_inv_eq_ringInverse] using hB z hz)
      (show ‖KY z-KX z‖ ≤ ε by simpa only [norm_sub_rev] using hε z hz) hq).1
    rw [he] at hu
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hXF : ∀ z ∈ jordanFilledRegion C, z ≠ pX → (KX z).det ≠ 0 := by
    intro z hz hzp
    rw [jordanFilledRegion_eq_union] at hz
    exact hz.elim (fun hc => hXboundary z hc) (fun hi => honlyX z hi hzp)
  have hYF : ∀ z ∈ jordanFilledRegion C, z ≠ pY → (KY z).det ≠ 0 := by
    intro z hz hzp
    rw [jordanFilledRegion_eq_union] at hz
    exact hz.elim (fun hc => hYboundary z hc) (fun hi => honlyY z hi hzp)
  have hpxF : pX ∈ jordanFilledRegion C := by
    rw [jordanFilledRegion_eq_union]
    exact Or.inr hpX
  have hpyF : pY ∈ jordanFilledRegion C := by
    rw [jordanFilledRegion_eq_union]
    exact Or.inr hpY
  have hb := jordanContour_matrix_observable_residue_error
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
  have herror : ‖simplePoleResidue (matrixInverseObservable KX Lout Lin) pX-
      simplePoleResidue (matrixInverseObservable KY Lout Lin) pY‖ ≤
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

end SourceStatement

end UV
