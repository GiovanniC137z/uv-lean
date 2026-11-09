import UV.JordanResidueWinding

/-! Actual simple-pole residues on nonspherical contours. The orientation
data are geometric argument lifts. The present analytic-domain theorem
uses a disk containing the curve; arbitrary rectifiable Jordan domains
require the additional geometric/regularity bridges recorded separately. -/

noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology

namespace UV

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]

omit [CompleteSpace Z] in
theorem parametrizedContourIntegral_congr {a b : ℂ} (γ : Path a b) {f g : ℂ → Z}
    (hfg : ∀ t ∈ Icc (0 : ℝ) 1, f (γ.extend t) = g (γ.extend t)) :
    parametrizedContourIntegral f γ = parametrizedContourIntegral g γ := by
  simp_rw [parametrizedContourIntegral_eq]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [hfg t (by simpa only [uIcc_of_le zero_le_one] using ht)]

omit [CompleteSpace Z] in
theorem parametrizedContourIntegral_add {a b : ℂ} (γ : Path a b) {f g : ℂ → Z}
    (hf : parametrizedContourIntegrable f γ) (hg : parametrizedContourIntegrable g γ) :
    parametrizedContourIntegral (fun z => f z+g z) γ =
      parametrizedContourIntegral f γ+parametrizedContourIntegral g γ := by
  simp_rw [parametrizedContourIntegral_eq, smul_add]
  exact intervalIntegral.integral_add ((parametrizedContourIntegrable_iff f γ).mp hf)
    ((parametrizedContourIntegrable_iff g γ).mp hg)

theorem parametrizedContourIntegral_smul_const {a b : ℂ} (γ : Path a b) (f : ℂ → ℂ) (v : Z) :
    parametrizedContourIntegral (fun z => f z • v) γ = parametrizedContourIntegral f γ • v := by
  simp_rw [parametrizedContourIntegral_eq, smul_smul, smul_eq_mul]
  exact intervalIntegral.integral_smul_const _ v

omit [CompleteSpace Z] in
theorem simplePole_residue_of_ball_holomorphic {G : ℂ → Z} {p c : ℂ} {r : ℝ}
    (hp : p ∈ ball c r) (hG : DifferentiableOn ℂ G (ball c r)) :
    simplePoleResidue (fun z : ℂ => (z-p)⁻¹ • G z) p = G p := by
  obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (isOpen_ball.mem_nhds hp)
  exact simplePole_residue (mem_ball_self hε) (hG.mono hsub) (fun _ _ _ => rfl)

/-- The residue identity is proved for the actual C1 curve integral using
the primitive of the holomorphic divided-difference regular part and the
separately derived geometric winding computation. -/
theorem parametrizedContour_simplePole_residue {a p c : ℂ} {r : ℝ} {G : ℂ → Z}
    (γ : Path a a) (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) (ball c r))
    (hp : p ∈ ball c r) (hG : DifferentiableOn ℂ G (ball c r))
    (L : C1ContourLogLift γ p) (hpos : contourLiftWinding L = 1) :
    (2*Real.pi*I : ℂ)⁻¹ • parametrizedContourIntegral (fun z : ℂ => (z-p)⁻¹ • G z) γ =
      simplePoleResidue (fun z : ℂ => (z-p)⁻¹ • G z) p := by
  let H := dslope G p
  have hH : DifferentiableOn ℂ H (ball c r) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hp)).mpr hG
  have hk : ContinuousOn (fun t : ℝ => (γ.extend t-p)⁻¹) (Icc (0 : ℝ) 1) :=
    (hγ.continuousOn.sub continuousOn_const).inv₀
      (fun t ht => sub_ne_zero.mpr (contourLogLift_avoids_pole L ht))
  have hconst : parametrizedContourIntegrable (fun z : ℂ => (z-p)⁻¹ • G p) γ :=
    parametrizedContour_c1_integrable γ hγ (hk.smul continuousOn_const)
  have hregular : parametrizedContourIntegrable H γ :=
    parametrizedContour_c1_integrable γ hγ (hH.continuousOn.comp hγ.continuousOn hmap)
  have hsplit : parametrizedContourIntegral (fun z : ℂ => (z-p)⁻¹ • G z) γ =
      parametrizedContourIntegral (fun z : ℂ => (z-p)⁻¹ • G p) γ+
        parametrizedContourIntegral H γ := by
    rw [← parametrizedContourIntegral_add γ hconst hregular]
    apply parametrizedContourIntegral_congr
    intro t ht
    have hne := contourLogLift_avoids_pole L ht
    dsimp only [H]
    rw [dslope_of_ne _ hne]
    simp only [slope, vsub_eq_sub, smul_sub]
    abel
  rw [hsplit, parametrizedContourIntegral_eq_zero_in_ball γ hγ hmap hH, add_zero,
    parametrizedContourIntegral_smul_const, smul_smul,
    normalizedContour_cauchyKernel_positive γ hγ L hpos, one_smul,
    simplePole_residue_of_ball_holomorphic hp hG]

/-- Different pole locations are allowed. This is an actual residue error
bound on a nonspherical positive-winding C1 contour, not an estimate of
unidentified contour quantities. -/
theorem parametrizedContour_simplePole_residue_error
    {a pX pY c : ℂ} {r C : ℝ} {GX GY : ℂ → Z}
    (γ : Path a a) (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) (ball c r))
    (hpX : pX ∈ ball c r) (hpY : pY ∈ ball c r)
    (hGX : DifferentiableOn ℂ GX (ball c r)) (hGY : DifferentiableOn ℂ GY (ball c r))
    (LX : C1ContourLogLift γ pX) (LY : C1ContourLogLift γ pY)
    (hposX : contourLiftWinding LX = 1) (hposY : contourLiftWinding LY = 1)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(γ.extend t-pX)⁻¹ • GX (γ.extend t)-(γ.extend t-pY)⁻¹ • GY (γ.extend t)‖ ≤ C) :
    ‖simplePoleResidue (fun z : ℂ => (z-pX)⁻¹ • GX z) pX-
        simplePoleResidue (fun z : ℂ => (z-pY)⁻¹ • GY z) pY‖ ≤
      parametrizedContourLength γ/(2*Real.pi)*C := by
  have hcX : ContinuousOn (fun t : ℝ => (γ.extend t-pX)⁻¹ • GX (γ.extend t)) (Icc (0 : ℝ) 1) :=
    ((hγ.continuousOn.sub continuousOn_const).inv₀
      (fun t ht => sub_ne_zero.mpr (contourLogLift_avoids_pole LX ht))).smul
        (hGX.continuousOn.comp hγ.continuousOn hmap)
  have hcY : ContinuousOn (fun t : ℝ => (γ.extend t-pY)⁻¹ • GY (γ.extend t)) (Icc (0 : ℝ) 1) :=
    ((hγ.continuousOn.sub continuousOn_const).inv₀
      (fun t ht => sub_ne_zero.mpr (contourLogLift_avoids_pole LY ht))).smul
        (hGY.continuousOn.comp hγ.continuousOn hmap)
  rw [← parametrizedContour_simplePole_residue γ hγ hmap hpX hGX LX hposX,
    ← parametrizedContour_simplePole_residue γ hγ hmap hpY hGY LY hposY]
  exact normalizedContour_difference_le γ (parametrizedContour_c1_speed_integrable γ hγ)
    (parametrizedContour_c1_integrable γ hγ hcX) (parametrizedContour_c1_integrable γ hγ hcY) hbound

end UV
