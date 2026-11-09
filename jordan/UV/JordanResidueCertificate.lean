import UV.JordanResidueFormula
import UV.JordanResidueLiftConstruction

/-! Nonspherical C1 residue certificates with intrinsic geometric winding.
The argument lift, simple-pole numerator, and contour/residue equality are
all constructed. The analytic-domain theorem is still restricted to a disk;
no arbitrary rectifiable Jordan-domain theorem is claimed here. -/

noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology

namespace UV

def c1ContourWinding {a p : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p) : ℤ :=
  contourLiftWinding (constructedContourLogLift γ hγ havoid)

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]

/-- The orientation is the intrinsic geometric winding of the original
curve. No argument lift or pole numerator is supplied by the caller. -/
theorem c1Contour_simple_denominator_residue {a p c : ℂ} {r : ℝ}
    {k : ℂ → ℂ} {n : ℂ → Z} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) (ball c r))
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hpos : c1ContourWinding γ hγ havoid = 1) (hp : p ∈ ball c r)
    (hk : DifferentiableOn ℂ k (closedBall c r))
    (hn : DifferentiableOn ℂ n (closedBall c r))
    (hzero : k p = 0) (hderiv : deriv k p ≠ 0)
    (honly : ∀ z ∈ closedBall c r, z ≠ p → k z ≠ 0) :
    (2*Real.pi*I : ℂ)⁻¹ • parametrizedContourIntegral (fun z => (k z)⁻¹ • n z) γ =
      simplePoleResidue (fun z => (k z)⁻¹ • n z) p := by
  let G : ℂ → Z := fun z => (dslope k p z)⁻¹ • n z
  obtain ⟨hG, hrepr⟩ := simple_denominator_pole_numerator hp hk hn hzero hderiv honly
  have hcontour : parametrizedContourIntegral (fun z => (k z)⁻¹ • n z) γ =
      parametrizedContourIntegral (fun z => (z-p)⁻¹ • G z) γ :=
    parametrizedContourIntegral_congr γ (fun t ht =>
      hrepr (γ.extend t) (ball_subset_closedBall (hmap ht)) (havoid t ht))
  rw [hcontour, parametrizedContour_simplePole_residue γ hγ hmap hp
    (hG.mono ball_subset_closedBall) (constructedContourLogLift γ hγ havoid) hpos,
    simplePole_residue_of_ball_holomorphic hp (hG.mono ball_subset_closedBall),
    simple_denominator_residue hp hk hn hzero hderiv honly]
  rw [dslope_same]

/-- The actual residue error on a geometric positive-winding C1 contour,
with possibly different simple denominator zeros and the exact length
factor. No contour/residue identity or holomorphic numerator is a premise. -/
theorem c1Contour_simple_denominator_residue_error {a pX pY c : ℂ} {r C : ℝ}
    {kX kY : ℂ → ℂ} {nX nY : ℂ → Z} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hmap : MapsTo γ.extend (Icc (0 : ℝ) 1) (ball c r))
    (havoidX : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ pX)
    (havoidY : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ pY)
    (hposX : c1ContourWinding γ hγ havoidX = 1)
    (hposY : c1ContourWinding γ hγ havoidY = 1)
    (hpX : pX ∈ ball c r) (hpY : pY ∈ ball c r)
    (hkX : DifferentiableOn ℂ kX (closedBall c r))
    (hkY : DifferentiableOn ℂ kY (closedBall c r))
    (hnX : DifferentiableOn ℂ nX (closedBall c r))
    (hnY : DifferentiableOn ℂ nY (closedBall c r))
    (hzeroX : kX pX = 0) (hzeroY : kY pY = 0)
    (hderivX : deriv kX pX ≠ 0) (hderivY : deriv kY pY ≠ 0)
    (honlyX : ∀ z ∈ closedBall c r, z ≠ pX → kX z ≠ 0)
    (honlyY : ∀ z ∈ closedBall c r, z ≠ pY → kY z ≠ 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(kX (γ.extend t))⁻¹ • nX (γ.extend t)-(kY (γ.extend t))⁻¹ • nY (γ.extend t)‖ ≤ C) :
    ‖simplePoleResidue (fun z => (kX z)⁻¹ • nX z) pX-
        simplePoleResidue (fun z => (kY z)⁻¹ • nY z) pY‖ ≤
      parametrizedContourLength γ/(2*Real.pi)*C := by
  have hcX : ContinuousOn (fun t : ℝ => (kX (γ.extend t))⁻¹ • nX (γ.extend t)) (Icc (0 : ℝ) 1) :=
    ((hkX.continuousOn.comp hγ.continuousOn
      (fun t ht => ball_subset_closedBall (hmap ht))).inv₀
      (fun t ht => honlyX _ (ball_subset_closedBall (hmap ht)) (havoidX t ht))).smul
        (hnX.continuousOn.comp hγ.continuousOn (fun t ht => ball_subset_closedBall (hmap ht)))
  have hcY : ContinuousOn (fun t : ℝ => (kY (γ.extend t))⁻¹ • nY (γ.extend t)) (Icc (0 : ℝ) 1) :=
    ((hkY.continuousOn.comp hγ.continuousOn
      (fun t ht => ball_subset_closedBall (hmap ht))).inv₀
      (fun t ht => honlyY _ (ball_subset_closedBall (hmap ht)) (havoidY t ht))).smul
        (hnY.continuousOn.comp hγ.continuousOn (fun t ht => ball_subset_closedBall (hmap ht)))
  rw [← c1Contour_simple_denominator_residue γ hγ hmap havoidX hposX hpX hkX hnX hzeroX hderivX honlyX,
    ← c1Contour_simple_denominator_residue γ hγ hmap havoidY hposY hpY hkY hnY hzeroY hderivY honlyY]
  exact normalizedContour_difference_le γ (parametrizedContour_c1_speed_integrable γ hγ)
    (parametrizedContour_c1_integrable γ hγ hcX) (parametrizedContour_c1_integrable γ hγ hcY) hbound

end UV
