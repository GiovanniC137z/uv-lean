import UV.RectifiableContourWinding

/-! The positive orientation convention is checked against the actual
counterclockwise unit circle. Continuous homotopies to that geometric
circle therefore supply positive winding without any integral premise. -/

noncomputable section
open Set Complex
open scoped Topology unitInterval NNReal

namespace UV

def positiveCircleCurve (p : ℂ) (t : ℝ) : ℂ :=
  circleMap p 1 (2*Real.pi*t)

def positiveCirclePath (p : ℂ) : Path (p+1) (p+1) where
  toFun t := positiveCircleCurve p t
  continuous_toFun := by unfold positiveCircleCurve; fun_prop
  source' := by simp [positiveCircleCurve, circleMap]
  target' := by simp [positiveCircleCurve, circleMap, Complex.exp_two_pi_mul_I]

theorem positiveCirclePath_extend (p : ℂ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (positiveCirclePath p).extend t = positiveCircleCurve p t := by
  rw [Path.extend_extends _ ht]
  rfl

theorem positiveCirclePath_c1 (p : ℂ) :
    ContDiffOn ℝ 1 (positiveCirclePath p).extend (Icc (0:ℝ) 1) := by
  have h : ContDiff ℝ 1 (positiveCircleCurve p) := by
    unfold positiveCircleCurve
    exact (contDiff_circleMap p 1).comp (contDiff_const.mul contDiff_id)
  exact h.contDiffOn.congr (fun t ht => positiveCirclePath_extend p ht)

theorem positiveCirclePath_avoids (p : ℂ) :
    ∀ t ∈ Icc (0:ℝ) 1, (positiveCirclePath p).extend t ≠ p := by
  intro t ht
  rw [positiveCirclePath_extend p ht]
  simp [positiveCircleCurve]

theorem positiveCirclePath_lipschitz (p : ℂ) :
    LipschitzWith (Real.nnabs (2*Real.pi)) (positiveCirclePath p).extend := by
  have h : LipschitzWith (Real.nnabs (2*Real.pi)) (positiveCircleCurve p) := by
    have hc : LipschitzWith (Real.nnabs (2*Real.pi))
        (fun t : ℝ => 2*Real.pi*t) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp [Real.dist_eq, ← mul_sub, abs_mul]
    have h := (lipschitzWith_circleMap p 1).comp hc
    simpa only [map_one, one_mul, Function.comp_def, positiveCircleCurve] using h
  have he : (positiveCirclePath p).extend =
      IccExtend zero_le_one (fun t : I => positiveCircleCurve p t) := rfl
  rw [he]
  exact lipschitz_IccExtend zero_le_one h.lipschitzOnWith

def positiveCircleLogLift (p : ℂ) : C1ContourLogLift (positiveCirclePath p) p where
  value t := (2*Real.pi*t : ℝ)*Complex.I
  c1 := by
    change ContDiffOn ℝ 1 (fun t : ℝ => Complex.ofRealCLM (2*Real.pi*t)*Complex.I) _
    exact ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_id)).mul contDiff_const).contDiffOn
  exponential t ht := by
    rw [positiveCirclePath_extend p ht]
    simp [positiveCircleCurve, circleMap]

theorem positiveCircleLogLift_winding (p : ℂ) :
    contourLiftWinding (positiveCircleLogLift p) = 1 := by
  have h := contourLiftWinding_spec (positiveCircleLogLift p)
  have hval : (positiveCircleLogLift p).value 1-(positiveCircleLogLift p).value 0 =
      (1:ℂ)*(2*Real.pi*Complex.I) := by simp [positiveCircleLogLift]
  rw [hval] at h
  have hn : (contourLiftWinding (positiveCircleLogLift p) : ℂ) = 1 :=
    (mul_right_cancel₀ (by simp [Real.pi_ne_zero]) h).symm
  exact_mod_cast hn

/-- The actual counterclockwise circle has geometric winding +1. -/
theorem lipschitzContourWinding_positiveCircle (p : ℂ) :
    lipschitzContourWinding (positiveCirclePath p) (positiveCirclePath_avoids p) = 1 := by
  rw [lipschitzContourWinding_eq_c1 _ (positiveCirclePath_lipschitz p)
    (positiveCirclePath_c1 p)]
  exact (contourLiftWinding_independent _ (positiveCirclePath_c1 p)
    _ (positiveCircleLogLift p)).trans (positiveCircleLogLift_winding p)

/-- A genuine continuous punctured-plane homotopy to the positive circle
certifies the orientation of any Lipschitz loop. -/
theorem lipschitzContourWinding_positive_of_circle_homotopy
    {a p : ℂ} {K : ℝ≥0} {γ : Path a a}
    (hLip : LipschitzWith K γ.extend)
    (havoid : ∀ t ∈ Icc (0:ℝ) 1, γ.extend t ≠ p)
    (φ : (γ : C(I, ℂ)).Homotopy (positiveCirclePath p))
    (hφ : ∀ s t : I, φ (s,t) ≠ p)
    (hclosed : ∀ s : I, φ (s,0) = φ (s,1)) :
    lipschitzContourWinding γ havoid = 1 :=
  (lipschitzContourWinding_homotopy hLip (positiveCirclePath_lipschitz p)
    havoid (positiveCirclePath_avoids p) φ hφ hclosed).trans
      (lipschitzContourWinding_positiveCircle p)

end UV
