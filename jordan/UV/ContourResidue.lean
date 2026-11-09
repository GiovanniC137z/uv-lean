import UV.PoleCertificates
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Quantitative contour estimates for genuine parametrized curve integrals.
The pinned library has no Jordan/winding-number residue theorem for arbitrary
rectifiable simple contours; no such identification is assumed here. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  {c d : ℂ}

def contourOneForm (f : ℂ → Z) (z : ℂ) : ℂ →L[ℂ] Z :=
  ContinuousLinearMap.toSpanSingleton ℂ (f z)

def parametrizedContourIntegral (f : ℂ → Z) (γ : Path c d) : Z :=
  curveIntegral (contourOneForm f) γ

def parametrizedContourSpeed (γ : Path c d) (t : ℝ) : ℝ :=
  ‖derivWithin γ.extend (Icc (0 : ℝ) 1) t‖

def parametrizedContourLength (γ : Path c d) : ℝ :=
  ∫ t in (0 : ℝ)..1, parametrizedContourSpeed γ t

def parametrizedContourIntegrable (f : ℂ → Z) (γ : Path c d) : Prop :=
  CurveIntegrable (contourOneForm f) γ

theorem parametrizedContour_fun (f : ℂ → Z) (γ : Path c d) :
    curveIntegralFun (contourOneForm f) γ =
      fun t : ℝ => (derivWithin γ.extend (Icc (0 : ℝ) 1) t) • f (γ.extend t) := by
  funext t
  rw [curveIntegralFun_def]
  rfl

theorem parametrizedContourIntegral_eq (f : ℂ → Z) (γ : Path c d) :
    parametrizedContourIntegral f γ =
      ∫ t in (0 : ℝ)..1, (derivWithin γ.extend (Icc (0 : ℝ) 1) t) • f (γ.extend t) := by
  rw [parametrizedContourIntegral, curveIntegral_def, parametrizedContour_fun]

theorem parametrizedContourIntegrable_iff (f : ℂ → Z) (γ : Path c d) :
    parametrizedContourIntegrable f γ ↔
      IntervalIntegrable (fun t : ℝ => (derivWithin γ.extend (Icc (0 : ℝ) 1) t) • f (γ.extend t))
        volume 0 1 := by
  rw [parametrizedContourIntegrable, CurveIntegrable, parametrizedContour_fun]

theorem parametrizedContourLength_nonneg (γ : Path c d) : 0 ≤ parametrizedContourLength γ :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)

theorem parametrizedContour_integrable_of_bound {f : ℂ → Z} (γ : Path c d) {C : ℝ}
    (hspeed : IntervalIntegrable (parametrizedContourSpeed γ) volume 0 1)
    (hmeas : AEStronglyMeasurable
      (fun t : ℝ => (derivWithin γ.extend (Icc (0 : ℝ) 1) t) • f (γ.extend t))
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ.extend t)‖ ≤ C) :
    parametrizedContourIntegrable f γ := by
  rw [parametrizedContourIntegrable_iff, intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  apply (hspeed.1.const_mul C).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hbound t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)).trans_eq (by dsimp [parametrizedContourSpeed]; ring)

theorem parametrizedContour_norm_le {f : ℂ → Z} (γ : Path c d) {C : ℝ}
    (hspeed : IntervalIntegrable (parametrizedContourSpeed γ) volume 0 1)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ.extend t)‖ ≤ C) :
    ‖parametrizedContourIntegral f γ‖ ≤ parametrizedContourLength γ * C := by
  rw [parametrizedContourIntegral_eq]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, C * parametrizedContourSpeed γ t := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one _ (hspeed.const_mul C)
      filter_upwards with t
      intro ht
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left (hbound t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)).trans_eq (by dsimp [parametrizedContourSpeed]; ring)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; dsimp [parametrizedContourLength]; ring

theorem normalizedContour_norm_le {f : ℂ → Z} (γ : Path c d) {C : ℝ}
    (hspeed : IntervalIntegrable (parametrizedContourSpeed γ) volume 0 1)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ.extend t)‖ ≤ C) :
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ • parametrizedContourIntegral f γ‖ ≤
      parametrizedContourLength γ / (2 * Real.pi) * C := by
  rw [norm_smul]
  have hn : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ = 1 / (2 * Real.pi) := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hn]
  exact (mul_le_mul_of_nonneg_left (parametrizedContour_norm_le γ hspeed hbound) (by positivity)).trans_eq (by ring)

theorem parametrizedContour_c1_integrable {f : ℂ → Z} (γ : Path c d)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hf : ContinuousOn (fun t : ℝ => f (γ.extend t)) (Icc (0 : ℝ) 1)) :
    parametrizedContourIntegrable f γ := by
  rw [parametrizedContourIntegrable_iff]
  exact ((hγ.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl).smul hf).intervalIntegrable_of_Icc zero_le_one

theorem parametrizedContour_c1_speed_integrable (γ : Path c d)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (parametrizedContourSpeed γ) volume 0 1 :=
  (hγ.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl).norm.intervalIntegrable_of_Icc zero_le_one

theorem parametrizedContourIntegral_sub {f g : ℂ → Z} (γ : Path c d)
    (hf : parametrizedContourIntegrable f γ) (hg : parametrizedContourIntegrable g γ) :
    parametrizedContourIntegral f γ - parametrizedContourIntegral g γ =
      parametrizedContourIntegral (fun z => f z - g z) γ := by
  simp_rw [parametrizedContourIntegral_eq]
  rw [← intervalIntegral.integral_sub ((parametrizedContourIntegrable_iff f γ).mp hf)
    ((parametrizedContourIntegrable_iff g γ).mp hg)]
  congr 1
  funext t
  exact (smul_sub _ _ _).symm

theorem normalizedContour_difference_le {f g : ℂ → Z} (γ : Path c d) {C : ℝ}
    (hspeed : IntervalIntegrable (parametrizedContourSpeed γ) volume 0 1)
    (hf : parametrizedContourIntegrable f γ) (hg : parametrizedContourIntegrable g γ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ.extend t) - g (γ.extend t)‖ ≤ C) :
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ • parametrizedContourIntegral f γ -
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • parametrizedContourIntegral g γ‖ ≤
        parametrizedContourLength γ / (2 * Real.pi) * C := by
  rw [← smul_sub, parametrizedContourIntegral_sub γ hf hg]
  exact normalizedContour_norm_le γ hspeed hbound

/-- At every point of the actual curve the Neumann estimate supplies the
response error. Integration then supplies the source's length factor. -/
theorem observable_parametrizedContour_error
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (KX KY : ℂ → H →L[ℂ] H) (U : ℂ → H →L[ℂ] K) (V : ℂ → K →L[ℂ] H)
    (γ : Path c d) {B ε Lout Lin : ℝ}
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (hX : ContinuousOn (fun t : ℝ =>
      (U (γ.extend t)).comp ((Ring.inverse (KX (γ.extend t))).comp (V (γ.extend t)))) (Icc (0 : ℝ) 1))
    (hY : ContinuousOn (fun t : ℝ =>
      (U (γ.extend t)).comp ((Ring.inverse (KY (γ.extend t))).comp (V (γ.extend t)))) (Icc (0 : ℝ) 1))
    (hε0 : 0 ≤ ε) (hLo : 0 ≤ Lout) (hq : B * ε < 1)
    (hKY : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (KY (γ.extend t)))
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖Ring.inverse (KY (γ.extend t))‖ ≤ B)
    (hε : ∀ t ∈ Icc (0 : ℝ) 1, ‖KX (γ.extend t) - KY (γ.extend t)‖ ≤ ε)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, ‖U (γ.extend t)‖ ≤ Lout)
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, ‖V (γ.extend t)‖ ≤ Lin) :
    (∀ t ∈ Icc (0 : ℝ) 1, IsUnit (KX (γ.extend t))) ∧
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
        parametrizedContourIntegral (fun z => (U z).comp ((Ring.inverse (KX z)).comp (V z))) γ -
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        parametrizedContourIntegral (fun z => (U z).comp ((Ring.inverse (KY z)).comp (V z))) γ‖ ≤
      parametrizedContourLength γ / (2 * Real.pi) * Lout * Lin * B ^ 2 * ε / (1 - B * ε) := by
  have hden : 0 < 1 - B * ε := sub_pos.mpr hq
  have he (z : ℂ) : KY z - (KY z - KX z) = KX z := by abel
  refine ⟨fun t ht => ?_, ?_⟩
  · have hx := (response_inverse_perturbation (hKY t ht) (hB t ht)
      (show ‖KY (γ.extend t) - KX (γ.extend t)‖ ≤ ε by
        simpa only [norm_sub_rev] using hε t ht) hq).1
    rwa [he] at hx
  · have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖(U (γ.extend t)).comp ((Ring.inverse (KX (γ.extend t))).comp (V (γ.extend t))) -
          (U (γ.extend t)).comp ((Ring.inverse (KY (γ.extend t))).comp (V (γ.extend t)))‖ ≤
            Lout * Lin * B ^ 2 * ε / (1 - B * ε) := by
      intro t ht
      rw [← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
      have hh := (response_schur_error (hKY t ht) (hB t ht)
        (show ‖KY (γ.extend t) - KX (γ.extend t)‖ ≤ ε by
          simpa only [norm_sub_rev] using hε t ht) hq (U (γ.extend t)) (V (γ.extend t))).2.2
      rw [he] at hh
      apply hh.trans
      gcongr
      · exact hU t ht
      · exact hV t ht
    have hIX : parametrizedContourIntegrable
        (fun z => (U z).comp ((Ring.inverse (KX z)).comp (V z))) γ :=
      parametrizedContour_c1_integrable γ hγ hX
    have hIY : parametrizedContourIntegrable
        (fun z => (U z).comp ((Ring.inverse (KY z)).comp (V z))) γ :=
      parametrizedContour_c1_integrable γ hγ hY
    have hb := normalizedContour_difference_le γ (parametrizedContour_c1_speed_integrable γ hγ) hIX hIY hbound
    exact hb.trans_eq (by ring)

/-- A strict norm margin also proves nonvanishing for the actual normalized
contour quantities. Identifying these with residues on an arbitrary Jordan
curve requires a separate residue theorem. -/
theorem normalizedContour_nonzero_of_margin {f g : ℂ → Z} (γ : Path c d) {C lower : ℝ}
    (hspeed : IntervalIntegrable (parametrizedContourSpeed γ) volume 0 1)
    (hf : parametrizedContourIntegrable f γ) (hg : parametrizedContourIntegrable g γ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ.extend t) - g (γ.extend t)‖ ≤ C)
    (hlower : lower ≤ ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ • parametrizedContourIntegral g γ‖)
    (hmargin : parametrizedContourLength γ / (2 * Real.pi) * C < lower) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • parametrizedContourIntegral f γ ≠ 0 := by
  intro hz
  have h := normalizedContour_difference_le γ hspeed hf hg hbound
  rw [hz, zero_sub, norm_neg] at h
  linarith

end UV
