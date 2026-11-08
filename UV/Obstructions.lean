import UV.Convergence
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Actual analytic obstructions for the source's explicitly displayed Ward
trace and combined constant-background trace. The derivations of those scalar
expressions from matrix-valued vertices remain separate tasks. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace UV

theorem ratio_shift_atTop (b c : ℝ) :
    Tendsto (fun u : ℝ => (u + b) / (u + c)) atTop (𝓝 1) := by
  have hd := tendsto_atTop_add_const_right atTop c (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add (hd.const_div_atTop (b - c))
  have heq : (fun u : ℝ => 1 + (b - c) / (u + c)) =ᶠ[atTop]
      (fun u : ℝ => (u + b) / (u + c)) := by
    filter_upwards [hd.eventually (eventually_ne_atTop 0)] with u hu
    change u + c ≠ 0 at hu
    field_simp [hu]
    ring
  simpa only [add_zero] using h.congr' heq

def wardTrace (a M m e u : ℝ) : ℝ :=
  e ^ 2 * (8 * (u + 2 * m ^ 2) / (u + m ^ 2) ^ 2 -
    8 * a * u / (Real.sqrt (u + M ^ 2) * (u + m ^ 2)) -
    4 * a ^ 2 * u / (u + M ^ 2))

/-- Exact nonzero UV asymptote of the scalar expression in
    eq:OQED-Ward-bubble-trace. -/
theorem wardTrace_tendsto (a M m e : ℝ) :
    Tendsto (wardTrace a M m e) atTop (𝓝 (-4 * e ^ 2 * a ^ 2)) := by
  have hdm := tendsto_atTop_add_const_right atTop (m ^ 2)
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hdM := tendsto_atTop_add_const_right atTop (M ^ 2)
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hs : Tendsto (fun u : ℝ => Real.sqrt (u + M ^ 2)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hdM
  have h1 := ((ratio_shift_atTop (2 * m ^ 2) (m ^ 2)).mul
    (hdm.const_div_atTop 1)).const_mul 8
  have h2 := ((ratio_shift_atTop 0 (m ^ 2)).mul
    (hs.const_div_atTop 1)).const_mul (8 * a)
  have h3 := (ratio_shift_atTop 0 (M ^ 2)).const_mul (4 * a ^ 2)
  have hall := ((h1.sub h2).sub h3).const_mul (e ^ 2)
  convert hall using 1
  · ext u
    simp only [wardTrace, add_zero, id_eq, div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    ring
  · ring

/-- Every cocompact set has infinite Haar measure in a noncompact group. -/
theorem haar_cocompact_infinite {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [WeaklyLocallyCompactSpace E]
    [NoncompactSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} (hs : s ∈ cocompact E) : μ s = ⊤ := by
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.mp hs
  have hKc : μ Kᶜ = ⊤ := by
    rw [measure_compl hK.measurableSet hK.measure_lt_top.ne,
      measure_univ_of_isAddLeftInvariant μ]
    exact ENNReal.top_sub hK.measure_lt_top.ne
  exact top_unique (hKc ▸ measure_mono hKs)

/-- A nonzero limit at spatial infinity precludes absolute integrability. -/
theorem not_integrable_of_cocompact_nonzero_limit {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [WeaklyLocallyCompactSpace E] [NoncompactSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ} {c : ℝ}
    (hc : c ≠ 0) (hf : Tendsto f (cocompact E) (𝓝 c)) : ¬ Integrable f μ := by
  intro h
  exact hc ((h.integrableAtFilter (cocompact E)).eq_zero_of_tendsto
    (fun _ hs => haar_cocompact_infinite μ hs) hf)

/-- The displayed Ward trace is genuinely nonintegrable over four-dimensional
    Euclidean loop momentum for positive depth and nonzero charge. -/
theorem wardTrace_not_integrable {a e : ℝ} (ha : 0 < a) (he : e ≠ 0) (M m : ℝ) :
    ¬ Integrable (fun k : EuclideanSpace ℝ (Fin 4) =>
      wardTrace a M m e (‖k‖ ^ 2)) := by
  apply not_integrable_of_cocompact_nonzero_limit volume
    (c := -4 * e ^ 2 * a ^ 2)
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 he))
      (pow_ne_zero 2 ha.ne')
  · exact (wardTrace_tendsto a M m e).comp
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        tendsto_norm_cocompact_atTop)

/-- The combined bubble and contact trace in eq:OQED-contact-trace, written with
    the equivalent square-root-cubed denominator. -/
def contactTrace (a M m e u : ℝ) : ℝ :=
  e ^ 2 * (4 * a * (3 * u + 4 * M ^ 2) / Real.sqrt (u + M ^ 2) ^ 3 +
    8 * (u + 2 * m ^ 2) / (u + m ^ 2) ^ 2)

theorem contactTrace_lower {a M e : ℝ} (ha : 0 < a) (hM : 0 < M)
    (m : ℝ) (r : ℝ) (hr : 0 ≤ r) :
    12 * a * e ^ 2 / (r + M) ≤ contactTrace a M m e (r ^ 2) := by
  let s := Real.sqrt (r ^ 2 + M ^ 2)
  have hu : 0 < r ^ 2 + M ^ 2 := by positivity
  have hs : 0 < s := Real.sqrt_pos.mpr hu
  have hsq : s ^ 2 = r ^ 2 + M ^ 2 := Real.sq_sqrt hu.le
  have hcube : s ^ 3 = (r ^ 2 + M ^ 2) * s := by
    calc
      s ^ 3 = s ^ 2 * s := by ring
      _ = _ := by rw [hsq]
  have hsr : s ≤ r + M := by
    have h := depthProfile_le_sqrt hM.le (sq_nonneg r)
    rw [Real.sqrt_sq hr] at h
    simpa only [depthProfile, sub_le_iff_le_add] using h
  have hfirst : 12 * a / s ≤ 4 * a * (3 * r ^ 2 + 4 * M ^ 2) / s ^ 3 := by
    apply (div_le_div_iff₀ hs (pow_pos hs 3)).mpr
    rw [hcube]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * a * s) (sq_nonneg M)]
  have hsecond : 0 ≤ 8 * (r ^ 2 + 2 * m ^ 2) / (r ^ 2 + m ^ 2) ^ 2 := by
    positivity
  have hsmall := div_le_div_of_nonneg_left (by positivity : 0 ≤ 12 * a) hs hsr
  have hb := mul_le_mul_of_nonneg_left (hsmall.trans hfirst) (sq_nonneg e)
  dsimp [contactTrace]
  calc
    12 * a * e ^ 2 / (r + M) = e ^ 2 * (12 * a / (r + M)) := by ring
    _ ≤ e ^ 2 * (4 * a * (3 * r ^ 2 + 4 * M ^ 2) /
        Real.sqrt (r ^ 2 + M ^ 2) ^ 3) := by simpa only [s] using hb
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hsecond) (sq_nonneg e)

/-- The source's combined constant-background scalar trace is strictly positive. -/
theorem contactTrace_pos {a M e u : ℝ} (ha : 0 < a) (hM : 0 < M)
    (he : e ≠ 0) (hu : 0 ≤ u) (m : ℝ) : 0 < contactTrace a M m e u := by
  have h := contactTrace_lower (e := e) ha hM m (Real.sqrt u) (Real.sqrt_nonneg u)
  rw [Real.sq_sqrt hu] at h
  exact (by positivity : 0 < 12 * a * e ^ 2 / (Real.sqrt u + M)).trans_le h

/-- A positive inverse-linear radial lower bound cannot be integrable in 4D.
    This proof uses only ball volumes and monotonicity of finite-domain integrals. -/
theorem not_integrable_inverse_linear_lower {f : EuclideanSpace ℝ (Fin 4) → ℝ}
    {C b : ℝ} (hC : 0 < C) (hb : 0 < b)
    (hbound : ∀ x, C / (‖x‖ + b) ≤ f x) : ¬ Integrable f := by
  intro hf
  let v := volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1)
  have hv : 0 < v := by
    apply ENNReal.toReal_pos_iff.mpr
    exact ⟨Metric.measure_ball_pos volume 0 (by norm_num), measure_ball_lt_top⟩
  have hball (R : ℝ) (hR : 0 ≤ R) :
      volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) R) = R ^ 4 * v := by
    rw [measureReal_def, Measure.addHaar_ball volume 0 hR, ENNReal.toReal_mul]
    simp only [finrank_euclideanSpace, Fintype.card_fin,
      ENNReal.toReal_ofReal (pow_nonneg hR _)]
    rfl
  have hpos : ∀ x, 0 ≤ f x := by
    intro x
    exact (by positivity : 0 ≤ C / (‖x‖ + b)).trans (hbound x)
  have hineq (R : ℝ) (hR : 0 ≤ R) : C * R ^ 4 / (R + b) * v ≤ ∫ x, f x := by
    have hlocal : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) R,
        C / (R + b) ≤ f x := by
      intro x hx
      have hn : ‖x‖ ≤ R := (show ‖x‖ < R by
        simpa only [Metric.mem_ball, dist_zero_right] using hx).le
      exact (div_le_div_of_nonneg_left hC.le (by positivity)
        (add_le_add_right hn b)).trans (hbound x)
    have hcint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 4) => C / (R + b))
        (Metric.ball 0 R) := integrableOn_const measure_ball_lt_top.ne
    calc
      _ = ∫ _ : EuclideanSpace ℝ (Fin 4) in Metric.ball 0 R, C / (R + b) := by
        simp only [setIntegral_const, smul_eq_mul, hball R hR]
        ring
      _ ≤ ∫ x in Metric.ball 0 R, f x :=
        integral_mono_ae hcint hf.integrableOn
          (ae_restrict_mem measurableSet_ball |>.mono (fun x hx => hlocal x hx))
      _ ≤ ∫ x, f x := setIntegral_le_integral hf (Eventually.of_forall hpos)
  have hdiv : Tendsto (fun R : ℝ => R ^ 4 / (R + b)) atTop atTop := by
    have h := (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).atTop_mul_pos
      (by norm_num : (0 : ℝ) < 1) (ratio_shift_atTop 0 b)
    convert h using 1
    ext R
    simp only [add_zero]
    ring
  have hg : Tendsto (fun R : ℝ => C * R ^ 4 / (R + b) * v) atTop atTop := by
    have h := (hdiv.const_mul_atTop hC).atTop_mul_const hv
    convert h using 1
    ext R
    ring
  have he := hg.eventually (eventually_gt_atTop (∫ x, f x))
  obtain ⟨R, hR, hlarge⟩ := (eventually_ge_atTop (0 : ℝ) |>.and he).exists
  exact (not_lt_of_ge (hineq R hR)) hlarge

/-- Actual nonintegrability of the combined bubble and contact trace in the
    source's raw constant-background test, in four Euclidean dimensions. -/
theorem contactTrace_not_integrable {a M e : ℝ} (ha : 0 < a)
    (hM : 0 < M) (he : e ≠ 0) (m : ℝ) :
    ¬ Integrable (fun k : EuclideanSpace ℝ (Fin 4) =>
      contactTrace a M m e (‖k‖ ^ 2)) := by
  apply not_integrable_inverse_linear_lower (C := 12 * a * e ^ 2) (b := M)
    (by positivity) hM
  intro k
  exact contactTrace_lower ha hM m ‖k‖ (norm_nonneg k)

end UV
