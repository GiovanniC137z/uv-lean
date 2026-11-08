import UV.Response
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries

/-! Pole coefficients are defined by their punctured limits. The Cauchy
formula identifies these actual coefficients with normalized contour
integrals, including vanishing residues and distinct pole locations. -/

noncomputable section
open Complex Filter Set Metric
open scoped Topology NNReal

namespace UV

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]

/-- The residue coefficient of an at-most-simple pole, defined by the
punctured limit rather than by a separately supplied contour integral. -/
def simplePoleResidue (f : ℂ → Z) (p : ℂ) : Z :=
  limUnder (𝓝[≠] p) (fun z => (z - p) • f z)

omit [CompleteSpace Z] in
/-- A holomorphic pole numerator determines the actual residue coefficient. -/
theorem simplePole_residue {f G : ℂ → Z} {c p : ℂ} {r : ℝ}
    (hp : p ∈ ball c r) (hG : DifferentiableOn ℂ G (closedBall c r))
    (hf : ∀ z ∈ closedBall c r, z ≠ p → f z = (z - p)⁻¹ • G z) :
    simplePoleResidue f p = G p := by
  have hlim : Tendsto (fun z => (z - p) • f z) (𝓝[≠] p) (𝓝 (G p)) := by
    have hc := (hG.differentiableAt (closedBall_mem_nhds_of_mem hp)).continuousAt
    apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    have hb : ∀ᶠ z in 𝓝[≠] p, z ∈ closedBall c r :=
      Filter.mem_of_superset (nhdsWithin_le_nhds (closedBall_mem_nhds_of_mem hp)) (fun _ h => h)
    filter_upwards [self_mem_nhdsWithin, hb] with z hz hbz
    have hzp : z ≠ p := hz
    rw [hf z hbz hzp, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hzp), one_smul]
  exact hlim.limUnder_eq

omit [CompleteSpace Z] in
/-- An at-most-simple pole with a holomorphic numerator is integrable on any
circle enclosing the pole and lying in its holomorphic domain. -/
theorem simplePole_circleIntegrable {f G : ℂ → Z} {c p : ℂ} {r : ℝ}
    (hp : p ∈ ball c r) (hG : DifferentiableOn ℂ G (closedBall c r))
    (hf : ∀ z ∈ closedBall c r, z ≠ p → f z = (z - p)⁻¹ • G z) :
    CircleIntegrable f c r := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hp
  have hne : ∀ z ∈ sphere c r, z ≠ p := fun z hz =>
    ne_of_mem_of_not_mem hz (ne_of_lt hp)
  have hc : ContinuousOn (fun z => (z - p)⁻¹ • G z) (sphere c r) :=
    ((continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz => sub_ne_zero.mpr (hne z hz))).smul
      (hG.continuousOn.mono sphere_subset_closedBall)
  apply (hc.congr (fun z hz => hf z (sphere_subset_closedBall hz) (hne z hz))).circleIntegrable hr.le

/-- The normalized Cauchy integral equals the actual simple-pole residue.
The residue is allowed to vanish. -/
theorem simplePole_circle_integral {f G : ℂ → Z} {c p : ℂ} {r : ℝ}
    (hp : p ∈ ball c r) (hG : DifferentiableOn ℂ G (closedBall c r))
    (hf : ∀ z ∈ closedBall c r, z ≠ p → f z = (z - p)⁻¹ • G z) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • circleIntegral f c r = simplePoleResidue f p := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hp
  rw [simplePole_residue hp hG hf]
  have he : circleIntegral f c r =
      circleIntegral (fun z => (z - p)⁻¹ • G z) c r := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    exact hf z (sphere_subset_closedBall hz) (ne_of_mem_of_not_mem hz (ne_of_lt hp))
  rw [he, hG.circleIntegral_sub_inv_smul hp, inv_smul_smul₀]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- Observable residue error for a circle, with actual residues at possibly
different enclosed poles. This upgrades the contour error to a residue error. -/
theorem simplePole_residue_error {fX fY GX GY : ℂ → Z} {c pX pY : ℂ} {r C : ℝ}
    (hpX : pX ∈ ball c r) (hpY : pY ∈ ball c r)
    (hGX : DifferentiableOn ℂ GX (closedBall c r))
    (hGY : DifferentiableOn ℂ GY (closedBall c r))
    (hfX : ∀ z ∈ closedBall c r, z ≠ pX → fX z = (z - pX)⁻¹ • GX z)
    (hfY : ∀ z ∈ closedBall c r, z ≠ pY → fY z = (z - pY)⁻¹ • GY z)
    (hbound : ∀ z ∈ sphere c r, ‖fX z - fY z‖ ≤ C) :
    ‖simplePoleResidue fX pX - simplePoleResidue fY pY‖ ≤ r * C := by
  rw [← simplePole_circle_integral hpX hGX hfX, ← simplePole_circle_integral hpY hGY hfY]
  exact response_circle_integral_error (le_of_lt (lt_of_le_of_lt dist_nonneg hpX))
    (simplePole_circleIntegrable hpX hGX hfX) (simplePole_circleIntegrable hpY hGY hfY) hbound

omit [NormedSpace ℂ Z] [CompleteSpace Z] in
/-- The strict approximate residue margin certifies a nonzero exact residue,
including its evaluation error through the supplied lower bound. -/
theorem pole_residue_nonzero_of_error {RX RY : Z} {error lower : ℝ}
    (herr : ‖RX - RY‖ ≤ error) (hlower : lower ≤ ‖RY‖) (hmargin : error < lower) :
    RX ≠ 0 := by
  intro hzero
  rw [hzero, zero_sub, norm_neg] at herr
  linarith

omit [CompleteSpace Z] in
/-- A continuous readout has zero simple-pole residue; a certified nonzero
residue therefore detects an actual singularity of that readout. -/
theorem simplePole_residue_of_continuous {f : ℂ → Z} {p : ℂ} (hf : ContinuousAt f p) :
    simplePoleResidue f p = 0 := by
  have hc : ContinuousAt (fun z : ℂ => (z - p) • f z) p :=
    (continuousAt_id.sub_const p).smul hf
  have hlim : Tendsto (fun z : ℂ => (z - p) • f z) (𝓝[≠] p) (𝓝 (0 : Z)) := by
    simpa only [sub_self, zero_smul] using hc.tendsto.mono_left
      (show (𝓝[≠] p) ≤ 𝓝 p from nhdsWithin_le_nhds)
  exact hlim.limUnder_eq

omit [CompleteSpace Z] in
theorem simplePole_not_continuous_of_residue_ne_zero {f : ℂ → Z} {p : ℂ}
    (hres : simplePoleResidue f p ≠ 0) : ¬ ContinuousAt f p := by
  intro hc
  exact hres (simplePole_residue_of_continuous hc)

omit [CompleteSpace Z] in
/-- A simple zero of the scalar denominator produces a holomorphic simple
pole numerator on the entire disk; this pole representation is constructed. -/
theorem simple_denominator_pole_numerator {k : ℂ → ℂ} {n : ℂ → Z}
    {c p : ℂ} {r : ℝ} (hp : p ∈ ball c r)
    (hk : DifferentiableOn ℂ k (closedBall c r))
    (hn : DifferentiableOn ℂ n (closedBall c r))
    (hkzero : k p = 0) (hderiv : deriv k p ≠ 0)
    (honly : ∀ z ∈ closedBall c r, z ≠ p → k z ≠ 0) :
    DifferentiableOn ℂ (fun z => (dslope k p z)⁻¹ • n z) (closedBall c r) ∧
      (∀ z ∈ closedBall c r, z ≠ p →
        (k z)⁻¹ • n z = (z - p)⁻¹ • ((dslope k p z)⁻¹ • n z)) := by
  have hd := (Complex.differentiableOn_dslope (closedBall_mem_nhds_of_mem hp)).mpr hk
  have hdne : ∀ z ∈ closedBall c r, dslope k p z ≠ 0 := by
    intro z hz
    by_cases hzp : z = p
    · simpa only [hzp, dslope_same] using hderiv
    · rw [dslope_of_ne _ hzp]
      simp only [slope, hkzero, vsub_eq_sub, sub_zero, smul_eq_mul]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hzp)) (honly z hz hzp)
  refine ⟨(hd.inv hdne).smul hn, ?_⟩
  intro z hz hzp
  rw [dslope_of_ne _ hzp]
  simp only [slope, hkzero, vsub_eq_sub, sub_zero, smul_eq_mul, smul_smul]
  congr 1
  field_simp [sub_ne_zero.mpr hzp]

omit [CompleteSpace Z] in
/-- The actual residue at a simple scalar denominator zero is the numerator
divided by the derivative, derived without postulating a residue formula. -/
theorem simple_denominator_residue {k : ℂ → ℂ} {n : ℂ → Z}
    {c p : ℂ} {r : ℝ} (hp : p ∈ ball c r)
    (hk : DifferentiableOn ℂ k (closedBall c r))
    (hn : DifferentiableOn ℂ n (closedBall c r))
    (hkzero : k p = 0) (hderiv : deriv k p ≠ 0)
    (honly : ∀ z ∈ closedBall c r, z ≠ p → k z ≠ 0) :
    simplePoleResidue (fun z => (k z)⁻¹ • n z) p = (deriv k p)⁻¹ • n p := by
  obtain ⟨hG, hf⟩ := simple_denominator_pole_numerator hp hk hn hkzero hderiv honly
  simpa only [dslope_same] using simplePole_residue hp hG hf

/-- Actual simple-denominator observables obey the circle residue bound.
The holomorphic pole numerators are constructed from their unique simple
denominator zeros, rather than assumed as residue data. -/
theorem simple_denominator_residue_error {kX kY : ℂ → ℂ} {nX nY : ℂ → Z}
    {c pX pY : ℂ} {r C : ℝ}
    (hpX : pX ∈ ball c r) (hpY : pY ∈ ball c r)
    (hkX : DifferentiableOn ℂ kX (closedBall c r))
    (hkY : DifferentiableOn ℂ kY (closedBall c r))
    (hnX : DifferentiableOn ℂ nX (closedBall c r))
    (hnY : DifferentiableOn ℂ nY (closedBall c r))
    (hkXzero : kX pX = 0) (hkYzero : kY pY = 0)
    (hderivX : deriv kX pX ≠ 0) (hderivY : deriv kY pY ≠ 0)
    (honlyX : ∀ z ∈ closedBall c r, z ≠ pX → kX z ≠ 0)
    (honlyY : ∀ z ∈ closedBall c r, z ≠ pY → kY z ≠ 0)
    (hbound : ∀ z ∈ sphere c r, ‖(kX z)⁻¹ • nX z - (kY z)⁻¹ • nY z‖ ≤ C) :
    ‖simplePoleResidue (fun z => (kX z)⁻¹ • nX z) pX -
      simplePoleResidue (fun z => (kY z)⁻¹ • nY z) pY‖ ≤ r * C := by
  obtain ⟨hGX, hfX⟩ := simple_denominator_pole_numerator hpX hkX hnX hkXzero hderivX honlyX
  obtain ⟨hGY, hfY⟩ := simple_denominator_pole_numerator hpY hkY hnY hkYzero hderivY honlyY
  exact simplePole_residue_error hpX hpY hGX hGY hfX hfY hbound

/-- The full inverse/readout circle bound applies to the actual residues
once the two at-most-simple pole numerators are holomorphic. Neither their
residues nor their pole positions are assumed equal or nonzero. -/
theorem observable_simplePole_residue_error
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]
    (KX KY : ℂ → H →L[ℂ] H) (U : ℂ → H →L[ℂ] K) (V : ℂ → K →L[ℂ] H)
    (GX GY : ℂ → K →L[ℂ] K) {c pX pY : ℂ} {r B ε Lout Lin : ℝ}
    (hpX : pX ∈ ball c r) (hpY : pY ∈ ball c r)
    (hGX : DifferentiableOn ℂ GX (closedBall c r))
    (hGY : DifferentiableOn ℂ GY (closedBall c r))
    (hfX : ∀ z ∈ closedBall c r, z ≠ pX →
      (U z).comp ((Ring.inverse (KX z)).comp (V z)) = (z - pX)⁻¹ • GX z)
    (hfY : ∀ z ∈ closedBall c r, z ≠ pY →
      (U z).comp ((Ring.inverse (KY z)).comp (V z)) = (z - pY)⁻¹ • GY z)
    (hε0 : 0 ≤ ε) (hLo : 0 ≤ Lout) (hq : B * ε < 1)
    (hKY : ∀ z ∈ sphere c r, IsUnit (KY z))
    (hB : ∀ z ∈ sphere c r, ‖Ring.inverse (KY z)‖ ≤ B)
    (hε : ∀ z ∈ sphere c r, ‖KX z - KY z‖ ≤ ε)
    (hU : ∀ z ∈ sphere c r, ‖U z‖ ≤ Lout)
    (hV : ∀ z ∈ sphere c r, ‖V z‖ ≤ Lin) :
    ‖simplePoleResidue (fun z => (U z).comp ((Ring.inverse (KX z)).comp (V z))) pX -
      simplePoleResidue (fun z => (U z).comp ((Ring.inverse (KY z)).comp (V z))) pY‖ ≤
      r * Lout * Lin * B ^ 2 * ε / (1 - B * ε) := by
  have hr : 0 ≤ r := (lt_of_le_of_lt dist_nonneg hpX).le
  rw [← simplePole_circle_integral hpX hGX hfX, ← simplePole_circle_integral hpY hGY hfY]
  have he : ∀ z, KY z - (KY z - KX z) = KX z := by intro z; abel
  have hx : CircleIntegrable
      (fun z => (U z).comp ((Ring.inverse (KY z - (KY z - KX z))).comp (V z))) c r := by
    simp_rw [he]
    exact simplePole_circleIntegrable hpX hGX hfX
  have h := response_observable_circle_error KY (fun z => KY z - KX z) U V
    hr hε0 hLo hq hKY hB
    (fun z hz => by simpa only [norm_sub_rev] using hε z hz) hU hV hx
    (simplePole_circleIntegrable hpY hGY hfY)
  simpa only [he] using h

/-- The source's contour margin certifies boundary invertibility for complex
bookkeeping parameters, preserving the ordered affine pencil. -/
theorem pole_complex_parameter_inverse
    {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [NormOneClass R] [CompleteSpace R]
    {A D : R} {θ : ℝ} (hA : IsUnit A) (hmargin : ‖Ring.inverse A * D‖ ≤ θ)
    {l : ℂ} (hl : ‖l‖ * θ < 1) : IsUnit (A + l • D) := by
  have ht : ‖-(l • (Ring.inverse A * D))‖ ≤ ‖l‖ * θ := by
    rw [norm_neg, norm_smul]
    exact mul_le_mul_of_nonneg_left hmargin (norm_nonneg _)
  have hu := (response_inverse_one_sub_bound ht hl).1
  have he : A * (1 - -(l • (Ring.inverse A * D))) = A + l • D := by
    rw [sub_neg_eq_add, mul_add, mul_one, mul_smul_comm, ← mul_assoc,
      Ring.mul_inverse_cancel A hA, one_mul]
  exact he ▸ hA.mul hu

/-- The boundary inverse is holomorphic in the entire complex parameter
domain certified by the Neumann margin. This does not assume root counts. -/
theorem pole_complex_parameter_inverse_analytic
    {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [NormOneClass R] [CompleteSpace R]
    {A D : R} {θ : ℝ} (hA : IsUnit A) (hmargin : ‖Ring.inverse A * D‖ ≤ θ) :
    AnalyticOnNhd ℂ (fun l : ℂ => Ring.inverse (A + l • D)) {l : ℂ | ‖l‖ * θ < 1} := by
  apply analyticOnNhd_inverse.comp
    (fun _ _ => analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  intro l hl
  exact pole_complex_parameter_inverse hA hmargin hl

/-- Taylor coefficients are the actual iterated derivatives at zero. -/
def poleTaylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- Cauchy's coefficient bound on a closed circle of holomorphy. -/
theorem pole_cauchy_coefficient_bound {f : ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedBall 0 r))
    (hbound : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ R) (n : ℕ) :
    ‖poleTaylorCoeff f n‖ ≤ R * r⁻¹ ^ n := by
  let rn : ℝ≥0 := ⟨r, hr.le⟩
  have hp := hf.hasFPowerSeriesOnBall (R := rn) hr
  have hzero : closedBall (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds _ hr
  have heq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    ((hf.analyticAt hzero).hasFPowerSeriesAt)
  have hc : cauchyPowerSeries f 0 r n (fun _ => (1 : ℂ)) = poleTaylorCoeff f n := by
    have h := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => (1 : ℂ))) heq
    simpa [FormalMultilinearSeries.ofScalars, poleTaylorCoeff, rn] using h
  rw [← hc, cauchyPowerSeries_apply]
  calc
    _ ≤ r * (r⁻¹ ^ n * r⁻¹ * R) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le
      intro z hz
      have hzNorm : ‖z‖ = r := by simpa only [mem_sphere_zero_iff_norm] using hz
      simp only [sub_zero, one_div, norm_smul, norm_pow, norm_inv, hzNorm]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound z hz)
        (show 0 ≤ r⁻¹ ^ n * r⁻¹ by positivity)
    _ = _ := by field_simp

/-- The sharp coefficient estimate on the source's open parameter disk is
obtained by approaching its radius from below. -/
theorem pole_taylor_coefficient_bound {f : ℂ → ℂ} {θ R : ℝ}
    (hθ : 0 < θ) (hf : DifferentiableOn ℂ f (ball 0 θ⁻¹))
    (hbound : ∀ z ∈ ball (0 : ℂ) θ⁻¹, ‖f z‖ ≤ R) (n : ℕ) :
    ‖poleTaylorCoeff f n‖ ≤ R * θ ^ n := by
  have hrad : 0 < θ⁻¹ := inv_pos.mpr hθ
  have hlim : Tendsto (fun r : ℝ => R * r⁻¹ ^ n) (𝓝[<] θ⁻¹) (𝓝 (R * θ ^ n)) := by
    have hc : ContinuousAt (fun r : ℝ => R * r⁻¹ ^ n) θ⁻¹ :=
      continuousAt_const.mul ((continuousAt_id.inv₀ (ne_of_gt hrad)).pow n)
    simpa only [inv_inv] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hrad] with r hr
  apply pole_cauchy_coefficient_bound hr.1 (hf.mono (closedBall_subset_ball hr.2))
  intro z hz
  exact hbound z (closedBall_subset_ball hr.2 (sphere_subset_closedBall hz))

/-- The Taylor series at the physical endpoint is proved from complex
holomorphy on the entire certified parameter disk. -/
theorem pole_taylor_hasSum {f : ℂ → ℂ} {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hf : DifferentiableOn ℂ f (ball 0 θ⁻¹)) :
    HasSum (poleTaylorCoeff f) (f 1) := by
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) θ⁻¹ := by
    simp only [mem_ball_zero_iff, norm_one]
    exact (one_lt_inv₀ hθ).mpr hθ1
  have hs := Complex.hasSum_taylorSeries_on_ball hf h1
  convert hs using 1
  ext n
  simp [poleTaylorCoeff, div_eq_mul_inv, mul_comm]

/-- Exact geometric Taylor-tail certificate, with the source endpoint
constant and the actual Taylor coefficients. -/
theorem pole_taylor_remainder {f : ℂ → ℂ} {θ R : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hf : DifferentiableOn ℂ f (ball 0 θ⁻¹))
    (hbound : ∀ z ∈ ball (0 : ℂ) θ⁻¹, ‖f z‖ ≤ R) (N : ℕ) :
    ‖f 1 - ∑ n ∈ Finset.range (N + 1), poleTaylorCoeff f n‖ ≤
      R * θ ^ (N + 1) / (1 - θ) := by
  rw [norm_sub_rev]
  exact norm_sub_le_of_geometric_bound_of_hasSum hθ1
    (pole_taylor_coefficient_bound hθ hf hbound) (pole_taylor_hasSum hθ hθ1 hf) (N + 1)

/-- Source rate convention for a complex pole shift. -/
def poleShiftRate (shift : ℂ) : ℝ := -2 * shift.im

theorem pole_shift_rate_error (x y : ℂ) :
    |poleShiftRate x - poleShiftRate y| ≤ 2 * ‖x - y‖ := by
  calc
    _ = 2 * |(x - y).im| := by
      simp only [poleShiftRate, Complex.sub_im]
      calc
        _ = |(-2 : ℝ) * (x.im - y.im)| := by congr 1; ring
        _ = _ := by rw [abs_mul]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (by norm_num)

/-- Endpoint root enclosure gives the finite-rate enclosure at one fixed
baseline; this does not assert baseline-mode identification. -/
theorem finite_pole_rate_enclosure {zX zY baseline : ℂ} {r : ℝ}
    (hclose : ‖zX - zY‖ < r) :
    |poleShiftRate (zX - baseline) - poleShiftRate (zY - baseline)| < 2 * r := by
  have h := pole_shift_rate_error (zX - baseline) (zY - baseline)
  have he : (zX - baseline) - (zY - baseline) = zX - zY := by ring
  rw [he] at h
  linarith

/-- Decay of the final pole is exactly the stronger threshold stated in the
source, including a possibly unstable baseline. -/
theorem finite_pole_decay_iff (z baseline : ℂ) :
    2 * baseline.im < poleShiftRate (z - baseline) ↔ z.im < 0 := by
  simp only [poleShiftRate, Complex.sub_im]
  constructor <;> intro h <;> linarith

/-- The shifted pole's Taylor coefficient at zero vanishes, and its first
coefficient is the derivative of the actual pole branch. -/
theorem pole_shift_taylor_coefficients (z : ℂ → ℂ) :
    poleTaylorCoeff (fun l => z l - z 0) 0 = 0 ∧
      poleTaylorCoeff (fun l => z l - z 0) 1 = deriv z 0 := by
  simp [poleTaylorCoeff, iteratedDeriv_zero, iteratedDeriv_one, deriv_sub_const]

/-- The exact first-order finite-rate remainder from the holomorphic pole
branch, with the source's sharp geometric constant. Holomorphic construction
of the branch from a matrix-pencil contour is a separate obligation. -/
theorem pole_branch_rate_remainder {z : ℂ → ℂ} {θ R : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hz : DifferentiableOn ℂ z (ball 0 θ⁻¹))
    (hbound : ∀ l ∈ ball (0 : ℂ) θ⁻¹, ‖z l - z 0‖ ≤ R) :
    |poleShiftRate (z 1 - z 0) - poleShiftRate (deriv z 0)| ≤
      2 * R * θ ^ 2 / (1 - θ) := by
  have hrem := pole_taylor_remainder hθ hθ1 (hz.sub_const (z 0)) hbound 1
  have hc := pole_shift_taylor_coefficients z
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc.1, hc.2] at hrem
  have hrate := pole_shift_rate_error (z 1 - z 0) (deriv z 0)
  exact hrate.trans ((mul_le_mul_of_nonneg_left hrem (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

/-- The source's complete error budget when a complementary block is
eliminated. Domain and codomain types preserve the displayed product order. -/
theorem retained_complement_error
    {Hr Hc : Type*} [NormedAddCommGroup Hr] [NormedSpace ℂ Hr]
    [NormedAddCommGroup Hc] [NormedSpace ℂ Hc]
    (A At : Hr →L[ℂ] Hr) (B : Hc →L[ℂ] Hr) (D : Hc →L[ℂ] Hc) (C : Hr →L[ℂ] Hc) :
    ‖A - B.comp ((Ring.inverse D).comp C) - At‖ ≤
      ‖A - At‖ + ‖B‖ * ‖Ring.inverse D‖ * ‖C‖ := by
  have he : A - B.comp ((Ring.inverse D).comp C) - At =
      (A - At) - B.comp ((Ring.inverse D).comp C) := by abel
  rw [he]
  calc
    _ ≤ ‖A - At‖ + ‖B.comp ((Ring.inverse D).comp C)‖ := norm_sub_le _ _
    _ ≤ ‖A - At‖ + ‖B‖ * (‖Ring.inverse D‖ * ‖C‖) := by
      gcongr
      exact (B.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left ((Ring.inverse D).opNorm_comp_le C) (norm_nonneg _))
    _ = _ := by ring

/-- Exact elimination transports both endpoint maps. The hypotheses are the
two actual block equations, with invertible complementary and Schur blocks;
the response identity is derived by solving them. -/
theorem schur_source_readout
    {Hr Hc O : Type*} [NormedAddCommGroup Hr] [NormedSpace ℂ Hr]
    [NormedAddCommGroup Hc] [NormedSpace ℂ Hc]
    [NormedAddCommGroup O] [NormedSpace ℂ O]
    (A : Hr →L[ℂ] Hr) (B : Hc →L[ℂ] Hr) (C : Hr →L[ℂ] Hc) (D : Hc →L[ℂ] Hc)
    (hD : IsUnit D) (hS : IsUnit (A - B.comp ((Ring.inverse D).comp C)))
    (Lr : Hr →L[ℂ] O) (Lc : Hc →L[ℂ] O)
    (Jr xr : Hr) (Jc xc : Hc)
    (hret : A xr + B xc = Jr) (hcomp : C xr + D xc = Jc) :
    Lr xr + Lc xc =
      (Lr - Lc.comp ((Ring.inverse D).comp C))
        ((Ring.inverse (A - B.comp ((Ring.inverse D).comp C)))
          (Jr - B ((Ring.inverse D) Jc))) + Lc ((Ring.inverse D) Jc) := by
  have hxc : xc = (Ring.inverse D) (Jc - C xr) := by
    have hc : D xc = Jc - C xr := by rw [← hcomp]; abel
    have hh := congrArg (fun v => (Ring.inverse D) v) hc
    change ((Ring.inverse D * D) xc) = _ at hh
    rw [Ring.inverse_mul_cancel D hD, ContinuousLinearMap.one_apply] at hh
    exact hh
  have hschur : (A - B.comp ((Ring.inverse D).comp C)) xr =
      Jr - B ((Ring.inverse D) Jc) := by
    rw [hxc] at hret
    simp only [map_sub] at hret
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    rw [← hret]
    abel
  have hxr : xr = (Ring.inverse (A - B.comp ((Ring.inverse D).comp C)))
      (Jr - B ((Ring.inverse D) Jc)) := by
    have hh := congrArg (fun v =>
      (Ring.inverse (A - B.comp ((Ring.inverse D).comp C))) v) hschur
    change ((Ring.inverse (A - B.comp ((Ring.inverse D).comp C)) *
      (A - B.comp ((Ring.inverse D).comp C))) xr) = _ at hh
    rw [Ring.inverse_mul_cancel _ hS, ContinuousLinearMap.one_apply] at hh
    exact hh
  calc
    _ = (Lr - Lc.comp ((Ring.inverse D).comp C)) xr + Lc ((Ring.inverse D) Jc) := by
      rw [hxc]
      simp only [map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
      abel
    _ = _ := by rw [hxr]

end UV
